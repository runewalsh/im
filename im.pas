{$mode objfpc} {$h+} {$typedaddress+} {$macro on} {$modeswitch duplicatelocals+} {$modeswitch typehelpers+} {$scopedenums+}
{$ifopt Q+} {$define assert} {$else} {$ifdef assert} {$error} {$endif} {$endif}
{$R *.res}
program im;

uses
	CTypes, Windows;

// Повторяет times раз фрагмент rep, с repid от 0 до times - 1.
// Например, {$define rep := {$if repid > 0} + {$endif} A[repid]} {$define times := 3} pp_repeat преобразуется в A[0] + A[1] + A[2].
{$define pp_repeat := {$if defined(repid)} {$error pp_repeat would hide defines} {$endif}
	{$if times >= 1} {$define repid := 0} rep {$endif} {$if times >= 2} {$define repid := 1} rep {$endif}
	{$if times >= 3} {$define repid := 2} rep {$endif} {$if times >= 4} {$define repid := 3} rep {$endif}
	{$if times >= 5} {$error too many repeats} {$endif} {$undef repid} {$undef times} {$undef rep}}

// Объявляет внутри объекта энум enum и константы, дублирующие его значения, чтобы вместо Object.EnumType.EnumValue можно было писать Object.EnumValue.
// Например, {$define enum := Channel} {$define items := Red _ 0 _ Green _ 1 _ Blue _ 2} преобразуется в
// type
//     Channel = (Red, Green, Blue);    // дословно: Channel = (Red := 0, Green := 1, Blue := 2);
// const
//     Red = Channel.Red;               //           Red = Channel(0);
//     Green = Channel.Green;           //           Green = Channel(1);
//     Blue = Channel.Blue;             //           Blue = Channel(2);
{$define declare_scoped_enum_with_shortcuts :=
	{$if defined(now_number) or defined(_)} {$error declare_scoped_enum_with_shortcuts would hide defines} {$endif}
	type
		enum = {$define _ := {$ifdef now_number} , {$undef now_number} {$else} := {$define now_number} {$endif}} (items); {$undef now_number}
	const
		{$define _ := {$ifdef now_number} ); {$undef now_number} {$else} = enum( {$define now_number} {$endif}} items _ {$undef now_number}
		{$undef enum} {$undef items} {$undef _}}

const
	EOL = LineEnding;
	CPU = {$if defined(CPU32)} 'x86' {$elseif defined(CPU64)} 'x64' {$else} {$error unknown CPU} {$endif};

type
	widestring = unicodestring;
	UTFchar = type uint32;
	FilePos = type uint64;
	FileSize = type uint64;
	casint = int32;
	sint = int32; uint = uint32;
	float = single;

{$define impl :=
	function ToString(const x: typename): string; begin str(x, result); end;
	function TryParse(const s: string; out v: typename; wrong: pSizeInt = nil): boolean;
	var
		code: word;
	begin
		val(s, v, code);
		result := code = 0;
		if not result and Assigned(wrong) then wrong^ := code;
	end;

	function min(const a, b: typename): typename; begin if a <= b then result := a else result := b; end;
	function max(const a, b: typename): typename; begin if a >= b then result := a else result := b; end; {$undef typename}}
	{$define typename := int32} impl {$define typename := uint32} impl  {$define typename := int64} impl {$define typename := uint64} impl
{$undef impl}

	function clamp(x, a, b: float): float;
	begin
		if (x >= a) and (x <= b) then result := x else
			if x > a then result := b else result := a;
	end;

type
	Exception = class;

	DLL = object
		class procedure Load(out lib: DLL; const fn: string; const fns: array of const); static;
		procedure Unload;
	private
		h: Windows.HANDLE;
		fptrs: array of pPointer;
	end;

	Win32 = object
	type
		NTSTATUS = record value: uint32; end;
		PTP_CALLBACK_INSTANCE = ^TP_CALLBACK_INSTANCE; TP_CALLBACK_INSTANCE = record end;
		PTP_CALLBACK_ENVIRON = ^TP_CALLBACK_ENVIRON; TP_CALLBACK_ENVIRON = record end;
		PTP_IO = ^TP_IO; TP_IO = record end;

		TP_IO_CALLBACK = procedure(Instance: PTP_CALLBACK_INSTANCE; Context: pointer;
			Overlapped: LPOVERLAPPED; IoResult: Windows.ULONG; NumberOfBytesTransferred: Windows.ULONG_PTR; Io: PTP_IO); stdcall;

		ErrorCode = object
		type
			Origin = (GetLastError, NTSTATUS);
		var
			value: dword;
			from: Origin;
			class function Create(value: dword; from: Origin): ErrorCode; static;
		end;

	class var
		CreateThreadpoolIo: function(fl: Windows.HANDLE; pfnio: TP_IO_CALLBACK; pv: pointer; pcbe: PTP_CALLBACK_ENVIRON): PTP_IO; stdcall;
		StartThreadpoolIo: procedure(pio: PTP_IO); stdcall;

		class procedure Init; static;
		class procedure Done; static;
		class function DescribeError(const code: ErrorCode): string; static;
		class function Error(const fmt: string; const args: array of const; const code: ErrorCode): Exception; static;
		class function FileError(const fn: string; const code: ErrorCode): Exception; static;
		class function OperationFailed(const what: string; const code: ErrorCode): Exception; static;
		class function Lowercase(const text: string): string; static;
		class procedure Warning(const what: string; const code: ErrorCode); static;
		class function CommandLineTail: string; static;

	const
		STATUS_CANCELLED = $C0000120;

	type
		QueryStringCallback = procedure(buf: pWideChar; nBuf: size_t; out len: size_t; param: pointer);
		UnparaQueryStringCallback = procedure(buf: pWideChar; nBuf: size_t; out len: size_t);
	const
		QUERY_STRING_LENGTH_UNKNOWN = High(size_t);
		class function QueryString(cb: QueryStringCallback; param: pointer; const ofWhat: string): widestring; static;
	private
		class procedure QueryModuleFileName(buf: pWideChar; nBuf: size_t; out len: size_t; param: pointer); static;

	strict private class var
		k32: DLL;
	end;

	operator :=(code: dword): Win32.ErrorCode; begin result := result.Create(code, result.Origin.GetLastError); end;
	operator :=(code: Win32.NTSTATUS): Win32.ErrorCode; begin result := result.Create(code.value, result.Origin.NTSTATUS); end;

type
	ThreadLock = object
		cs: CRITICAL_SECTION;
		ok: boolean;
		procedure Init;
		procedure Done;
		procedure Enter;
		procedure Leave;
	end;

	ThreadEvent = object
		h: HANDLE;
		procedure Init(manual: boolean; initialState: boolean = false);
		procedure Done;
		function OK: boolean;
		procedure &Set;
		procedure Reset;
		procedure Wait;
	end;

	Console = object
	{$define enum := Color} {$define items := Black _ 0 _ Maroon _ 1 _ Green _ 2 _ Olive _ 3 _ Navy _ 4 _ Purple _ 5 _ Teal _ 6 _ Silver _ 7 _
		Gray _ 8 _ Red _ 9 _ Lime _ 10 _ Yellow _ 11 _ Blue _ 12 _ Fuchsia _ 13 _ Aqua _ 14 _ White _ 15} declare_scoped_enum_with_shortcuts
	var
		procedure Init;
		procedure Done;
		function OK: boolean;
		procedure Write(const s: string);
		procedure Line(const s: string);
		procedure Colored(const s: string; baseCol: SizeInt = -1); procedure Colored(const s: string; baseCol: Color);
		procedure ColoredLine(const s: string);                    procedure ColoredLine(const s: string; baseCol: Color);
		class function Escape(const s: string): string; static;
	strict private
		lock: ThreadLock;
		hOut: HANDLE;
		hOutSet, handlerAdded, broken: boolean;
		defCol, defBg: Color;
		defAttrWoCol: word;
		class function CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; stdcall; static;
	type
		Piece = record
			data: string;
			color: cint; // энум или -1
		end;
		PiecesList = array of Piece;
		class function ParseMarkdown(const s: string): PiecesList; static;
		procedure UseWriteConsoleW(const text: string);

	public const
		ColorNames: array[Color] of string = ('0', 'r', 'g', 'rg', 'b', 'rb', 'gb', '.3', '.6', 'R', 'G', 'RG', 'B', 'RB', 'GB', '1');
	strict private const
		BitsToColor: array[0 .. 15] of Color = (Black, Navy, Green, Teal, Maroon, Purple, Olive, Gray, Silver, Blue, Lime, Aqua, Red, Fuchsia, Yellow, White);
		ColorToBits: array[Color] of word = (%0000, %0100, %0010, %0110, %0001, %0101, %0011, %1000, %0111, %1100, %1010, %1110, %1001, %1101, %1011, %1111);

	class var
		CtrlCHit: boolean;
	end;

	&File = object
	{$define enum := Flag} {$define items := Readable _ 0 _ Writeable _ 1 _ Existing _ 2 _ New _ 3 _ Temp _ 4} declare_scoped_enum_with_shortcuts
	type
		Flags = set of Flag;

		pOpenResult = ^OpenResult;
		OpenResult = object
			ok, exist: boolean;
			errmsg: string;
		const
			Empty: OpenResult = (ok: false; exist: false; errmsg: '');
		end;
		transferred_t = type SizeUint;

		IOStatus = object
			function OK: boolean;
			function Partial: boolean;
			function Cancelled: boolean;
			function Failed: boolean;
			function ToException: Exception;
		private
			req: pointer; // pIORequest
			code: Win32.ErrorCode;
			transferred: transferred_t;
			class function Create(req: pointer; const code: Win32.ErrorCode; const transferred: transferred_t; forceFail: boolean = false): IOStatus; static;
		const
			STRANGE_ERROR = High(DWORD) - 1; // code = STRANGE_ERROR обозначает случай, когда операция провалилась с code = 0 (ну мало ли).
		end;

		CompletionHandler = procedure(const status: IOStatus; param: pointer);

		class procedure Open(out f: &File; const fn: string; flags: Flags = [Flag.Readable]; r: pOpenResult = nil); static;
		procedure Close;
		procedure Invalidate;
		function Valid: boolean;
		procedure Read(const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler = nil; param: pointer = nil);
		procedure Write(const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler = nil; param: pointer = nil);
		function Size: FileSize;
		procedure CancelMyIORequests;

	const
		RW = [Readable, Writeable];

	strict private type
		pSharedHandle = ^SharedHandle;
		SharedHandle = object
			h: HANDLE;
			refcount: casint;
			fn: string;
			class function Create(h: HANDLE; const fn: string): pSharedHandle; static;
			function Ref: pSharedHandle;
			procedure Close(var ref: pSharedHandle);
		end;

		pIORequest = ^IORequest;
		IORequest = object
			ov: Windows.OVERLAPPED;
			h: pSharedHandle;
			size: SizeUint;
			write: boolean;
			onDone: CompletionHandler;
			param: pointer;
			data: array[0 .. 0] of ptruint;
		end;

		// Запоминает, какие папки были созданы впервые, чтобы была возможность удалить их, если понадобится
		// (например, если дерево сделано в ходе создания файла, но создание самого файла провалилось).
		// Так, для TryCreatePath('base\sub\folder\file.txt', ...), когда sub и folder не существовало, будет folders = ('base\sub', 'base\sub\folder').
		PathRollback = object
			type Folder = widestring;
			var folders: array of folder;
			const Empty: PathRollback = (folders: nil);
			procedure Rollback;
		end;
	strict private
		ref: pSharedHandle;
		class function TryCreatePath(const fn: string; out err: dword; out rollback: PathRollback): boolean; static;
		class procedure IOCompletionHandler(dwErrorCode: dword; dwNumberOfBytesTransfered: dword; lpOverlapped: Windows.LPOVERLAPPED); stdcall; static;
		class function CreateIORequest(h: pSharedHandle; const offset: FilePos; size, extraSize: SizeUint; write: boolean; onDone: CompletionHandler; param: pointer): pIORequest; static;
		class procedure CloseIORequest(a: pIORequest; const status: IOStatus); static;
		procedure IO(write: boolean; const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler; param: pointer);
		class procedure OnDoneSync(const status: IOStatus; param: pointer); static;
	strict private class var
		IOPending: casint;
		HeyNoIOPending: ThreadEvent;
		class procedure GlobalInitialize; static;
		class procedure GlobalFinalize; static;
	public
		class procedure WaitForAllIORequests; static;
	end;

type
	// Это чтобы можно было добавлять элементы в массивы одной строкой (к сожалению, на типобезопасность при этом кладётся болт):
	// Ary(a).Push(newItem, TypeInfo(a));
	//
	// вместо
	// SetLength(a, length(a) + 1);
	// a[High(a)] := newItem;
	//
	// Или, то же самое: ItemType(Ary(a).Grow(TypeInfo(a))^) := newItem;
	//
	// Q: Почему не дженерики?
	// A: Fatal: Internal error 200509181 и подобное.
	//
	// Q: Почему не дженерик-списки из FGL?
	// A: Все без исключения «стандартные» «правильные» решения, т. е. без публичных полей типа array of, будут иметь следующее ограничение:
	//    type Struct = record x, y: integer; end;
	//    var a: specialize TFPGList<Struct>;
	//    a[1].y := 5;
	//    Последняя строчка не скомпилируется. Array property перенаправляется в функцию, а функция в паскале не может вернуть l-value.
	Ary = type pointer;
	AryHelper = type helper for Ary
		function Grow(elemSize: size_t): pointer;         function Grow(arrayTypeInfo: pointer): pointer;
		function GrowBy(by, elemSize: size_t): pointer;   function GrowBy(by: size_t; arrayTypeInfo: pointer): pointer;
		procedure Push(const elem; arrayTypeInfo: pointer);
		function Empty: boolean;

	strict private const
		tkDynArray = 21;
	type
		pDynArrayHeader = ^DynArrayHeader;
		DynArrayHeader = record
			refcount: PtrInt;
			high: TDynArrayIndex;
		end;

		pDynArrayTypeData = ^DynArrayTypeData;
		DynArrayTypeData = {$if not defined(FPC_REQUIRES_PROPER_ALIGNMENT) or defined(powerpc64) and defined(VER3_0_0)} packed {$endif} record
			elSize : SizeUint;
			{$ifdef VER3_0} elType2 : Pointer; {$else} {$error} elType2 : PPointer; {$endif} // всегда заполнена
			varType : Longint;
			{$ifdef VER3_0} elTypeManaged : Pointer; {$else} {$error} elTypeManaged : PPointer; {$endif} // = nil, если элементы POD
		end;

		class function CreateNew(elems, elemSize: size_t): Ary; static;
		class function ExtractDynArrayTypeData(arrayTypeInfo: pointer): pDynArrayTypeData; static;
	end;

	StringHelper = type helper for string
		function Peek(pos: SizeInt; out len: SizeInt): UTFchar;
		function CodepointLen(pos: SizeInt): SizeInt;
		function ToUTF16: widestring;
		function Format(const args: array of const): string;
		function Prefixed(const p: string; pos: SizeInt = 1): boolean;
		function Tail(start: SizeInt): string;
		function Lowercase: string; function LowercaseFirst: string;
		function Stuffed(at, remove: SizeInt; const &with: string): string;

	const
		UTFInvalid = High(UTFchar);
		Tab = #9;

	type
		PAnsiRec = ^TAnsiRec;
		TAnsiRec = record
			cpes: record
			case uint of
				0: (CodePage: TSystemCodePage; ElementSize: Word);
				1: (Padding: SizeInt);
			end;
			ref: SizeInt;
			len: SizeInt;
		end;
		function AR: PAnsiRec;
	end;

	WidestringHelper = type helper for widestring
		function ToUTF8: string;
	end;

	VarRec = object
		class procedure AssertType(const v: TVarRec; expected: SizeInt; pos: SizeInt); static;
		class function VTypeToString(vt: SizeInt): string; static;
		class function ToString(const v: TVarRec): string; static;
	end;

	Exception = class
		msg: string;
		constructor Create(const msg: string);
		class function Message(obj: TObject): string; static;
	end;
	LogicError = class(Exception) end;
	OutOfMemory = class
	class var
		Instance: OutOfMemory;
		procedure FreeInstance; override;
		procedure FireAnEmergency;
	private
		CanDieNow: boolean;
		RainyDayReserve: pointer;
		procedure ReleaseReserve;
		class procedure InitGlobal; static;
		class procedure DoneGlobal; static;
	end;

	Session = object
	private
		class constructor Init;
		class procedure Done; static; // все правильно, разруливается через AddExitProc
		class function HumanTrace(frames: pCodePointer = nil; frameCount: SizeInt = -1): string; static;
		class procedure OnUnhandledException(Obj: TObject; Addr: CodePointer; FrameCount: LongInt; Frame: PCodePointer); static;
		class procedure OnRuntimeError(ErrNo: Longint; Address: CodePointer; Frame: Pointer); static;
		class procedure TestHacks; static;
	end;

var
	SingletonLock: ThreadLock;
	Con: Console;
	ExecRoot: string;

	class procedure DLL.Load(out lib: DLL; const fn: string; const fns: array of const);
	var
		i: SizeInt;
		prefix: string;
		parsed: array of record
			funcName: string;
			funcPtr: pPointer;
		end;
	begin
		lib.h := 0;
		lib.h := LoadLibraryW(pWideChar(fn.ToUTF16));
		if lib.h = 0 then raise Win32.Error('Не удалось загрузить {}. {Err.}', [fn], GetLastError);
		prefix := '';

		try
			parsed := nil;
			i := 0;
			while i < length(fns) do
			begin
				if (fns[i].VType = vtAnsiString) and ansistring(fns[i].VAnsiString).Prefixed('prefix=') then
				begin
					prefix := ansistring(fns[i].VAnsiString).Tail(length('prefix=') + 1);
					inc(i);
				end;

				SetLength(parsed, length(parsed) + 1);
				if fns[i].VType <> vtAnsiString then raise LogicError.Create('В позиции {} vt = {}, ожидается {} (vtAnsiString).'.Format([i, fns[i].VType, vtAnsiString]));
				parsed[High(parsed)].funcName := prefix + ansistring(fns[i].VAnsiString);
				inc(i); if i >= length(fns) then raise LogicError.Create('В позиции {} ожидается указатель на указатель на функцию.');

				if fns[i].VType <> vtPointer then raise LogicError.Create('В позиции {} vt = {}, ожидается {} (vtPpointer).'.Format([i, fns[i].VType, vtPointer]));
				parsed[High(parsed)].funcPtr := fns[i].VPointer;
				inc(i);
			end;

			SetLength(lib.fptrs, length(parsed));
			for i := 0 to High(parsed) do
			begin
				lib.fptrs[i] := parsed[i].funcPtr;
				lib.fptrs[i]^ := GetProcAddress(lib.h, pChar(parsed[i].funcName));
				if not Assigned(lib.fptrs[i]^) then
					raise Exception.Create('Функция {} не найдена в {}.'.Format([parsed[i].funcName, fn]));
			end;
		except
			lib.Unload;
			raise;
		end;
	end;

	procedure DLL.Unload;
	var
		i: SizeInt;
	begin
		for i := 0 to High(fptrs) do
			if Assigned(fptrs[i]) then fptrs[i]^ := nil;
		if (h <> 0) and not FreeLibrary(h) then Win32.Warning('FreeLibrary', GetLastError);
		h := 0;
	end;

	function GetFileSizeEx(hFile: HANDLE; lpFileSize: PLARGE_INTEGER): Windows.BOOL; stdcall; external kernel32;
	function BindIoCompletionCallback(FileHandle: Windows.HANDLE; func: LPOVERLAPPED_COMPLETION_ROUTINE; flags: Windows.ULONG): Windows.BOOL; stdcall; external kernel32;

	class function Win32.ErrorCode.Create(value: dword; from: Origin): Win32.ErrorCode;
	begin
		result.value := value;
		result.from := from;
	end;

	class procedure Win32.Init;
	var
		exe: string;
		p: SizeInt;
	begin
		DLL.Load(k32, kernel32, ['CreateThreadpoolIo', @CreateThreadpoolIo, 'StartThreadpoolIo', @StartThreadpoolIo]);
		exe := QueryString(QueryStringCallback(@Win32.QueryModuleFileName), nil, 'имени исполняемого файла').ToUTF8;
		p := length(exe);
		while (p > 0) and not (exe[p] in ['\', '/']) do dec(p);
		ExecRoot := Copy(exe, 1, p);
	end;

	class procedure Win32.Done;
	begin
		k32.Unload;
	end;

	class function Win32.DescribeError(const code: ErrorCode): string; static;
	var
		werr: widestring;
		scode: string;
		fflags: dword;
		ptr, fsrc: pointer;
		dll: im.DLL;
	begin
		result := '';
		if code.value = 0 then
			result := 'Причина неизвестна.'
		else
		begin
			if code.from = code.Origin.NTSTATUS then dll.Load(dll, 'NTDLL.DLL', []);
			fflags := FORMAT_MESSAGE_ALLOCATE_BUFFER or FORMAT_MESSAGE_FROM_SYSTEM or FORMAT_MESSAGE_IGNORE_INSERTS or FORMAT_MESSAGE_MAX_WIDTH_MASK;
			fsrc := nil;
			if code.from = code.Origin.NTSTATUS then
			begin
				fflags := fflags or FORMAT_MESSAGE_FROM_HMODULE;
				pPtrUint(@fsrc)^ := dll.h;
			end;
			if FormatMessageW(fflags, fsrc, code.value, 0, pWideChar(@ptr), 0, nil) > 0 then
			begin
				werr := pWideChar(ptr);
				if Assigned(ptr) then HeapFree(GetProcessHeap, 0, ptr);
				result := werr.ToUTF8;
				while (length(result) > 0) and (result[length(result)] = ' ') do SetLength(result, length(result) - 1);
			end;
			if code.from = code.Origin.NTSTATUS then dll.Unload;
		end;

		if code.from = code.Origin.NTSTATUS then scode := HexStr(code.value, bitsizeof(Win32.NTSTATUS) div 4) else scode := ToString(code.value);
		if result = '' then result := 'Ошибка с кодом {}.'.Format([scode]) else result += ' ({})'.Format([scode]);
	end;

	class function Win32.Error(const fmt: string; const args: array of const; const code: ErrorCode): Exception;
	type
		Shortcut = (TitleError, LowercaseError);
	const
		Shortcuts: array[Shortcut] of string = ('{Err.}', '{err.}');
	var
		i, p: SizeInt;
		fmt2: string;
		args2: array of TVarRec;
		sc: Shortcut;
		storage: array[Shortcut] of string;

	begin
		fmt2 := fmt;
		SetLength(args2, length(args));
		for i := 0 to High(args2) do args2[i] := args[i];

		for sc in Shortcut do
		begin
			p := Pos(Shortcuts[sc], fmt2);
			if p > 0 then
			begin
				storage[sc] := DescribeError(code);
				if sc = Shortcut.LowercaseError then storage[sc] := storage[sc].LowercaseFirst;
				TVarRec(Ary(args2).Grow(sizeof(TVarRec))^).VType := vtAnsiString;
				pointer(args2[High(args2)].VAnsiString) := pointer(storage[sc]);
				fmt2 := fmt2.Stuffed(p, length(Shortcuts[sc]), '{{{}}'.Format([High(args2)]));
			end;
		end;
		result := Exception.Create(fmt2.Format(args2));
	end;

	class function Win32.FileError(const fn: string; const code: ErrorCode): Exception;
	begin
		result := Error('{}: {err.}', [fn], code);
	end;

	class function Win32.OperationFailed(const what: string; const code: ErrorCode): Exception;
	begin
		result := Error('Не удалось {}: {err.}', [what], code);
	end;

	class function Win32.Lowercase(const text: string): string;
	var
		ws: widestring;
	begin
		ws := text.ToUTF16;
		CharLowerW(pWideChar(ws));
		result := ws.ToUTF8;
	end;

	class procedure Win32.Warning(const what: string; const code: ErrorCode);
	begin
		writeln(stderr, what.ToUTF16, ': ', DescribeError(code).LowercaseFirst.ToUTF16);
	end;

	class function Win32.CommandLineTail: string;
	var
		i, d: SizeInt;
	begin
		result := widestring(GetCommandLineW).ToUTF8;
		// отрезать argv[0], https://stackoverflow.com/a/36876057
		i := 0;
		if pChar(result)[i] = '"' then
		begin
			d := IndexChar(pChar(result)[i+1], length(result) - i - 1, '"');
			if d >= 0 then i += d + 2;
		end else
			while not (pChar(result)[i] in [#0, ' ', StringHelper.Tab]) do inc(i);
		while pChar(result)[i] in [' ', StringHelper.Tab] do inc(i);
		delete(result, 1, i);
	end;

	class function Win32.QueryString(cb: QueryStringCallback; param: pointer; const ofWhat: string): widestring;
	const
		ReasonableLimit = 16383;
	var
		len, report: size_t;
	begin
		len := 64;
		repeat
			SetLength(result, len);
			cb(pWideChar(result), len + ord(len > 0), report, param);
			if report <= len then exit(Copy(result, 1, report));
			if report = QUERY_STRING_LENGTH_UNKNOWN then
			begin
				if len = ReasonableLimit then raise Exception.Create('Неправдоподобная длина {}.'.Format([ofWhat]));
				len := min(2 * len, SizeUint(ReasonableLimit));
			end else
			begin
				if (report = len + 1) or (report - 1 > ReasonableLimit) then
					raise Exception.Create('Получена неправдоподобная длина {} ({}).'.Format([ofWhat, len]));
				len := report - 1;
			end;
		until false;
	end;

	class procedure Win32.QueryModuleFileName(buf: pWideChar; nBuf: size_t; out len: size_t; param: pointer);
	var
		r: dword;
	begin
		Assert(param = param);
		r := GetModuleFileNameW(0, buf, nBuf);
		if (r = 0) and (nBuf > 0) then raise OperationFailed('получить имя исполняемого файла (GetModuleFileName)', GetLastError);
		if r >= nBuf then len := QUERY_STRING_LENGTH_UNKNOWN else len := r;
	end;

	procedure ThreadLock.Init;
	begin
		Assert(not ok);
		InitializeCriticalSection(cs);
		ok := true;
	end;

	procedure ThreadLock.Done;
	begin
		if ok then
		begin
			DeleteCriticalSection(cs);
			ok := false;
		end;
	end;
	procedure ThreadLock.Enter; begin EnterCriticalSection(cs); end;
	procedure ThreadLock.Leave; begin LeaveCriticalSection(cs); end;

	procedure ThreadEvent.Init(manual: boolean; initialState: boolean = false);
	begin
		Assert(h = 0);
		h := CreateEventW(nil, manual, initialState, nil);
		if h = 0 then raise Win32.OperationFailed('создать событие (CreateEvent)', GetLastError);
	end;

	procedure ThreadEvent.Done;
	begin
		if (h <> 0) and not CloseHandle(h) then Win32.Warning('CloseHandle', GetLastError);
		h := 0;
	end;

	function ThreadEvent.OK: boolean;
	begin
		result := h <> 0;
	end;

	procedure ThreadEvent.&Set; begin if not SetEvent(h) then raise Win32.OperationFailed('выставить событие (SetEvent)', GetLastError); end;
	procedure ThreadEvent.Reset; begin if not ResetEvent(h) then raise Win32.OperationFailed('сбросить событие (ResetEvent)', GetLastError); end;
	procedure ThreadEvent.Wait;
	var
		r: dword;
	begin
		r := WaitForSingleObject(h, INFINITE);
		if r <> WAIT_OBJECT_0 then
			if r = WAIT_FAILED then
				raise Win32.OperationFailed('подождать события (WaitForSingleObject)', GetLastError)
			else
				raise Exception.Create('WaitForSingleObject вернула {}'.Format([r]));
	end;

	procedure Console.Init;
	var
		info: CONSOLE_SCREEN_BUFFER_INFO;
	begin
		Assert(not hOutSet and not handlerAdded and not broken);
		try
			lock.Init;
			if not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), true) then
				raise Win32.OperationFailed('установить обработчик Ctrl-C (SetConsoleCtrlHandler)', GetLastError);
			handlerAdded := true;
			hOut := CreateFile('CONOUT$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_WRITE, nil, OPEN_EXISTING, 0, 0);
			if hOut = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для вывода', GetLastError);
			hOutSet := true;

			if not GetConsoleScreenBufferInfo(hOut, (@info)^) then raise Win32.OperationFailed('получить информацию от консоли (GetConsoleScreenBufferInfo)', GetLastError);
			defCol := BitsToColor[info.wAttributes and %1111];
			defBg := BitsToColor[info.wAttributes shr 4 and %1111];
			defAttrWoCol := info.wAttributes and not word(%11111111); // FOREGROUND_* и BACKGROUND_*
		except
			Done;
			raise;
		end;
	end;

	procedure Console.Done;
	begin
		if handlerAdded and not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), false) then Win32.Warning('SetConsoleCtrlHandler', GetLastError);
		handlerAdded := false;
		if hOutSet and (hOut <> INVALID_HANDLE_VALUE) and not CloseHandle(hOut) then Win32.Warning('CloseHandle', GetLastError);
		hOutSet := false; broken := false;
		lock.Done;
	end;
	function Console.OK: boolean; begin result := lock.ok; end;

	procedure Console.Write(const s: string);
	begin
		if hOutSet or broken then
		begin
			system.write(s.ToUTF16);
			exit;
		end;

		lock.Enter;
		try
			UseWriteConsoleW(s);
		finally
			lock.Leave;
		end;
	end;
	procedure Console.Line(const s: string); begin Write(s + EOL); end;

	procedure Console.Colored(const s: string; baseCol: SizeInt = -1);
	var
		pieces: PiecesList;
		i: SizeInt;
		activeColor, newColor, activeBg, newBg: Color;
	begin
		pieces := ParseMarkdown(s);
		if not hOutSet or broken then
		begin
			for i := 0 to High(pieces) do system.write(pieces[i].data);
			exit;
		end;

		lock.Enter;
		try
			activeColor := defCol; activeBg := defBg;
			for i := 0 to High(pieces) do
			begin
				if pieces[i].color >= 0 then newColor := Color(pieces[i].color) else if baseCol >= 0 then newColor := Color(baseCol) else newColor := defCol;
				if newColor = defBg then newBg := Color(ord(High(Color)) - ord(newColor)) else newBg := defBg;
				if (activeColor <> newColor) or (activeBg <> defBg) then SetConsoleTextAttribute(hOut, defAttrWoCol or ColorToBits[newColor] or ColorToBits[newBg] shl 4);
				activeColor := newColor;
				activeBg := newBg;
				UseWriteConsoleW(pieces[i].data);
			end;
			if (activeColor <> defCol) or (activeBg <> newBg) then SetConsoleTextAttribute(hOut, defAttrWoCol or ColorToBits[defCol] or ColorToBits[defBg] shl 4);
		finally
			lock.Leave;
		end;
	end;
	procedure Console.Colored(const s: string; baseCol: Color); begin Colored(s, ord(baseCol)); end;
	procedure Console.ColoredLine(const s: string); begin Colored(s + EOL); end;
	procedure Console.ColoredLine(const s: string; baseCol: Color); begin Colored(s + EOL, baseCol); end;

	class function Console.Escape(const s: string): string;
	var
		start, i: SizeInt;
	begin
		start := 1; i := 1; result := '';
		while i <= length(s) do
			case s[i] of
				'<':
					begin
						result += Copy(s, start, i - start + 1) + '<';
						start := i + 1; i := start;
					end;
				else inc(i);
			end;
		result += Copy(s, start, i - start + 1);
	end;

	class function Console.CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; stdcall;
	begin
		if dwCtrlType = CTRL_C_EVENT then
		begin
			// Внимание, система запускает этот обработчик в отдельном потоке, бросать исключение не вариант.
			result := true;
			CtrlCHit := true;
		end else
			result := false;
	end;

	class function Console.ParseMarkdown(const s: string): PiecesList;
	label nextsym;
		procedure Append(start, count: SizeInt; color: cint);
		begin
			Assert(count >= 0); if count = 0 then exit;
			if Ary(result).Empty or (result[High(result)].color <> color) then
				Piece(Ary(result).Grow(TypeInfo(result))^).color := color;
			result[High(result)].data += Copy(s, start, count);
		end;

	var
		start, i: SizeInt;
		csp: sint;
		colorStack: array[0 .. 15] of cint;
		c: Color;
	begin
		result := nil;
		start := 1;
		i := 1;
		colorStack[0] := -1; csp := 0;

		while i <= length(s) do
		begin
			case s[i] of
				'<':
					begin
						if (i + 1 <= length(s)) and (s[i + 1] = '<') then
						begin
							Append(start, i - start + 1, colorStack[csp]);
							start := i + 2; i := start; goto nextsym;
						end;
						if s.Prefixed('/>', i + 1) then
						begin
							if csp = 0 then raise Exception.Create('{}: антипереполнение стека цветов.'.Format([s.Stuffed(i, 0, '|')]));
							Append(start, i - start, colorStack[csp]);
							dec(csp);
							start := i + 3; i := start; goto nextsym;
						end;
						for c in Color do
							if s.Prefixed(ColorNames[c], i + 1) and (pChar(s)[i + length(ColorNames[c])] = '>') then
							begin
								if csp = High(colorStack) then raise Exception.Create('Переполнен стек цветов ({}).'.Format([High(colorStack)]));
								Append(start, i - start, colorStack[csp]);
								inc(csp); colorStack[csp] := ord(c);
								start := i + 1 + length(ColorNames[c]) + 1; i := start; goto nextsym;
							end;
					end;
			end;
			inc(i); nextsym:
		end;
		Append(start, i - start + 1, colorStack[csp]);
	end;

	procedure Console.UseWriteConsoleW(const text: string);
	const
		BlockSize = 4096;
	var
		ws: widestring;
		p: pWideChar;
		n: SizeUint;
		written: DWORD;
	begin
		ws := text.ToUTF16; p := pWideChar(ws);
		repeat
			n := min(length(ws) - (p - pWideChar(ws)), BlockSize);
			if not WriteConsoleW(hOut, p, n, (@written)^, nil) then begin broken := true; raise Win32.OperationFailed('WriteConsoleW', GetLastError); end;
			if written <> n then begin broken := true; raise Exception.Create('WriteConsoleW: n = {}, written = {}.'.Format([n, written])); end;
			p += n;
		until p = pWideChar(ws) + length(ws);
	end;

	function &File.IOStatus.OK: boolean; begin result := (code.value = 0) and (transferred = pIORequest(req)^.size); end;
	function &File.IOStatus.Partial: boolean; begin result := (code.value = 0) and (transferred <= pIORequest(req)^.size); end;
	function &File.IOStatus.Cancelled: boolean;
	begin
		result := (code.from = code.Origin.GetLastError) and (code.value = ERROR_OPERATION_ABORTED) or
			(code.from = code.Origin.NTSTATUS) and (code.value = Win32.STATUS_CANCELLED);
	end;
	function &File.IOStatus.Failed: boolean; begin result := code.value <> 0; end;

	function &File.IOStatus.ToException: Exception;
	const
		Fmt: array[boolean] of string = ('Из {} прочитано {} b (вместо {} b).', 'В {} записались {} b (вместо {} b).');
		RW: array[boolean] of string = ('чтения', 'записи');
	var
		c2: Win32.ErrorCode;
	begin
		if (code.value = 0) and (transferred < pIORequest(req)^.size) then
			result := Exception.Create(Fmt[pIORequest(req)^.write].Format([pIORequest(req)^.h^.fn, transferred, pIORequest(req)^.size]))
		else
		begin
			if code.value = STRANGE_ERROR then c2 := 0 else c2 := code;
			result := Win32.Error('Ошибка {} {}: {err.}', [RW[pIORequest(req)^.write], pIORequest(req)^.h^.fn], c2);
		end;
	end;

	class function &File.IOStatus.Create(req: pointer; const code: Win32.ErrorCode; const transferred: transferred_t; forceFail: boolean = false): IOStatus;
	begin
		result.req := req;
		result.code := code;
		if forceFail and (code.value = 0) then result.code.value := STRANGE_ERROR;
		result.transferred := transferred;
	end;

	class procedure &File.Open(out f: &File; const fn: string; flags: Flags; r: pOpenResult = nil);
	var
		wfn: widestring;
		access, share, disp, attrs, err: dword;
		tryId: uint;
		h: HANDLE;
		ok: boolean;
		rb: PathRollback;
	begin
		f.ref := nil;
		if not HeyNoIOPending.OK then
		begin
			SingletonLock.Enter;
			try
				if not HeyNoIOPending.OK then GlobalInitialize;
			finally
				SingletonLock.Leave;
			end;
		end;

		if Assigned(r) then r^ := OpenResult.Empty;
		rb := rb.Empty;

		wfn := fn.ToUTF16;
		access := 0;
		if Readable in flags then access := access or GENERIC_READ;
		if Writeable in flags then access := access or GENERIC_READ or GENERIC_WRITE; // без GENERIC_READ не работает mmap на запись :(
		share := 0;
		if (Readable in flags) and not (Writeable in flags) then share := share or FILE_SHARE_READ;
		if (Writeable in flags) and not (Existing in flags) then
			if New in flags then disp := CREATE_NEW
			else if Readable in flags then disp := OPEN_ALWAYS
			else disp := CREATE_ALWAYS
		else
		begin
			if New in flags then raise LogicError.Create('{}: New + RO?'.Format([fn]));
			disp := OPEN_EXISTING;
		end;

		attrs := FILE_FLAG_OVERLAPPED;
		if Temp in flags then attrs := attrs or FILE_ATTRIBUTE_TEMPORARY or FILE_FLAG_DELETE_ON_CLOSE;

		tryId := 0;
		repeat
			h := CreateFileW(pWideChar(wfn), access, share, nil, disp, attrs, 0);
			inc(tryId);
			ok := h <> INVALID_HANDLE_VALUE;
			if not ok or Assigned(r) then err := GetLastError;
		until ok or (tryId > 1) or not ((Writeable in flags) and (err = ERROR_PATH_NOT_FOUND) and TryCreatePath(fn, err, rb));

		if ok then
			try
				f.ref := SharedHandle.Create(h, fn);
			except
				CloseHandle(h);
				rb.Rollback;
				raise;
			end;

		if Assigned(r) then
		begin
			r^.ok := ok;
			case disp of
				CREATE_ALWAYS, OPEN_ALWAYS: r^.exist := ok and (err = ERROR_ALREADY_EXISTS);
				CREATE_NEW:                 r^.exist := not ok and (err = ERROR_FILE_EXISTS);
				else                        r^.exist := ok and (Existing in flags);
			end;
			if not ok then r^.errmsg := Win32.DescribeError(err);
		end else
			if not ok then raise Win32.FileError(fn, err);
	end;

	procedure &File.Close;
	begin
		ref^.Close(ref);
	end;

	procedure &File.Invalidate; begin ref := nil; end;
	function &File.Valid: boolean; begin result := Assigned(ref); end;

	procedure &File.Read(const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler = nil; param: pointer = nil);
	begin
		IO(false, at, buf, size, onDone, param);
	end;


	procedure &File.Write(const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler = nil; param: pointer = nil);
	begin
		IO(true, at, buf, size, onDone, param);
	end;

	function &File.Size: FileSize;
	var
		sz: LARGE_INTEGER;
	begin
		if GetFileSizeEx(ref^.h, @sz) then result := sz.QuadPart else raise Win32.OperationFailed('получить размер файла (GetFileSizeEx)', GetLastError);
	end;

	procedure &File.CancelMyIORequests;
	begin
		if not CancelIO(ref^.h) then
			raise Exception.Create('{}: не удалось отменить I/O (CancelIO), {}.'.Format([ref^.fn, Win32.DescribeError(GetLastError).LowercaseFirst]));
	end;

	class function &File.SharedHandle.Create(h: HANDLE; const fn: string): pSharedHandle;
	var
		code: dword;
	begin
		system.new(result); result^.h := h; result^.fn := fn; result^.refcount := 1;
		try
			if not BindIoCompletionCallback(h, LPOVERLAPPED_COMPLETION_ROUTINE(@&File.IOCompletionHandler), 0) then
			begin
				code := GetLastError;
				raise Win32.OperationFailed('назначить асинхронный обработчик I/O для {} (BindIoCompletionCallback)'.Format([fn]), code);
			end;
		except
			result^.Close(result);
			raise;
		end;
	end;

	function &File.SharedHandle.Ref: pSharedHandle;
	begin
		InterlockedIncrement(refcount);
		result := @self;
	end;

	procedure &File.SharedHandle.Close(var ref: pSharedHandle);
	begin
		Assert(ref = @self);
		if Assigned(@self) then
		begin
			if InterlockedDecrement(refcount) = 0 then
			begin
				CloseHandle(h);
				dispose(@self);
			end;
			ref := nil;
		end;
	end;

	procedure &File.PathRollback.Rollback;
	var
		i: SizeInt;
	begin
		for i := High(folders) downto 0 do
			if not RemoveDirectoryW(pWideChar(folders[i])) then Win32.Warning('RemoveDirectoryW', GetLastError);
		folders := nil;
	end;

	class function &File.TryCreatePath(const fn: string; out err: dword; out rollback: PathRollback): boolean;
	var
		i: SizeInt;
		dir: widestring;
	begin
		rollback := rollback.Empty;
		i := 1;
		while i <= length(fn) do
		begin
			if fn[i] in ['\', '/'] then
				if (i-1 >= 0) and not (fn[i-1] in [':', '\', '/']) then // E:
				begin
					dir := Copy(fn, 1, i-1).ToUTF16;
					if CreateDirectoryW(pWideChar(dir), nil) then
						Ary(rollback.folders).Push(Rollback.Folder(dir), TypeInfo(rollback.folders))
					else
					begin
						err := GetLastError;
						if err = ERROR_ALREADY_EXISTS then
							rollback.folders := nil // на всякий случай
						else
						begin
							rollback.Rollback;
							exit(false);
						end;
					end;
				end;
			inc(i);
		end;
		result := true;
	end;

	class procedure &File.IOCompletionHandler(dwErrorCode: dword; dwNumberOfBytesTransfered: dword; lpOverlapped: Windows.LPOVERLAPPED); stdcall;
	var
		req: pIORequest absolute lpOverlapped;
	begin
		CloseIORequest(req, IOStatus.Create(req, Win32.NTSTATUS(dwErrorCode), dwNumberOfBytesTransfered));
	end;

	class function &File.CreateIORequest(h: pSharedHandle; const offset: FilePos; size, extraSize: SizeUint; write: boolean; onDone: CompletionHandler; param: pointer): pIORequest;
	begin
		if InterlockedIncrement(IOPending) = 1 then HeyNoIOPending.Reset;
		result := GetMem(sizeof(IORequest) - sizeof(IORequest.data) + extraSize);
		result^.ov.Internal     := 0;
		result^.ov.InternalHigh := 0;
		result^.ov.hEvent       := 0;
		result^.ov.Offset       := Lo(offset);
		result^.ov.OffsetHigh   := Hi(offset);
		result^.h := h^.Ref;
		result^.size := size;
		result^.write := write;
		result^.onDone := onDone;
		result^.param  := param;
	end;

	class procedure &File.CloseIORequest(a: pIORequest; const status: IOStatus);
	begin
		// try ... except Die, как вариант.
		a^.onDone(status, a^.param);

		// Нельзя закрывать до onDone. onDone иногда смотрит внутрь a^.h, например, чтобы узнать имя файла для сообщения об ошибке.
		a^.h^.Close(a^.h);

		FreeMem(a);
		if InterlockedDecrement(IOPending) = 0 then HeyNoIOPending.&Set;
	end;

	procedure &File.IO(write: boolean; const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler; param: pointer);
	const
		GenOp: array[boolean] of string = ('чтения', 'записи');
		function ExtraSize: SizeUint; begin if write then result := size else result := 0; end;
	var
		a: pIORequest;
		transferred: dword;
		ok, onDoneWasSet: boolean;
		syncExc: Exception;
	begin
		// Запросы без onDone считаются синхронными.
		// В этом случае используется вспомогательный onDone, который, возможно, запишет ошибку в syncExc.
		// Если запишет — она бросается в вызывающего.
		onDoneWasSet := Assigned(onDone);
		syncExc := nil;
		if not Assigned(onDone) then
		begin
			onDone := CompletionHandler(@&File.OnDoneSync);
			param  := @syncExc;
		end;

		// Если это запись — выделить вместе с IORequest временную область и скопировать в неё данные буфера.
		// Если чтение — за целостность буфера на протяжении операции отвечает вызывающий.
		a := CreateIORequest(ref, at, size, ExtraSize, write, onDone, param);
		if write then Move(buf^, a^.data[0], size);

		if write then
			ok := WriteFile(ref^.h, a^.data[0], size, dword(nil^), @a^.ov)
		else
			ok := ReadFile(ref^.h, buf^, size, dword(nil^), @a^.ov);

		if ok then
		begin
			// Операция завершилась синхронно, IOCompletionHandler выполнен.

		end else if GetLastError = ERROR_IO_PENDING then
		begin
			// Операция начата асинхронно, IOCompletionHandler когда-нибудь выполнится.
			// Если это чтение и не задан onDone, подождать завершения.
			// Если это запись, никогда не ждать. Без onDone получится fire-and-forget реквест.
			// (Может быть, я изменю это на полностью синхронный вариант, как с чтением — тогда extraSize можно будет убрать).
			if not write and not onDoneWasSet then
				if not GetOverlappedResult(ref^.h, a^.ov, (@transferred)^, true) then raise Win32.Error('Не удалось получить результат {} {}. {Err.}', [GenOp[write], ref^.fn], GetLastError);

		end else
			// Операция провалилась, IOCompletionHandler не выполнен и не будет.
			CloseIORequest(a, IOStatus.Create(a, GetLastError, 0, true));

		if Assigned(syncExc) then raise syncExc;
	end;

	class procedure &File.OnDoneSync(const status: IOStatus; param: pointer);
	begin
		if not status.OK then Exception(param^) := status.ToException;
	end;

	class procedure &File.GlobalInitialize;
	begin
		if HeyNoIOPending.OK then raise LogicError.Create('File.GlobalInitialize уже вызвана.');
		HeyNoIOPending.Init(true, true);
		AddExitProc(TProcedure(@&File.GlobalFinalize));
	end;

	class procedure &File.GlobalFinalize;
	begin
		WaitForAllIORequests;
		HeyNoIOPending.Done;
	end;

	class procedure &File.WaitForAllIORequests;
	begin
		if HeyNoIOPending.OK then HeyNoIOPending.Wait;
	end;

	function fpc_addref(data, typeInfo: pointer): SizeInt; [external name 'FPC_ADDREF'];
	function AryHelper.Grow(elemSize: size_t): pointer; begin result := GrowBy(1, elemSize); end;
	function AryHelper.Grow(arrayTypeInfo: pointer): pointer; begin result := GrowBy(1, arrayTypeInfo); end;

	function AryHelper.GrowBy(by, elemSize: size_t): pointer;
	var
		oldLen: size_t;
		block: pDynArrayHeader;
	begin
		if Assigned(self) then
		begin
			block := pDynArrayHeader(self) - 1; Assert(block^.refcount = 1, 'AryHelper.Grow: RefCount = {}.'.Format([block^.refcount]));
			oldLen := size_t(block^.high) + 1;
			self := ReallocMem(block, size_t(sizeof(DynArrayHeader) + (oldLen + by) * elemSize)) + sizeof(DynArrayHeader);
			block^.high := oldLen + (by - 1);
			result := self + oldLen * elemSize;
		end else
		begin
			self := CreateNew(by, elemSize);
			result := self;
		end;
	end;

	function AryHelper.GrowBy(by: size_t; arrayTypeInfo: pointer): pointer;
	var
		td: pDynArrayTypeData;
	begin
		td := ExtractDynArrayTypeData(arrayTypeInfo);
		result := GrowBy(by, td^.elSize);
		InitializeArray(result, td^.elType2, by);
	end;

	procedure AryHelper.Push(const elem; arrayTypeInfo: pointer);
	var
		target: pointer;
		td: pDynArrayTypeData;
	begin
		td := ExtractDynArrayTypeData(arrayTypeInfo);
		Assert((@elem < self) or not Assigned(self) or (@elem > self + td^.elSize * SizeUint((pDynArrayHeader(self) - 1)^.high)), 'Опасно передавать ссылку на ячейку.');
		target := Grow(td^.elSize);
		Move(elem, target^, td^.elSize);
		fpc_addref(target, td^.elType2);
	end;

	function AryHelper.Empty: boolean;
	begin
		result := not Assigned(pointer(self));
	end;

	class function AryHelper.CreateNew(elems, elemSize: size_t): Ary;
	var
		block: pDynArrayHeader;
	begin
		Assert(elems > 0);

		block := GetMem(sizeof(DynArrayHeader) + elems * elemSize);
		block^.refcount := 1;
		block^.high := elems - 1;

		result := block + 1; Assert(pPtrUint(@result)^ and (sizeof(pointer) - 1) = 0, 'misaligned array');
	end;

	class function AryHelper.ExtractDynArrayTypeData(arrayTypeInfo: pointer): pDynArrayTypeData;
	begin
		Assert(pByte(arrayTypeInfo)^ = tkDynArray);
		result := arrayTypeInfo + 2 + pByte(arrayTypeInfo)[1];
	end;

	function StringHelper.Peek(pos: SizeInt; out len: SizeInt): UTFchar;
	begin
		if length(self) - pos + 1 > 0 then result := UTFchar(self[pos]) else begin len := 0; exit(UTFInvalid); end;
		if result <= %01111111 then len := 1
		{$define n_more :=
			{$define times := n} {$define rep := and (ord(pChar(self)[pos + (1 + repid) - 1]) shr 6 = %10)} pp_repeat then
			begin
				result := (result and (%00011111 shr (n-1))) shl (6*n)
						{$define rep := or (UTFchar(ord(self[pos + (1 + repid)]) and %00111111) shl (6*(n-1-repid)))} {$define times := n} pp_repeat;
				len := n + 1;
			end {$undef n}}
		else if (result >= %11000000) and (result <= %11011111) {$define n := 1} n_more
		else if (result >= %11100000) and (result <= %11101111) {$define n := 2} n_more
		else if (result >= %11110000) and (result <= %11110111) {$define n := 3} n_more
		{$undef n_more} else begin len := 0; exit(UTFInvalid); end;
	end;

	function StringHelper.CodepointLen(pos: SizeInt): SizeInt;
	begin
		result := 1;
		if uint8(self[pos]) and %11000000 = %11000000 then
			while uint8(pChar(self)[pos - 1 + result]) and %11000000 = %10000000 do inc(result);
	end;

	function StringHelper.ToUTF16: widestring;
	begin
		result := UTF8Decode(self);
	end;

	function StringHelper.Format(const args: array of const): string;
	var
		start, p, nn, index, next: SizeInt;
	begin
		result := '';
		start := 1;
		p := 1;
		next := 0;
		while p <= length(self) do
			case self[p] of
				'{':
					if (p + 1 <= length(self)) and (self[p + 1] = '{') then
					begin
						result += Copy(self, start, p + 1 - start); inc(p, 2); start := p;
					end else
					begin
						nn := p + 1;
						while (nn <= length(self)) and (self[nn] in ['0' .. '9']) do inc(nn);
						if (nn <= length(self)) and (self[nn] = '}') and
							((nn = p + 1) and (next < length(args)) or
								TryParse(Copy(self, p + 1, nn - p - 1), index) and (index >= 0) and (index < length(args))) then
						begin
							if nn = p + 1 then begin index := next; inc(next); end;
							result += Copy(self, start, p - start) + VarRec.ToString(args[index]); p := nn + 1; start := p;
						end else
							inc(p);
					end;
				else
					inc(p);
			end;
		result += Copy(self, start, p - start);
	end;

	function StringHelper.Prefixed(const p: string; pos: SizeInt = 1): boolean;
	begin
		result := (pos + length(p) - 1 <= length(self)) and (CompareChar(self[pos], p[1], length(p)) = 0);
	end;

	function StringHelper.Tail(start: SizeInt): string;
	begin
		result := Copy(self, start, length(self) - start + 1);
	end;

	function StringHelper.Lowercase: string; begin result := Win32.Lowercase(self); end;
	function StringHelper.LowercaseFirst: string;
	var
		n: SizeInt;
	begin
		if length(self) >= 1 then n := CodepointLen(1) else n := 0;
		result := Copy(self, 1, n).Lowercase + Copy(self, n + 1, length(self) - n);
	end;

	function StringHelper.Stuffed(at, remove: SizeInt; const &with: string): string;
	begin
		remove := min(remove, length(self) - at + 1);
		result := Copy(self, 1, at - 1) + &with + Copy(self, at + remove, length(self) - at - remove + 1);
	end;
	function StringHelper.AR: PAnsiRec; begin result := PAnsiRec(self) - 1; end;

	function WidestringHelper.ToUTF8: string;
	begin
		result := UTF8Encode(self);
		if Assigned(pointer(result)) then result.AR^.cpes.CodePage := CP_ACP;
	end;

	class procedure VarRec.AssertType(const v: TVarRec; expected: SizeInt; pos: SizeInt);
	begin
		if v.VType <> expected then
			raise LogicError.Create('В позиции {} vt = {}, ожидается {}.'.Format([pos, VTypeToString(v.VType), VTypeToString(expected)]));
	end;

	class function VarRec.VTypeToString(vt: SizeInt): string;
	const
		Known: array[0 .. 18] of string = ('Integer', 'Boolean', 'Char', 'Extended', 'String', 'Pointer', 'PChar', 'Object', 'Class', 'WideChar',
		'PWideChar', 'AnsiString', 'Currency', 'Variant', 'Interface', 'WideString', 'Int64', 'QWord', 'UnicodeString');
	begin
		if vt < length(Known) then result := 'vt{} ({})'.Format([Known[vt], vt]) else result := '? ({})'.Format([vt]);
	end;

	class function VarRec.ToString(const v: TVarRec): string;
	begin
		case v.VType of
			vtInteger: result := im.ToString(v.VInteger);
			vtBoolean: if v.VBoolean then result := 'да' else result := 'нет';
			vtChar:    result := v.VChar;
			vtExtended: str(v.VExtended^, result);
			vtString:   result := v.VString^;
			vtPointer:  result := '$' + HexStr(v.VPointer);
			vtObject:   if Assigned(v.VObject) then result := v.VObject.ToString else result := 'TObject(nil)';
			vtClass:    if Assigned(v.VClass) then result := v.VClass.ClassName else result := 'TClass(nil)';
			vtAnsiString: result := ansistring(v.VAnsiString);
			vtInt64:      result := im.ToString(v.VInt64^);
			vtQWord:      result := im.ToString(v.VQWord^);
			else          result := '(vt = {})'.Format([VTypeToString(v.VType)]);
		end;
	end;

	constructor Exception.Create(const msg: string);
	begin
		inherited Create;
		self.msg := msg;
	end;

	class function Exception.Message(obj: TObject): string;
	begin
		if obj is LogicError then exit('Программная ошибка. ' + LogicError(obj).msg);
		if obj is Exception then exit(Exception(obj).msg);
		if obj is OutOfMemory then exit('Недостаточно памяти.');
		if Assigned(obj) then exit(obj.ClassName);
		result := 'Произошла странная ошибка.';
	end;

	procedure OutOfMemory.FreeInstance; begin ReleaseReserve; if Instance = self then Instance := nil; inherited; end;
	procedure OutOfMemory.FireAnEmergency; begin ReleaseReserve; end;
	procedure OutOfMemory.ReleaseReserve;
	begin
		if SingletonLock.OK then SingletonLock.Enter;
		if Assigned(RainyDayReserve) then FreeMem(RainyDayReserve);
		RainyDayReserve := nil;
		if SingletonLock.OK then SingletonLock.Leave;
	end;

	class procedure OutOfMemory.InitGlobal;
	begin
		Instance := OutOfMemory.Create;
		Instance.RainyDayReserve := GetMem(4096);
	end;

	class procedure OutOfMemory.DoneGlobal;
	begin
		if Assigned(Instance) then
		begin
			Instance.CanDieNow := true;
			Instance.Free;
		end;
	end;

	procedure DoneSession; begin Session.Done; end;
	class constructor Session.Init;
	begin
		ExceptProc := TExceptProc(@Session.OnUnhandledException);
		ErrorProc  := TErrorProc(@Session.OnRuntimeError);
		AddExitProc(@DoneSession); // иначе не вызовется при сбое инициализации
		OutOfMemory.InitGlobal;
		Win32.Init;
		SingletonLock.Init;
		Con.Init;
		TestHacks;
	end;

	class procedure Session.Done;
	begin
		&File.WaitForAllIORequests;
		Con.Done;
		SingletonLock.Done;
		Win32.Done;
		OutOfMemory.DoneGlobal;
	end;

	class function Session.HumanTrace(frames: pCodePointer = nil; frameCount: SizeInt = -1): string;
	type
		TraceItem = record
			line: string;
			uninteresting: SizeInt;
		end;

		function InterestingTraceLine(const line: string): boolean;
		var
			p: SizeInt;
		begin
			p := 0;
			while (pChar(line)[p] in [StringHelper.Tab, ' ']) do inc(p);
			while (pChar(line)[p] in ['$']) do inc(p);
			while (pChar(line)[p] in ['0' .. '9', StringHelper.Tab, ' ']) do inc(p);
			result := p < length(line);
		end;
	var
		i: SizeInt;
		line: string;
		frame: CodePointer;
		trace: array of TraceItem;
	begin
		trace := nil; frame := nil;
		i := 0;
		repeat
			if frameCount >= 0 then
			begin
				if i >= frameCount then break;
				frame := frames[i];
			end else
			begin
				if i = 0 then if Assigned(frames) then frame := frames[0] else frame := get_caller_frame(get_frame);
				if not Assigned(frame) then break;
			end;

			line := BacktraceStrFunc(frame);
			if InterestingTraceLine(line) then
			begin
				TraceItem(Ary(trace).Grow(TypeInfo(trace))^).uninteresting := 0;
				trace[High(trace)].line := line;
			end else
				if (length(trace) > 0) and (trace[High(trace)].uninteresting > 0) then
					inc(trace[High(trace)].uninteresting)
				else
					TraceItem(Ary(trace).Grow(TypeInfo(trace))^).uninteresting := 1;

			if frameCount < 0 then frame := get_caller_frame(frame);
			inc(i);
		until false;

		result := '';
		if not ((length(trace) = 1) and (trace[0].uninteresting > 0)) then
			for i := 0 to High(trace) do
				if trace[i].uninteresting > 0 then
				begin
					result += EOL + '(...)';
					if trace[i].uninteresting > 1 then result += ' x{}'.Format([trace[i].uninteresting]);
				end else
					result += EOL + trace[i].line;
	end;

	class procedure Session.OnUnhandledException(Obj: TObject; Addr: CodePointer; FrameCount: LongInt; Frame: PCodePointer);
	var
		msg: string;
		eo, nx: PExceptObject;
	begin
		Assert(Addr = Addr);
		if Obj is OutOfMemory then OutOfMemory(Obj).FireAnEmergency;
		msg := Exception.Message(Obj);
		if not (Obj is OutOfMemory) then msg += HumanTrace(Frame, FrameCount);
		if Con.OK then Con.Colored(msg, Con.Red) else writeln(stderr, msg.ToUTF16);
		readln;

		// А этот хак настолько грязный, что нельзя легко проверить его состоятельность при недокументированных изменениях в RTL
		// (к счастью, всегда есть альтернатива: не заморачиваться и сделать сеппуку aka ExitProcess). Дело вот в чём.
		//
		// Если ExceptProc вернулась, RTL вызывает halt, которая несколько мягче ExitProcess: она выполняет финализацию,
		// давая отработать class destructor'ам, ExitProc и секциям finalization, в т. ч. в heaptrc.
		// Поэтому я целенаправленно возвращаюсь из ExceptProc, чтобы проверить код на корректность и отсутствие утечек даже в аварийной ситуации.
		//
		// Но FPC сам не освобождает все внутренние структуры! А именно, узлы стека исключений (RaiseList), внутри которых, в свою очередь,
		// языковые объекты исключений (FObject: TObject) и динамически выделенные блоки Frames.
		//
		// Подчищаю руками, но это потенциально сломается без предупреждения. RaiseList и TExceptObject документированы,
		// но такая багофича при необработанном исключении — нет.
		eo := RaiseList;
		while Assigned(eo) do
		begin
			eo^.FObject.Free;
			if Assigned(eo^.Frames) then FreeMem(eo^.Frames);
			nx := eo^.next; dispose(eo); eo := nx;
		end;
	end;

	class procedure Session.OnRuntimeError(ErrNo: Longint; Address: CodePointer; Frame: Pointer);
	var
		name: string;
		i: SizeInt;
	begin
		Assert(Address = Address);
		if ErrNo = RuntimeErrorExitCodes[reOutOfMemory] then raise OutOfMemory.Instance;

		i := -1;
		if ErrNo <= High(byte) then i := IndexByte(RuntimeErrorExitCodes, length(RuntimeErrorExitCodes), ErrNo);
		if i >= 0 then
		begin
			str(TRuntimeError(i), name);
			if name.Prefixed('re') then name := name.Tail(length('re') + 1);
		end else
			name := 'с кодом ' + ToString(ErrNo);
		raise Exception.Create('Произошла ошибка {}.'.Format([name]) + HumanTrace(@Frame));
	end;

	class procedure Session.TestHacks;
		procedure TestAnsiRecHack;
		var
			s, s2: string;
		begin
			s := im.ToString(ThreadID);
			(@s2)^ := s;
			if (s.AR^.cpes.CodePage <> CP_ACP) or (s.AR^.cpes.ElementSize <> 1) or (s.AR^.ref <> 2) or (length(s) <> s.AR^.len) then
				raise Exception.Create('AnsiRec hack failed: CP = {0} ({1}), ElementSize = {2} (1), RefCount = {3} (2), Length = {4} ({5}).'.Format([
					s.AR^.cpes.CodePage, CP_ACP, s.AR^.cpes.ElementSize, s.AR^.ref, s.AR^.len, length(s)]));
		end;

		procedure TestDynArrayHack;
		type
			MType = record s: string; x: SizeInt; end;
			ExpectedItem = record m: MType; ref: SizeInt; end; ExpectedItems = array of ExpectedItem;

			procedure ConstructExpected(var exp: ExpectedItems);
			begin
				SetLength(exp, 4);
				exp[0].m.s := 'Test 1: ' + ToString(ThreadID); exp[0].m.x := 1; exp[0].ref := 2;
				exp[1].m.s := 'Test 2';                        exp[1].m.x := 2; exp[1].ref := -1;
				exp[2].m.s := 'Test 3: ' + ToString(ThreadID); exp[2].m.x := 3; exp[2].ref := 1;
				exp[3] := exp[0];
			end;
			function MRepr(const c: MType; ref: SizeInt): string; begin result := '(''{0}'', {1}, ref={2})'.Format([c.s, c.x, ref]); end;

		var
			a: array of MType;
			exp: ExpectedItems;
			i: SizeInt;
		begin
			ConstructExpected(exp);
			Ary(a).Push(exp[0].m, TypeInfo(a));
			Ary(a).Push(exp[1].m, TypeInfo(a));
			MType(Ary(a).Grow(TypeInfo(a))^) := exp[2].m;
			exp := nil; SetLength(exp, 1); exp[0].m := a[0]; Ary(a).Push(exp[0].m, TypeInfo(a)); exp := nil;
			if length(a) <> 4 then raise Exception.Create('{0}: len = {1} (4).'.Format(['DynArray hack failed', length(a)]));

			ConstructExpected(exp);
			for i := 0 to High(a) do
				if (a[i].s <> exp[i].m.s) or (a[i].s.AR^.ref <> exp[i].ref) or (a[i].x <> exp[i].m.x) then
					raise Exception.Create('{0}: a[{1}] = {2}, exp. {3}'.Format(['DynArray hack failed', i, MRepr(a[i], a[i].s.AR^.ref), MRepr(exp[i].m, exp[i].ref)]));
		end;

	begin
		TestAnsiRecHack;
		TestDynArrayHack;
	end;

type
	LodePNGLib = object(DLL)
		procedure Load(const fn: string);
	type
		reallocf = function(p: pointer; nsize: csize_t): pointer; cdecl;
		Allocator = record
			realloc: reallocf;
		end;

		CompressionSettings = record
			btype: cuint;        // the block type for LZ (0, 1, 2 or 3, see zlib standard). Should be 2 for proper compression.
			use_lz77: cuint;     // whether or not to use LZ77. Should be 1 for proper compression.
			windowsize: cuint;   // must be a power of two <= 32768. higher compresses more but is slower. Default value: 2048.
			minmatch: cuint;     // mininum lz77 length. 3 is normally best, 6 can be better for some PNGs. Default: 0
			nicematch: cuint;    // stop searching if >= this length found. Set to 258 for best compression. Default: 128
			lazymatching: cuint; // use lazy matching: better compression but a bit slower. Default: true
		end;
		{$define enum := Preset} {$define items := Fast _ 0 _ Good _ 1 _ Uber _ 2} declare_scoped_enum_with_shortcuts

	const
		CT_GREY = 0;       // greyscale: 1, 2, 4, 8, 16 bit
		CT_RGB = 2;        // RGB: 8, 16 bit
		CT_PALETTE = 3;    // palette: 1, 2, 4, 8 bit
		CT_GREY_ALPHA = 4; // greyscale with alpha: 8, 16 bit
		CT_RGBA = 6;       // RGB with alpha: 8, 16 bit

		Presets: array[Preset] of CompressionSettings = (
			(btype: 1; use_lz77: 1; windowsize: 1024; minmatch: 3; nicematch: 128; lazymatching: 1),
			(btype: 2; use_lz77: 1; windowsize: 2048; minmatch: 3; nicematch: 128; lazymatching: 1),
			(btype: 2; use_lz77: 1; windowsize: 32768; minmatch: 3; nicematch: 258; lazymatching: 1));

	var
		decode_memory: function(out &out: pointer; out w, h: cuint; &in: pointer; insize: csize_t; colortype: cint; bitdepth: cuint;
			constref alloc: Allocator): cuint; cdecl;
		encode_memory: function(out &out: pointer; out outsize: csize_t; image: pointer; w, h: cuint; colortype: cint; bitdepth: cuint;
			constref settings: CompressionSettings; constref alloc: Allocator): cuint; cdecl;

		class function LodeReAlloc(p: pointer; nsize: csize_t): pointer; cdecl; static;
		class function DefaultAllocator: Allocator; static;
		class function ErrorMessage(code: cuint): string; static;
	end;

	procedure LodePNGLib.Load(const fn: string);
	begin
		DLL.Load(DLL(pointer(@self)^), fn, ['prefix=lodepng_', 'decode_memory', @decode_memory, 'encode_memory', @encode_memory]);
	end;

	class function LodePNGLib.LodeReAlloc(p: pointer; nsize: csize_t): pointer; cdecl;
	begin
		result := ReallocMem((@p)^, nsize);
	end;

	class function LodePNGLib.DefaultAllocator: Allocator;
	begin
		result.realloc := reallocf(@LodePNGLib.LodeReAlloc);
	end;

	// потом поставлю студию и вкомпилирую lodepng_error_text >___<"
	class function LodePNGLib.ErrorMessage(code: cuint): string;
	var
		msg: string;
	begin
		msg := '';
		case code of
			1: msg := 'nothing done yet'; // the Encoder/Decoder has done nothing yet, error checking makes no sense yet
			10: msg := 'end of input memory reached without huffman end code'; // while huffman decoding
			11: msg := 'error in code tree made it jump outside of huffman tree'; // while huffman decoding
			13: msg := 'problem while processing dynamic deflate block';
			14: msg := 'problem while processing dynamic deflate block';
			15: msg := 'problem while processing dynamic deflate block';
			16: msg := 'unexisting code while processing dynamic deflate block';
			17: msg := 'end of out buffer memory reached while inflating';
			18: msg := 'invalid distance code while inflating';
			19: msg := 'end of out buffer memory reached while inflating';
			20: msg := 'invalid deflate block BTYPE encountered while decoding';
			21: msg := 'NLEN is not ones complement of LEN in a deflate block';
			// end of out buffer memory reached while inflating:
			// This can happen if the inflated deflate data is longer than the amount of bytes required to fill up
			// all the pixels of the image, given the color depth and image dimensions. Something that doesn't
			// happen in a normal, well encoded, PNG image.
			22: msg := 'end of out buffer memory reached while inflating';
			23: msg := 'end of in buffer memory reached while inflating';
			24: msg := 'invalid FCHECK in zlib header';
			25: msg := 'invalid compression method in zlib header';
			26: msg := 'FDICT encountered in zlib header while it''s not used for PNG';
			27: msg := 'PNG file is smaller than a PNG header';
			28: msg := 'incorrect PNG signature, it''s no PNG or corrupted'; // Checks the magic file header, the first 8 bytes of the PNG file
			29: msg := 'first chunk is not the header chunk';
			30: msg := 'chunk length too large, chunk broken off at end of file';
			31: msg := 'illegal PNG color type or bpp';
			32: msg := 'illegal PNG compression method';
			33: msg := 'illegal PNG filter method';
			34: msg := 'illegal PNG interlace method';
			35: msg := 'chunk length of a chunk is too large or the chunk too small';
			36: msg := 'illegal PNG filter type encountered';
			37: msg := 'illegal bit depth for this color type given';
			38: msg := 'the palette is too big'; // more than 256 colors
			39: msg := 'more palette alpha values given in tRNS chunk than there are colors in the palette';
			40: msg := 'tRNS chunk has wrong size for greyscale image';
			41: msg := 'tRNS chunk has wrong size for RGB image';
			42: msg := 'tRNS chunk appeared while it was not allowed for this color type';
			43: msg := 'bKGD chunk has wrong size for palette image';
			44: msg := 'bKGD chunk has wrong size for greyscale image';
			45: msg := 'bKGD chunk has wrong size for RGB image';
			48: msg := 'empty input buffer given to decoder. Maybe caused by non-existing file?';
			49: msg := 'jumped past memory while generating dynamic huffman tree';
			50: msg := 'jumped past memory while generating dynamic huffman tree';
			51: msg := 'jumped past memory while inflating huffman block';
			52: msg := 'jumped past memory while inflating';
			53: msg := 'size of zlib data too small';
			54: msg := 'repeat symbol in tree while there was no value symbol yet';
			// jumped past tree while generating huffman tree, this could be when the
			// tree will have more leaves than symbols after generating it out of the
			// given lenghts. They call this an oversubscribed dynamic bit lengths tree in zlib.
			55: msg := 'jumped past tree while generating huffman tree';
			56: msg := 'given output image colortype or bitdepth not supported for color conversion';
			57: msg := 'invalid CRC encountered (checking CRC can be disabled)';
			58: msg := 'invalid ADLER32 encountered (checking ADLER32 can be disabled)';
			59: msg := 'requested color conversion not supported';
			60: msg := 'invalid window size given in the settings of the encoder (must be 0-32768)';
			61: msg := 'invalid BTYPE given in the settings of the encoder (only 0, 1 and 2 are allowed)';
			// LodePNG leaves the choice of RGB to greyscale conversion formula to the user.
			62: msg := 'conversion from color to greyscale not supported';
			63: msg := 'length of a chunk too long, max allowed for PNG is 2147483647 bytes per chunk'; // (2^31-1)
			// this would msg in the inability of a deflated block to ever contain an end code. It must be at least 1.
			64: msg := 'the length of the END symbol 256 in the Huffman tree is 0';
			66: msg := 'the length of a text chunk keyword given to the encoder is longer than the maximum of 79 bytes';
			67: msg := 'the length of a text chunk keyword given to the encoder is smaller than the minimum of 1 byte';
			68: msg := 'tried to encode a PLTE chunk with a palette that has less than 1 or more than 256 colors';
			69: msg := 'unknown chunk type with ''critical'' flag encountered by the decoder';
			71: msg := 'unexisting interlace mode given to encoder (must be 0 or 1)';
			72: msg := 'while decoding, unexisting compression method encountering in zTXt or iTXt chunk (it must be 0)';
			73: msg := 'invalid tIME chunk size';
			74: msg := 'invalid pHYs chunk size';
			75: msg := 'no null termination char found while decoding text chunk'; // length could be wrong, or data chopped off
			76: msg := 'iTXt chunk too short to contain required bytes';
			77: msg := 'integer overflow in buffer size'; // 78, 79
			80: msg := 'tried creating a tree of 0 symbols';
			81: msg := 'lazy matching at pos 0 is impossible';
			82: msg := 'color conversion to palette requested while a color isn''t in palette';
			83: msg := 'memory allocation failed';
			84: msg := 'given image too small to contain all pixels to be encoded';
			86: msg := 'impossible offset in lz77 encoding (internal bug)';
			87: msg := 'must provide custom zlib function pointer if LODEPNG_COMPILE_ZLIB is not defined';
			88: msg := 'invalid filter strategy given for LodePNGEncoderSettings.filter_strategy';
			89: msg := 'text chunk keyword too short or long: must have size 1-79';
			// the windowsize in the LodePNGCompressSettings. Requiring POT(==> & instead of %) makes encoding 12% faster.
			90: msg := 'windowsize must be a power of two';
			91: msg := 'invalid decompressed idat size';
			92: msg := 'too many pixels, not supported';
			93: msg := 'zero width or height is invalid';
			94: msg := 'header chunk must have a size of 13 bytes';
		end;
		result := 'код LodePNG {}'.Format([ToString(code)]);
		if msg <> '' then result := '{} ({})'.Format([msg, result]);
	end;

var
	lodepng: LodePNGLib;
	data: array[0 .. 2047, 0 .. 2047, 0 .. 2] of uint8;
	x, y: SizeInt;
	r: pointer;
	rsize: size_t;
	loder: cuint;
	f: &File;

begin
	con.ColoredLine('<B>В пору <1>белого</> хлада не ешь <RG>жёлтый</> снег.');
	Assert(not f.Valid);
	try
		lodepng.Load('{}lib\{}\lodepng.dll'.Format([ExecRoot, CPU]));
		Con.Line('Генерация...');
		for y := 0 to High(data) do
			for x := 0 to High(data[0]) do
				data[x, y, 0] := round(High(data[0, 0, 0]) * clamp(sqr(1 - abs(1 - (x/High(data[0]) + y/High(data)))), 0, 1));

		loder := lodepng.encode_memory(r, rsize, @data, length(data[0]), length(data), lodepng.CT_RGB, 8, lodepng.Presets[lodepng.Uber], lodepng.DefaultAllocator);
		if loder <> 0 then raise Exception.Create('Не удалось сохранить картинку: {}.'.Format([lodepng.ErrorMessage(loder)]));
		Con.Line('Сохранение...');
		&File.Open(f, 'test.png', [f.Writeable]);
		f.Write(0, r, rsize);
		Con.ColoredLine('<G>Картинка сохранена</>, <R>а ты пидор :з</>.');
	finally
		f.Close;
		FreeMem(r);
		lodepng.Unload;
	end;
	readln;
end.
