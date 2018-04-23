{$mode objfpc} {$h+} {$typedaddress+} {$macro on} {$modeswitch duplicatelocals+} {$modeswitch typehelpers+} {$scopedenums+}
{$ifdef assert} {$error} {$endif} {$ifopt Q+} {$define assert} {$endif}
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
// (если вообще выключить scopedenums, EnumValue попадёт в глобальную область видимости и будет с чем-нибудь конфликтовать.)
// Например, {$define enum := Channel} {$define items := Red _ 0 _ Green _ 1 _ Blue _ 2} преобразуется в
// type
//     Channel = (Red, Green, Blue);    // дословно: Channel = (Red := 0, Green := 1, Blue := 2);
// const
//     Red   = Channel.Red;             //           Red   = Channel(0);
//     Green = Channel.Green;           //           Green = Channel(1);
//     Blue  = Channel.Blue;            //           Blue  = Channel(2);
{$define enum_with_shortcuts :=
	{$if defined(now_number) or defined(_)} {$error enum_with_shortcuts would hide defines} {$endif}
	type
		enum = {$define _ := {$ifdef now_number} , {$undef now_number} {$else} := {$define now_number} {$endif}} (items); {$undef now_number}
	const
		{$define _ := {$ifdef now_number} ); {$undef now_number} {$else} = enum( {$define now_number} {$endif}} items _ {$undef now_number}
		{$undef enum} {$undef items} {$undef _}}

// {$define args := A _ B} unused_args => Assert((@A >= nil) and (@B >= nil));
{$define unused_args := {$if defined(_)} {$error unused_argrs would hide defines} {$endif}
	{$define _ := >= nil) and (@} Assert((@args >= nil)); {$undef _} {$undef args}}

const
	EOL = LineEnding;
	CPUArch = {$if defined(CPU32)} 'x86' {$elseif defined(CPU64)} 'x64' {$else} {$error unknown CPU} {$endif};

type
	widestring = unicodestring;
	UTFchar = type uint32;
	FilePos = type uint64;
	FileSize = type uint64;
	sint = int32; uint = uint32;
	float = single;
{$push} {$scopedenums off} ThrowBehaviour = (Throw, DontThrow); {$pop}
	&Case = (Lower, Upper);

{$define ifthenimpl :=
	function IfThen(cond: boolean; const yes: typename; const no: typename {$ifdef default_no} = default_no {$endif}): typename;
	begin
		if cond then result := yes else result := no;
	end; {$undef default_no} {$ifndef keep_typename} {$undef typename} {$endif}}

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
	function max(const a, b: typename): typename; begin if a >= b then result := a else result := b; end;
	{$define keep_typename} {$define default_no := 0} ifthenimpl {$undef keep_typename}
	{$undef typename}}
	{$define typename := int32} impl {$define typename := uint32} impl  {$define typename := int64} impl {$define typename := uint64} impl
{$undef impl}

{$define typename := string} {$define default_no := ''} ifthenimpl
{$define typename := pointer} ifthenimpl
{$undef ifthenimpl}

	function clamp(const x, a, b: float): float;
	begin
		if (x >= a) and (x <= b) then result := x else
			if x > a then result := b else result := a;
	end;

	// При получении нулевого указателя ничего не делать. Без "Weak" дополнительно зануляет указатель.
	procedure FreeMemWeak(p: pointer); begin if Assigned(p) then System.FreeMem(p); end;
	procedure FreeMem(var p: pointer); begin FreeMemWeak(p); p := nil; end;
	procedure FreeAndNil(var p); var t: TObject; begin t := TObject(p); TObject(p) := nil; t.Free; end;

type
	Exception = class;

	DLL = object
	type
		Proxy = object
			function Prefix(const prefix: string): Proxy;
			function Func(const name: string; var funcPtr{: CodePointer}): Proxy;
		private
			dll: ^DLL;
		end;

		function Load(const fn: string; e: ThrowBehaviour = Throw): Proxy;
		procedure Unload;
	private
		h: HANDLE;
		fn, prefix: string;
		temper: ThrowBehaviour;
		fptrs: array of pCodePointer;
	end;

	Win32 = object
	type
		NTSTATUS = record value: uint32; end;

	type
		PTP_CALLBACK_INSTANCE = ^TP_CALLBACK_INSTANCE; TP_CALLBACK_INSTANCE = record end;
		PTP_CALLBACK_ENVIRON = ^TP_CALLBACK_ENVIRON; TP_CALLBACK_ENVIRON = record end;
		PTP_IO = ^TP_IO; TP_IO = record end;

		TP_IO_CALLBACK = procedure(Instance: PTP_CALLBACK_INSTANCE; Context: pointer;
			Overlapped: LPOVERLAPPED; IoResult: Windows.ULONG; NumberOfBytesTransferred: Windows.ULONG_PTR; Io: PTP_IO); stdcall;
	class var
		CreateThreadpoolIo: function(fl: HANDLE; pfnio: TP_IO_CALLBACK; pv: pointer; pcbe: PTP_CALLBACK_ENVIRON): PTP_IO; stdcall;
		StartThreadpoolIo: procedure(pio: PTP_IO); stdcall;
		CancelThreadpoolIo: procedure(pio: PTP_IO); stdcall;
		CloseThreadpoolIo: procedure(pio: PTP_IO); stdcall;

	type
		SRWLOCK = ^_SRWLOCK; _SRWLOCK = record end;
	class var
		InitializeSRWLock: procedure(out lock: SRWLOCK); stdcall;
		AcquireSRWLockExclusive: procedure(var lock: SRWLOCK); stdcall;
		ReleaseSRWLockExclusive: procedure(var lock: SRWLOCK); stdcall;

	type
		CONDITION_VARIABLE = ^_CONDITION_VARIABLE; _CONDITION_VARIABLE = record end;
	class var
		InitializeConditionVariable: procedure(out cv: CONDITION_VARIABLE); stdcall;
		WakeAllConditionVariable: procedure(var cv: CONDITION_VARIABLE); stdcall;
		WakeConditionVariable: procedure(var cv: CONDITION_VARIABLE); stdcall;
		SleepConditionVariableSRW: function(var cv: CONDITION_VARIABLE; var lock: SRWLOCK; dwMilliseconds: dword; flags: Windows.ULONG): Windows.BOOL; stdcall;

	type
		ErrorCode = object
		type
			Origin = (GetLastError, NTSTATUS);
		var
			value: dword;
			from: Origin;
			class function Create(value: dword; from: Origin): ErrorCode; static;
		end;

		class procedure Init; static;
		class procedure Done; static;
		class function DescribeError(const code: ErrorCode): string; static;
		class function ErrorMessage(const fmt: string; const args: array of const; const code: ErrorCode): string; static;
		class function Error(const fmt: string; const args: array of const; const code: ErrorCode): Exception; static;
		class function OperationFailed(const what: string; const code: ErrorCode): Exception; static;
		class function ConvertCase(const text: string; &to: &Case): string; static;
		class procedure Warning(const text: string); static;
		class procedure Warning(const what: string; const code: ErrorCode); static;
		class function CommandLineTail: string; static;

	const
		STATUS_CANCELLED = $C0000120;

	type
		// В nBuf получает длину буфера, с учётом нулевого терминатора.
		// Если строка умещается в буфер, возвращает в len её длину БЕЗ нулевого символа (т. е. строго < nBuf).
		// Если не умещается — возвращает в len необходимую длину буфера С УЧЁТОМ нулевого символа,
		// или QUERY_STRING_LENGTH_UNKNOWN, если известен только факт, что строка не умещается.
		QueryStringCallback = procedure(buf: pWideChar; nBuf: size_t; out len: size_t; param: pointer);
	const
		QUERY_STRING_LENGTH_UNKNOWN = High(size_t);
		class function QueryString(cb: QueryStringCallback; param: pointer; const ofWhat: string): widestring; static;
	private
		class procedure QueryModuleFileName(buf: pWideChar; nBuf: size_t; out len: size_t; param: pointer); static;
		class function ReplaceWithErrorDescription(const src, sample: string; pos: SizeInt; param: pointer): string; static;

	strict private class var
		k32: DLL;
	end;

	operator :=(code: dword): Win32.ErrorCode; begin result := result.Create(code, result.Origin.GetLastError); end;
	operator :=(code: Win32.NTSTATUS): Win32.ErrorCode; begin result := result.Create(code.value, result.Origin.NTSTATUS); end;

type
	ThreadLock = object
		srw: Win32.SRWLOCK;
	{$ifdef Debug} owner: TThreadID; guard: pointer; {$endif}
		procedure Init;
		procedure Done;
		procedure Enter;
		procedure Leave;
		function AcquiredAssert: boolean;
	end;

	ThreadCV = object
		cv: Win32.CONDITION_VARIABLE;
	{$ifdef Debug} guard: pointer; {$endif}
		procedure Init;
		procedure Done;
		procedure Wait(var lock: ThreadLock);
		procedure WakeAll;
		procedure WakeOne;
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

	CookieManager = class;
	// Для разных штук, которые можно захватывать и освобождать.
	Cookie = class
		destructor Destroy; override;
	private
		man: CookieManager;
		index: SizeInt;
	end;

	CookieManager = class
		cookies: array of Cookie;
		constructor Create;
		destructor Destroy; override;
		procedure Lock;
		procedure Unlock;
		procedure Add(ck: Cookie);
		function Count: SizeInt;
	private
		lck: ThreadLock;
	end;

	pConsole = ^Console;
	Console = object
	{$define enum := Color} {$define items := Black _ 0 _ Maroon _ 1 _ Green _ 2 _ Olive _ 3 _ Navy _ 4 _ Purple _ 5 _ Teal _ 6 _ Silver _ 7 _
		Gray _ 8 _ Red _ 9 _ Lime _ 10 _ Yellow _ 11 _ Blue _ 12 _ Fuchsia _ 13 _ Aqua _ 14 _ White _ 15} enum_with_shortcuts
	var
		procedure Init;
		procedure Done;
		function OK: boolean;
		procedure Write(const s: string);
		procedure Line(const s: string = '');
		procedure Colored(const s: string; baseCol: SizeInt = -1); procedure Colored(const s: string; baseCol: Color);
		procedure ColoredLine(const s: string);                    procedure ColoredLine(const s: string; baseCol: Color);
		class function Escape(const s: string): string; static;
		function ReadLine: string;
		procedure Intercept;
		procedure DisableCtrlC;

	type
		CtrlCHandler = function(param: pointer): boolean;
		CtrlCCookie = class(Cookie)
			handler: CtrlCHandler;
			param: pointer;
		end;
		function RegisterCtrlCHandler(handler: CtrlCHandler; param: pointer): CtrlCCookie;

	strict private
	{$define enum := InternalFlag} {$define items := LockCreated _ 0 _ HInSet _ 1 _ HOutSet _ 2 _ HandlerInstalled _ 3 _ Broken _ 4 _ CtrlCPending _ 5 _ CtrlCDisabled _ 6} enum_with_shortcuts
	var
		lock: ThreadLock;
		hIn, hOut: HANDLE;
		bookkeep: set of InternalFlag;
		defCol, defBg: Color;
		defAttrWoCol: word;
		ctrlCHandlers: CookieManager;
		class function CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; stdcall; static;
	type
		Piece = record
			data: string;
			color: cint; // энум или -1
		end;
		PiecesList = array of Piece;
		class function ParseMarkdown(const s: string): PiecesList; static;
		procedure UseWriteConsoleW(const text: string);
		procedure FlushInput;
		procedure UnlockedIntercept;

	public const
		ColorNames: array[Color] of string = ('0', 'r', 'g', 'rg', 'b', 'rb', 'gb', '.3', '.6', 'R', 'G', 'RG', 'B', 'RB', 'GB', '1');
	strict private const
		BitsToColor: array[0 .. 15] of Color = (Black, Navy, Green, Teal, Maroon, Purple, Olive, Gray, Silver, Blue, Lime, Aqua, Red, Fuchsia, Yellow, White);
		ColorToBits: array[Color] of word = (%0000, %0100, %0010, %0110, %0001, %0101, %0011, %1000, %0111, %1100, %1010, %1110, %1001, %1101, %1011, %1111);

	class var
		Instance: pConsole;
	end;

	&File = object
	{$define enum := Flag} {$define items := Readable _ 0 _ Writeable _ 1 _ Existing _ 2 _ New _ 3 _ Temp _ 4} enum_with_shortcuts
	type
		Flags = set of Flag;

		// Запоминает, какие папки были созданы впервые, чтобы была возможность удалить их, если понадобится
		// (например, если они созданы как часть процесса создания файла, но создание самого файла провалилось).
		// Так, для TryCreatePath('base\sub\folder\file.txt', ...), когда sub и folder не существовало, будет folders = ('base\sub', 'base\sub\folder').
		PathRollback = object
			type Folder = widestring;
			var folders: array of folder;
			const Empty: PathRollback = ();
			procedure Rollback;
		end;

		pOpenResult = ^OpenResult;
		OpenResult = object
			ok, exist: boolean;
			errmsg: string;
			rb: PathRollback;
		const
			Empty: OpenResult = ();
		end;

		IOStatus = object
			function OK: boolean;
			function Partial: boolean;
			function Cancelled: boolean;
			function Failed: boolean;
			function ToException: Exception;
		private
			req: pointer; // pIORequest
			code: Win32.ErrorCode;
			transferred: SizeUint;
			class function Create(req: pointer; const code: Win32.ErrorCode; const transferred: SizeUint; forceFail: boolean = false): IOStatus; static;
		const
			STRANGE_ERROR = High(DWORD) - 1; // code = STRANGE_ERROR обозначает случай, когда операция провалилась с code = 0 (ну мало ли).
			Dummy: IOStatus = ();
		end;

		CompletionHandler = procedure(const status: IOStatus; param: pointer);

		procedure Open(const fn: string; flags: Flags = [Flag.Readable]; r: pOpenResult = nil);
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
			tp_io: Win32.PTP_IO;
			refcount: SizeInt;
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
	var
		ref: pSharedHandle;
		class function TryCreatePath(const fn: string; out err: dword; out rollback: PathRollback): boolean; static;
		class procedure IOCompletionHandler(Instance: Win32.PTP_CALLBACK_INSTANCE; Context: pointer;
			Overlapped: LPOVERLAPPED; IoResult: Windows.ULONG; NumberOfBytesTransferred: Windows.ULONG_PTR; Io: Win32.PTP_IO); stdcall; static;
		class function CreateIORequest(h: pSharedHandle; const offset: FilePos; size, extraSize: SizeUint; write: boolean; onDone: CompletionHandler; param: pointer): pIORequest; static;
		class procedure CloseIORequest(a: pIORequest; const status: IOStatus; fromCompletionCallback: boolean); static;
		procedure IO(write: boolean; const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler; param: pointer);
		class procedure OnDoneSync(const status: IOStatus; param: pointer); static;
	const
		RWGenitive: array[boolean] of string = ('чтения', 'записи');
	class var
		IOPending: SizeInt;
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
	// Самодельные дженерик-object'ы выдают internal error'ы, а class'ы нужно СОЗДАВАТЬ и УНИЧТОЖАТЬ (так бы я взял тот же TFPGList... хотя... он тянет SysUtils...).
	Ary = type pointer;
	AryHelper = type helper for Ary
		function Grow(elemSize: size_t): pointer;         function Grow(arrayTypeInfo: pointer): pointer;
		function GrowBy(by, elemSize: size_t): pointer;   function GrowBy(by: size_t; arrayTypeInfo: pointer): pointer;
		procedure Push(const elem; arrayTypeInfo: pointer);
		function Empty: boolean;
		class function GrowStgy(n, alloc: SizeUint): SizeUint; static;
		class function ShrinkStgy(n, alloc: SizeUint; out na: SizeUint): boolean; static;

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

	CharSet = set of char;
	Strings = array of string;
	StringHelper = type helper for string
		function Peek(pos: SizeInt; out len: SizeInt): UTFchar;
		function CodepointLen(pos: SizeInt): SizeInt;
		function ToUTF16: widestring;
		function Format(const args: array of const): string;
		function Prefixed(const p: string; pos: SizeInt = 1): boolean;
		function Head(count: SizeInt): string;
		function AB(start, ed: SizeInt): string;
		function Tail(start: SizeInt): string;
		function ConvertCase(&to: &Case): string;
		function ConvertCaseFirst(&to: &Case): string;
		function Uppercase: string; function UppercaseFirst: string;
		function Lowercase: string; function LowercaseFirst: string;
		function Stuffed(at, remove: SizeInt; const &with: string): string;
		function Split(sep: char; mergeSeps: boolean = true): Strings;
		function Split(const seps: CharSet; mergeSeps: boolean = true): Strings;
		function Consume(const syms: CharSet; p: SizeInt; out np: SizeInt): boolean;
		function ConsumeUntil(const syms: CharSet; p: SizeInt; out np: SizeInt): boolean;

	type
		ReplaceFunction = function(const src, sample: string; pos: SizeInt; param: pointer): string;
		function Replace(const sample: string; repl: ReplaceFunction; param: pointer): string;
		function Replace(const sample, by: string): string;
	private
		class function ReplaceByString(const src, sample: string; pos: SizeInt; param: pointer): string; static;

	public const
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
		class function VTypeToString(vt: SizeInt): string; static;
		class function ToString(const v: TVarRec): string; static;
	end;

	Exception = class
		msg: string;
		constructor Create(const msg: string);
		constructor Create(const msg: string; const args: array of const);
		class function Message(obj: TObject): string; static;
		class function Message: string; static;
	end;

	LogicError = class(Exception)
		procedure AfterConstruction; override;
	end;

	Interception = class(Exception) end;
	InvisibleInterception = class(Interception)
		procedure AfterConstruction; override;
	end;

	SpecialException = class(Exception)
		procedure AskForLastResort; virtual; abstract;
	end;

	OutOfMemory = class(SpecialException)
		procedure FreeInstance; override;
		procedure AskForLastResort; override;
	private
		CanDieNow: boolean;
		RainyDayReserve: pointer;
		procedure ReleaseReserve;
		class procedure InitGlobal; static;
		class procedure DoneGlobal; static;
	public const
		ReserveAmount = 1024 * sizeof(pointer);
		DefaultMessage = 'Недостаточно памяти.';
	class var
		Instance: OutOfMemory;
	end;

	StackOverflow = class(SpecialException)
		destructor Destroy; override;
		procedure AskForLastResort; override;
	private
		lastResort: boolean;
	public const
		DefaultMessage = 'Произошло переполнение стека вызовов.';
	end;

	Session = object
	private class var
		oldExceptProc: TExceptProc;
		msvcrt: DLL;
		_resetstkoflw: function: cint; cdecl;
		class constructor Init;
		class procedure Done; static; // все правильно, разруливается через AddExitProc
		class function HumanTrace(frames: pCodePointer = nil; frameCount: SizeInt = -1): string; static;
		class procedure PrintError(const msg: string); static;
		class procedure OnUnhandledException(Obj: TObject; Addr: CodePointer; FrameCount: LongInt; Frame: PCodePointer); static;
		class procedure OnRuntimeError(ErrNo: Longint; Address: CodePointer; Frame: Pointer); static;
	{$ifdef assert} class procedure OnFailedAssert(const msg, fname: shortstring; lineno: longint; erroraddr: pointer); static; {$endif}
		// не собирает трейс, просто печатает сообщение и убивает процесс
		class procedure Die(const msg: string; exitcode: Windows.UINT = 1); noreturn; static;
		class procedure TestHacks; static;
	end;

var
	SingletonLock: ThreadLock;
	Con: Console;
	ExecRoot: string;
	MainThreadID: TThreadID;

{$ifdef _} {$error} {$endif}
{$define _ := result := self;}
	function DLL.Proxy.Prefix(const prefix: string): Proxy;
	begin _
		dll^.prefix := prefix;
	end;

	function DLL.Proxy.Func(const name: string; var funcPtr{: CodePointer}): Proxy;
	var
		finalName: string;
		fptr: CodePointer absolute funcPtr;
	begin _
		finalName := dll^.prefix + name;
		fptr := GetProcAddress(dll^.h, pChar(finalName));
		if not Assigned(fptr) and (dll^.temper <> DontThrow) then
		begin
			dll^.Unload;
			raise Exception.Create('Функция {} не найдена в {}.', [finalName, dll^.fn]);
		end;
		pCodePointer(Ary(dll^.fptrs).Grow(TypeInfo(dll^.fptrs))^) := @fptr;
	end;
{$undef _}

	function DLL.Load(const fn: string; e: ThrowBehaviour = Throw): Proxy;
	begin
		Assert(h = 0);
		h := LoadLibraryW(pWideChar(fn.ToUTF16));
		if (h = 0) and (e <> DontThrow) then raise Win32.Error('Не удалось загрузить {}. {Err.}', [fn], GetLastError);
		self.fn := fn;
		temper := e;
		result.dll := @self;
	end;

	procedure DLL.Unload;
	var
		i: SizeInt;
	begin
		for i := 0 to High(fptrs) do fptrs[i]^ := nil;
		fptrs := nil;
		if (h <> 0) and not FreeLibrary(h) then Win32.Warning('FreeLibrary', GetLastError);
		h := 0;
	end;

	function GetFileSizeEx(hFile: HANDLE; lpFileSize: PLARGE_INTEGER): Windows.BOOL; stdcall; external kernel32;

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
		k32.Load(kernel32).Func('CreateThreadpoolIo', CreateThreadpoolIo).Func('CloseThreadpoolIo', CloseThreadpoolIo).
			Func('StartThreadpoolIo', StartThreadpoolIo).Func('CancelThreadpoolIo', CancelThreadpoolIo).
			Func('InitializeSRWLock', InitializeSRWLock).
			Func('AcquireSRWLockExclusive', AcquireSRWLockExclusive).
			Func('ReleaseSRWLockExclusive', ReleaseSRWLockExclusive).
			Func('InitializeConditionVariable', InitializeConditionVariable).
			Func('WakeAllConditionVariable', WakeAllConditionVariable).Func('WakeConditionVariable', WakeConditionVariable).
			Func('SleepConditionVariableSRW', SleepConditionVariableSRW);
		exe := QueryString(QueryStringCallback(@Win32.QueryModuleFileName), nil, 'имени исполняемого файла').ToUTF8;
		p := length(exe);
		while (p > 0) and not (exe[p] in ['\', '/']) do dec(p);
		ExecRoot := exe.Head(p);
	end;

	class procedure Win32.Done;
	begin
		k32.Unload;
	end;

	class function Win32.DescribeError(const code: ErrorCode): string; static;
	var
		werr: widestring;
		fflags: dword;
		ptr, fsrc: pointer;
		dll: im.DLL;
	begin
		result := '';
		if code.value = 0 then
			result := 'Причина неизвестна.'
		else
		begin
			if code.from = code.Origin.NTSTATUS then dll.Load('NTDLL.DLL');
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

		result := IfThen(result = '', 'Ошибка с кодом {1}.', '{0} ({1})').Format([result,
			IfThen(code.from = code.Origin.NTSTATUS, HexStr(code.value, bitsizeof(Win32.NTSTATUS) div 4), ToString(code.value))]);
	end;

	class function Win32.ErrorMessage(const fmt: string; const args: array of const; const code: ErrorCode): string;
	begin
		result := fmt
			.Replace('{Err.}', StringHelper.ReplaceFunction(@Win32.ReplaceWithErrorDescription), @code)
			.Replace('{err.}', StringHelper.ReplaceFunction(@Win32.ReplaceWithErrorDescription), @code).Format(args);
	end;

	class function Win32.Error(const fmt: string; const args: array of const; const code: ErrorCode): Exception;
	begin
		result := Exception.Create(ErrorMessage(fmt, args, code));
	end;

	class function Win32.OperationFailed(const what: string; const code: ErrorCode): Exception;
	begin
		result := Error('Не удалось {}: {err.}', [what], code);
	end;

	class function Win32.ConvertCase(const text: string; &to: &Case): string;
	var
		ws: widestring;
	begin
		ws := text.ToUTF16;
		case &to of
			&Case.Lower: CharLowerW(pWideChar(ws));
			&Case.Upper: CharUpperW(pWideChar(ws));
			else raise LogicError.Create('CharCase = {}'.Format([ord(&to)]));
		end;
		result := ws.ToUTF8;
	end;

	class procedure Win32.Warning(const text: string);
	begin
		writeln(stderr, text.ToUTF16);
	end;

	class procedure Win32.Warning(const what: string; const code: ErrorCode);
	begin
		Warning(ErrorMessage('{}: {err.}', [what], code));
	end;

	class function Win32.CommandLineTail: string;
	var
		i, d: SizeInt;
	begin
		result := widestring(GetCommandLineW).ToUTF8;
		// отрезать argv[0], https://stackoverflow.com/a/36876057
		i := 1;
		if pChar(result)[i-1] = '"' then
		begin
			d := IndexChar(pChar(result)[i+1-1], length(result) - i, '"');
			if d >= 0 then i += {"} 1 + d + {"} 1;
		end else
			result.ConsumeUntil([' ', StringHelper.Tab], i, i);
		result.Consume([' ', StringHelper.Tab], i, i);
		delete(result, 1, i - 1);
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
				if len = ReasonableLimit then raise Exception.Create('Неправдоподобная длина {}.', [ofWhat]);
				len := min(2 * len, SizeUint(ReasonableLimit));
			end else
			begin
				if (report = len + 1) or (report - 1 > ReasonableLimit) then
					raise Exception.Create('Получена неправдоподобная длина {} ({}).', [ofWhat, len]);
				len := report - 1;
			end;
		until false;
	end;

	class procedure Win32.QueryModuleFileName(buf: pWideChar; nBuf: size_t; out len: size_t; param: pointer);
	var
		r: dword;
	begin {$define args := param} unused_args
		r := GetModuleFileNameW(0, buf, nBuf);
		if (r = 0) and (nBuf > 0) then raise OperationFailed('получить имя исполняемого файла (GetModuleFileName)', GetLastError);
		if r >= nBuf then len := QUERY_STRING_LENGTH_UNKNOWN else len := r; // документированная багофича GetModuleFileName
	end;

	class function Win32.ReplaceWithErrorDescription(const src, sample: string; pos: SizeInt; param: pointer): string;
	begin {$define args := src _ pos} unused_args
		result := Win32.DescribeError(Win32.ErrorCode(param^));
		if sample[2] = 'e' then result := result.LowercaseFirst;
	end;

	procedure ThreadLock.Init;
	begin
		Win32.InitializeSRWLock(srw);
	{$ifdef Debug} Assert(not Assigned(guard)); guard := GetMem(1); {$endif}
	end;

	procedure ThreadLock.Done;
	begin
	{$ifdef Debug} FreeMem(guard); {$endif}
	end;

	procedure ThreadLock.Enter;
	begin
	{$ifdef Debug} Assert(owner <> ThreadID, 'эта блокировка не захватывается рекурсивно'); {$endif}
		Win32.AcquireSRWLockExclusive(srw);
	{$ifdef Debug} owner := ThreadID; {$endif}
	end;

	procedure ThreadLock.Leave;
	begin
	{$ifdef Debug} owner := 0; {$endif}
		Win32.ReleaseSRWLockExclusive(srw);
	end;

	function ThreadLock.AcquiredAssert: boolean;
	begin
		result := {$ifdef Debug} owner = ThreadID {$else} true {$endif};
	end;

	procedure ThreadCV.Init;
	begin
		Win32.InitializeConditionVariable(cv);
	{$ifdef Debug} Assert(not Assigned(guard)); guard := GetMem(1); {$endif}
	end;

	procedure ThreadCV.Done;
	begin
	{$ifdef Debug} FreeMem(guard); {$endif}
	end;

	procedure ThreadCV.Wait(var lock: ThreadLock);
	begin
		Assert(lock.AcquiredAssert);
	{$ifdef Debug} lock.owner := 0; {$endif}
		if not Win32.SleepConditionVariableSRW(cv, lock.srw, INFINITE, 0) then
			raise Win32.OperationFailed('выполнить ожидание (SleepConditionVariableSRW)', GetLastError);
	{$ifdef Debug} lock.owner := ThreadID; {$endif}
	end;

	procedure ThreadCV.WakeAll;
	begin
		Win32.WakeAllConditionVariable(cv);
	end;

	procedure ThreadCV.WakeOne;
	begin
		Win32.WakeConditionVariable(cv);
	end;

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
				raise Exception.Create('WaitForSingleObject вернула {}', [r]);
	end;

	destructor Cookie.Destroy;
	begin
		if Assigned(man) then
		begin
			man.Lock;
			try
				if (index >= length(man.cookies)) or (man.cookies[index] <> self) then raise LogicError.Create('Что-то не так с печенькой.');
				man.cookies[index] := man.cookies[High(man.cookies)];
				man.cookies[index].index := index;
				SetLength(man.cookies, length(man.cookies) - 1);
			finally
				man.Unlock;
				man := nil;
			end;
		end;
		inherited;
	end;

	constructor CookieManager.Create;
	begin
		inherited Create;
		lck.Init;
	end;

	destructor CookieManager.Destroy;
	begin
		lck.Done;
		inherited;
	end;

	procedure CookieManager.Lock;
	begin
		lck.Enter;
	end;

	procedure CookieManager.Unlock;
	begin
		lck.Leave;
	end;

	procedure CookieManager.Add(ck: Cookie);
	begin
		if Assigned(ck.man) then raise LogicError.Create('Печенька уже добавлена.');
		ck.man := self;
		Lock;
		try
			ck.index := length(cookies);
			Ary(cookies).Push(ck, TypeInfo(cookies));
		finally
			Unlock;
		end;
	end;

	function CookieManager.Count: SizeInt;
	begin
		Assert(lck.AcquiredAssert);
		result := length(cookies);
	end;

	procedure Console.Init;
	var
		info: CONSOLE_SCREEN_BUFFER_INFO;
	begin
		Assert(bookkeep = []);
		if Assigned(Instance) then raise LogicError.Create('Консоль должна быть одна.');
		Instance := @self;

		try
			lock.Init; bookkeep += [LockCreated];
			hIn := CreateFileW('CONIN$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_READ, nil, OPEN_EXISTING, 0, 0);
			if hIn = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для ввода', GetLastError);
			bookkeep += [HInSet];
			hOut := CreateFileW('CONOUT$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_WRITE, nil, OPEN_EXISTING, 0, 0);
			if hOut = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для вывода', GetLastError);
			bookkeep += [HOutSet];

			if not GetConsoleScreenBufferInfo(hOut, (@info)^) then raise Win32.OperationFailed('получить информацию от консоли (GetConsoleScreenBufferInfo)', GetLastError);
			defCol := BitsToColor[info.wAttributes and %1111];
			defBg := BitsToColor[info.wAttributes shr 4 and %1111];
			defAttrWoCol := info.wAttributes and not word(%11111111); // FOREGROUND_* и BACKGROUND_*
			ctrlCHandlers := CookieManager.Create;

			if not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), true) then
				raise Win32.OperationFailed('установить Ctrl-обработчик (SetConsoleCtrlHandler)', GetLastError);
			bookkeep += [HandlerInstalled];
		except
			Done;
			raise;
		end;
	end;

	procedure Console.Done;
	begin
		if LockCreated in bookkeep then lock.Enter;
		try
			if (HandlerInstalled in bookkeep) and not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), false) then Win32.Warning('SetConsoleCtrlHandler', GetLastError);
			bookkeep -= [HandlerInstalled];
			FreeAndNil(ctrlCHandlers);
			if Instance = @self then Instance := nil;
		finally
			if LockCreated in bookkeep then lock.Leave;
		end;
		if (HOutSet in bookkeep) and (hOut <> INVALID_HANDLE_VALUE) and not CloseHandle(hOut) then Win32.Warning('CloseHandle', GetLastError);
		bookkeep -= [HOutSet];
		lock.Done; bookkeep -= [LockCreated];
	end;
	function Console.OK: boolean; begin result := HOutSet in bookkeep; end;

	procedure Console.Write(const s: string);
	begin
		lock.Enter;
		try
			if bookkeep * [HOutSet, Broken] <> [HOutSet] then
			begin
				system.write(s.ToUTF16);
				exit;
			end;

			UseWriteConsoleW(s);
		finally
			lock.Leave;
		end;
	end;
	procedure Console.Line(const s: string = ''); begin Write(s + EOL); end;

	procedure Console.Colored(const s: string; baseCol: SizeInt = -1);
	var
		pieces: PiecesList;
		i: SizeInt;
		activeColor, newColor, activeBg, newBg: Color;
	begin
		pieces := ParseMarkdown(s);
		activeColor := defCol; activeBg := defBg;
		lock.Enter;
		try
			if bookkeep * [HOutSet, Broken] <> [HOutSet] then
			begin
				for i := 0 to High(pieces) do system.write(pieces[i].data.ToUTF16);
				exit;
			end;

			for i := 0 to High(pieces) do
			begin
				if pieces[i].color >= 0 then newColor := Color(pieces[i].color) else if baseCol >= 0 then newColor := Color(baseCol) else newColor := defCol;
				if newColor = defBg then newBg := Color(ord(High(Color)) - ord(newColor)) else newBg := defBg;
				if (activeColor <> newColor) or (activeBg <> defBg) then SetConsoleTextAttribute(hOut, defAttrWoCol or ColorToBits[newColor] or ColorToBits[newBg] shl 4);
				activeColor := newColor;
				activeBg := newBg;
				UseWriteConsoleW(pieces[i].data);
			end;
		finally
			if (activeColor <> defCol) or (activeBg <> newBg) then SetConsoleTextAttribute(hOut, defAttrWoCol or ColorToBits[defCol] or ColorToBits[defBg] shl 4);
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
						result += s.AB(start, i + 1) + '<';
						start := i + 1; i := start;
					end;
				else inc(i);
			end;
		result += s.Tail(start);
	end;

	function Console.ReadLine: string;
	var
		buf: packed array[0 .. 255] of widechar;
		data: widestring;
		got, i: dword;
	begin
		data := '';
		// Я, наверное, что-то делаю не так, потому что у меня после WriteConsoleInput первая (и только первая) ReadConsole возвращает мусор.
		if not ReadConsoleW(hIn, nil, 0, (@got)^, nil) then raise Win32.OperationFailed('выполнить фиктивное чтение с консоли (ReadConsole)', GetLastError);
		Intercept;

		repeat
			if not ReadConsoleW(hIn, @buf, length(buf), (@got)^, nil) then raise Win32.OperationFailed('прочитать ввод с консоли (ReadConsole)', GetLastError);
			Intercept;
			i := 0;
			while i < got do
				if buf[i] in [#13, #10] then break else inc(i);
			data += Copy(buf, 0, i);
		until i < got;

		FlushInput;
		result := data.ToUTF8;
	end;

	procedure Console.Intercept;
	begin
		lock.Enter; try UnlockedIntercept; finally lock.Leave; end;
	end;

	procedure Console.DisableCtrlC;
	begin
		lock.Enter;
		try
			bookkeep := bookkeep - [CtrlCPending] + [CtrlCDisabled];
		finally
			lock.Leave;
		end;
	end;

	function Console.RegisterCtrlCHandler(handler: CtrlCHandler; param: pointer): CtrlCCookie;
	begin
		result := CtrlCCookie.Create;
		try
			result.handler := handler;
			result.param := param;
			ctrlCHandlers.Add(result);
		except
			result.Free;
			raise;
		end;
	end;

	class function Console.CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; stdcall;
	var
		i: SizeInt;
		inp: array of INPUT_RECORD;
		written: dword;
		hey: widestring;
		any: boolean;
	begin
		result := false;
		if dwCtrlType = CTRL_C_EVENT then
		begin
			if Assigned(Instance) then
			begin
				Instance^.lock.Enter;
				try
					if CtrlCDisabled in Instance^.bookkeep then exit;

					result := true;
					// Внимание, система запускает этот обработчик в отдельном потоке, бросать исключение не вариант.
					Instance^.ctrlCHandlers.Lock;
					try
						any := false;
						for i := 0 to Instance^.ctrlCHandlers.Count - 1 do
							with CtrlCCookie(Instance^.ctrlCHandlers.cookies[i]) do
								any := any or handler(param);
					finally
						Instance^.ctrlCHandlers.Unlock;
					end;

					if not any then
					begin
						Instance^.bookkeep += [CtrlCPending];
						// Разблокировать ReadConsole: https://blog.not-a-kernel-guy.com/2009/12/29/726/.
						// По умолчанию ReadConsole не возвращается до конца строки (включен режим ENABLE_LINE_INPUT).
						hey := #13;
						SetLength(inp, 2 * length(hey));
						for i := 0 to High(inp) do
						begin
							inp[i].EventType := KEY_EVENT;
							inp[i].Event.KeyEvent.bKeyDown := i mod 2 = 0;
							inp[i].Event.KeyEvent.wRepeatCount := 1;
							inp[i].Event.KeyEvent.wVirtualKeyCode := 0;
							inp[i].Event.KeyEvent.wVirtualScanCode := 0;
							inp[i].Event.KeyEvent.UnicodeChar := hey[1 + uint(i) div 2];
							inp[i].Event.KeyEvent.dwControlKeyState := 0;
						end;
						if not WriteConsoleInput(Instance^.hIn, INPUT_RECORD(pointer(inp)^), length(inp), (@written)^) then Win32.Warning('WriteConsoleInput', GetLastError);
						if written <> SizeUint(length(inp)) then Win32.Warning('WriteConsoleInput: запрошено {} <-> записано {}.'.Format([ToString(length(inp)), ToString(written)]));
					end;
				finally
					Instance^.lock.Leave;
				end;
			end;
		end;
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
						if pChar(s)[i + 1 - 1] = '<' then
						begin
							Append(start, i - start + 1, colorStack[csp]);
							start := i + 2; i := start; goto nextsym;
						end;
						if s.Prefixed('/>', i + 1) then
						begin
							if csp = 0 then raise Exception.Create('{}: антипереполнение стека цветов.', [s.Stuffed(i, 0, '|')]);
							Append(start, i - start, colorStack[csp]);
							dec(csp);
							start := i + 3; i := start; goto nextsym;
						end;
						for c in Color do
							if s.Prefixed(ColorNames[c], i + 1) and (pChar(s)[i + length(ColorNames[c]) + 1 - 1] = '>') then
							begin
								if csp = High(colorStack) then raise Exception.Create('Переполнен стек цветов ({}).', [High(colorStack)]);
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
		UnlockedIntercept;
		ws := text.ToUTF16; p := pWideChar(ws);
		repeat
			n := min(length(ws) - (p - pWideChar(ws)), BlockSize);
			if not WriteConsoleW(hOut, p, n, (@written)^, nil) then begin bookkeep += [Broken]; raise Win32.OperationFailed('вывести на консоль {} с. (WriteConsoleW)'.Format([n]), GetLastError); end;
			if written <> n then begin bookkeep += [Broken]; raise Exception.Create('WriteConsoleW: n = {}, written = {}.', [n, written]); end;
			p += n;
			UnlockedIntercept;
		until p = pWideChar(ws) + length(ws);
	end;

	procedure Console.FlushInput;
	begin
		if not FlushConsoleInputBuffer(hIn) then raise Win32.OperationFailed('очистить буфер консоли (FlushConsoleInputBuffer)', GetLastError);
	end;

	procedure Console.UnlockedIntercept;
	begin
		Assert(lock.AcquiredAssert);
		if CtrlCPending in bookkeep then
		begin
			bookkeep -= [CtrlCPending];
			FlushInput;
			raise Interception.Create('Получено прерывание с клавиатуры (Ctrl-C).');
		end;
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
	var
		c2: Win32.ErrorCode;
	begin
		if (code.value = 0) and (transferred < pIORequest(req)^.size) then
			result := Exception.Create(
				IfThen(pIORequest(req)^.write, 'В {} записались {} b (вместо {} b).', 'Из {} прочитано {} b (вместо {} b).'),
					[pIORequest(req)^.h^.fn, transferred, pIORequest(req)^.size])
		else
		begin
			if code.value = STRANGE_ERROR then c2 := 0 else c2 := code;
			result := Win32.Error('Ошибка {} {}: {err.}', [RWGenitive[pIORequest(req)^.write], pIORequest(req)^.h^.fn], c2);
		end;
	end;

	class function &File.IOStatus.Create(req: pointer; const code: Win32.ErrorCode; const transferred: SizeUint; forceFail: boolean = false): IOStatus;
	begin
		result.req := req;
		result.code := code;
		if forceFail and (code.value = 0) then result.code.value := STRANGE_ERROR;
		result.transferred := transferred;
	end;

	procedure &File.Open(const fn: string; flags: Flags; r: pOpenResult = nil);
	var
		wfn: widestring;
		access, share, disp, attrs, err: dword;
		tryId: uint;
		h: HANDLE;
		ok: boolean;
		rb: PathRollback;
	begin
		ref := nil;
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
				ref := SharedHandle.Create(h, fn);
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
			if ok then r^.rb := rb else r^.errmsg := Win32.DescribeError(err);
		end else
			if not ok then raise Win32.Error('{}: {err.}', [fn], err);
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
			raise Win32.Error('{}: не удалось отменить I/O (CancelIO), {err.}', [ref^.fn], GetLastError);
	end;

	class function &File.SharedHandle.Create(h: HANDLE; const fn: string): pSharedHandle;
	begin
		system.new(result); result^.h := h; result^.tp_io := nil; result^.refcount := 1; result^.fn := fn;
		try
			result^.tp_io := Win32.CreateThreadpoolIo(h, Win32.TP_IO_CALLBACK(@&File.IOCompletionHandler), nil, nil);
			if not Assigned(result^.tp_io) then
				raise Win32.Error('{}: не удалось создать обработчик I/O (CreateThreadpoolIo), {err.}', [fn], GetLastError);
		except
			result^.h := 0; // до успешного завершения h принадлежит вызывающему
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
				if h <> 0 then CloseHandle(h);

				// You should close the associated file handle and wait for all outstanding overlapped I/O operations to complete
				// before calling this function.
				if Assigned(tp_io) then Win32.CloseThreadpoolIo(tp_io);
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
				if (i-1 > 0) and not (fn[i-1] in [':', '\', '/']) then // E:
				begin
					dir := fn.Head(i-1).ToUTF16;
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

	class procedure &File.IOCompletionHandler(Instance: Win32.PTP_CALLBACK_INSTANCE; Context: pointer;
		Overlapped: LPOVERLAPPED; IoResult: Windows.ULONG; NumberOfBytesTransferred: Windows.ULONG_PTR; Io: Win32.PTP_IO); stdcall;
	var
		req: pIORequest absolute Overlapped;
	begin {$define args := Instance _ Context _ Io} unused_args
		// IoResult — код GetLastError, а не NTSTATUS, как в BindIoCompletionCallback.
		CloseIORequest(req, IOStatus.Create(req, IoResult, NumberOfBytesTransferred), true);
	end;

	class function &File.CreateIORequest(h: pSharedHandle; const offset: FilePos; size, extraSize: SizeUint; write: boolean; onDone: CompletionHandler; param: pointer): pIORequest;
	begin
		result := nil;
		try
			if InterlockedIncrement(IOPending) = 1 then HeyNoIOPending.Reset;
			result := GetMem(sizeof(IORequest) - sizeof(IORequest.data) + extraSize);
		except
			CloseIORequest(nil, IOStatus.Dummy, false);
			raise;
		end;
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
		Win32.StartThreadpoolIo(h^.tp_io);
	end;

	class procedure &File.CloseIORequest(a: pIORequest; const status: IOStatus; fromCompletionCallback: boolean);
	begin
		if Assigned(a) then
		begin
			if not fromCompletionCallback then Win32.CancelThreadpoolIo(a^.h^.tp_io);
			a^.onDone(status, a^.param);

			// Нельзя закрывать до onDone. onDone иногда смотрит внутрь a^.h, например, чтобы узнать имя файла для сообщения об ошибке.
			a^.h^.Close(a^.h);
		end;
		FreeMemWeak(a);
		if InterlockedDecrement(IOPending) = 0 then HeyNoIOPending.&Set;
	end;

	procedure &File.IO(write: boolean; const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler; param: pointer);
	var
		a: pIORequest;
		transferred: dword;
		ok: boolean;
		syncExc: Exception;
	begin
		syncExc := nil;
		a := CreateIORequest(ref, at, size,

			// Если это «синхронная» запись — выделить вместе с IORequest временную область и скопировать в неё данные буфера.
			// В остальных случаях за целостность буфера на протяжении операции отвечает вызывающий.
			IfThen(write and not Assigned(onDone), size),
			write,

			// Запросы без onDone считаются синхронными.
			// В этом случае используется вспомогательный onDone, который, возможно, запишет ошибку в syncExc.
			// Если запишет — она бросается в вызывающего.
			CompletionHandler(IfThen(Assigned(onDone), onDone, @&File.OnDoneSync)),
			IfThen(Assigned(onDone), param, @syncExc));

		if write then
		begin
			if not Assigned(onDone) then Move(buf^, a^.data[0], size);
			ok := WriteFile(ref^.h, IfThen(Assigned(onDone), buf, @a^.data[0])^, size, dword(nil^), @a^.ov)
		end else
			ok := ReadFile(ref^.h, buf^, size, dword(nil^), @a^.ov);

		if ok then
		begin
			// Операция завершилась синхронно, IOCompletionHandler выполнен.

		end else if GetLastError = ERROR_IO_PENDING then
		begin
			// Операция начата асинхронно, IOCompletionHandler выполнится в будущем (в т. ч. при ошибке).
			// Если это чтение и не задан onDone, подождать завершения.
			// Если это запись, никогда не ждать. Без onDone получится fire-and-forget реквест.
			// (Может быть, я изменю это на полностью синхронный вариант, как с чтением — тогда extraSize можно будет убрать).
			if not write and not Assigned(onDone) then
				if not GetOverlappedResult(ref^.h, a^.ov, (@transferred)^, true) then
					raise Win32.Error('Не удалось получить результат {} {}. {Err.}', [RWGenitive[write], ref^.fn], GetLastError);

		end else
			// Операция провалилась, IOCompletionHandler не выполнен и не будет.
			CloseIORequest(a, IOStatus.Create(a, GetLastError, 0, true), false);

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
			if by > 0 then self := CreateNew(by, elemSize) else self := nil;
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
		Assert((@elem < self) or not Assigned(self) or (@elem > self + td^.elSize * SizeUint((pDynArrayHeader(self) - 1)^.high)), 'опасно передавать ссылку на ячейку');
		target := Grow(td^.elSize);
		Move(elem, target^, td^.elSize);
		fpc_addref(target, td^.elType2);
	end;

	function AryHelper.Empty: boolean;
	begin
		result := not Assigned(pointer(self));
	end;

	class function AryHelper.GrowStgy(n, alloc: SizeUint): SizeUint;
	var
		delta: SizeUint;
	begin
		Assert(n > alloc);
		if alloc <= 8 then delta := 4 else
		if alloc <= 128 then delta := 16 else
		if alloc <= 8*1024*1024 then delta := alloc div 4 else
			delta := alloc div 8;
		result := alloc + max(delta, n - alloc);
	end;

	class function AryHelper.ShrinkStgy(n, alloc: SizeUint; out na: SizeUint): boolean;
	begin
		result := (alloc >= 64) and (n < alloc div 4) or (n = 0) and (alloc > 0);
		if result then
			if n = 0 then na := 0 else na := alloc div 2;
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
		start, p, next, last: SizeInt;

		procedure Append(brkAt: SizeInt; const frag: string; continueAt: SizeInt);
		begin
			result += AB(start, brkAt) + frag; p := continueAt; start := p;
		end;

		function ParsePlural(brkAt, start: SizeInt; arg: SizeInt): boolean;
		var
			form, &end, cls: SizeInt;
			s: string;
		begin
			if (arg < 0) or (arg >= length(args)) then exit(false);
			s := VarRec.ToString(args[arg]);
			if length(s) < 1 then exit(false);
			form := 2 - ord(s[length(s)] = '1') + ord((s[length(s)] in ['0', '5'..'9']) or (length(s) >= 2) and (s[length(s) - 1] = '1'));

			while form > 1 do
				if not ConsumeUntil(['/', '}'], start, start) or (pChar(self)[start-1] = '}') then exit(false) else
					if pChar(self)[start-1] = '/' then dec(form);

			ConsumeUntil(['/', '}'], start, &end);
			ConsumeUntil(['}'], &end, cls);
			result := pChar(self)[cls - 1] = '}';
			if result then Append(brkAt, AB(start, &end), cls + 1);
		end;

		function ParseArg(brkAt, start: SizeInt): boolean;
		var
			nn, index: SizeInt;
		begin
			Consume(['0' .. '9'], start, nn);
			if not (((nn = start) and (next < length(args)) or TryParse(AB(start, nn), index) and (index >= 0) and (index < length(args)))) then exit(false);
			if pChar(self)[nn - 1] = '}' then
			begin
				if nn = start then begin index := next; inc(next); end;
				Append(brkAt, VarRec.ToString(args[index]), nn + 1);
				last := index;
				result := true;
			end else
				result := (nn > start) and (pChar(self)[nn - 1] = ':') and ParsePlural(brkAt, nn + 1, index);
		end;

	begin
		result := ''; start := 1; p := 1; next := 0; last := -1;
		while p <= length(self) do
		begin
			if self[p] = '{' then
				if pChar(self)[p + 1 - 1] = '{' then
					Append(p + 1, '', p + 2)
				else
					if ParseArg(p, p + 1) or ParsePlural(p, p + 1, last) then continue;
			inc(p);
		end;
		result += Tail(start);
	end;

	function StringHelper.Prefixed(const p: string; pos: SizeInt = 1): boolean;
	begin
		result := (pos + length(p) - 1 <= length(self)) and (CompareChar(self[pos], p[1], length(p)) = 0);
	end;

	function StringHelper.Head(count: SizeInt): string;
	begin
		result := AB(1, count + 1);
	end;

	function StringHelper.AB(start, ed: SizeInt): string;
	begin
		if (start <= 1) and (ed > length(self)) then result := self else result := Copy(self, start, ed - start);
	end;

	function StringHelper.Tail(start: SizeInt): string;
	begin
		result := AB(start, length(self) + 1);
	end;

	function StringHelper.ConvertCase(&to: &Case): string; begin result := Win32.ConvertCase(self, &to); end;
	function StringHelper.ConvertCaseFirst(&to: &Case): string;
	var
		n, t, nsp: SizeInt;
	begin
		t := 1; nsp := 0;
		while t <= length(self) do
			case self[t] of
				'A' .. 'Z', '_', '.', ':': begin inc(nsp); inc(t); end;
				'a' .. 'z': inc(t);
				else break;
			end;
		if nsp >= 3 then exit(self);

		if length(self) >= 1 then n := CodepointLen(1) else n := 0;
		result := Head(n).ConvertCase(&to) + Tail(n + 1);
	end;

	function StringHelper.Uppercase: string; begin result := ConvertCase(&Case.Upper); end;
	function StringHelper.UppercaseFirst: string; begin result := ConvertCaseFirst(&Case.Upper); end;
	function StringHelper.Lowercase: string; begin result := ConvertCase(&Case.Lower); end;
	function StringHelper.LowercaseFirst: string; begin result := ConvertCaseFirst(&Case.Lower); end;

	function StringHelper.Stuffed(at, remove: SizeInt; const &with: string): string;
	begin
		remove := min(remove, length(self) - at + 1);
		result := Head(at - 1) + &with + Tail(at + remove);
	end;

	function StringHelper.Split(sep: char; mergeSeps: boolean = true): Strings;
	begin
		result := Split([sep], mergeSeps);
	end;

	function StringHelper.Split(const seps: CharSet; mergeSeps: boolean = true): Strings;
	var
		start, ed, n, pass: SizeInt;
	begin
		for pass := 0 to 1 do
		begin
			start := 1; n := 0;
			while start <= length(self) do
			begin
				ed := start;
				while (ed <= length(self)) and not (self[ed] in seps) do inc(ed);

				if pass = 1 then result[n] := AB(start, ed);
				inc(n);
				start := ed;

				while (start <= length(self)) and (self[start] in seps) do
				begin
					inc(start);
					if not mergeSeps then break;
				end;
			end;
			if pass = 0 then SetLength(result, n);
		end;
	end;

{$if defined(consume_impl) or defined(complement)} {$error} {$endif}
{$define consume_impl :=
	begin
		np := p;
		while (np <= length(self)) and {$ifdef complement} not {$endif} (self[np] in syms) do inc(np);
		result := np > p;
	end; {$undef complement}}
	function StringHelper.Consume(const syms: CharSet; p: SizeInt; out np: SizeInt): boolean; consume_impl
	function StringHelper.ConsumeUntil(const syms: CharSet; p: SizeInt; out np: SizeInt): boolean; {$define complement} consume_impl
{$undef consume_impl}

	function StringHelper.Replace(const sample: string; repl: ReplaceFunction; param: pointer): string;
	var
		p, start: SizeInt;
	begin
		p := 1;
		start := 1;
		result := '';
		while p <= length(self) - length(sample) + 1 do
			if Prefixed(sample, p) then
			begin
				result += AB(start, p) + repl(self, sample, p, param);
				p += length(sample); start := p;
			end else
				inc(p);
		result += Tail(start);
	end;

	function StringHelper.Replace(const sample, by: string): string;
	begin
		result := Replace(sample, ReplaceFunction(@StringHelper.ReplaceByString), pointer(by));
	end;

	class function StringHelper.ReplaceByString(const src, sample: string; pos: SizeInt; param: pointer): string;
	begin {$define args := src _ sample _ pos} unused_args
		result := string(param);
	end;
	function StringHelper.AR: PAnsiRec; begin result := PAnsiRec(self) - 1; end;

	function WidestringHelper.ToUTF8: string;
	begin
		result := UTF8Encode(self);
		if Assigned(pointer(result)) then result.AR^.cpes.CodePage := CP_ACP;
	end;

	class function VarRec.VTypeToString(vt: SizeInt): string;
	var
		Known: Strings;
	begin
		Known := ('Integer/Boolean/Char/Extended/String/Pointer/PChar/Object/Class/WideChar/PWideChar/AnsiString/Currency/Variant/Interface/' +
			'WideString/Int64/QWord/UnicodeString').Split('/');
		if vt < length(Known) then result := 'vt{} ({})'.Format([Known[vt], vt]) else result := '? ({})'.Format([vt]);
	end;

	class function VarRec.ToString(const v: TVarRec): string;
	begin
		case v.VType of
			vtInteger: result := im.ToString(v.VInteger);
			vtBoolean: result := IfThen(v.VBoolean, 'да', 'нет');
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

	constructor Exception.Create(const msg: string; const args: array of const);
	begin
		Create(msg.Format(args));
	end;

	class function Exception.Message(obj: TObject): string;
	begin
		if obj is Exception then exit(Exception(obj).msg);
		if Assigned(obj) then exit(obj.ClassName);
		result := 'Произошла странная ошибка.';
	end;

	class function Exception.Message: string;
	begin
		if not Assigned(RaiseList) then raise LogicError.Create('Exception.Message вызвана вне блока обработки исключения.');
		result := Message(RaiseList[0].FObject);
	end;

	procedure LogicError.AfterConstruction;
	begin
		inherited;
		msg := 'Программная ошибка. ' + msg;
	end;

	procedure InvisibleInterception.AfterConstruction;
	begin
		inherited;
		msg += IfThen(msg <> '', ' ') + 'Вы не должны видеть этот текст, если видите — это баг.';
	end;

	procedure OutOfMemory.FreeInstance;
	begin
		// небольшой нюанс: деструктор отрабатывает ПЕРЕД FreeInstance, и единственная причина, благодаря которой
		// содержимое OutOfMemory.Instance остаётся тем же и OutOfMemory.Instance можно переиспользовать — это то,
		// что деструктор не вызывает CleanupInstance. А вот (inherited) TObject.FreeInstance — делает CleanupInstance и FreeMem(self).
		if CanDieNow then
		begin
			ReleaseReserve;
			if Instance = self then Instance := nil;
			inherited;
		end;
	end;

	procedure OutOfMemory.AskForLastResort;
	begin
		ReleaseReserve;
	end;

	procedure OutOfMemory.ReleaseReserve;
	begin
		FreeMemWeak(System.InterlockedExchange(RainyDayReserve, nil));
	end;

	class procedure OutOfMemory.InitGlobal;
	begin
		Instance := OutOfMemory.Create(OutOfMemory.DefaultMessage);
		Instance.RainyDayReserve := GetMem(ReserveAmount);
	end;

	class procedure OutOfMemory.DoneGlobal;
	begin
		if Assigned(Instance) then Instance.CanDieNow := true;
		Instance.Free;
	end;

	destructor StackOverflow.Destroy;
	begin
		if lastResort or Assigned(Session._resetstkoflw) and (Session._resetstkoflw() <> 0) then
			// OK
		else
			Session.Die(msg, RuntimeErrorExitCodes[reStackOverflow]);
		inherited;
	end;

	procedure StackOverflow.AskForLastResort;
	begin
		lastResort := true;
	end;

	procedure DoneSession; begin Session.Done; end;
	class constructor Session.Init;
	begin
		oldExceptProc := ExceptProc; ExceptProc := TExceptProc(@Session.OnUnhandledException);
		ErrorProc  := TErrorProc(@Session.OnRuntimeError);
	{$ifdef assert} AssertErrorProc := TAssertErrorProc(@Session.OnFailedAssert); {$endif}

		MainThreadID := ThreadID;
		OutOfMemory.InitGlobal;
		AddExitProc(@DoneSession); // иначе не вызовется при сбое инициализации

		// Чтобы операции вида sqrt(-5) или 1.0/0.0 давали NaN/Inf вместо floating-point exception.
		// Для полноты картины нужно сделать SetMXCSR(GetMXCSR or %1111110000000), но поговаривают, что SSE ведёт себя тихо по умолчанию.
		Set8087CW(Get8087CW or %111111);

		Win32.Init;
		SingletonLock.Init;
		Con.Init;
		TestHacks;
		msvcrt.Load('msvcrt.dll', DontThrow).Func('_resetstkoflw', _resetstkoflw);
	end;

	class procedure Session.Done;
	begin
		&File.WaitForAllIORequests;
		msvcrt.Unload;
		Con.Done;
		SingletonLock.Done;
		Win32.Done;
		OutOfMemory.DoneGlobal;
	end;

	// Если frameCount >= 0, frames — готовый трейс, который просто просят преобразовать в строку.
	// Если frameCount < 0, frames — указатель на единственный кадр, с которого трейс раскручивается автоматически.
	// Если при этом frames не указан, берётся вызывающий.
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
			p := 1;
			result := ((line.Consume([StringHelper.Tab, ' '], p, p) and false) or not line.Consume(['$'], p, p) or
				not line.Consume(['0' .. '9', 'A' .. 'F'], p, p)) or (line.Consume([StringHelper.Tab, ' '], p, p) and false) or
				(p < length(line));
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
				if i = 0 then if Assigned(frames) then frame := frames^ else frame := get_caller_frame(get_frame);
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
				result += EOL + IfThen(trace[i].uninteresting = 0,
					trace[i].line,
					'(...)' + IfThen(trace[i].uninteresting > 1, ' x{}'.Format([trace[i].uninteresting])));
	end;

	class procedure Session.PrintError(const msg: string);
	begin
		if Con.OK then
		begin
			Con.ColoredLine(msg, Con.Red);
			Con.ReadLine;
		end else
		begin
			writeln(stderr, msg.ToUTF16);
			readln;
		end;
	end;

	// При обработке исключения может вылететь другое исключение.
	// Пока забил, вызовется стандартный обработчик RTL через старую ExceptProc.
	// По-хорошему можно показать TaskDialog, а если и он провалится — MessageBox.
	//
	// Это даже не совсем паранойя, у меня часто перестают работать русские буквы в консоли после смены системной локали :).
	// (WriteConsole возвращает 31 ERROR_GEN_FAILURE).
	class procedure Session.OnUnhandledException(Obj: TObject; Addr: CodePointer; FrameCount: LongInt; Frame: PCodePointer);
	var
		msg: string;
		eo, nx: PExceptObject;
	begin {$define args := Addr} unused_args
		if Con.OK then Con.DisableCtrlC;
		ExceptProc := oldExceptProc;
		if Obj is SpecialException then SpecialException(Obj).AskForLastResort;
		msg := Exception.Message(Obj);
		if not (Obj is SpecialException) then msg += HumanTrace(Frame, FrameCount);
		PrintError(msg);

		// А этот хак настолько грязный, что нельзя легко проверить его состоятельность при недокументированных изменениях в RTL
		// (к счастью, всегда есть альтернатива: не заморачиваться и сделать сеппуку aka TerminateProcess). Дело вот в чём.
		//
		// Если ExceptProc вернулась, RTL вызывает halt, которая несколько мягче TerminateProcess: она выполняет финализацию,
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
			FreeMemWeak(eo^.Frames);
			nx := eo^.next; dispose(eo); eo := nx;
		end;
	end;

	class procedure Session.OnRuntimeError(ErrNo: Longint; Address: CodePointer; Frame: Pointer);
	type
	{$push} {$scopedenums off} Plan = (ThrowMessage, ThrowOOM, ThrowStackOverflow, Seppuku); {$pop}
	const
		KnownErrors: array[0 .. 6] of record
			re: TRuntimeError;
			plan: Plan;
			msg: string;
		end =
		(
			(re: reOutOfMemory; plan: ThrowOOM; msg: OutOfMemory.DefaultMessage),
			(re: reDivByZero; plan: ThrowMessage; msg: 'Произошло деление на 0.'),
			(re: reRangeError; plan: ThrowMessage; msg: 'Range check: целочисленное значение вышло за допустимые границы.'),
			(re: reIntOverflow; plan: ThrowMessage; msg: 'Overflow check: произошло целочисленное переполнение.'),
			(re: reInvalidOp; plan: ThrowMessage; msg: 'Выполнена недопустимая процессорная операция.'),
			(re: reAccessViolation; plan: Seppuku; msg: 'Произошло обращение по неверному адресу (AV).'),
			(re: reStackOverflow; plan: ThrowStackOverflow; msg: StackOverflow.DefaultMessage)
		);
	var
		name: string;
		i: SizeInt;
	begin {$define args := Address} unused_args
		for i := 0 to High(KnownErrors) do
			if ErrNo = RuntimeErrorExitCodes[KnownErrors[i].re] then
			begin
				case KnownErrors[i].plan of
					ThrowMessage: raise Exception.Create(KnownErrors[i].msg);
					ThrowOOM: if Assigned(OutOfMemory.Instance) then raise OutOfMemory.Instance;
					ThrowStackOverflow: raise StackOverflow.Create(StackOverflow.DefaultMessage);
				end;
				Die(KnownErrors[i].msg + HumanTrace(@Frame), ErrNo);
			end;

		i := IndexByte(RuntimeErrorExitCodes, length(RuntimeErrorExitCodes), ErrNo);
		if (ErrNo <= High(byte)) and (i >= 0) then
		begin
			str(TRuntimeError(i), name);
			if name.Prefixed('re') then name := name.Tail(length('re') + 1);
		end else
			name := 'с кодом {}'.Format([ToString(ErrNo)]);
		Die('Возникла ошибка {}.'.Format([name]) + HumanTrace(@Frame), ErrNo);
	end;

{$ifdef assert}
	class procedure Session.OnFailedAssert(const msg, fname: shortstring; lineno: longint; erroraddr: pointer);
	var
		m: string;
	begin
		m := IfThen(msg <> '', msg, 'ассерт провален');
		if fname <> '' then m := fname + IfThen(lineno >= 0, ':' + ToString(lineno)) + ': ' + m else m := m.UppercaseFirst;
		Die(m + '.' + HumanTrace(@erroraddr));
	end;
{$endif}

	class procedure Session.Die(const msg: string; exitcode: Windows.UINT = 1);
	begin
		try
			PrintError(msg);
		finally
			// Лучше не ExitProcess: https://blog.not-a-kernel-guy.com/2007/07/15/210/.
			// Алсо, в общем случае TerminateProcess не ждёт завершения процесса и сразу возвращается,
			// но TerminateProcess(GetCurrentProcess) — не очень документированный синхронный частный случай: https://stackoverflow.com/a/40499062.
			TerminateProcess(GetCurrentProcess, exitcode);
		end;
	end;

	class procedure Session.TestHacks;
		procedure TestAnsiRecHack;
		var
			s, s2: string;
		begin
			s := im.ToString(ThreadID);
			(@s2)^ := s;
			if (s.AR^.cpes.CodePage <> CP_ACP) or (s.AR^.cpes.ElementSize <> 1) or (s.AR^.ref <> 2) or (length(s) <> s.AR^.len) then
				raise Exception.Create('Хак AnsiRec не работает: CP = {0} ({1}), ElementSize = {2} (1), RefCount = {3} (2), Length = {4} ({5}).'.Format([
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
			if length(a) <> 4 then raise Exception.Create('{0}: len = {1} (4).'.Format(['Хак DynArray не работает', length(a)]));

			ConstructExpected(exp);
			for i := 0 to High(a) do
				if (a[i].s <> exp[i].m.s) or (a[i].s.AR^.ref <> exp[i].ref) or (a[i].x <> exp[i].m.x) then
					raise Exception.Create('{0}: a[{1}] = {2}, exp. {3}'.Format(['Хак DynArray не работает', i, MRepr(a[i], a[i].s.AR^.ref), MRepr(exp[i].m, exp[i].ref)]));
		end;

	begin
		TestAnsiRecHack;
		TestDynArrayHack;
	end;

type
	// Учитывает память, выделенную какой-либо библиотекой, чтобы можно было доосвободить её руками, если аллокация бросила исключение.
	// Было бы намного проще ловить в аллокации исключение и преобразовывать в exit(nil), но у меня такой вариант почему-то часто сегфолтится.
	// Если выделенный блок предполагалось вернуть вызывающему, его придётся «отобрать» у следилки через TakeAway, которая вернёт real —
	// указатель, который нужно освободить через FreeMem (p указывает внутрь него).
	//
	// Например, lodepng_encode_memory выделяет блок для результата (зд. outData) самостоятельно, поэтому придётся делать так:
	// try
	//    errorcode := lodepng.encode_memory(outData, ...);
	// except
	//    lodepng.Purge(ThreadID);
	//    raise;
	// end;
	// if r = 0 then lodepng.TakeAway(outData, outDataBlock);
	// ...
	// FreeMem(outDataBlock);
	//
	// Кроме того, можно зарегистрировать пользовательский обработчик (RegisterHook), вызываемый при реаллокации.
	// Например, такой обработчик может бросить исключение, чтобы прервать процесс (это слегка рискованно, т. к. C-стек при этом не раскручивается).
	MemoryIsland = object
		procedure Init;
		procedure Done;
		function Realloc(p: pointer; nsize: size_t): pointer;
		procedure TakeAway(p: pointer; out real: pointer);
		procedure Purge(ownedBy: TThreadID);

	type
		Hook = procedure(param: pointer);
		HookCookie = class(im.Cookie)
		private
			thread: TThreadID;
			cb: Hook;
			param: pointer;
		end;
		function RegisterHook(thread: TThreadID; cb: Hook; param: pointer): HookCookie;

	strict private type
		pHeader = ^Header;
		Header = record
			watchIndex: SizeInt;
		end;
	var
		lock: ThreadLock;
		watchCount: SizeInt;
		watch: array of record
			data: pointer;
			thread: TThreadID;
		end;
		hooks: CookieManager;
		procedure Unwatch(index: SizeInt);
	end;

	procedure MemoryIsland.Init;
	begin
		lock.Init;
		Assert(watchCount = 0);
		hooks := CookieManager.Create;
	end;

	procedure MemoryIsland.Done;
	begin
		FreeAndNil(hooks);
		lock.Done;
	end;

	function MemoryIsland.Realloc(p: pointer; nsize: size_t): pointer;
	var
		watchIndex, i: SizeInt;
	begin
		lock.Enter;
		try
			hooks.Lock;
			try
				for i := 0 to hooks.Count - 1 do
					with HookCookie(hooks.cookies[i]) do
						if thread = ThreadID then cb(param);
			finally
				hooks.Unlock;
			end;

			if Assigned(p) then
			begin
				watchIndex := (pHeader(p) - 1)^.watchIndex;
				Assert(watchIndex < watchCount);
				Assert(watch[watchIndex].data = p);
				Assert(watch[watchIndex].thread = ThreadID);
				p -= sizeof(Header);
			end else
				watchIndex := -1;
			if nsize > 0 then nsize += sizeof(Header);
			result := ReallocMem((@p)^, nsize);

			if Assigned(result) then
			begin
				result += sizeof(Header);
				if watchIndex >= 0 then
					watch[watchIndex].data := result
				else
					try
						watchIndex := watchCount;
						inc(watchCount); if watchCount > length(watch) then SetLength(watch, Ary.GrowStgy(watchCount, length(watch)));
						(pHeader(result) - 1)^.watchIndex := watchIndex;
						watch[watchIndex].data := result;
						watch[watchIndex].thread := ThreadID;
					except
						FreeMemWeak(result - sizeof(Header));
						raise;
					end;
			end else
				if watchIndex >= 0 then Unwatch(watchIndex);
		finally
			lock.Leave;
		end;
	end;

	procedure MemoryIsland.TakeAway(p: pointer; out real: pointer);
	begin
		real := pHeader(p) - 1;
		Lock.Enter;
		try
			Unwatch(pHeader(real)^.watchIndex);
		finally
			Lock.Leave;
		end;
	end;

	procedure MemoryIsland.Purge(ownedBy: TThreadID);
	var
		p: SizeInt;
	begin
		lock.Enter;
		try
			p := 0;
			while p < watchCount do
				if watch[p].thread = ownedBy then
				begin
					FreeMemWeak(pHeader(watch[p].data) - 1);
					Unwatch(p);
				end else
					inc(p);
		finally
			lock.Leave;
		end;
	end;

	function MemoryIsland.RegisterHook(thread: TThreadID; cb: Hook; param: pointer): HookCookie;
	begin
		result := HookCookie.Create;
		try
			result.thread := thread;
			result.cb := cb;
			result.param := param;
			hooks.Add(result);
		except
			result.Free;
			raise;
		end;
	end;

	procedure MemoryIsland.Unwatch(index: SizeInt);
	var
		na: SizeInt;
	begin
		Assert(lock.AcquiredAssert);
		if index + 1 <> watchCount then
		begin
			watch[index] := watch[watchCount - 1];
			(pHeader(watch[index].data) - 1)^.watchIndex := index;
		end;
		dec(watchCount); if Ary.ShrinkStgy(watchCount, length(watch), SizeUint(na)) then SetLength(watch, na);
	end;

type
	lodepng = object
		class procedure Load(const fn: string); static;
		class procedure Unload; static;

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
		{$define enum := Preset} {$define items := Draft _ 0 _ Fast _ 1 _ Good _ 2 _ Uber _ 3} enum_with_shortcuts

	const
		CT_GREY = 0;       // greyscale: 1, 2, 4, 8, 16 bit
		CT_RGB = 2;        // RGB: 8, 16 bit
		CT_PALETTE = 3;    // palette: 1, 2, 4, 8 bit
		CT_GREY_ALPHA = 4; // greyscale with alpha: 8, 16 bit
		CT_RGBA = 6;       // RGB with alpha: 8, 16 bit

		Presets: array[Preset] of CompressionSettings = (
			(btype: 2; use_lz77: 1; windowsize: 256; minmatch: 3; nicematch: 64; lazymatching: 0),
			(btype: 2; use_lz77: 1; windowsize: 1024; minmatch: 3; nicematch: 128; lazymatching: 1),
			(btype: 2; use_lz77: 1; windowsize: 8192; minmatch: 3; nicematch: 128; lazymatching: 1),
			(btype: 2; use_lz77: 1; windowsize: 32768; minmatch: 3; nicematch: 258; lazymatching: 1));

	class var
		lib: DLL;
		island: MemoryIsland;
		decode_memory: function(out &out: pointer; out w, h: cuint; &in: pointer; insize: csize_t; colortype: cint; bitdepth: cuint;
			constref alloc: Allocator): cuint; cdecl;
		encode_memory: function(out &out: pointer; out outsize: csize_t; image: pointer; w, h: cuint; colortype: cint; bitdepth: cuint;
			constref settings: CompressionSettings; constref alloc: Allocator): cuint; cdecl;
		error_text: function(code: cuint): pChar; cdecl;

		class function ErrorMessage(code: cuint): string; static;
		class function GlobalAllocator: Allocator; static;
		class function LodeReAlloc(p: pointer; nsize: csize_t): pointer; cdecl; static;
	end;

	class procedure lodepng.Load(const fn: string);
	begin
		try
			island.Init;
			lib.Load(fn).Prefix('lodepng_').Func('decode_memory', decode_memory).Func('encode_memory', encode_memory).Func('error_text', error_text);
		except
			Unload;
			raise;
		end;
	end;

	class procedure lodepng.Unload;
	begin
		lib.Unload;
		island.Done;
	end;
	
	class function lodepng.ErrorMessage(code: cuint): string;
	var
		msg: string;
	begin
		msg := error_text(code);
		result := IfThen(msg <> 'unknown error code', '{0} (код ошибки {1})', 'код ошибки {1}').Format([msg, ToString(code)]);
	end;

	class function lodepng.GlobalAllocator: Allocator;
	begin
		result.realloc := reallocf(@lodepng.LodeReAlloc);
	end;

	class function lodepng.LodeReAlloc(p: pointer; nsize: csize_t): pointer; cdecl;
	begin
		result := island.Realloc(p, nsize);
	end;

type
	ImageFormat = (G, GA, RGB, RGBA);

	ImageFormatHelper = type helper for ImageFormat
		function PixelSize: size_t;
	const
		Info: array[ImageFormat] of record
			pixelSize: size_t;
		end =
		(
			(pixelSize: 1),
			(pixelSize: 2),
			(pixelSize: 3),
			(pixelSize: 4)
		);
	end;

	Image = object
		data: pointer;
		w, h: uint;
		format: ImageFormat;
		own: pointer;
		class function Create(data: pointer; w, h: uint; format: ImageFormat; own: pointer = nil): Image; static;
		procedure Done;

	type
		p1x8 = ^_1x8; _1x8 = array[0 .. 0] of uint8;
		p2x8 = ^_2x8; _2x8 = array[0 .. 1] of uint8;
		p3x8 = ^_3x8; _3x8 = array[0 .. 2] of uint8;
		p4x8 = ^_4x8; _4x8 = array[0 .. 3] of uint8;
	end;

	function ImageFormatHelper.PixelSize: size_t;
	begin
		result := Info[self].pixelSize;
	end;

	class function Image.Create(data: pointer; w, h: uint; format: ImageFormat; own: pointer = nil): Image;
	begin
		result.data := data;
		result.w := w;
		result.h := h;
		result.format := format;
		result.own := own; {$ifdef Debug} if not Assigned(own) then result.own := GetMem(1); {$endif}
	end;

	procedure Image.Done;
	begin
		FreeMem(own);
	end;

(*type
	pImageRegistry = ^ImageRegistry;
	ImageRegistry = object
	type
		ItemState = (Loading, Loaded, Failed);

		pItem = ^Item;
		Item = object
			img: Image;
			refcount: SizeInt;
			state: ItemState;
			ir: pImageRegistry;
			function Ref: pItem;
			procedure Release(var item: pItem);
		end;

		function Add(const data: Image; const name: string): pItem;
		function Load(const fn: string): pItem;
	private
		lock: ThreadLock;
		hey: ThreadCV;
	end;*)

var
	data: array[0 .. 1023, 0 .. 1023, 0 .. 2] of uint8;
	x, y: SizeInt;
	r_data, r_mem: pointer;
	rsize: size_t;
	loder: cuint;
	f: &File;
	conCtrlC: Console.CtrlCCookie;
	lodeThrow: lodepng.island.HookCookie;

	procedure InterceptLodeRealloc(param: pointer);
	begin {$define args := param} unused_args
		raise InvisibleInterception.Create('Прерывание lodepng_*.');
	end;

	function PostInterceptionOnCtrlC(param: pointer): boolean;
	begin {$define args := param} unused_args
		SingletonLock.Enter;
		try
			result := not Assigned(lodeThrow);
			if result then lodeThrow := lodepng.island.RegisterHook(MainThreadID, @InterceptLodeRealloc, nil);
		finally
			SingletonLock.Leave;
		end;
	end;

begin
	try
		try
			lodepng.Load('{}lib\{}\lodepng.dll'.Format([ExecRoot, CPUArch]));
			Con.Line('Генерация...');
			for y := 0 to High(data) do
				for x := 0 to High(data[0]) do
				begin
					data[y, x, 0] := round(High(data[0, 0, 0]) * clamp(sqr(1 - abs(1 - (x/High(data[0]) + y/High(data)))), 0, 1));
					data[y, x, 1] := round(High(data[0, 0, 0]) * clamp(1 - sqrt(abs(x/High(data[0])-0.5)) - sqrt(abs(y/High(data)-0.5)), 0, 1));
					data[y, x, 2] := round(High(data[0, 0, 0]) * clamp(1 - 4*sqr(x/High(data[0])-0.5) - 4*sqr(y/High(data)-0.5), 0, 1));
				end;
			Con.Line('Кодирование PNG...');
			conCtrlC := Con.RegisterCtrlCHandler(@PostInterceptionOnCtrlC, nil);
			try
				loder := lodepng.encode_memory(r_data, rsize, @data, length(data[0]), length(data), lodepng.CT_RGB, 8, lodepng.Presets[lodepng.Fast], lodepng.GlobalAllocator);
			except
				lodepng.island.Purge(ThreadID);
				raise;
			end;
			FreeAndNil(conCtrlC);
			if loder <> 0 then raise Exception.Create('Не удалось сохранить картинку: {}.'.Format([lodepng.ErrorMessage(loder)]));
			lodepng.island.TakeAway(r_data, r_mem);
			Con.Line('Сохранение...');
			f.Open(ExecRoot + 'test.png', [f.Writeable]);
			f.Write(0, r_data, rsize);
			Con.ColoredLine('<G>Картинка сохранена</>, <R>а ты пидор :з</>.');
		finally
			FreeAndNil(conCtrlC);
			FreeAndNil(lodeThrow);
			f.Close;
			FreeMem(r_mem);
			lodepng.Unload;
		end;
	except
		on e: Interception do Con.ColoredLine('<R>Выполнение прервано.');
	end;
	Con.ReadLine;
end.
