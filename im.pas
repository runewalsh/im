{$mode objfpc} {$h+} {$typedaddress+} {$macro on} {$modeswitch duplicatelocals+} {$modeswitch typehelpers+} {$scopedenums+}
{$ifopt Q+} {$define assert} {$else} {$ifdef assert} {$error} {$endif} {$endif}
{$R *.res}
program im;

uses
	CTypes, Windows;

{$define pp_repeat :=
	{$if times >= 1} {$define repid := 0} rep {$endif} {$if times >= 2} {$define repid := 1} rep {$endif}
	{$if times >= 3} {$define repid := 2} rep {$endif} {$if times >= 4} {$define repid := 3} rep {$endif}
	{$if times >= 5} {$error too many repeats} {$endif} {$undef repid} {$undef times} {$undef rep}}

{$define impl :=
	function ToString(x: typename): string; begin str(x, result); end;
	function TryParse(const s: string; out v: typename; wrong: pSizeInt = nil): boolean;
	var
		code: word;
	begin
		val(s, v, code);
		result := code = 0;
		if not result and Assigned(wrong) then wrong^ := code;
	end;

	function min(a, b: typename): typename; begin if a <= b then result := a else result := b; end;
	function max(a, b: typename): typename; begin if a >= b then result := a else result := b; end; {$undef typename}}
	{$define typename := int32} impl {$define typename := uint32} impl  {$define typename := int64} impl {$define typename := uint64} impl
{$undef impl}

type
	widestring = unicodestring;
	UTFchar = type uint32;
	FilePos = type uint64;
	FileSize = type uint64;
	casint = int32;
	sint = int32; uint = uint32;

type
	Exception = class;

	Win32 = object
	const
		USE_GETLASTERROR = High(DWORD) - 1;

		class function DescribeError(code: DWORD = USE_GETLASTERROR): string; static;
		class function OperationFailed(const what: string; code: DWORD = USE_GETLASTERROR): Exception; static;
		class function FileError(const fn: string; code: DWORD = USE_GETLASTERROR): Exception; static;
		class function Lowercase(const text: string): string; static;
		class procedure Warning(const what: string; code: DWORD = USE_GETLASTERROR); static;
		class function CommandLineTail: string; static;
	strict private
		class procedure CheckForUSE_GETLASTERROR(var code: DWORD); static;
	end;

	ThreadLock = object
		cs: CRITICAL_SECTION;
		ok: boolean;
		procedure Init; procedure Done; procedure Enter; procedure Leave;
	end;

	ThreadEvent = object
		h: HANDLE;
		procedure Init(manual, initialState: boolean); procedure Done; function OK: boolean; procedure &Set; procedure Reset; procedure Wait;
	end;

	Console = object
	type
		Color = (Black, Maroon, Green, Olive, Navy, Purple, Teal, Silver, Gray, Red, Lime, Yellow, Blue, Fuchsia, Aqua, White);
	var
		procedure Init;
		procedure Done;
		function OK: boolean;
		procedure Write(const s: string);
		procedure Line(const s: string);
		procedure Colored(const s: string; cl: SizeInt = -1); procedure Colored(const s: string; cl: Color);
		procedure ColoredLine(const s: string);               procedure ColoredLine(const s: string; cl: Color);
		function Escape(const s: string): string;
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
		Black = Color.Black; Maroon  = Color.Maroon;  Green = Color.Green; Olive = Color.Olive; Navy = Color.Navy; Purple = Color.Purple;
		Teal  = Color.Teal;  Silver  = Color.Silver;  Gray  = Color.Gray;  Red   = Color.Red;   Lime = Color.Lime; Yellow = Color.Yellow;
		Blue  = Color.Blue;  Fuchsia = Color.Fuchsia; Aqua  = Color.Aqua;  White = Color.White;
		ColorNames: array[Color] of string = ('0', 'r', 'g', 'rg', 'b', 'rb', 'gb', '.3', '.6', 'R', 'G', 'RG', 'B', 'RB', 'GB', '1');
	strict private const
		BitsToColor: array[0 .. 15] of Color = (Black, Navy, Green, Teal, Maroon, Purple, Olive, Gray, Silver, Blue, Lime, Aqua, Red, Fuchsia, Yellow, White);
		ColorToBits: array[Color] of word = (%0000, %0100, %0010, %0110, %0001, %0101, %0011, %1000, %0111, %1100, %1010, %1110, %1001, %1101, %1011, %1111);

	class var
		CtrlCHit: boolean;
	end;

	&File = object
	type
		Flag = (Readable, Writeable, Existing, New, Temp);
		Flags = set of Flag;

		pOpenResult = ^OpenResult;
		OpenResult = object
			ok, exist: boolean;
			errmsg: string;
		const
			Empty: OpenResult = (ok: false; exist: false; errmsg: '');
		end;

	const
		Readable = Flag.Readable; Writeable = Flag.Writeable; RW = [Readable, Writeable]; Existing = Flag.Existing; New = Flag.New; Temp = Flag.Temp;

		class procedure Open(out f: &File; const fn: string; flags: Flags = [Flag.Readable]; r: pOpenResult = nil); static;
		procedure Close;
		procedure Read(at: FilePos; buf: pointer; size: SizeUint);
		procedure Write(at: FilePos; buf: pointer; size: SizeUint);
		function Size: FileSize;

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

		pAsyncIORequest = ^AsyncIORequest;
		AsyncIORequest = object
			ov: Windows.OVERLAPPED;
			h: pSharedHandle;
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
		class function CreateAsyncIORequest(h: pSharedHandle; const offset: FilePos; extraSize: SizeUint): pAsyncIORequest; static;
		class procedure CloseAsyncIORequest(a: pAsyncIORequest); static;
	strict private class var
		AsioPending: casint;
		HeyNoAsioPending: ThreadEvent;
		class procedure GlobalInitialize; static;
		class procedure GlobalFinalize; static;
	public
		class procedure WaitForAllIORequests; static;
	end;

type
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
		class function ToString(const v: TVarRec): string; static;
		function Prefixed(const p: string; pos: SizeInt = 1): boolean;
		function Lowercase: string; function LowercaseFirst: string;
		function Stuffed(at: SizeInt; const &with: string): string;

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
		class constructor InitGlobal;
		class destructor DoneGlobal;
	end;

	Session = object
	private
		class constructor Init;
		class procedure Done; // все правильно, разруливается через AddExitProc
		class function HumanTrace(frames: pCodePointer = nil; frameCount: SizeInt = -1): string; static;
		class procedure OnUnhandledException(Obj: TObject; Addr: CodePointer; FrameCount: LongInt; Frame: PCodePointer); static;
		class procedure OnRuntimeError(ErrNo: Longint; Address: CodePointer; Frame: Pointer); static;
		class procedure TestHacks; static;
	end;

var
	SingletonLock: ThreadLock;
	Con: Console;

	function GetFileSizeEx(hFile: HANDLE; lpFileSize: PLARGE_INTEGER): Windows.BOOL; stdcall; external kernel32;
	function BindIoCompletionCallback(FileHandle: Windows.HANDLE; func: LPOVERLAPPED_COMPLETION_ROUTINE; flags: Windows.ULONG): Windows.BOOL; stdcall; external kernel32;

	class function Win32.DescribeError(code: DWORD = USE_GETLASTERROR): string; static;
	var
		werr: widestring;
		ptr: pointer;
	begin
		CheckForUSE_GETLASTERROR(code);
		if code = 0 then result := 'Причина неизвестна.' else
		begin
			if FormatMessageW(FORMAT_MESSAGE_ALLOCATE_BUFFER or FORMAT_MESSAGE_FROM_SYSTEM or FORMAT_MESSAGE_IGNORE_INSERTS or FORMAT_MESSAGE_MAX_WIDTH_MASK, nil,
				code, 0, pWideChar(@ptr), 0, nil) > 0 then
			begin
				werr := pWideChar(ptr);
				if Assigned(ptr) then HeapFree(GetProcessHeap, 0, ptr);
				result := werr.ToUTF8;
				while (length(result) > 0) and (result[length(result)] = ' ') do SetLength(result, length(result) - 1);
			end else
				result := '';

			if result = '' then exit('Нет текстового описания системной ошибки, код {}.'.Format([code]));
		end;
		result += ' ({})'.Format([code]);
	end;

	class function Win32.OperationFailed(const what: string; code: DWORD = USE_GETLASTERROR): Exception;
	begin
		CheckForUSE_GETLASTERROR(code);
		result := Exception.Create('Не удалось {}. {}'.Format([what, DescribeError(code)]));
	end;

	class function Win32.FileError(const fn: string; code: DWORD = USE_GETLASTERROR): Exception;
	begin
		CheckForUSE_GETLASTERROR(code);
		result := Exception.Create('{}: {}.'.Format([fn, DescribeError(code).LowercaseFirst]));
	end;

	class function Win32.Lowercase(const text: string): string;
	var
		ws: widestring;
	begin
		ws := text.ToUTF16;
		CharLowerW(pWideChar(ws));
		result := ws.ToUTF8;
	end;

	class procedure Win32.Warning(const what: string; code: DWORD = USE_GETLASTERROR);
	begin
		CheckForUSE_GETLASTERROR(code);
		writeln(stderr, what, ': ', code);
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

	class procedure Win32.CheckForUSE_GETLASTERROR(var code: DWORD);
	begin
		if code = USE_GETLASTERROR then code := GetLastError;
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

	procedure ThreadEvent.Init(manual, initialState: boolean);
	begin
		Assert(h = 0);
		h := CreateEventW(nil, manual, initialState, nil);
		if h = 0 then raise Win32.OperationFailed('создать событие');
	end;

	procedure ThreadEvent.Done;
	begin
		if (h <> 0) and not CloseHandle(h) then Win32.Warning('CloseHandle');
		h := 0;
	end;

	function ThreadEvent.OK: boolean;
	begin
		result := h <> 0;
	end;

	procedure ThreadEvent.&Set; begin if not SetEvent(h) then raise Win32.OperationFailed('выставить событие (SetEvent)'); end;
	procedure ThreadEvent.Reset; begin if not ResetEvent(h) then raise Win32.OperationFailed('сбросить событие (ResetEvent)'); end;
	procedure ThreadEvent.Wait;
	var
		r: dword;
	begin
		r := WaitForSingleObject(h, INFINITE);
		if r <> WAIT_OBJECT_0 then
			if r = WAIT_FAILED then
				raise Win32.OperationFailed('подождать события (WaitForSingleObject)')
			else
				raise Exception.Create('WaitForSingleObject вернула {}'.format([r]));
	end;

	procedure Console.Init;
	var
		info: CONSOLE_SCREEN_BUFFER_INFO;
	begin
		Assert(not hOutSet and not handlerAdded and not broken);
		try
			lock.Init;
			if not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), true) then
				raise Win32.OperationFailed('установить обработчик Ctrl-C (SetConsoleCtrlHandler)');
			handlerAdded := true;
			hOut := CreateFile('CONOUT$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_WRITE, nil, OPEN_EXISTING, 0, 0);
			if hOut = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для вывода');
			hOutSet := true;

			if not GetConsoleScreenBufferInfo(hOut, (@info)^) then raise Win32.OperationFailed('получить информацию от консоли (GetConsoleScreenBufferInfo)');
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
		if handlerAdded and not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), false) then Win32.Warning('SetConsoleCtrlHandler');
		handlerAdded := false;
		if hOutSet and (hOut <> INVALID_HANDLE_VALUE) and not CloseHandle(hOut) then Win32.Warning('CloseHandle');
		hOutSet := false;
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
	procedure Console.Line(const s: string); begin Write(s + LineEnding); end;

	procedure Console.Colored(const s: string; cl: SizeInt = -1);
	var
		pieces: PiecesList;
		i: SizeInt;
		activeColor, newColor, activeBg, newBg: Color;
	begin
		if not hOutSet or broken then
		begin
			for i := 0 to High(pieces) do system.write(pieces[i].data);
			exit;
		end;

		pieces := ParseMarkdown(s);
		lock.Enter;
		try
			activeColor := defCol; activeBg := defBg;
			for i := 0 to High(pieces) do
			begin
				if pieces[i].color >= 0 then newColor := Color(pieces[i].color) else if cl >= 0 then newColor := Color(cl) else newColor := defCol;
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
	procedure Console.Colored(const s: string; cl: Color); begin Colored(s, ord(cl)); end;
	procedure Console.ColoredLine(const s: string); begin Colored(s + LineEnding); end;
	procedure Console.ColoredLine(const s: string; cl: Color); begin Colored(s + LineEnding, cl); end;

	function Console.Escape(const s: string): string;
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
							if csp = 0 then raise Exception.Create('{}: антипереполнение стека цветов.'.Format([s.Stuffed(i, '|')]));
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
			if not WriteConsoleW(hOut, p, n, (@written)^, nil) then begin broken := true; raise Win32.OperationFailed('WriteConsoleW'); end;
			if written <> n then begin broken := true; raise Exception.Create('WriteConsoleW: n = {}, written = {}.'.Format([n, written])); end;
			p += n;
		until p = pWideChar(ws) + length(ws);
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
		if not HeyNoAsioPending.OK then
		begin
			SingletonLock.Enter;
			try
				if not HeyNoAsioPending.OK then GlobalInitialize;
			finally
				SingletonLock.Leave;
			end;
		end;

		f.ref := nil;
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

	procedure &File.Read(at: FilePos; buf: pointer; size: SizeUint);
	var
		a: pAsyncIORequest;
		actual, code: dword;
		rfOk: boolean;
	begin
		a := CreateAsyncIORequest(ref, at, 0);
		rfOk := Windows.ReadFile(ref^.h, buf^, size, (@actual)^, @a^.ov);
		if not rfOk then code := GetLastError;
		if rfOk or (code = ERROR_IO_PENDING) then
		begin
			if not rfOk and not GetOverlappedResult(ref^.h, a^.ov, actual, true) then
			begin
				code := GetLastError;
				raise Win32.FileError(ref^.fn, code);
			end;
			if actual <> size then raise Exception.Create('Из {} прочитано {} b (вместо {} b).'.Format([ref^.fn, actual, size]));
		end else
		begin
			CloseAsyncIORequest(a);
			raise Win32.FileError(ref^.fn, code);
		end;
	end;

	procedure &File.Write(at: FilePos; buf: pointer; size: SizeUint);
	var
		a: pAsyncIORequest;
		actual, code: dword;
		wfOk: boolean;
	begin
		a := CreateAsyncIORequest(ref, at, size);
		Move(buf^, a^.data[0], size);

		wfOk := WriteFile(ref^.h, a^.data[0], size, (@actual)^, @a^.ov);
		if not wfOk then code := GetLastError;
		if wfOk then
			if actual <> size then raise Exception.Create('В {} записалось {} b (вместо {} b).'.Format([ref^.fn, actual, size])) else
		else if code <> ERROR_IO_PENDING then
		begin
			CloseAsyncIORequest(a);
			raise Win32.FileError(ref^.fn, code);
		end;
	end;

	function &File.Size: FileSize;
	var
		sz: LARGE_INTEGER;
	begin
		if GetFileSizeEx(ref^.h, @sz) then result := sz.QuadPart else raise Win32.OperationFailed('получить размер файла (GetFileSizeEx)');
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
			if not RemoveDirectoryW(pWideChar(folders[i])) then Win32.Warning('RemoveDirectoryW');
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
	begin
		Assert((dwErrorCode = dwErrorCode) and (dwNumberOfBytesTransfered = dwNumberOfBytesTransfered));
		CloseAsyncIORequest(pAsyncIORequest(lpOverlapped));
	end;

	class function &File.CreateAsyncIORequest(h: pSharedHandle; const offset: FilePos; extraSize: SizeUint): pAsyncIORequest;
	begin
		if InterlockedIncrement(AsioPending) = 1 then HeyNoAsioPending.Reset;
		result := GetMem(sizeof(AsyncIORequest) - sizeof(AsyncIORequest.data) + extraSize);
		result^.ov.Internal     := 0;
		result^.ov.InternalHigh := 0;
		result^.ov.hEvent       := 0;
		result^.ov.Offset       := Lo(offset);
		result^.ov.OffsetHigh   := Hi(offset);
		result^.h := h^.Ref;
	end;

	class procedure &File.CloseAsyncIORequest(a: pAsyncIORequest);
	begin
		a^.h^.Close(a^.h);
		FreeMem(a);
		if InterlockedDecrement(AsioPending) = 0 then HeyNoAsioPending.&Set;
	end;

	class procedure &File.GlobalInitialize;
	begin
		if HeyNoAsioPending.OK then raise LogicError.Create('File.GlobalInitialize уже вызвана.');
		HeyNoAsioPending.Init(true, true);
		AddExitProc(TProcedure(@&File.GlobalFinalize));
	end;

	class procedure &File.GlobalFinalize;
	begin
		WaitForAllIORequests;
		HeyNoAsioPending.Done;
	end;

	class procedure &File.WaitForAllIORequests;
	begin
		if HeyNoAsioPending.OK then HeyNoAsioPending.Wait;
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
			(1 + n <= length(self) - pos + 1) {$define times := n} {$define rep := and (ord(self[pos + (1 + repid)]) shr 6 = %10)} pp_repeat then
			begin
				result := (result and (%00011111 shr (n-1))) shl (6*n)
						{$define rep := or (UTFchar(ord(self[pos + (1+repid)]) and %00111111) shl (6*(n-1-repid)))} {$define times := n} pp_repeat;
				len := n + 1;
			end {$undef n}}
		else if (result >= %11000000) and (result <= %11011111) and {$define n := 1} n_more
		else if (result >= %11100000) and (result <= %11101111) and {$define n := 2} n_more
		else if (result >= %11110000) and (result <= %11110111) and {$define n := 3} n_more
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
						inc(p); result += Copy(self, start, p - start); start := p;
					end else
					begin
						nn := p + 1;
						while (nn <= length(self)) and (self[nn] in ['0' .. '9']) do inc(nn);
						if (nn <= length(self)) and (self[nn] = '}') and
							((nn = p + 1) and (next < length(args)) or
								TryParse(Copy(self, p + 1, nn - p - 1), index) and (index >= 0) and (index < length(args))) then
						begin
							if nn = p + 1 then begin index := next; inc(next); end;
							result += Copy(self, start, p - start) + ToString(args[index]); p := nn + 1; start := p;
						end else
							inc(p);
					end;
				else
					inc(p);
			end;
		result += Copy(self, start, p - start);
	end;

	class function StringHelper.ToString(const v: TVarRec): string;
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
			else          result := '(VType ' + im.ToString(v.VType) + ')';
		end;
	end;

	function StringHelper.Prefixed(const p: string; pos: SizeInt = 1): boolean;
	begin
		result := (pos + length(p) - 1 <= length(self)) and (CompareChar(self[pos], p[1], length(p)) = 0);
	end;

	function StringHelper.Lowercase: string; begin result := Win32.Lowercase(self); end;
	function StringHelper.LowercaseFirst: string;
	var
		n: SizeInt;
	begin
		if length(self) >= 1 then n := CodepointLen(1) else n := 0;
		result := Copy(self, 1, n).Lowercase + Copy(self, n + 1, length(self) - n);
	end;

	function StringHelper.Stuffed(at: SizeInt; const &with: string): string;
	begin
		result := Copy(self, 1, at - 1) + &with + Copy(self, at, length(self) - at + 1);
	end;
   function StringHelper.AR: PAnsiRec; begin result := PAnsiRec(self) - 1; end;

	function WidestringHelper.ToUTF8: string;
	begin
		result := UTF8Encode(self);
		if Assigned(pointer(result)) then result.AR^.cpes.CodePage := CP_ACP;
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
	procedure OutOfMemory.FireAnEmergency; begin ReleaseReserve; CanDieNow := true; end;
	procedure OutOfMemory.ReleaseReserve; begin if Assigned(RainyDayReserve) then FreeMem(RainyDayReserve); RainyDayReserve := nil; end;

	class constructor OutOfMemory.InitGlobal;
	begin
		Instance := OutOfMemory.Create;
		Instance.RainyDayReserve := GetMem(4096);
	end;

	class destructor OutOfMemory.DoneGlobal;
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
		SingletonLock.Init;
		Con.Init;
		TestHacks;
	end;

	class procedure Session.Done;
	begin
		&File.WaitForAllIORequests;
		Con.Done;
		SingletonLock.Done;
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
			p := 1;
			while (p <= length(line)) and (line[p] in [StringHelper.Tab, ' ']) do inc(p);
			while (p <= length(line)) and (line[p] in ['$']) do inc(p);
			while (p <= length(line)) and (line[p] in ['0' .. '9']) do inc(p);
			result := p < length(line);
		end;
	var
		i: longint;
		line: string;
		frame: CodePointer;
		trace: array of TraceItem;
	begin
		trace := nil;
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
					result += LineEnding + '(...)';
					if trace[i].uninteresting > 1 then result += ' x{}'.Format([trace[i].uninteresting]);
				end else
					result += LineEnding + trace[i].line;
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
		// (к счастью, альтернатива есть: не заморачиваться и сделать сеппуку aka ExitProcess). Дело вот в чём.
		//
		// Если ExceptProc вернулась, RTL вызывает halt, которая несколько мягче ExitProcess: она выполняет финализацию,
		// давая отработать class destructor'ам, ExitProc и секциям finalization, в т. ч. в heaptrc.
		// Поэтому я целенаправленно возвращаюсь из ExceptProc, чтобы дать всему этому отработать и проверить корректность и
		// отсутствие утечек памяти даже после необработанного исключения.
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

		i := {$if sizeof(ErrNo) <> sizeof(dword)} {$error} {$endif} IndexDWord(RuntimeErrorExitCodes, length(RuntimeErrorExitCodes), dword(ErrNo));
		if i >= 0 then
		begin
			str(TRuntimeError(i), name);
			if name.Prefixed('re') then delete(name, 1, length('re'));
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

begin
	con.ColoredLine('<B>В пору <1>белого</> хлада не ешь <RG>жёлтый</> снег.');
	readln;
end.

