{$mode objfpc} {$h+} {$typedaddress+} {$macro on} {$modeswitch duplicatelocals+} {$modeswitch typehelpers+} {$scopedenums+}
{$R *.res}
uses
	CTypes, Windows;

{$define pp_repeat :=
	{$if times >= 1} {$define repid := 0} rep {$endif} {$if times >= 2} {$define repid := 1} rep {$endif}
	{$if times >= 3} {$define repid := 2} rep {$endif} {$if times >= 4} {$define repid := 3} rep {$endif}
	{$if times >= 5} {$error too many repeats} {$endif} {$undef repid} {$undef times} {$undef rep}}

{$define impl :=
	function ToString(x: typename): string; begin str(x, result); end;
	function min(a, b: typename): typename; begin if a <= b then result := a else result := b; end;
	function max(a, b: typename): typename; begin if a >= b then result := a else result := b; end;}
	{$define typename := int32} impl {$define typename := uint32} impl  {$define typename := int64} impl {$define typename := uint64} impl
{$undef impl}

type
	widestring = unicodestring;
	UTFchar = type uint32;
	FilePos = type uint64;
	FileSize = type uint64;
	casint = int32;

const
	UTFInvalid = High(UTFchar);

type
	Exception = class(TObject)
		msg: string;
		constructor Create(const msg: string);
	end;
	LogicError = class(Exception) end;

	Win32 = object
	const
		USE_GETLASTERROR = High(DWORD) - 1;

		class function DescribeError(code: DWORD = USE_GETLASTERROR): string; static;
		class function OperationFailed(const what: string; code: DWORD = USE_GETLASTERROR): Exception; static;
		class function FileError(const fn: string; code: DWORD = USE_GETLASTERROR): Exception; static;
		class function LowercaseFirst(const msg: string): string; static;
		class procedure Warning(const what: string; code: DWORD = USE_GETLASTERROR); static;
	private
		class procedure CheckForUSE_GETLASTERROR(var code: DWORD); static;
	end;

	Lock = object
		cs: CRITICAL_SECTION;
		ok: boolean;
		procedure Init;
		procedure Done;
		procedure Enter;
		procedure Leave;
	end;

	Console = object
		procedure Init;
		procedure Done;
		procedure Write(const s: string);
		procedure Line(const s: string);
	private
		hOut: HANDLE;
		handlerAdded, hOutSet: boolean;
		class function CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; static; stdcall;
	private class var
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

		class procedure Open(out f: &File; const fn: string; flags: Flags; r: pOpenResult = nil); static;
		procedure Close;
		procedure Read(at: FilePos; buf: pointer; size: SizeUint);
		procedure Write(at: FilePos; buf: pointer; size: SizeUint);
		function Size: FileSize;

	private type
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

		pPathRollback = ^PathRollback;
		PathRollback = object
			folders: array of widestring;
			procedure Rollback;
		const
			Empty: PathRollback = (folders: nil);
		end;
	private
		ref: pSharedHandle;
		class function TryCreatePath(const fn: string; out err: dword; rollback: pPathRollback = nil): boolean; static;
		class procedure IOCompletionHandler(dwErrorCode: dword; dwNumberOfBytesTransfered: dword; lpOverlapped: Windows.LPOVERLAPPED); static; stdcall;
		class function CreateAsyncIORequest(h: pSharedHandle; const offset: FilePos; extraSize: SizeUint): pAsyncIORequest; static;
		class procedure CloseAsyncIORequest(a: pAsyncIORequest); static;
	private class var
		AsioPending: casint;
		HeyNoAsioPending: HANDLE;
		class procedure GlobalInitialize; static;
		class procedure GlobalFinalize; static;
	public const
		Readable = Flag.Readable; Writeable = Flag.Writeable; RW = [Readable, Writeable]; Existing = Flag.Existing; New = Flag.New;
		Temp = Flag.Temp;

		class procedure WaitForAllIORequests; static;
	end;

	StringHelper = type helper for string
		function Peek(pos: SizeInt; out len: SizeInt): UTFchar;
		function ToUTF16: widestring;

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
	end;

	WidestringHelper = type helper for widestring
		function ToUTF8: string;
	end;

var
	Con: Console;
	SingletonLock: Lock;

	function GetFileSizeEx(hFile: HANDLE; lpFileSize: PLARGE_INTEGER): Windows.BOOL; stdcall; external kernel32;
	function BindIoCompletionCallback(FileHandle: Windows.HANDLE; func: LPOVERLAPPED_COMPLETION_ROUTINE; flags: Windows.ULONG): Windows.BOOL; stdcall; external kernel32;

	class function Win32.DescribeError(code: DWORD = USE_GETLASTERROR): string;
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

			if result = '' then exit('Нет текстового описания системной ошибки, код ' + ToString(code) + '.');
		end;
	{$ifdef Debug} result += ' (' + ToString(code) + ')'; {$endif}
	end;

	class function Win32.OperationFailed(const what: string; code: DWORD = USE_GETLASTERROR): Exception;
	begin
		CheckForUSE_GETLASTERROR(code);
		result := Exception.Create('Не удалось ' + what + '. ' + DescribeError(code));
	end;

	class function Win32.FileError(const fn: string; code: DWORD = USE_GETLASTERROR): Exception;
	begin
		CheckForUSE_GETLASTERROR(code);
		result := Exception.Create(fn + ': ' + LowercaseFirst(DescribeError(code)) + '.');
	end;

	class function Win32.LowercaseFirst(const msg: string): string;
	var
		n: SizeInt;
		ws: widestring;
	begin
		result := msg;
		if result.Peek(1, n) <> UTFInvalid then
		begin
			ws := Copy(result, 1, n).ToUTF16;
			CharLowerW(pWideChar(ws));
			result := ws.ToUTF8 + Copy(result, n + 1, length(result) - n);
		end;
	end;

{$ifdef Debug}
	class procedure Win32.Warning(const what: string; code: DWORD = USE_GETLASTERROR);
	begin
		CheckForUSE_GETLASTERROR(code);
		writeln(stderr, what, ': ', code);
	end;
{$endif}

	class procedure Win32.CheckForUSE_GETLASTERROR(var code: DWORD);
	begin
		if code = USE_GETLASTERROR then code := GetLastError;
	end;

	function StringHelper.Peek(pos: SizeInt; out len: SizeInt): UTFchar;
	begin
		if length(self) - pos + 1 > 0 then result := UTFchar(self[pos]) else exit(UTFInvalid);
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
		{$undef n_more} else exit(UTFInvalid);
	end;

	function StringHelper.ToUTF16: widestring;
	begin
		result := UTF8Decode(self);
	end;

	function WidestringHelper.ToUTF8: string;
	begin
		result := UTF8Encode(self);
		if Assigned(pointer(result)) then (StringHelper.PAnsiRec(result) - 1)^.cpes.CodePage := CP_ACP;
	end;

	procedure Lock.Init;
	begin
		Assert(not ok);
		InitializeCriticalSection(cs);
		ok := true;
	end;

	procedure Lock.Done;
	begin
		if ok then
		begin
			DeleteCriticalSection(cs);
			ok := false;
		end;
	end;

	procedure Lock.Enter; begin Assert(ok); EnterCriticalSection(cs); end;
	procedure Lock.Leave; begin Assert(ok); LeaveCriticalSection(cs); end;

	procedure Console.Init;
	begin
		Assert(not hOutSet and not handlerAdded);
		if not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), true) then
			raise Win32.OperationFailed('установить обработчик Ctrl-C (SetConsoleCtrlHandler)');
		handlerAdded := true;
		hOut := CreateFile('CONOUT$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_WRITE, nil, OPEN_EXISTING, 0, 0);
		if hOut = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для вывода');
		hOutSet := true;
	end;

	procedure Console.Done;
	begin
		if handlerAdded and not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), false) then {$ifdef Debug} Win32.Warning('SetConsoleCtrlHandler') {$endif};
		handlerAdded := false;
		if hOutSet and (hOut <> INVALID_HANDLE_VALUE) and not CloseHandle(hOut) then {$ifdef Debug} Win32.Warning('CloseHandle') {$endif};
		hOutSet := false;
	end;

	procedure Console.Write(const s: string);
	const
		BlockSize = 4096;
	var
		ws: widestring;
		p: pWideChar;
		n: SizeUint;
		written: DWORD;
	begin
		if not hOutSet then
		begin
			system.write(s.ToUTF16);
			exit;
		end;

		ws := s.ToUTF16;
		p := pWideChar(ws);
		repeat
			n := min(length(ws) - (p - pWideChar(ws)), BlockSize);
			if not WriteConsoleW(hOut, p, n, (@written)^, nil) then raise Win32.OperationFailed('WriteConsoleW');
			if written <> n then raise Exception.Create('WriteConsoleW: n = ' + ToString(n) + ', written = ' + ToString(written) + '.');
			p += n;
		until p = pWideChar(ws) + length(ws);
	end;

	procedure Console.Line(const s: string);
	begin
		Write(s + LineEnding);
	end;

	class function Console.CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; stdcall;
	begin
		if dwCtrlType = CTRL_C_EVENT then
		begin
			// Я особо не искал, что именно происходит...
			// Во всяком случае похоже, что ReadConsole прерывается без дополнительных телодвижений, так что остаётся проигнорировать сам Ctrl-C.
			// Внимание, система запускает этот обработчик в отдельном потоке, бросать исключение не вариант.
			result := true;
			CtrlCHit := true;
		end else
			result := false;
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
		if HeyNoAsioPending = 0 then
		begin
			SingletonLock.Enter;
			try
				if HeyNoAsioPending = 0 then GlobalInitialize;
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
			if New in flags then raise LogicError.Create(fn + ': New + RO?');
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
		until ok or (tryId > 1) or not ((Writeable in flags) and (err = ERROR_PATH_NOT_FOUND) and TryCreatePath(fn, err, @rb));

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
			if actual <> size then raise Exception.Create('Из ' + ref^.fn + ' прочитано ' + ToString(actual) + ' b (вместо ' + ToString(size) + ' b).');
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
			if actual <> size then raise Exception.Create('В ' + ref^.fn + ' записалось ' + ToString(actual) + ' b (вместо ' + ToString(size) + ' b).')
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
		if GetFileSizeEx(ref^.h, @sz) then
			result := sz.QuadPart
		else
			raise Win32.OperationFailed('получить размер файла (GetFileSizeEx)');
	end;

	class function &File.SharedHandle.Create(h: HANDLE; const fn: string): pSharedHandle;
	var
		code: dword;
	begin
		system.new(result);
		result^.h := h;
		result^.fn := fn;
		result^.refcount := 1;
		if not BindIoCompletionCallback(h, LPOVERLAPPED_COMPLETION_ROUTINE(@&File.IOCompletionHandler), 0) then
		begin
			code := GetLastError;
			dispose(result);
			raise Win32.OperationFailed('назначить асинхронный обработчик I/O для ' + fn + ' (BindIoCompletionCallback)', code);
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
			if not RemoveDirectoryW(pWideChar(folders[i])) then {$ifdef Debug} Win32.Warning('RemoveDirectoryW') {$endif};
		folders := nil;
	end;

	class function &File.TryCreatePath(const fn: string; out err: dword; rollback: pPathRollback = nil): boolean;
	var
		i, start: SizeInt;
		created: PathRollback;
		dir: widestring;
	begin
		created.folders := nil;
		if Assigned(rollback) then rollback^ := created;
		start := 1;
		i := 1;
		while i <= length(fn) do
		begin
			if fn[i] in ['\', '/'] then
			begin
				if (i-1 >= start) and (fn[i-1] <> ':') then // E:
				begin
					dir := Copy(fn, 1, i-1).ToUTF16;
					if CreateDirectoryW(pWideChar(dir), nil) then
					begin
						SetLength(created.folders, length(created.folders) + 1);
						created.folders[High(created.folders)] := dir;
					end else
					begin
						err := GetLastError;
						if err = ERROR_ALREADY_EXISTS then
							created.folders := nil // на всякий случай
						else
						begin
							created.Rollback;
							exit(false);
						end;
					end;
				end;
				start := i + 1;
			end;
			inc(i);
		end;
		if Assigned(rollback) then rollback^ := created;
		result := true;
	end;

	class procedure &File.IOCompletionHandler(dwErrorCode: dword; dwNumberOfBytesTransfered: dword; lpOverlapped: Windows.LPOVERLAPPED); stdcall;
	begin
		Assert((dwErrorCode = dwErrorCode) and (dwNumberOfBytesTransfered = dwNumberOfBytesTransfered));
		CloseAsyncIORequest(pAsyncIORequest(lpOverlapped));
	end;

	class function &File.CreateAsyncIORequest(h: pSharedHandle; const offset: FilePos; extraSize: SizeUint): pAsyncIORequest;
	begin
		result := GetMem(sizeof(AsyncIORequest) - sizeof(AsyncIORequest.data) + extraSize);
		result^.ov.Internal     := 0;
		result^.ov.InternalHigh := 0;
		result^.ov.hEvent       := 0;
		result^.ov.Offset       := Lo(offset);
		result^.ov.OffsetHigh   := Hi(offset);
		result^.h := h^.Ref;
		if InterlockedIncrement(AsioPending) = 1 then
			if not ResetEvent(HeyNoAsioPending) then {$ifdef Debug} Win32.Warning('SetEvent(NoAsioPending)') {$endif};
	end;

	class procedure &File.CloseAsyncIORequest(a: pAsyncIORequest);
	begin
		a^.h^.Close(a^.h);
		FreeMem(a);
		if InterlockedDecrement(AsioPending) = 0 then
			if not SetEvent(HeyNoAsioPending) then {$ifdef Debug} Win32.Warning('SetEvent(NoAsioPending)') {$endif};
	end;

	class procedure &File.GlobalInitialize;
	begin
		if HeyNoAsioPending <> 0 then raise LogicError.Create('File.GlobalInitialize уже вызвана.');
		HeyNoAsioPending := CreateEventW(nil, true, true, nil);
		if HeyNoAsioPending = 0 then raise Win32.OperationFailed('создать событие');
		AddExitProc(TProcedure(@&File.GlobalFinalize));
	end;

	class procedure &File.GlobalFinalize;
	begin
		WaitForAllIORequests;
		if (HeyNoAsioPending <> 0) and not CloseHandle(HeyNoAsioPending) then {$ifdef Debug} Win32.Warning('CloseHandle(AsioPendingEvent)') {$endif};
		HeyNoAsioPending := 0;
	end;

	class procedure &File.WaitForAllIORequests;
	var
		r: dword;
	begin
		if HeyNoAsioPending <> 0 then
		begin
			r := WaitForSingleObject(HeyNoAsioPending, INFINITE);
			if r <> WAIT_OBJECT_0 then {$ifdef Debug} Win32.Warning('WaitFor(AsioPendingEvent) = ' + ToString(r)) {$endif};
		end;
	end;

	constructor Exception.Create(const msg: string);
	begin
		inherited Create;
		self.msg := msg;
	end;

	function TestHacks: boolean;
		function Fail(const msg: string): boolean;
		begin
			writeln(msg);
			result := false;
		end;
	var
		s, s2: string;
		a: StringHelper.PAnsiRec;
	begin
		s := ToString(ThreadID);
		(@s2)^ := s;
		a := StringHelper.PAnsiRec(s) - 1;
		if (a^.cpes.CodePage <> CP_ACP) or (a^.cpes.ElementSize <> 1) or (a^.ref <> 2) or (length(s) <> a^.len) then
			exit(Fail('AnsiRec hack failed: CP = ' + ToString(a^.cpes.CodePage) + ' (' + ToString(CP_ACP) + '), ' +
				'ElementSize = ' + ToString(a^.cpes.ElementSize) + ' (1), ' +
				'RefCount = ' + ToString(a^.ref) + ' (2), Length = ' + ToString(a^.len) + ' (' + ToString(length(s)) + ')'));
		result := true;
	end;

begin
	if not TestHacks then exit;
	try
		try
			SingletonLock.Init;
			Con.Init;
		except
			on e: Exception do Con.Write(e.msg);
		end;
	finally
		&File.WaitForAllIORequests;
		Con.Done;
		SingletonLock.Done;
	end;
end.
