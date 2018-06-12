{$mode objfpc} {$h+} {$typedaddress+} {$macro on} {$modeswitch duplicatelocals+} {$modeswitch typehelpers+} {$scopedenums+}
{$modeswitch advancedrecords}
{$ifdef assert} {$error} {$endif} {$ifopt Q+} {$define assert} {$endif}
{$define suppress_false_dfa_alarms}
{$warn 2005 off} // comment level 2 found
{$R *.res}
program im;

uses
	CTypes, Windows;

// Повторяет times раз фрагмент rep, со счётчиком repid от 0 до times - 1.
// Например, {$define rep := {$if repid > 0} + {$endif} A[repid]} {$define times := 3} pp_repeat преобразуется в A[0] + A[1] + A[2].
{$define pp_repeat := {$if defined(repid)} {$error pp_repeat would hide defines} {$endif}
	{$if times >= 1} {$define repid := 0} rep {$endif} {$if times >= 2} {$define repid := 1} rep {$endif}
	{$if times >= 3} {$define repid := 2} rep {$endif} {$if times >= 4} {$define repid := 3} rep {$endif}
	{$if times >= 5} {$error too many repeats} {$endif} {$undef repid} {$undef times} {$undef rep}}

// Объявляет внутри объекта энум enum и константы, дублирующие его значения, чтобы вместо Object.EnumType.EnumValue можно было писать Object.EnumValue.
// (Если вообще выключить scopedenums, EnumValue попадёт в глобальную область видимости и будет с чем-нибудь конфликтовать.)
// Например, {$define enum := Channel} {$define items := Red _ 0 _ Green _ 1 _ Blue _ 2} преобразуется в
// type
//     Channel = (Red := 0, Green := 1, Blue := 2);
// const
//     Red   = Channel(0);
//     Green = Channel(1);
//     Blue  = Channel(2);
{$define enum_with_shortcuts := {$if defined(now_number) or defined(_)} {$error enum_with_shortcuts would hide defines} {$endif}
	type
		enum = {$define _ := {$ifdef now_number} , {$undef now_number} {$else} := {$define now_number} {$endif}} (items); {$undef now_number}
	{$ifdef and_set} and_set = set of enum; {$endif}
	const
		{$define _ := {$ifdef now_number} ); {$undef now_number} {$else} = enum( {$define now_number} {$endif}} items _ {$undef now_number}
		{$undef enum} {$undef items} {$undef and_set} {$undef _}}

// {$define args := A _ B} unused_args => Assert((@A >= nil) and (@B >= nil)), подавляет ворнинги.
{$define unused_args := {$if defined(_)} {$error unused_argrs would hide defines} {$endif}
	{$define _ := >= nil) and (@} Assert((@args >= nil)); {$undef _} {$undef args}}

// unchecked
// ...код, сознательно использующий целочисленные переполнения
// _end
{$define unchecked := {$if defined(_end)} {$error unchecked would hide defines} {$endif}
	{$push} {$rangechecks off} {$overflowchecks off} {$define _end := {$pop} {$undef _end}}}

// шаблон для векторов
{$define all_vectors :=
	{$if defined(veclen) or defined(vec) or defined(pvec) or defined(pair3) or defined(foreach_component) or defined(reduce_vec) or
		defined(iterate) or
		defined(item_conv) or defined(op)}
		{$error all_vectors would hide defines}
	{$endif}

	{$define foreach_component :=
		{$if defined(item) or defined(itemid) or defined(first)} {$error foreach_component would hide defines} {$endif}
		{$define item := x} {$define itemid := 0} {$define first} iterate {$undef first}
		{$define item := y} {$define itemid := 1} iterate
		{$if veclen >= 3} {$define item := z} {$define itemid := 2} iterate {$endif}
		{$if veclen >= 4} {$define item := w} {$define itemid := 3} iterate {$endif}
		{$undef item} {$undef itemid} {$undef iterate}}

	{$define reduce_vec :=
		{$define iterate :=
			{$ifndef first} {$ifdef op} op {$else} + {$endif} {$endif}
			{$ifdef item_conv} item_conv {$else} item {$endif}} foreach_component {$undef op} {$undef item_conv}}

	{$define pair3 := Vec3}
	{$define veclen := 2} {$define vec := Vec2} {$define pvec := pVec2} vecf
	{$define veclen := 3} {$define vec := Vec3} {$define pvec := pVec3} vecf
	{$define veclen := 4} {$define vec := Vec4} {$define pvec := pVec4} vecf
	{$undef veclen} {$undef vec} {$undef pvec} {$undef pair3} {$undef vecf} {$undef foreach_component} {$undef reduce_vec}}

const
	EOL = LineEnding;
	CPUArch = {$if defined(CPU32)} 'x86' {$elseif defined(CPU64)} 'x64' {$else} {$error unknown CPU} {$endif};

type
	widestring = unicodestring; // system.widestring под Windows реализован через какую-то неведомую ебанину уровня BSTR,
	                            // с выделением памяти через SysAllocString (!), без обычного подсчёта ссылок (!) и copy-on-write.
	                            // Тогда как unicodestring аналогичен ansistring в смысле выделения памяти через RTL и подсчёта ссылок,
	                            // поэтому генерирует меньше кода и работает быстрее.
	                            // Но вообще я везде использую однобайтовые (ansi)string, подразумевая UTF-8, а widestring нужен только для общения с UTF-16-нутыми API.
	UTFchar = type uint32;
	FilePos = type uint64;
	FileSize = type uint64;
	FilePath = type string;
	sint = int32; uint = uint32;
	float = single;
{$push} {$scopedenums off} ThrowBehaviour = (Throw, DontThrow); {$pop}
	&Case = (Lower, Upper);

	TObjectEx = class(TObject)
		procedure Free(var link); overload; // Аналог FreeAndNil с хоть какой-то проверкой на этапе компиляции.
	end;

{$define ifthenimpl :=
	function IfThen(cond: boolean; const yes: typename; const no: typename {$ifdef default_no} = default_no {$endif}): typename;
	begin
		if cond then result := yes else result := no;
	end; {$undef default_no} {$ifndef keep_typename} {$undef typename} {$endif}}

{$define impl :=
	function ToString(const x: typename): string;
	{$ifdef floating} var len: SizeInt; {$endif}
	begin
	{$ifdef floating}
		if (x = 0) or (abs(x) > 0.1) then str(x:0:2, result)
		else if abs(x) > 0.001 then str(x:0:4, result)
		else if abs(x) > 0.00001 then str(x:0:6, result)
		else begin str(x, result); exit; end;

		len := length(result);
		while result[len] = '0' do dec(len);
		if result[len] = '.' then dec(len);
		delete(result, len + 1, length(result) - len);
	{$else}
		str(x, result);
	{$endif}
	end;

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

	function clamp(const x, a, b: typename): typename;
	begin
		if (x >= a) and (x <= b) then result := x else
			if x > a then result := b else result := a;
	end;

{$ifdef floating}
	function lerp(const a, b, x: typename): typename;
	begin
		result := a * (1 - x) + b * x;
	end;

	function smoothstep(const a, b, x: typename): typename;
	var
		t: typename;
	begin
		t := clamp((x - a) / (b - a), 0, 1);
		result := t * t * (3 - 2*t);
	end;
{$endif}

	{$undef typename}
	{$ifndef keep_integer} {$undef integer} {$endif}
	{$ifndef keep_floating} {$undef floating} {$endif}}

	{$define integer} {$define keep_integer}
	{$define typename := int32} impl {$define typename := uint32} impl  {$define typename := int64} impl {$define typename := uint64} {$undef keep_integer} impl

	{$define floating} {$define keep_floating}
	{$define typename := single} impl {$define typename := double} {$undef keep_floating} impl
{$undef impl}

{$define typename := string} {$define default_no := ''} ifthenimpl
{$define typename := pointer} ifthenimpl
{$undef ifthenimpl}

	function pow(const base, exponent: float): float;
	begin
		result := exp(ln(base) * exponent);
	end;

	// При получении нулевого указателя ничего не делать. Без "Weak" дополнительно зануляет указатель.
	procedure FreeMemWeak(p: pointer); begin if Assigned(p) then System.FreeMem(p); end;
	procedure FreeMem(var p: pointer); begin FreeMemWeak(p); p := nil; end;

	procedure TObjectEx.Free(var link);
	begin
		Assert(TObject(link) = self);
		TObject(link) := nil;
		Free;
	end;

type
	Exception = class(TObjectEx)
		msg: string;
		constructor Create(const msg: string);
		constructor Create(const msg: string; const args: array of const);
		class function Current: TObject; static;
		class function Message(obj: TObject): string; static;
		class function Message: string; static;
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

	DLL = object
	type
		Proxy = object
			function Prefix(const prefix: string): Proxy;
			function Func(const namex: string; var funcPtr{: CodePointer}): Proxy;
		private
			dll: ^DLL;
		end;

		function Load(const fn: FilePath; e: ThrowBehaviour = Throw): Proxy;
		procedure Unload;
	private
		h: HANDLE;
		fn, prefix, lastNonStarred: string;
		temper: ThrowBehaviour;
		fptrs: array of pCodePointer;
	end;

	Win32 = object
	type
		LPTOP_LEVEL_EXCEPTION_FILTER = function(ExceptionInfo: PEXCEPTION_POINTERS): Windows.LONG; stdcall;
	const
		ERROR_NOT_FOUND = $490;

	type
		NTSTATUS = record value: uint32; end;
	const
		STATUS_CANCELLED = $C0000120;

	type
		PTP_CALLBACK_INSTANCE = ^TP_CALLBACK_INSTANCE; TP_CALLBACK_INSTANCE = record end;
		PTP_CALLBACK_ENVIRON = ^TP_CALLBACK_ENVIRON; TP_CALLBACK_ENVIRON = record end;
		PTP_IO = ^TP_IO; TP_IO = record end;
		PTP_WORK = ^TP_WORK; TP_WORK = record end;

		TP_IO_CALLBACK = procedure(Instance: PTP_CALLBACK_INSTANCE; Context: pointer;
			Overlapped: LPOVERLAPPED; IoResult: Windows.ULONG; NumberOfBytesTransferred: Windows.ULONG_PTR; Io: PTP_IO); stdcall;
		TP_WORK_CALLBACK = procedure(Instance: PTP_CALLBACK_INSTANCE; Context: pointer; Work: PTP_WORK); stdcall;
	class var
		CreateThreadpoolIo: function(fl: HANDLE; pfnio: TP_IO_CALLBACK; pv: pointer; pcbe: PTP_CALLBACK_ENVIRON): PTP_IO; stdcall;
		StartThreadpoolIo: procedure(pio: PTP_IO); stdcall;
		CancelThreadpoolIo: procedure(pio: PTP_IO); stdcall;
		CloseThreadpoolIo: procedure(pio: PTP_IO); stdcall;
		CreateThreadpoolWork: function(pfnwk: TP_WORK_CALLBACK; pv: pointer; pcbe: PTP_CALLBACK_ENVIRON): PTP_WORK; stdcall;
		SubmitThreadpoolWork: procedure(pwk: PTP_WORK); stdcall;
		CloseThreadpoolWork: procedure(pwk: PTP_WORK); stdcall;
		WaitForThreadpoolWorkCallbacks: procedure(pwk: PTP_WORK; fCancelPendingCallbacks: Windows.BOOL); stdcall;

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
		class procedure Warning(const text: string); static;
		class procedure Warning(const what: string; const code: ErrorCode); static;
		class function CommandLineTail: string; static;

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
	seconds = type float;
	Ticks = object
		internal: int64;
		class function Get: Ticks; static;
		class procedure Init; static;
	private class var
		ifreq: double;
	end;
	operator -(const a, b: Ticks): Ticks; begin unchecked result.internal := (a.internal - b.internal); _end Assert(result.internal >= 0); end;
	operator :=(const t: Ticks): seconds; begin result := t.internal * Ticks.ifreq; end;

type
	pThreadLock = ^ThreadLock;
	ThreadLock = object
		srw: Win32.SRWLOCK;
	{$ifdef Debug} owner: TThreadID; guard: pointer; {$endif}
		procedure Invalidate;
		procedure Init;
		procedure Done;
		procedure Enter;
		procedure Leave;
		function AcquiredAssert: boolean;
	end;

	pThreadCV = ^ThreadCV;
	ThreadCV = object
		cv: Win32.CONDITION_VARIABLE;
	{$ifdef Debug} guard: pointer; {$endif}
		procedure Invalidate;
		procedure Init;
		procedure Done;
		procedure Wait(var lock: ThreadLock; timeout: uint = 0);
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

	pTask = ^Task;
	Task = object
	type
		Body = procedure(param: pointer);
		class procedure Post(proc: Body; param: pointer); static;
		class procedure Post(out task: pTask; proc: Body; param: pointer); static;
		class procedure Post(out task: Task; proc: Body; param: pointer); static;
		procedure Close;
		procedure Close(var link: pTask);

	private
	{$define enum := InternalFlag} {$define items := Dynamic _ 0 _ WillWait _ 1} {$define and_set := InternalFlagSet} enum_with_shortcuts
	var
		work: Win32.PTP_WORK;
		proc: Body;
		param: pointer;
		flags: InternalFlagSet;
		class procedure TrustedPost(out task: Task; flags: InternalFlagSet; proc: Body; param: pointer); static;
		class procedure TrustedPost(out task: pTask; flags: InternalFlagSet; proc: Body; param: pointer); static;
		procedure InternalClose(wait: boolean);
		class procedure ThreadpoolWorker(Instance: Win32.PTP_CALLBACK_INSTANCE; Context: pointer; Work: Win32.PTP_WORK); stdcall; static;
	class var
		// 'fire and forget' задачи ожидаются перед завершением программы. Они соответствуют Post без out-параметра и отличаются невыставленным WillWait.
		// Задачи вида Post(out task) здесь не учитываются, вызывающий обязан закрывать их самостоятельно, причём закрытие подождёт завершения.
		pendingFnFs: SizeInt;
		heyNoFnFs: pThreadCV;
	public
		class procedure WaitForAllFnFs; static;
	end;

	CookieManager = class;
	// Для разных штук, которые можно захватывать и освобождать.
	Cookie = class(TObjectEx)
		destructor Destroy; override;
	private
		man: CookieManager;
		index: SizeInt;
	end;

	CookieManager = class(TObjectEx)
		constructor Create(lck: pThreadLock);
		destructor Destroy; override;
		procedure Add(ck: Cookie);

	type
		CookieProc = procedure(cookie: Cookie; param: pointer);
		procedure ForEach(proc: CookieProc; param: pointer);
	private
		lck: pThreadLock;
		cookies: array of Cookie;
	{$ifdef Debug} busy: uint; {$endif}
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
		procedure StickToCurrentThread; // для совсем-совсем аварийных сценариев (т. е. которых вообще не должно быть — Assertion failed, Access violation),
		                                // чтобы вывести сообщение о фатальной ошибке из произвольного потока и впоследствии
		                                // усыплять (MaybeFreeze) остальные, которые попытаются тронуть консоль, включая считавшего себя её хозяином.
		procedure BypassStickForCurrentThread;
		function Width: uint;

	type
		CtrlC = class(Interception)
			con: pConsole;
			destructor Destroy; override;
			procedure Recover;
		end;

		CtrlCHandler = procedure(param: pointer);
		CtrlCCookie = class(Cookie)
			handler: CtrlCHandler;
			param: pointer;
		end;
		function RegisterCtrlCHandler(handler: CtrlCHandler; param: pointer): CtrlCCookie;
		procedure ResetCtrlC;

	strict private
	{$define enum := InternalFlag} {$define items := LockCreated _ 0 _ HInSet _ 1 _ HOutSet _ 2 _ HandlerInstalled _ 3 _ Reading _ 4 _ CtrlCPending _ 5} enum_with_shortcuts
	var
		lock: ThreadLock;
		hIn, hOut: HANDLE;
		bookkeep: set of InternalFlag;
		defCol, defBg: Color;
		defAttrWoCol: word;
		ctrlCHandlers: CookieManager;
		ctrlCs: array of Ticks;
		stick, bypassStick: TThreadID;
		dying: pTask; // Die напоследок вызывает блокирующую ReadConsole. Заблокированный ctrl-обработчик перестаёт реагировать на события.
		              // Поэтому Die выполняется вне обработчика.
		function GetScreenBufferInfoE: CONSOLE_SCREEN_BUFFER_INFO;
		class procedure RunCtrlCHandler(cookie: CtrlCCookie; param: pointer); static;
		class procedure DieTask(param: pointer); static;
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
		procedure MaybeFreeze(lock: boolean);

	public const
		ColorNames: array[Color] of string = ('0', 'r', 'g', 'rg', 'b', 'rb', 'gb', '.3', '.6', 'R', 'G', 'RG', 'B', 'RB', 'GB', '1');
		MinCtrlCsForHardShutdown = 3;
		CtrlCPeriod = seconds(1.4);
	strict private const
		// Биты CONSOLE_SCREEN_BUFFER_INFO.wAttributes.
		BitsToColor: array[0 .. 15] of Color = (Black, Navy, Green, Teal, Maroon, Purple, Olive, Gray, Silver, Blue, Lime, Aqua, Red, Fuchsia, Yellow, White);
		ColorToBits: array[Color] of word = (%0000, %0100, %0010, %0110, %0001, %0101, %0011, %1000, %0111, %1100, %1010, %1110, %1001, %1101, %1011, %1111);

	class var
		Instance: pConsole;
	end;

	&File = object
	{$define enum := Flag} {$define items := Readable _ 0 _ Writeable _ 1 _ Existing _ 2 _ New _ 3 _ Temp _ 4} {$define and_set := Flags} enum_with_shortcuts
	type
		// Запоминает, какие папки были созданы впервые, чтобы была возможность удалить их, если понадобится
		// (например, если они созданы как часть процесса создания файла, но создание самого файла провалилось).
		// Так, для TryCreatePath('base\sub\folder\file.txt', ...), когда sub и folder не существовало, будет folders = ('base\sub', 'base\sub\folder').
		PathRollback = object
			type Folder = widestring;
			var folders: array of Folder;
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
			function ToExceptionMessage: string;
			function ToException: Exception;
		private
			req: pointer; // pIORequest
			code: Win32.ErrorCode;
			transferred: SizeUint;
			class function Create(req: pointer; const code: Win32.ErrorCode; const transferred: SizeUint; forceFail: boolean = false): IOStatus; static;
		const
			STRANGE_ERROR = High(DWORD) - 42; // code = STRANGE_ERROR обозначает случай, когда операция провалилась с code = 0 (ну мало ли).
		end;

		CompletionHandler = procedure(const status: IOStatus; param: pointer);

		procedure Open(const fn: FilePath; flags: Flags = [Flag.Readable]; r: pOpenResult = nil);
		procedure Close;
		procedure Invalidate;
		function Valid: boolean;
		procedure Read(const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler = nil; param: pointer = nil);
		procedure Write(const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler = nil; param: pointer = nil);
		function Size: FileSize;
		function CancelPendingIO: boolean;
		class procedure Erase(const fn: string); static;

	const
		RW = [Readable, Writeable];

	strict private type
		pSharedHandle = ^SharedHandle;
		SharedHandle = object
			h: HANDLE;
			tp_io: Win32.PTP_IO;
			refcount: SizeInt;
			fn: FilePath;
			class function Create(h: HANDLE; const fn: FilePath): pSharedHandle; static;
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
	const
		WouldntCareAboutIOStatus: IOStatus = ();
	var
		ref: pSharedHandle;
		class function TryCreatePath(const fn: FilePath; out err: dword; out rollback: PathRollback): boolean; static;
		class procedure IOCompletionHandler(Instance: Win32.PTP_CALLBACK_INSTANCE; Context: pointer;
			Overlapped: LPOVERLAPPED; IoResult: Windows.ULONG; NumberOfBytesTransferred: Windows.ULONG_PTR; Io: Win32.PTP_IO); stdcall; static;
		class function CreateIORequest(h: pSharedHandle; const offset: FilePos; size, extraSize: SizeUint; write: boolean; onDone: CompletionHandler; param: pointer): pIORequest; static;
		class procedure CloseIORequest(a: pIORequest; const status: IOStatus; fromCompletionCallback: boolean); static;
		procedure IO(write: boolean; const at: FilePos; buf: pointer; size: SizeUint; onDone: CompletionHandler; param: pointer);
		class procedure OnDoneSync(const status: IOStatus; param: pointer); static;
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
		function Grow(elemSize: size_t): pointer; function Grow(arrayTypeInfo: pointer): pointer;
		function GrowBy(by, elemSize: size_t): pointer; function GrowBy(by: size_t; arrayTypeInfo: pointer): pointer;
		procedure Push(const elem; arrayTypeInfo: pointer);
		procedure RemoveShift(index, elemSize: size_t); procedure RemoveShift(index: size_t; arrayTypeInfo: pointer);
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
		function ConvertCase(&to: &Case): string; function Uppercase: string; function Lowercase: string;
		function ConvertCaseFirst(&to: &Case): string; function UppercaseFirst: string; function LowercaseFirst: string;
		function Stuffed(at, remove: SizeInt; const &with: string): string;
		function Split(sep: char; mergeSeps: boolean = true): Strings;
		function Split(const seps: CharSet; mergeSeps: boolean = true): Strings;

	{$define all_string_helper_consume_functions := {$if defined(func) or defined(rbool) or defined(complement) or defined(rev)} {$error all_string_helper_consume_functions would hide defines} {$endif}
		{$define func := Consume} one {$define rbool} one {$undef rbool}
		{$define func := ConsumeUntil} {$define complement} one {$define rbool} one {$undef rbool} {$undef complement}
		{$define func := ConsumeRev} {$define rev} one {$define rbool} one {$undef rbool} {$undef rev}
		{$define func := ConsumeRevUntil} {$define rev} {$define complement} one {$define rbool} one {$undef rbool} {$undef rev} {$undef complement}
		{$undef func} {$undef one}}
	{$define one :=
		function func(const syms: CharSet; p: SizeInt {$ifdef rbool}; out np: SizeInt {$endif}): {$ifdef rbool} boolean {$else} SizeInt {$endif};}
		all_string_helper_consume_functions

		function Find(const sample: string; start: SizeInt = 1): SizeInt;
		function FindRev(const sample: string; start: SizeInt = High(SizeInt)): SizeInt;
		function Quote: string;

	type
		ReplaceFunction = function(const src, sample: string; pos: SizeInt; param: pointer): string;
		function Replace(const sample: string; repl: ReplaceFunction; param: pointer): string;
		function Replace(const sample, by: string): string;
	private
		class function ReplaceByString(const src, sample: string; pos: SizeInt; param: pointer): string; static;

	public const
		UTFInvalid = High(UTFchar);
		Tab = #9;
		AsciiSpaces = [Tab, ' ', #13, #10];
		UTF8BOM = #$EF#$BB#$BF;

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

	FilePathHelper = type helper for FilePath
		function Path: FilePath;
		function Filename: string;
		function FilenameWoExt: string;
		function Extension: string;
	end;

	VarRec = object
		class function VTypeToString(vt: SizeInt): string; static;
		class function ToString(const v: TVarRec): string; static;
	type
		uint = uint64;
	end;

{$define vecf :=
type
	pvec = ^vec;
	vec = record
	type
		LinearData = array[0 .. veclen - 1] of float;
	var
		data: LinearData;
		class function Make(const value: float): vec; static;
		class function Make(const {$define op := ,} reduce_vec: float): vec; static;
	{$if veclen = 4}
		class function Make(const v: Vec3; const w: float): vec; static;
		class function Make31(const xyz, w: float): vec; static;
	{$endif}
		function ToString: string;
		function Length: float;
		function SquareLength: float;
		function Normalized: vec;
	{$if veclen = 4} function xyz: Vec3; {$endif}
	{$define iterate := property item: float read data[itemid] write data[itemid];} foreach_component
	end;} all_vectors

type
	Session = object
	private class var
		oldExceptProc: TExceptProc;
		prevFilter: Win32.LPTOP_LEVEL_EXCEPTION_FILTER;
		msvcrt: DLL;
		_resetstkoflw: function: cint; cdecl;
		class constructor Init;
		class procedure Done; static; // все правильно, разруливается через AddExitProc
		class function HumanTrace(frames: pCodePointer = nil; frameCount: SizeInt = -1): string; static;
		class procedure PrintError(const msg: string; fatal: boolean); static;
		class procedure OnUnhandledException(Obj: TObject; Addr: CodePointer; FrameCount: LongInt; Frame: PCodePointer); static;
		class procedure OnRuntimeError(ErrNo: Longint; Address: CodePointer; Frame: Pointer); static;
	{$ifdef assert} class procedure OnFailedAssert(const msg, fname: shortstring; lineno: longint; erroraddr: pointer); static; {$endif}
		class function Win32ExceptionFilter(ExceptionInfo: PEXCEPTION_POINTERS): Windows.LONG; stdcall; static;
		// не собирает трейс, просто печатает сообщение и убивает процесс
		class procedure Die(const msg: string; exitcode: Windows.UINT = 1); noreturn; static;
		class procedure Impossible(const what: string); noreturn; static;
		class procedure TestHacks; static;
	end;

var
	SingletonLock: ThreadLock;
	Con: Console;
	Executable: FilePath;
	MainThreadID: TThreadID;
	CPUCount, PageSize: SizeUint;

	constructor Exception.Create(const msg: string);
	begin
		inherited Create;
		self.msg := msg;
	end;

	constructor Exception.Create(const msg: string; const args: array of const);
	begin
		Create(msg.Format(args));
	end;

	class function Exception.Current: TObject;
	begin
		if not Assigned(RaiseList) then Session.Impossible('Exception.Current вызвана вне блока обработки исключения.');
		result := RaiseList[0].FObject;
	end;

	class function Exception.Message(obj: TObject): string;
	begin
		if obj is Exception then exit(Exception(obj).msg);
		if Assigned(obj) then exit(obj.ClassName);
		result := 'Произошла странная ошибка.';
	end;

	class function Exception.Message: string;
	begin
		result := Message(Current);
	end;

	procedure InvisibleInterception.AfterConstruction;
	begin
		inherited;
		msg += IfThen(msg <> '', ' ') + 'Вы не должны видеть этот текст, если видите — это баг.';
	end;

	procedure OutOfMemory.FreeInstance;
	begin
		// небольшой нюанс: деструктор отрабатывает ПЕРЕД FreeInstance, и единственная причина, благодаря которой
		// содержимое OutOfMemory.Instance остаётся нетронутым и OutOfMemory.Instance можно переиспользовать — это то,
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
		Instance.Free(Instance);
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

{$define _ := result := self;}
	function DLL.Proxy.Prefix(const prefix: string): Proxy;
	begin _
		dll^.prefix := prefix;
	end;

	function DLL.Proxy.Func(const namex: string; var funcPtr{: CodePointer}): Proxy;
	var
		name: string;
		fptr: CodePointer absolute funcPtr;
		star, startAt: SizeInt;
	begin _
		name := namex;
		star := name.Find('*');
		if star >= 1 then
		begin
			// Звёздочка ссылается на часть последнего беззвёздочного имени после первого «слова»: "CreateThreadpoolWork", "Close*" -> CloseThreadpoolWork
			startAt := dll^.lastNonStarred.ConsumeUntil(['A' .. 'Z', '_'], 2);
			if (startAt <= length(dll^.lastNonStarred)) and (dll^.lastNonStarred[startAt] = '_') then inc(startAt);
			name := name.Stuffed(star, length('*'), dll^.lastNonStarred.Tail(startAt));
		end else
			dll^.lastNonStarred := name;
		name := dll^.prefix + name;

		fptr := GetProcAddress(dll^.h, pChar(name));
		if not Assigned(fptr) and (dll^.temper <> DontThrow) then
		begin
			dll^.Unload;
			raise Exception.Create('Функция {} не найдена в {}.', [name, dll^.fn]);
		end;
		pCodePointer(Ary(dll^.fptrs).Grow(TypeInfo(dll^.fptrs))^) := @fptr;
	end;
{$undef _}

	function DLL.Load(const fn: FilePath; e: ThrowBehaviour = Throw): Proxy;
	begin
		Assert(h = 0);
		h := LoadLibraryW(pWideChar(string(fn).ToUTF16));
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
	function SetUnhandledExceptionFilter(lpTopLevelExceptionFilter: Win32.LPTOP_LEVEL_EXCEPTION_FILTER): Win32.LPTOP_LEVEL_EXCEPTION_FILTER; stdcall; external kernel32;
	function CancelIoEx(hFile: HANDLE; lpOverlapped: LPOVERLAPPED): Windows.BOOL; stdcall; external kernel32;

	class function Win32.ErrorCode.Create(value: dword; from: Origin): Win32.ErrorCode;
	begin
		result.value := value;
		result.from := from;
	end;

	class procedure Win32.Init;
	begin
		k32.Load(kernel32).Func('CreateThreadpoolIo', CreateThreadpoolIo).Func('Close*', CloseThreadpoolIo).
			Func('Start*', StartThreadpoolIo).Func('Cancel*', CancelThreadpoolIo).
			Func('CreateThreadpoolWork', CreateThreadpoolWork).Func('Submit*', SubmitThreadpoolWork).
			Func('Close*', CloseThreadpoolWork).Func('WaitFor*Callbacks', WaitForThreadpoolWorkCallbacks).
			Func('InitializeSRWLock', InitializeSRWLock).
			Func('Acquire*Exclusive', AcquireSRWLockExclusive).
			Func('Release*Exclusive', ReleaseSRWLockExclusive).
			Func('InitializeConditionVariable', InitializeConditionVariable).
			Func('WakeAll*', WakeAllConditionVariable).Func('Wake*', WakeConditionVariable).
			Func('Sleep*SRW', SleepConditionVariableSRW);
		Executable := QueryString(QueryStringCallback(@Win32.QueryModuleFileName), nil, 'имени исполняемого файла').ToUTF8;
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
			if d >= 0 then i += {"} 1 + d + {"} 1 else raise Exception.Create('Не закрыта кавычка: {}.', [result]);
		end else
			i := result.ConsumeUntil(StringHelper.AsciiSpaces, i);
		result := result.Tail(result.Consume(StringHelper.AsciiSpaces, i));
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
			cb(pWideChar(result), len + size_t(len > 0), report, param);
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

	class function Ticks.Get: Ticks;
	begin
		// On systems that run Windows XP or later, the function will always succeed and will thus never return zero.
		QueryPerformanceCounter((@result)^.internal);
	end;

	class procedure Ticks.Init;
	var
		freq: int64;
	begin
		QueryPerformanceFrequency((@freq)^);
		ifreq := 1 / freq;
	end;

	procedure ThreadLock.Invalidate;
	begin
	{$ifdef Debug} guard := nil; {$endif}
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

	procedure ThreadCV.Invalidate;
	begin
	{$ifdef Debug} guard := nil; {$endif}
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

	procedure ThreadCV.Wait(var lock: ThreadLock; timeout: uint = 0);
	var
		wt: dword;
	begin
		Assert(lock.AcquiredAssert);
	{$ifdef Debug} lock.owner := 0; {$endif}
		if timeout = 0 then wt := INFINITE else wt := timeout;
		if not Win32.SleepConditionVariableSRW(cv, lock.srw, wt, 0) and (GetLastError <> ERROR_TIMEOUT) then
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

	class procedure Task.Post(proc: Body; param: pointer); var t: pTask; begin TrustedPost(t, [], proc, param); end;
	class procedure Task.Post(out task: pTask; proc: Body; param: pointer); begin TrustedPost(task, [WillWait], proc, param); end;
	class procedure Task.Post(out task: Task; proc: Body; param: pointer); begin TrustedPost(task, [WillWait], proc, param); end;

	procedure Task.Close;
	begin
		Assert(not Assigned(work) or (flags * [Dynamic, WillWait] = [WillWait]));
		InternalClose(true);
	end;

	procedure Task.Close(var link: pTask);
	begin
		Assert(link = @self);
		if Assigned(link) then
		begin
			Assert(not Assigned(work) or (flags * [Dynamic, WillWait] = [Dynamic, WillWait]));
			link := nil;
			InternalClose(true);
		end;
	end;

	class procedure Task.TrustedPost(out task: Task; flags: InternalFlagSet; proc: Body; param: pointer);
	begin
		task.flags := flags;
		task.proc := proc;
		task.param := param;
		task.work := Win32.CreateThreadpoolWork(Win32.TP_WORK_CALLBACK(@im.Task.ThreadpoolWorker), @task, nil);
		if not Assigned(task.work) then raise Win32.OperationFailed('создать задачу для пула потоков (CreateThreadpoolWork)', GetLastError);
		if not (WillWait in flags) then InterlockedIncrement(pendingFnFs);
		Win32.SubmitThreadpoolWork(task.work);
	end;

	class procedure Task.TrustedPost(out task: pTask; flags: InternalFlagSet; proc: Body; param: pointer);
	begin
		Assert(not (Dynamic in flags));
		new(task);
		try
			TrustedPost(task^, flags + [Dynamic], proc, param);
		except
			dispose(task); task := nil;
			raise;
		end;
	end;

	procedure Task.InternalClose(wait: boolean);
	var
		untrack: boolean;
	begin
		untrack := Assigned(work) and not (WillWait in flags);
		if Assigned(work) then
		begin
			if wait then Win32.WaitForThreadpoolWorkCallbacks(work, false);
			Win32.CloseThreadpoolWork(work); work := nil;
		end;
		if Dynamic in flags then dispose(@self);

		if untrack and (InterlockedDecrement(pendingFnFs) = 0) then
		begin
			SingletonLock.Enter;
			if Assigned(heyNoFnFs) then heyNoFnFs^.WakeAll;
			SingletonLock.Leave;
		end;
	end;

	class procedure Task.ThreadpoolWorker(Instance: Win32.PTP_CALLBACK_INSTANCE; Context: pointer; Work: Win32.PTP_WORK); stdcall;
	var
		task: ^Task absolute Context;
	begin {$define args := Instance _ Work} unused_args
		task^.proc(task^.param);
		if not (WillWait in task^.flags) then task^.InternalClose(false);
	end;

	class procedure Task.WaitForAllFnFs;
	begin
		SingletonLock.Enter;
		try
			new(heyNoFnFs); heyNoFnFs^.Invalidate; heyNoFnFs^.Init;
			while pendingFnFs <> 0 do heyNoFnFs^.Wait(SingletonLock);
			heyNoFnFs^.Done; dispose(heyNoFnFs); heyNoFnFs := nil;
		finally
			SingletonLock.Leave;
		end;
	end;

	destructor Cookie.Destroy;
	begin
		if Assigned(man) then
		begin
			man.lck^.Enter;
			try
				Assert((index < length(man.cookies)) and (man.cookies[index] = self), 'что-то не так с печенькой');
			{$ifdef Debug} Assert(man.busy = 0, 'удаление во время обхода запрещено'); {$endif}
				man.cookies[index] := man.cookies[High(man.cookies)];
				man.cookies[index].index := index;
				SetLength(man.cookies, length(man.cookies) - 1);
			finally
				man.lck^.Leave;
				man := nil;
			end;
		end;
		inherited;
	end;

	constructor CookieManager.Create(lck: pThreadLock);
	begin
		inherited Create;
		self.lck := lck;
	end;

	destructor CookieManager.Destroy;
	begin
		inherited;
	end;

	procedure CookieManager.Add(ck: Cookie);
	begin
		Assert(not Assigned(ck.man), 'печенька уже добавлена');
		ck.man := self;
		lck^.Enter;
		try
		{$ifdef Debug} Assert(busy = 0, 'добавление во время обхода запрещено'); {$endif}
			Ary(cookies).Push(ck, TypeInfo(cookies));
			ck.index := High(cookies);
		finally
			lck^.Leave;
		end;
	end;

	procedure CookieManager.ForEach(proc: CookieProc; param: pointer);
	var
		i: SizeInt;
	begin
		Assert(lck^.AcquiredAssert);
	{$ifdef Debug} inc(busy); try {$endif}
		for i := 0 to High(cookies) do
			proc(cookies[i], param);
	{$ifdef Debug} finally dec(busy); end; {$endif}
	end;

	procedure Console.Init;
	var
		info: CONSOLE_SCREEN_BUFFER_INFO;
	begin
		Assert((bookkeep = []) and Ary(ctrlCs).Empty and (stick = 0) and not Assigned(dying));
		Assert(not Assigned(Instance), 'консоль должна быть одна');
		Instance := @self;

		try
			lock.Init; bookkeep += [LockCreated];
			hIn := CreateFileW('CONIN$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_READ, nil, OPEN_EXISTING, 0, 0);
			if hIn = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для ввода', GetLastError);
			bookkeep += [HInSet];
			hOut := CreateFileW('CONOUT$',  GENERIC_READ or GENERIC_WRITE, FILE_SHARE_WRITE, nil, OPEN_EXISTING, 0, 0);
			if hOut = INVALID_HANDLE_VALUE then raise Win32.OperationFailed('открыть дескриптор консоли для вывода', GetLastError);
			bookkeep += [HOutSet];

			info := GetScreenBufferInfoE;
			defCol := BitsToColor[info.wAttributes and %1111];
			defBg := BitsToColor[info.wAttributes shr 4 and %1111];
			defAttrWoCol := info.wAttributes and not word(%11111111); // FOREGROUND_* и BACKGROUND_*
			ctrlCHandlers := CookieManager.Create(@lock);

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
			if (HandlerInstalled in bookkeep) and not SetConsoleCtrlHandler(PHANDLER_ROUTINE(@Console.CtrlHandler), false) then Win32.Warning('SetConsoleCtrlHandler', GetLastError); bookkeep -= [HandlerInstalled];
		finally
			if LockCreated in bookkeep then lock.Leave;
		end;
		if Assigned(dying) then dying^.Close(dying);
		ctrlCHandlers.Free(ctrlCHandlers);
		if Instance = @self then Instance := nil;
		if (HOutSet in bookkeep) and (hOut <> INVALID_HANDLE_VALUE) and not CloseHandle(hOut) then Win32.Warning('CloseHandle', GetLastError); bookkeep -= [HOutSet];
		lock.Done; bookkeep -= [LockCreated];
	end;
	function Console.OK: boolean; begin result := HOutSet in bookkeep; end;

	procedure Console.Write(const s: string);
	begin
		if not OK then
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
	procedure Console.Line(const s: string = ''); begin Write(s + EOL); end;

	procedure Console.Colored(const s: string; baseCol: SizeInt = -1);
	var
		pieces: PiecesList;
		i: SizeInt;
		activeColor, newColor, activeBg, newBg: Color;
	begin
		pieces := ParseMarkdown(s);
		if not OK then
		begin
			for i := 0 to High(pieces) do system.write(pieces[i].data.ToUTF16);
			exit;
		end;

		activeColor := defCol; activeBg := defBg;
		lock.Enter;
		MaybeFreeze(false);
		try
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
		MaybeFreeze(true);
		// Assert(not (Reading in bookkeep));
		lock.Enter; bookkeep += [Reading]; lock.Leave;

		try
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
		finally
			lock.Enter; Assert(Reading in bookkeep); bookkeep -= [Reading]; lock.Leave;
			FlushInput;
		end;
		result := data.ToUTF8;
	end;

	procedure Console.Intercept;
	begin
		lock.Enter;
		try
			UnlockedIntercept;
		finally
			lock.Leave;
		end;
	end;

	procedure Console.StickToCurrentThread;
	begin
		lock.Enter;
		MaybeFreeze(false);
		stick := ThreadID;
		lock.Leave;
	end;

	procedure Console.BypassStickForCurrentThread;
	begin
		lock.Enter;
		bypassStick := ThreadID;
		lock.Leave;
	end;

	function Console.Width: uint;
	begin
		result := GetScreenBufferInfoE.dwSize.x;
	end;

	destructor Console.CtrlC.Destroy;
	begin
		Recover;
		inherited;
	end;

	procedure Console.CtrlC.Recover;
	begin
		if Assigned(con) then
		begin
			con^.ResetCtrlC;
			con := nil;
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

	procedure Console.ResetCtrlC;
	begin
		lock.Enter;
		MaybeFreeze(false);
		bookkeep -= [CtrlCPending];
		lock.Leave;
	end;

	function Console.GetScreenBufferInfoE: CONSOLE_SCREEN_BUFFER_INFO;
	begin
		if not GetConsoleScreenBufferInfo(hOut, (@result)^) then raise Win32.OperationFailed('получить информацию от консоли (GetConsoleScreenBufferInfo)', GetLastError);
	end;

	class procedure Console.RunCtrlCHandler(cookie: CtrlCCookie; param: pointer);
	begin {$define args := param} unused_args
		cookie.handler(cookie.param);
	end;

	class procedure Console.DieTask(param: pointer);
	begin {$define args := param} unused_args
		Con.BypassStickForCurrentThread;
		Session.Die('Получен{/ы/о} {} сигнал{/а/ов} Ctrl-C за {1}секунд{2:у/ы/}; жёсткое завершение.'.Format(
			[MinCtrlCsForHardShutdown, IfThen(round(CtrlCPeriod) <> 1, '{} ', '').Format([round(CtrlCPeriod)]), round(CtrlCPeriod)]));
	end;

	class function Console.CtrlHandler(dwCtrlType: DWORD): Windows.BOOL; stdcall;
		function PushCtrlC(var con: Console): boolean;
		begin
			Ary(con.ctrlCs).Push(Ticks.Get, TypeInfo(con.ctrlCs));
			if length(con.ctrlCs) > MinCtrlCsForHardShutdown then Ary(con.ctrlCs).RemoveShift(0, TypeInfo(con.ctrlCs));
			result := (length(con.ctrlCs) >= MinCtrlCsForHardShutdown) and
				(seconds(con.ctrlCs[High(con.ctrlCs)] - con.ctrlCs[High(con.ctrlCs) - MinCtrlCsForHardShutdown + 1]) <= CtrlCPeriod);
		end;

		procedure PostCR;
		var
         hey: widestring;
			i: SizeInt;
			inp: array of INPUT_RECORD;
			written: dword;
		begin
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

	begin
		result := false;
		if dwCtrlType = CTRL_C_EVENT then
		begin
			if Assigned(Instance) then
			begin
				Instance^.lock.Enter;
				try
					// Внимание, система запускает этот обработчик в отдельном потоке, бросать исключение не вариант.
					result := true;
					Instance^.FlushInput;

					if not Assigned(Instance^.dying) then
						if (Instance^.stick = 0) and PushCtrlC(Instance^) then
						begin
							// Убить процесс, если нажато слишком много Ctrl-C.
							Instance^.bookkeep -= [CtrlCPending];
							Task.Post(Instance^.dying, Task.Body(@Console.DieTask), nil);
						end else
						begin
							// Вызвать обработчики.
							Instance^.ctrlCHandlers.ForEach(Instance^.ctrlCHandlers.CookieProc(@Console.RunCtrlCHandler), nil);

							// Безусловно (!) запомнить флаг «нажат Ctrl-C» и бросить CtrlC на следующей операции с консолью, либо при явном вызове Con.Intercept.
							// Это состояние можно отменить через Console.ResetCtrlC.
							// На данный момент ResetCtrlC нельзя вызвать из самого обработчика, только извне.
							Instance^.bookkeep += [CtrlCPending];
						end;

					// Разблокировать ReadConsole: https://blog.not-a-kernel-guy.com/2009/12/29/726/.
					// По умолчанию ReadConsole не возвращается до конца строки (включен режим ENABLE_LINE_INPUT).
					if Reading in Instance^.bookkeep then PostCR;
				finally
					Instance^.lock.Leave;
				end;
			end;
		end;
	end;

	class function Console.ParseMarkdown(const s: string): PiecesList;
	label nextsym;
	var
		start, i: SizeInt;
		csp: sint;
		colorStack: array[0 .. 15] of cint;
		c: Color;

		procedure Append(ed: SizeInt; color: cint; ns: SizeInt);
		begin
			if ed > start then
			begin
				if Ary(result).Empty or (result[High(result)].color <> color) then
					Piece(Ary(result).Grow(TypeInfo(result))^).color := color;
				result[High(result)].data += s.AB(start, ed);
			end;
			start := ns; i := start;
		end;

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
							Append(i + 1, colorStack[csp], i + 2);
							goto nextsym;
						end;
						if s.Prefixed('/>', i + 1) then
						begin
							if csp = 0 then raise Exception.Create('{}: антипереполнение стека цветов.', [s.Stuffed(i, 0, '|').Quote]);
							Append(i, colorStack[csp], i + 3);
							dec(csp);
							goto nextsym;
						end;
						for c in Color do
							if s.Prefixed(ColorNames[c], i + 1) and (pChar(s)[i + length(ColorNames[c]) + 1 - 1] = '>') then
							begin
								if csp = High(colorStack) then raise Exception.Create('{}: переполнен стек цветов ({}).', [s.Stuffed(i, 0, '|').Quote, High(colorStack)]);
								Append(i, colorStack[csp], i + 1 + length(ColorNames[c]) + 1);
								inc(csp); colorStack[csp] := ord(c);
								goto nextsym;
							end;
					end;
			end;
			inc(i); nextsym:
		end;
		Append(i + 1, colorStack[csp], i + 1);
	end;

	procedure Console.UseWriteConsoleW(const text: string);
	var
		ws: widestring;
		p: pWideChar;
		n: SizeUint;
		written: DWORD;
	begin
		MaybeFreeze(false);
		UnlockedIntercept;
		ws := text.ToUTF16; p := pWideChar(ws);
		repeat
			n := min(length(ws) - (p - pWideChar(ws)), 4096);
			if not WriteConsoleW(hOut, p, n, (@written)^, nil) then raise Win32.OperationFailed('вывести на консоль {} символ{/а/ов} (WriteConsoleW)'.Format([n]), GetLastError);
			if written <> n then raise Exception.Create('WriteConsoleW: n = {}, written = {}.', [n, written]);
			p += n;
			UnlockedIntercept;
		until p = pWideChar(ws) + length(ws);
	end;

	procedure Console.FlushInput;
	begin
		if not FlushConsoleInputBuffer(hIn) then raise Win32.OperationFailed('очистить буфер консоли (FlushConsoleInputBuffer)', GetLastError);
	end;

	procedure Console.UnlockedIntercept;
	var
		cc: CtrlC;
	begin
		Assert(lock.AcquiredAssert);
		if CtrlCPending in bookkeep then
		begin
			bookkeep -= [CtrlCPending];
			cc := CtrlC.Create('Получено прерывание с клавиатуры (Ctrl-C).');
			cc.con := @self;
			raise cc;
		end;
	end;

	procedure Console.MaybeFreeze(lock: boolean);
	begin
		if lock then self.lock.Enter;
		if (stick <> 0) and (stick <> ThreadID) and (stick <> bypassStick) then
		begin
			self.lock.Leave;
			Sleep(INFINITE);
		end;
		if lock then self.lock.Leave;
	end;

	function &File.IOStatus.OK: boolean; begin result := (code.value = 0) and (transferred = pIORequest(req)^.size); end;
	function &File.IOStatus.Partial: boolean; begin result := (code.value = 0) and (transferred <= pIORequest(req)^.size); end;
	function &File.IOStatus.Cancelled: boolean;
	begin
		result := (code.from = code.Origin.GetLastError) and (code.value = ERROR_OPERATION_ABORTED) or
			(code.from = code.Origin.NTSTATUS) and (code.value = Win32.STATUS_CANCELLED);
	end;
	function &File.IOStatus.Failed: boolean; begin result := code.value <> 0; end;

	function &File.IOStatus.ToExceptionMessage: string;
	var
		c2: Win32.ErrorCode;
	begin
		if (code.value = 0) and (transferred < pIORequest(req)^.size) then
			result := IfThen(pIORequest(req)^.write,
				'В {} записал{1:ся/ись/ось} {} байт{/а/} (вместо {}).', 'Из {} прочитан{/ы/о} {} байт{/а/} (вместо {}).').Format(
					[pIORequest(req)^.h^.fn, transferred, pIORequest(req)^.size])
		else
		begin
			if code.value = STRANGE_ERROR then c2 := 0 else c2 := code;
			result := Win32.ErrorMessage('Ошибка {} {}: {err.}', [IfThen(pIORequest(req)^.write, 'записи', 'чтения'), pIORequest(req)^.h^.fn], c2);
		end;
	end;

	function &File.IOStatus.ToException: Exception;
	begin
		result := Exception.Create(ToExceptionMessage);
	end;

	class function &File.IOStatus.Create(req: pointer; const code: Win32.ErrorCode; const transferred: SizeUint; forceFail: boolean = false): IOStatus;
	begin
		result.req := req;
		result.code := code;
		if forceFail and (code.value = 0) then result.code.value := STRANGE_ERROR;
		result.transferred := transferred;
	end;

	procedure &File.Open(const fn: FilePath; flags: Flags; r: pOpenResult = nil);
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

		wfn := string(fn).ToUTF16;
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
			if New in flags then Session.Impossible('{}: New + RO?'.Format([fn]));
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
				CREATE_NEW: r^.exist := not ok and (err = ERROR_FILE_EXISTS);
				else r^.exist := ok and (Existing in flags);
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

	function &File.CancelPendingIO: boolean;
	begin
		if CancelIoEx(ref^.h, nil) or (GetLastError = Win32.ERROR_NOT_FOUND) then
			result := GetLastError <> Win32.ERROR_NOT_FOUND
		else
			raise Win32.Error('{}: не удалось отменить I/O (CancelIO), {err.}', [ref^.fn], GetLastError);
	end;

	class procedure &File.Erase(const fn: string);
	begin
		if not DeleteFileW(pWideChar(fn.ToUTF16)) then Win32.Warning(fn, GetLastError);
	end;

	class function &File.SharedHandle.Create(h: HANDLE; const fn: FilePath): pSharedHandle;
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

	class function &File.TryCreatePath(const fn: FilePath; out err: dword; out rollback: PathRollback): boolean;
	var
		i: SizeInt;
		dir: widestring;
	begin
		rollback := rollback.Empty;
		i := 1;
		repeat
			if string(fn).ConsumeUntil(['\', '/'], i, i) and (i <= length(fn) {не создавать file в first\second\file}) and (fn[i-1] <> ':' {E:\}) then
			begin
				dir := string(fn).Head(i-1).ToUTF16;
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
		until not string(fn).Consume(['\', '/'], i, i);
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
			CloseIORequest(nil, WouldntCareAboutIOStatus, false);
			raise;
		end;
		result^.ov.Internal     := 0;
		result^.ov.InternalHigh := 0;
		// Внимание: это НЕПРАВИЛЬНО.
		// Нужно ждать по отдельному событию на каждый OVERLAPPED, иначе нельзя будет одновременно выполнять более одного запроса на хэндле.
		// (Без hEvent система в качестве события использует сам объект файла.)
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
			if fromCompletionCallback then
				a^.onDone(status, a^.param)
			else
				Win32.CancelThreadpoolIo(a^.h^.tp_io);

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
			// В остальных случаях (асинхронная запись, любое чтение) за целостность буфера на протяжении операции отвечает вызывающий.
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
			// Операция начата асинхронно, IOCompletionHandler выполнится в будущем (в т. ч. при ошибке) пулом потоков.
			// Если это чтение и не задан onDone, подождать завершения.
			// Если это запись, никогда не ждать. Без onDone получится fire-and-forget реквест.
			// (Может быть, я изменю это на полностью синхронный вариант, как с чтением — тогда extraSize можно будет убрать).
			if not write and not Assigned(onDone) then
				if not GetOverlappedResult(ref^.h, a^.ov, (@transferred)^, true) then
					raise Win32.Error('Не удалось получить результат {} {}. {Err.}', [IfThen(write, 'записи', 'чтения'), ref^.fn], GetLastError);
		end else
		begin
			// Операция провалилась, IOCompletionHandler не выполнен и не будет.
			CloseIORequest(a, WouldntCareAboutIOStatus, false);
			raise IOStatus.Create(a, GetLastError, 0, true).ToException;
		end;
		if Assigned(syncExc) then raise syncExc;
	end;

	class procedure &File.OnDoneSync(const status: IOStatus; param: pointer);
	begin
		if not status.OK then Exception(param^) := status.ToException;
	end;

	class procedure &File.GlobalInitialize;
	begin
		Assert(not HeyNoIOPending.OK, 'File.GlobalInitialize уже вызвана');
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
			block := pDynArrayHeader(self) - 1; Assert(block^.refcount = 1, 'AryHelper.Grow: RefCount = {}'.Format([block^.refcount]));
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
		if Assigned(td^.elTypeManaged) then InitializeArray(result, td^.elTypeManaged, by);
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
		if Assigned(td^.elTypeManaged) then fpc_addref(target, td^.elTypeManaged);
	end;

	procedure AryHelper.RemoveShift(index, elemSize: size_t);
	var
		block: pDynArrayHeader;
		newSize, holeOffset: size_t;
	begin
		Assert(Assigned(self));
		block := pDynArrayHeader(self) - 1;
		Assert((block^.refcount = 1) and (block^.high >= 0) and (index <= size_t(block^.high)), 'Index = {}, High = {}, RefCount = {}'.Format([index, block^.high, block^.refcount]));

		newSize := size_t(block^.high) * elemSize;
		holeOffset := index * elemSize;
		dec(block^.high);
		Move((self + holeOffset + elemSize)^, (self + holeOffset)^, newSize - holeOffset);
		if newSize > 0 then
			self := ReallocMem(block, sizeof(DynArrayHeader) + newSize) + sizeof(DynArrayHeader)
		else
		begin
			FreeMem(block);
			self := nil;
		end;
	end;

	procedure AryHelper.RemoveShift(index: size_t; arrayTypeInfo: pointer);
	var
		td: pDynArrayTypeData;
	begin
		td := ExtractDynArrayTypeData(arrayTypeInfo);
		if Assigned(td^.elTypeManaged) then FinalizeArray(pointer(self) + index * td^.elSize, td^.elTypeManaged, 1);
		RemoveShift(index, td^.elSize);
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
			form, i, fs, fe: SizeInt;
			s: string;

			function ConsumeForm(iform: SizeInt; fe: pSizeInt = nil): boolean;
			begin
				ConsumeUntil(['/', '}'], start, start);
				result := pChar(self)[start-1] = IfThen(iform < 3, '/', '}');
				if Assigned(fe) then fe^ := start;
				inc(start); // пропустит как /, так и заключительный }.
			end;

		begin
			if (arg < 0) or (arg >= length(args)) then exit(false);
			s := VarRec.ToString(args[arg]);
			if length(s) < 1 then exit(false);
			if (s[length(s)] in ['0', '5'..'9']) or (length(s) >= 2) and (s[length(s) - 1] = '1') then
				form := 3
			else
				form := 2 - ord(s[length(s)] = '1');

			// эти странные конструкции вместо for i := 1 to 3 затыкают компилятор насчёт неинициализированных fs/fe.
			for i := 1 to form - 1 do if not ConsumeForm(i) then exit(false);
			fs := start;
			if not ConsumeForm(form, @fe) then exit(false);
			for i := form + 1 to 3 do if not ConsumeForm(i) then exit(false);

			result := true;
			Append(brkAt, AB(fs, fe), start);
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
		result := ''; start := 1; p := 1; next := 0; last := 0;
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

	function StringHelper.ConvertCase(&to: &Case): string;
	begin
		case &to of
			&Case.Lower: result := System.LowerCase(self.ToUTF16).ToUTF8;
			&Case.Upper: result := System.UpCase(self.ToUTF16).ToUTF8;
			else Session.Impossible('Case = {}'.Format([ord(&to)]));
		end;
	end;
	function StringHelper.Uppercase: string; begin result := ConvertCase(&Case.Upper); end;
	function StringHelper.Lowercase: string; begin result := ConvertCase(&Case.Lower); end;

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
	function StringHelper.UppercaseFirst: string; begin result := ConvertCaseFirst(&Case.Upper); end;
	function StringHelper.LowercaseFirst: string; begin result := ConvertCaseFirst(&Case.Lower); end;

	function StringHelper.Stuffed(at, remove: SizeInt; const &with: string): string;
	begin
		result := Head(at - 1) + &with + Tail(at + min(remove, length(self) - at + 1));
	end;

	function StringHelper.Split(sep: char; mergeSeps: boolean = true): Strings; begin result := Split([sep], mergeSeps); end;
	function StringHelper.Split(const seps: CharSet; mergeSeps: boolean = true): Strings;
	var
		start, ed, n, pass: SizeInt;
	begin
		for pass := 0 to 1 do
		begin
			start := 1; n := 0;
			while start <= length(self) do
			begin
				ConsumeUntil(seps, start, ed);
				if pass = 1 then result[n] := AB(start, ed);
				inc(n);
				start := ed;

				if mergeSeps then Consume(seps, start, start)
				else if start <= length(self) then begin Assert(self[start] in seps); inc(start); end;
			end;
			if pass = 0 then SetLength(result, n);
		end;
	end;

{$define one :=
	function StringHelper.func(const syms: CharSet; p: SizeInt {$ifdef rbool}; out np: SizeInt {$endif}): {$ifdef rbool} boolean {$else} SizeInt {$endif};
	{$ifndef rbool} var np: SizeInt absolute result; {$endif}
	begin
		np := p;
		while {$ifdef rev} (np > 0) {$else} (np <= length(self)) {$endif} and {$ifdef complement} not {$endif} (self[np] in syms) do
			{$ifdef rev} dec {$else} inc {$endif} (np);
	{$ifdef rbool} result := np <> p; {$endif}
	end;}
	all_string_helper_consume_functions

	function StringHelper.Find(const sample: string; start: SizeInt = 1): SizeInt;
	var
		i: SizeInt;
	begin
		for i := start to length(self) - length(sample) + 1 do
			if (self[i] = sample[1]) and (CompareChar(self[i], sample[1], length(sample)) = 0) then
				exit(i);
		result := 0;
	end;

	function StringHelper.FindRev(const sample: string; start: SizeInt = High(SizeInt)): SizeInt;
	var
		i: SizeInt;
	begin
		for i := min(start, length(self) - length(sample) + 1) downto 1 do
			if (self[i] = sample[1]) and (CompareChar(self[i], sample[1], length(sample)) = 0) then
				exit(i);
		result := 0;
	end;

	function StringHelper.Quote: string;
	const
		Variants: array[0 .. 4, 0 .. 1] of string = (('"', '"'), ('''', ''''), ('«', '»'), ('„', '“'), ('<', '>'));
	var
		i: SizeInt;
	begin
		for i := 0 to High(Variants) do
			if (i = High(Variants)) or (Find(Variants[i, 0]) = 0) and ((Variants[i, 1] = Variants[i, 0]) or (Find(Variants[i, 1]) = 0)) then
				exit(Variants[i, 0] + self + Variants[i, 1]);
	end;

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

	function FilePathHelper.Path: FilePath;
	begin
		result := string(self).Head(string(self).ConsumeRevUntil(['/', '\'], length(self)));
	end;

	function FilePathHelper.Filename: string;
	begin
		result := string(self).Tail(string(self).ConsumeRevUntil(['/', '\'], length(self)) + 1);
	end;

	function FilePathHelper.FilenameWoExt: string;
	var
		p: SizeInt;
	begin
		p := string(self).ConsumeRevUntil(['/', '\', '.'], length(self));
		if (p > 0) and (self[p] = '.') then result := string(self).AB(string(self).ConsumeRevUntil(['/', '\'], p) + 1, p) else result := string(self).Tail(p + 1);
	end;

	function FilePathHelper.Extension: string;
	var
		p: SizeInt;
	begin
		p := string(self).ConsumeRevUntil(['/', '\', '.'], length(self));
		if (p > 0) and (self[p] = '.') then result := string(self).Tail(p + 1) else result := '';
	end;

	class function VarRec.VTypeToString(vt: SizeInt): string;
	var
		Known: Strings;
	begin
		Known := ('Integer/Boolean/Char/Extended/String/Pointer/PChar/Object/Class/WideChar/PWideChar/AnsiString/Currency/Variant/Interface/' +
			'WideString/Int64/QWord/UnicodeString').Split('/');
		if (vt >= 0) and (vt < length(Known)) then result := 'vt{} ({})'.Format([Known[vt], vt]) else result := '? ({})'.Format([vt]);
	end;

	class function VarRec.ToString(const v: TVarRec): string;
	begin
		case v.VType of
			vtInteger: result := im.ToString(v.VInteger);
			vtBoolean: result := IfThen(v.VBoolean, 'да', 'нет');
			vtChar:    result := v.VChar;
			vtExtended: result := im.ToString(v.VExtended^);
			vtString:   result := v.VString^;
			vtPChar:    result := v.VPChar;
			vtPointer:  result := '$' + HexStr(v.VPointer);
			vtObject:   if Assigned(v.VObject) then result := v.VObject.ToString else result := 'TObject(nil)';
			vtClass:    if Assigned(v.VClass) then result := v.VClass.ClassName else result := 'TClass(nil)';
			vtAnsiString: result := ansistring(v.VAnsiString);
			vtInt64:      result := im.ToString(v.VInt64^);
			vtQWord:      result := im.ToString(v.VQWord^);
			else          result := '(vt = {})'.Format([VTypeToString(v.VType)]);
		end;
	end;

{$define vecf :=
	class function vec.Make(const value: float): vec; begin {$define iterate := result.item := value;} foreach_component end;
	class function vec.Make(const {$define op := ,} reduce_vec: float): vec; begin {$define iterate := result.data[itemid] := item;} foreach_component end;
{$if veclen = 4}
	class function vec.Make(const v: Vec3; const w: float): vec; begin {$define iterate := {$if itemid <= 2} result.data[itemid] := v.data[itemid]; {$else} result.w := w; {$endif}} foreach_component end;
	class function vec.Make31(const xyz, w: float): vec; begin {$define iterate := result.data[itemid] := {$if itemid <= 2} xyz {$else} w {$endif};} foreach_component end;
{$endif}

	function vec.ToString: string;
	begin
		result := {$define item_conv := {$ifndef first} ', ' + {$endif} im.ToString(data[itemid])} reduce_vec;
	end;

	function vec.Length: float;
	begin
		result := sqrt(SquareLength);
	end;

	function vec.SquareLength: float;
	begin
		result := {$define item_conv := sqr(data[itemid])} reduce_vec;
	end;

	function vec.Normalized: vec;
	var
		ilen: float;
	begin
		ilen := 1.0 / sqrt(SquareLength);
		{$define iterate := result.data[itemid] := data[itemid] * ilen;} foreach_component
	end;

{$if veclen = 4}
	function vec.xyz: pair3; begin result.data[0] := data[0]; result.data[1] := data[1]; result.data[2] := data[2]; end;
{$endif}

	operator +(const a, b: vec): vec; begin {$define iterate := result.data[itemid] := a.data[itemid] + b.data[itemid];} foreach_component end;
	operator -(const a, b: vec): vec; begin {$define iterate := result.data[itemid] := a.data[itemid] - b.data[itemid];} foreach_component end;
	operator -(const v: vec): vec; begin {$define iterate := result.data[itemid] := -v.data[itemid];} foreach_component end;
	operator *(const a, b: vec): vec; begin {$define iterate := result.data[itemid] := a.data[itemid] * b.data[itemid];} foreach_component end;
	operator *(const x: float; const v: vec): vec; begin {$define iterate := result.data[itemid] := v.data[itemid] * x;} foreach_component end;
	operator *(const v: vec; const x: float): vec; begin result := x * v; end;
	operator /(const a, b: vec): vec; begin {$define iterate := result.data[itemid] := a.data[itemid] / b.data[itemid];} foreach_component end;
	operator /(const a: vec; const x: float): vec; begin {$define iterate := result.data[itemid] := a.data[itemid] / x;} foreach_component end;
	operator /(const x: float; const b: vec): vec; begin {$define iterate := result.data[itemid] := x / b.data[itemid];} foreach_component end;} all_vectors

	class constructor Session.Init;
	var
		si: SYSTEM_INFO;
	begin
		oldExceptProc := ExceptProc; ExceptProc := TExceptProc(@Session.OnUnhandledException);
		prevFilter := SetUnhandledExceptionFilter(Win32.LPTOP_LEVEL_EXCEPTION_FILTER(@Session.Win32ExceptionFilter));
		ErrorProc := TErrorProc(@Session.OnRuntimeError);
	{$ifdef assert} AssertErrorProc := TAssertErrorProc(@Session.OnFailedAssert); {$endif}

		MainThreadID := ThreadID;
		CPUCount := GetCPUCount;
		OutOfMemory.InitGlobal;
		AddExitProc(TProcedure(@Session.Done)); // иначе не вызовется при сбое инициализации

		GetSystemInfo((@si)^);
		PageSize := si.dwPageSize;

		// Чтобы операции вида sqrt(-5) или 1.0/0.0 давали NaN/Inf вместо floating-point exception.
		// Для полноты картины нужно сделать SetMXCSR(GetMXCSR or %1111110000000), но поговаривают, что SSE ведёт себя тихо по умолчанию.
		Set8087CW(Get8087CW or %111111);

		Win32.Init;
		SingletonLock.Init;
		Ticks.Init;
		Con.Init;
		TestHacks;
		msvcrt.Load('msvcrt.dll', DontThrow).Func('_resetstkoflw', _resetstkoflw);
	end;

	class procedure Session.Done;
	begin
		&File.WaitForAllIORequests;
		Task.WaitForAllFnFs;
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
			result := ((line.Consume(StringHelper.AsciiSpaces, p, p) and false) or not line.Consume(['$'], p, p) or
				not line.Consume(['0' .. '9', 'A' .. 'F'], p, p)) or (line.Consume(StringHelper.AsciiSpaces, p, p) and false) or
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
				if not Assigned(frame) then break
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
					'  ...{}'.Format([IfThen(trace[i].uninteresting > 1, '+{}...'.Format([trace[i].uninteresting]))]));
	end;

	class procedure Session.PrintError(const msg: string; fatal: boolean);
	begin
		if Con.OK then
		begin
			if fatal then Con.StickToCurrentThread;
			Con.ResetCtrlC;
			Con.Colored(Con.Escape(msg), Con.Red);
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
		ExceptProc := oldExceptProc;
		if Obj is SpecialException then SpecialException(Obj).AskForLastResort;
		if (ThreadID = MainThreadID) and (Obj is Interception) and not (Obj is InvisibleInterception) then
			// просто выйти; но прилетевшая сюда InvisibleInterception означает баг, поэтому должна быть видна.
		else
		begin
			msg := Exception.Message(Obj);
			if not (Obj is SpecialException) then msg += HumanTrace(Frame, FrameCount);
			PrintError(msg, true);
		end;

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

threadvar
	// Глупая RTL, я хочу видеть сообщение о сегфолте как «чтение/запись по адресу XXXX», а не как «Runtime error 216» или «EAccessViolation: Access violation»!
	// Эта информация в 80% случаев выдаёт ошибку без необходимости смотреть в отладчик, который здесь к тому же глючный до неюзабельности.
	LastException: EXCEPTION_RECORD;

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
			(re: reAccessViolation; plan: Seppuku; msg: 'Произошло обращение по неверному адресу.'),
			(re: reStackOverflow; plan: ThrowStackOverflow; msg: StackOverflow.DefaultMessage)
		);
	var
		name, msg: string;
		i: SizeInt;
	begin {$define args := Address} unused_args
		for i := 0 to High(KnownErrors) do
			if ErrNo = RuntimeErrorExitCodes[KnownErrors[i].re] then
			begin
				msg := KnownErrors[i].msg;
				case KnownErrors[i].plan of
					ThrowMessage: raise Exception.Create(msg);
					ThrowOOM: if Assigned(OutOfMemory.Instance) then raise OutOfMemory.Instance;
					ThrowStackOverflow: raise StackOverflow.Create(msg);
				end;

				if (ErrNo = RuntimeErrorExitCodes[reAccessViolation]) and (LastException.ExceptionCode = STATUS_ACCESS_VIOLATION) then
				begin
					if LastException.NumberParameters >= 2 then
						msg := 'Программа выполнила {} по неверному адресу (${}).'.Format([
							IfThen(LastException.ExceptionInformation[0] > 0, 'запись', 'чтение'),
							HexStr(LastException.ExceptionInformation[1], bitsizeof(pointer) div 4), ThreadID]);
					msg := 'STATUS_ACCESS_VIOLATION' + EOL + msg;
				end;
				Die(msg + HumanTrace(@Frame), ErrNo);
			end;

		i := IndexByte(RuntimeErrorExitCodes, length(RuntimeErrorExitCodes), ErrNo);
		if (ErrNo <= High(byte)) and (i >= 0) then
		begin
			str(TRuntimeError(i), name);
			if name.Prefixed('re') then name := name.Tail(length('re') + 1);
		end else
			name := 'с кодом {}'.Format([ToString(ErrNo)]);
		Die('{}.'.Format([name]) + HumanTrace(@Frame), ErrNo);
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

	class function Session.Win32ExceptionFilter(ExceptionInfo: PEXCEPTION_POINTERS): Windows.LONG; stdcall;
	begin
		LastException := ExceptionInfo^.ExceptionRecord^;
		result := prevFilter(ExceptionInfo);
	end;

	class procedure Session.Die(const msg: string; exitcode: Windows.UINT = 1);
	begin
		try
			PrintError(msg, true);
		finally
			// Лучше не ExitProcess: https://blog.not-a-kernel-guy.com/2007/07/15/210/.
			// Алсо, в общем случае TerminateProcess не ждёт завершения процесса и сразу возвращается,
			// но TerminateProcess(GetCurrentProcess) — не очень документированный синхронный частный случай: https://stackoverflow.com/a/40499062.
			TerminateProcess(GetCurrentProcess, exitcode);
		end;
	end;

	class procedure Session.Impossible(const what: string);
	begin
		Die('Внутренняя ошибка: {}.'.Format([what]));
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
			ManagedType = record s: string; x: SizeInt; end;
			ExpectedItem = record m: ManagedType; ref: SizeInt; end; ExpectedItems = array of ExpectedItem;

			procedure ConstructExpected(var exp: ExpectedItems);
			begin
				SetLength(exp, 4);
				exp[0].m.s := 'Test 1: ' + ToString(ThreadID); exp[0].m.x := 1; exp[0].ref := 2;
				exp[1].m.s := 'Test 2';                        exp[1].m.x := 2; exp[1].ref := -1;
				exp[2].m.s := 'Test 3: ' + ToString(ThreadID); exp[2].m.x := 3; exp[2].ref := 1;
				exp[3] := exp[0];
			end;
			function MRepr(const c: ManagedType; ref: SizeInt): string; begin result := '(''{0}'', {1}, ref={2})'.Format([c.s, c.x, ref]); end;

		var
			a: array of ManagedType;
			exp: ExpectedItems;
			i: SizeInt;
		begin
			ConstructExpected(exp);
			Ary(a).Push(exp[0].m, TypeInfo(a));
			Ary(a).Push(exp[1].m, TypeInfo(a));
			ManagedType(Ary(a).Grow(TypeInfo(a))^) := exp[2].m;
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
	// Учитывает выделенную кем-либо память, чтобы можно было доосвободить её руками, если аллокация бросила исключение.
	// Подразумевается, что «кто-либо» — C-библиотека, и исключение бесцеремонно срезает весь её C-стек в обход нормальной финализации.
	// Было бы намного проще ловить в аллокации исключение и преобразовывать в exit(nil), но у меня такой вариант почему-то часто сегфолтится.
	// Возможно, я накосячил при модификации LodePNG, т. к. там проверки alloc'ов вроде как везде стоят.
	//
	// Если выделенный блок P предполагалось вернуть вызывающему, его придётся отобрать у следилки через TakeAway(P, {out} real), которая вернёт real —
	// настоящий указатель, который нужно освободить через FreeMem (P указывает внутрь него).
	//
	// Например, lodepng_encode_memory выделяет блок для результата (зд. outData) самостоятельно, поэтому придётся делать так:
	// try
	//    errorcode := lodepng.encode_memory({out} outData, ...);
	// except
	//    lodepng.island.Purge(ThreadID); // освобождение всего, что навыделяла и не успела освободить encode_memory
	//    raise;
	// end;
	// lodepng.TakeAway(outData, outDataBlock); // владение outData переходит от island'а вызывающему
	// ...работа с outData...
	// FreeMem(outDataBlock);
	//
	// Кроме того, можно зарегистрировать пользовательский обработчик (RegisterHook), вызываемый при реаллокации.
	// Например, такой обработчик может бросить исключение, чтобы прервать процесс (и нарваться на вышеописанный сценарий с необходимостью Purge).
	MemoryIsland = object
		procedure Init;
		procedure Done;
		function Realloc(p: pointer; nsize: size_t): pointer;
		procedure TakeAway(p: pointer; out real: pointer);
		procedure Purge(ownedBy: TThreadID);

	type
		Hook = procedure(param: pointer);
		HookCookie = class(Cookie)
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
		class procedure RunHook(cookie: HookCookie; param: pointer); static;
		procedure Unwatch(index: SizeInt);
	{$ifdef Debug} procedure Validate(index: SizeInt; p: pointer); {$endif}
	end;

	procedure MemoryIsland.Init;
	begin
		lock.Init;
		Assert(watchCount = 0);
		hooks := CookieManager.Create(@lock);
	end;

	procedure MemoryIsland.Done;
	begin
		hooks.Free(hooks);
		lock.Done;
	end;

	function MemoryIsland.Realloc(p: pointer; nsize: size_t): pointer;
	var
		watchIndex: SizeInt;
	begin
		lock.Enter;
		try
			hooks.ForEach(hooks.CookieProc(@MemoryIsland.RunHook), nil);
			if Assigned(p) then
			begin
				watchIndex := (pHeader(p) - 1)^.watchIndex;
			{$ifdef Debug} Validate(watchIndex, p); {$endif}
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
		{$ifdef Debug} Validate(pHeader(real)^.watchIndex, p); {$endif}
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

	class procedure MemoryIsland.RunHook(cookie: HookCookie; param: pointer);
	begin {$define args := param} unused_args
		cookie.cb(cookie.param);
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

{$ifdef Debug}
	procedure MemoryIsland.Validate(index: SizeInt; p: pointer);
	begin
		Assert(index < watchCount);
		Assert((watch[index].data = p) and (watch[index].thread = ThreadID));
	end;
{$endif}

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
			lib.Load(fn).Prefix('lodepng_').Func('decode_memory', decode_memory).Func('encode_*', encode_memory).Func('error_text', error_text);
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
		result := IfThen(msg <> 'unknown error code', '{0} ({1})', '{1}').Format([msg, 'код ошибки LodePNG ' + ToString(code)]);
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
		function pixelSize: size_t;
		function id: string;
	const
		Info: array[ImageFormat] of record
			id: string;
			pixelSize: size_t;
		end =
		(
			(id: 'g'; pixelSize: 1),
			(id: 'ga'; pixelSize: 2),
			(id: 'rgb'; pixelSize: 3),
			(id: 'rgba'; pixelSize: 4)
		);
	end;

	p1x8 = ^_1x8; _1x8 = array[0 .. 0] of uint8;
	p2x8 = ^_2x8; _2x8 = array[0 .. 1] of uint8;
	p3x8 = ^_3x8; _3x8 = array[0 .. 2] of uint8;
	p4x8 = ^_4x8; _4x8 = array[0 .. 3] of uint8;

	ImageSpec = object
		w, h, frames: SizeUint;
		format: ImageFormat;
		class function Make(w, h, frames: SizeUint; format: ImageFormat): ImageSpec; static;
	end;

	pImage = ^Image;
	Image = object
		data: pointer;
		spec: ImageSpec;
		own: pointer;
		procedure Invalidate;
		procedure Init(const name: string; data: pointer; const spec: ImageSpec; own: pointer = nil);
		procedure Done;
		class procedure ValidateSize(const spec: ImageSpec; const name: string); static;
		class procedure ValidateFrame(index, count: uint; const name: string); static;
		class function AllocateData(const spec: ImageSpec; const name: string): pointer; static;
		function PixelPtr(x, y, f: SizeUint): pointer;
		procedure DecodePixelNumber(pixel: SizeUint; out x, y, f: SizeUint; out ofs: pointer);
		procedure NextPixel(var pixel: SizeUint; var x, y, f: SizeUint);
		property w: SizeUint read spec.w;
		property h: SizeUint read spec.h;
		property frames: SizeUint read spec.frames;
		property format: ImageFormat read spec.format;

		class function ApplyGamma(const linear: float): float; static;
		class function UnapplyGamma(const rgbcomponent: float): float; static;
		class function ReadG(ofs: pointer; format: ImageFormat): float; static;
		class function ReadGA(ofs: pointer; format: ImageFormat): Vec2; static;
		class function ReadRGB(ofs: pointer; format: ImageFormat): Vec3; static;
		class function ReadRGBA(ofs: pointer; format: ImageFormat): Vec4; static;
		class function ReadLinearRGBA(ofs: pointer; format: ImageFormat): Vec4; static;
		class procedure WriteG(ofs: pointer; format: ImageFormat; const px: float); static;
		class procedure WriteGA(ofs: pointer; format: ImageFormat; const px: Vec2); static;
		class procedure WriteRGB(ofs: pointer; format: ImageFormat; const px: Vec3); static;
		class procedure WriteRGBA(ofs: pointer; format: ImageFormat; const px: Vec4); static;
		class procedure WriteLinearRGBA(ofs: pointer; format: ImageFormat; const px: Vec4); static;
		class function RGB8ToGray(ofs: pointer): float; static;
		class function RGBToGray(const r, g, b: float): float; static;
		class function LinearRGBToLinearGray(const r, g, b: float): float; static;
		class function Denorm8(const value: float): uint8; static;

		class function SizeToString(const spec: ImageSpec): string; static;
		class function SpecToString(const spec: ImageSpec): string; static;

	const
		MaxDataSize = {$if defined(CPU32)} High(SizeUint) {$elseif defined(CPU64)} High(SizeUint) shr 16 {$else} {$error platform?} {$endif} div 8;
		MaxDimension = 65536;
		MaxFrames = 1000;
		Norm8 = 1 / High(uint8);
		RToGrayK = 0.21;
		GToGrayK = 0.72;
		BToGrayK = 0.07;
	end;

	function ImageFormatHelper.pixelSize: size_t; begin result := Info[self].pixelSize; end;
	function ImageFormatHelper.id: string; begin result := Info[self].id; end;

	class function ImageSpec.Make(w, h, frames: SizeUint; format: ImageFormat): ImageSpec;
	begin
		result.w := w;
		result.h := h;
		result.frames := frames;
		result.format := format;
	end;

	procedure Image.Invalidate;
	begin
		data := nil;
	end;

	procedure Image.Init(const name: string; data: pointer; const spec: ImageSpec; own: pointer = nil);
	var
		allocate: boolean;
	begin
		allocate := not Assigned(data);
		try
			ValidateSize(spec, name);
			if allocate then
			begin
				own := AllocateData(spec, name);
				data := own;
			end;
			self.data := data;
			self.spec := spec;
			self.own := own; {$ifdef Debug} if not Assigned(own) then self.own := GetMem(1); {$endif}
		except
			if allocate then FreeMem(own);
			Invalidate;
			raise;
		end;
	end;

	procedure Image.Done;
	begin
		if Assigned(data) then
		begin
			FreeMem(own);
			data := nil;
		end;
	end;

	class procedure Image.ValidateSize(const spec: ImageSpec; const name: string);
	begin
		if (spec.w = 0) or (spec.h = 0) or (spec.frames = 0) then raise Exception.Create('Неверный размер {}: {}.'.Format([name, SizeToString(spec)]));
		if (spec.w > MaxDimension) or (spec.h > MaxDimension) or (spec.frames > MaxFrames) or
			(spec.w > MaxDataSize div spec.format.pixelSize) or (spec.h > MaxDataSize div (spec.format.pixelSize * spec.w)) or
			(spec.frames > MaxDataSize div spec.format.pixelSize div (spec.w * spec.h))
		then
			raise Exception.Create('{}: слишком большая картинка ({}).'.Format([name, SpecToString(spec)]));
	end;

	class procedure Image.ValidateFrame(index, count: uint; const name: string);
	begin
		if index >= count then
			raise Exception.Create('Запрошен {}-й кадр {}, но там всего {}.'.Format([index, name, count]));
	end;

	class function Image.AllocateData(const spec: ImageSpec; const name: string): pointer;
	begin
		ValidateSize(spec, name);
		result := GetMem(ImageFormatHelper.Info[spec.format].pixelSize * spec.w * spec.h * spec.frames);
	end;

	function Image.PixelPtr(x, y, f: SizeUint): pointer;
	var
		ofs: SizeUint;
	begin
		Assert((x < w) and (y < h) and (f < frames), 'x = {}/{}, y = {}/{}, frames = {}/{}'.Format([x, w, y, h, f, frames]));
		ofs := y * w + x;
		if f > 0 then ofs += w * h * f;
		result := data + ofs * format.pixelSize;
	end;

	procedure Image.DecodePixelNumber(pixel: SizeUint; out x, y, f: SizeUint; out ofs: pointer);
	begin
		f := pixel div (w * h);
		y := pixel mod (w * h) div w;
		x := pixel mod w;
		ofs := data + pixel * format.pixelSize;
	end;

	procedure Image.NextPixel(var pixel: SizeUint; var x, y, f: SizeUint);
	begin
		inc(pixel);
		inc(x);
		if x = w then
		begin
			x := 0; inc(y);
			if y = h then
			begin
				y := 0; inc(f);
			end;
		end;
	end;

	class function Image.ApplyGamma(const linear: float): float; begin result := sqrt(linear); end;
	class function Image.UnapplyGamma(const rgbcomponent: float): float; begin result := sqr(rgbcomponent); end;

	class function Image.ReadG(ofs: pointer; format: ImageFormat): float;
	begin
		case format of
			ImageFormat.G, ImageFormat.GA: result := p1x8(ofs)^[0] * Norm8;
			ImageFormat.RGB, ImageFormat.RGBA: result := RGB8ToGray(ofs);
			else {$ifdef Debug} raise Exception.Create('ReadG: {}'.Format([ord(format)])) {$else} result := 0 {$endif};
		end;
	end;

	class function Image.ReadGA(ofs: pointer; format: ImageFormat): Vec2;
	begin
		case format of
			ImageFormat.G: result := Vec2.Make(p1x8(ofs)^[0] * Norm8, 1.0);
			ImageFormat.GA: result := Vec2.Make(p2x8(ofs)^[0] * Norm8, p2x8(ofs)^[1] * Norm8);
			ImageFormat.RGB: result := Vec2.Make(RGB8ToGray(ofs), 1.0);
			ImageFormat.RGBA: result := Vec2.Make(RGB8ToGray(ofs), p4x8(ofs)^[3] * Norm8);
			else {$ifdef Debug} raise Exception.Create('ReadGA: {}'.Format([ord(format)])) {$else} result := Vec2.Make(0, 1) {$endif};
		end;
	end;

	class function Image.ReadRGB(ofs: pointer; format: ImageFormat): Vec3;
	begin
		case format of
			ImageFormat.G, ImageFormat.GA: result := Vec3.Make(p1x8(ofs)^[0] * Norm8);
			ImageFormat.RGB, ImageFormat.RGBA: result := Vec3.Make(p3x8(ofs)^[0] * Norm8, p3x8(ofs)^[1] * Norm8, p3x8(ofs)^[2] * Norm8);
			else {$ifdef Debug} raise Exception.Create('ReadRGB: {}'.Format([ord(format)])) {$else} result := Vec3.Make(0) {$endif};
		end;
	end;

	class function Image.ReadRGBA(ofs: pointer; format: ImageFormat): Vec4;
	begin
		case format of
			ImageFormat.G: result := Vec4.Make31(p1x8(ofs)^[0] * Norm8, 1.0);
			ImageFormat.GA: result := Vec4.Make31(p2x8(ofs)^[0] * Norm8, p2x8(ofs)^[1] * Norm8);
			ImageFormat.RGB: result := Vec4.Make(p3x8(ofs)^[0] * Norm8, p3x8(ofs)^[1] * Norm8, p3x8(ofs)^[2] * Norm8, 1.0);
			ImageFormat.RGBA: result := Vec4.Make(p4x8(ofs)^[0] * Norm8, p4x8(ofs)^[1] * Norm8, p4x8(ofs)^[2] * Norm8, p4x8(ofs)^[3] * Norm8);
			else {$ifdef Debug} raise Exception.Create('ReadRGBA: {}'.Format([ord(format)])) {$else} result := Vec4.Make(0, 0, 0, 1) {$endif};
		end;
	end;

	class function Image.ReadLinearRGBA(ofs: pointer; format: ImageFormat): Vec4;
	begin
		case format of
			ImageFormat.G: result := Vec4.Make31(UnapplyGamma(p1x8(ofs)^[0] * Norm8), 1.0);
			ImageFormat.GA: result := Vec4.Make31(UnapplyGamma(p2x8(ofs)^[0] * Norm8), p2x8(ofs)^[1] * Norm8);
			ImageFormat.RGB: result := Vec4.Make(UnapplyGamma(p3x8(ofs)^[0] * Norm8), UnapplyGamma(p3x8(ofs)^[1] * Norm8), UnapplyGamma(p3x8(ofs)^[2] * Norm8), 1.0);
			ImageFormat.RGBA: result := Vec4.Make(UnapplyGamma(p4x8(ofs)^[0] * Norm8), UnapplyGamma(p4x8(ofs)^[1] * Norm8), UnapplyGamma(p4x8(ofs)^[2] * Norm8), p4x8(ofs)^[3] * Norm8);
			else {$ifdef Debug} raise Exception.Create('ReadLinearRGBA: {}'.Format([ord(format)])) {$else} result := Vec4.Make(0, 0, 0, 1) {$endif};
		end;
	end;

	class procedure Image.WriteG(ofs: pointer; format: ImageFormat; const px: float);
	begin
		case format of
			ImageFormat.G: p1x8(ofs)^[0] := Denorm8(px);
			ImageFormat.GA: begin p2x8(ofs)^[0] := Denorm8(px); p2x8(ofs)^[1] := High(uint8); end;
			ImageFormat.RGB: begin p3x8(ofs)^[0] := Denorm8(px); p3x8(ofs)^[1] := p3x8(ofs)^[0]; p3x8(ofs)^[2] := p3x8(ofs)^[0]; end;
			ImageFormat.RGBA: begin p4x8(ofs)^[0] := Denorm8(px); p4x8(ofs)^[1] := p4x8(ofs)^[0]; p4x8(ofs)^[2] := p4x8(ofs)^[0]; p4x8(ofs)^[3] := High(uint8); end;
			else {$ifdef Debug} raise Exception.Create('WriteLinearG: {}'.Format([ord(format)])) {$endif};
		end;
	end;

	class procedure Image.WriteGA(ofs: pointer; format: ImageFormat; const px: Vec2);
	begin
		case format of
			ImageFormat.G: p1x8(ofs)^[0] := Denorm8(px.data[0]);
			ImageFormat.GA: begin p2x8(ofs)^[0] := Denorm8(px.data[0]); p2x8(ofs)^[1] := Denorm8(px.data[1]); end;
			ImageFormat.RGB: begin p3x8(ofs)^[0] := Denorm8(px.data[0]); p3x8(ofs)^[1] := p3x8(ofs)^[0]; p3x8(ofs)^[2] := p3x8(ofs)^[0]; end;
			ImageFormat.RGBA: begin p4x8(ofs)^[0] := Denorm8(px.data[0]); p4x8(ofs)^[1] := p4x8(ofs)^[0]; p4x8(ofs)^[2] := p4x8(ofs)^[0]; p4x8(ofs)^[3] := Denorm8(px.data[1]); end;
			else {$ifdef Debug} raise Exception.Create('WriteLinearGA: {}'.Format([ord(format)])) {$endif};
		end;
	end;

	class procedure Image.WriteRGB(ofs: pointer; format: ImageFormat; const px: Vec3);
	begin
		case format of
			ImageFormat.G: p1x8(ofs)^[0] := Denorm8(RGBToGray(px.data[0], px.data[1], px.data[2]));
			ImageFormat.GA: begin p2x8(ofs)^[0] := Denorm8(RGBToGray(px.data[0], px.data[1], px.data[2])); p2x8(ofs)^[1] := High(uint8); end;
			ImageFormat.RGB: begin p3x8(ofs)^[0] := Denorm8(px.data[0]); p3x8(ofs)^[1] := Denorm8(px.data[1]); p3x8(ofs)^[2] := Denorm8(px.data[2]); end;
			ImageFormat.RGBA: begin p3x8(ofs)^[0] := Denorm8(px.data[0]); p3x8(ofs)^[1] := Denorm8(px.data[1]); p3x8(ofs)^[2] := Denorm8(px.data[2]); p4x8(ofs)^[3] := High(uint8); end;
			else {$ifdef Debug} raise Exception.Create('WriteLinearRGB: {}'.Format([ord(format)])) {$endif};
		end;
	end;

	class procedure Image.WriteRGBA(ofs: pointer; format: ImageFormat; const px: Vec4);
	begin
		case format of
			ImageFormat.G: p1x8(ofs)^[0] := Denorm8(RGBToGray(px.data[0], px.data[1], px.data[2]));
			ImageFormat.GA: begin p2x8(ofs)^[0] := Denorm8(RGBToGray(px.data[0], px.data[1], px.data[2])); p2x8(ofs)^[1] := Denorm8(px.data[3]); end;
			ImageFormat.RGB: begin p3x8(ofs)^[0] := Denorm8(px.data[0]); p3x8(ofs)^[1] := Denorm8(px.data[1]); p3x8(ofs)^[2] := Denorm8(px.data[2]); end;
			ImageFormat.RGBA: begin p4x8(ofs)^[0] := Denorm8(px.data[0]); p4x8(ofs)^[1] := Denorm8(px.data[1]); p4x8(ofs)^[2] := Denorm8(px.data[2]); p4x8(ofs)^[3] := Denorm8(px.data[3]); end;
			else {$ifdef Debug} raise Exception.Create('WriteLinearRGBA: {}'.Format([ord(format)])) {$endif};
		end;
	end;

	class procedure Image.WriteLinearRGBA(ofs: pointer; format: ImageFormat; const px: Vec4);
	begin
		case format of
			ImageFormat.G: p1x8(ofs)^[0] := Denorm8(ApplyGamma(LinearRGBToLinearGray(px.data[0], px.data[1], px.data[2])));
			ImageFormat.GA: begin p2x8(ofs)^[0] := Denorm8(ApplyGamma(LinearRGBToLinearGray(px.data[0], px.data[1], px.data[2]))); p2x8(ofs)^[1] := Denorm8(px.data[3]); end;
			ImageFormat.RGB: begin p3x8(ofs)^[0] := Denorm8(ApplyGamma(px.data[0])); p3x8(ofs)^[1] := Denorm8(ApplyGamma(px.data[1])); p3x8(ofs)^[2] := Denorm8(ApplyGamma(px.data[2])); end;
			ImageFormat.RGBA: begin p4x8(ofs)^[0] := Denorm8(ApplyGamma(px.data[0])); p4x8(ofs)^[1] := Denorm8(ApplyGamma(px.data[1])); p4x8(ofs)^[2] := Denorm8(ApplyGamma(px.data[2])); p4x8(ofs)^[3] := Denorm8(px.data[3]); end;
			else {$ifdef Debug} raise Exception.Create('WriteLinearRGBA: {}'.Format([ord(format)])) {$endif};
		end;
	end;

	class function Image.RGB8ToGray(ofs: pointer): float;
	begin
		result := RGBToGray(p3x8(ofs)^[0] * Norm8, p3x8(ofs)^[1] * Norm8, p3x8(ofs)^[2] * Norm8);
	end;

	class function Image.RGBToGray(const r, g, b: float): float;
	begin
		result := ApplyGamma(LinearRGBToLinearGray(UnapplyGamma(clamp(r, 0, 1)), UnapplyGamma(clamp(g, 0, 1)), UnapplyGamma(clamp(b, 0, 1))));
	end;

	class function Image.LinearRGBToLinearGray(const r, g, b: float): float;
	begin
		result := RToGrayK * r + GToGrayK * g + BToGrayK * b;
	end;

	class function Image.Denorm8(const value: float): uint8;
	begin
		result := round(clamp(value * High(result), 0, High(result)));
	end;

	class function Image.SizeToString(const spec: ImageSpec): string;
	begin
		result := ('{}x{}' + IfThen(spec.frames <> 1, 'x{}')).Format([VarRec.uint(spec.w), VarRec.uint(spec.h), VarRec.uint(spec.frames)]);
	end;

	class function Image.SpecToString(const spec: ImageSpec): string;
	begin
		result := ('{}' + IfThen(spec.format <> ImageFormat.RGB, '{}')).Format([SizeToString(spec), ImageFormatHelper.Info[spec.format].id]);
	end;

type
	ImageName = object
	{$define enum := ModeEnum} {$define items := Filename _ 0 _ Alias _ 1} enum_with_shortcuts
	var
		mode: ModeEnum;
		name, orig: string;
		frame, insertFrameNoAt: SizeInt;
		class function Parse(const data: string; forceMode: sint = -1): ImageName; static;
		class function &File(const fn: string): ImageName; static;
	end;

	class function ImageName.Parse(const data: string; forceMode: sint = -1): ImageName;
	var
		i, np, len: SizeInt;
		canBeAlias: boolean;
		nn: string absolute result.name;
	begin
		result.frame := -1;
		result.insertFrameNoAt := 0;
		i := 1;
		nn := data;
		result.orig := data;
		if (forceMode >= 0) and (forceMode <= ord(High(ModeEnum))) then
			result.mode := ModeEnum(forceMode)
		else
		begin
			canBeAlias := true;
			while i <= length(nn) do
				case nn[i] of
					'\', '/': begin canBeAlias := false; inc(i); end;
					'.': begin canBeAlias := false; inc(i); end;
					'%':
						begin
							if result.insertFrameNoAt = 0 then
							begin
								if nn.Prefixed('f%', i + 1) then len := length('%f%')
								else if nn.Prefixed('frame%', i + 1) then len := length('%frame')
								else len := 0;

								if len > 0 then
								begin
									result.insertFrameNoAt := i;
									delete(nn, i, len);
									continue;
								end;
							end;

							canBeAlias := false;
							inc(i);
						end;
					':':
						if nn.Consume(['0' .. '9'], i + 1, np) and (np > length(nn)) and TryParse(nn.AB(i + 1, np), result.frame) then
						else
						begin
							canBeAlias := false;
							inc(i);
						end;
					else inc(i);
				end;

			if canBeAlias then result.mode := Alias else result.mode := Filename;
		end;
	end;

	class function ImageName.&File(const fn: string): ImageName;
	begin
		result := Parse(fn, ord(Filename));
	end;

type
	pImageRegistry = ^ImageRegistry;
	ImageRegistry = object
	type
		pItem = ^Item;
		Item = object
			im: Image;
			refcount: SizeInt;
			ir: pImageRegistry;
			class function Create: pItem; static;
			function Ref: pItem;
			procedure Release(var item: pItem);
		end;

		procedure Init;
		procedure Done;
		procedure Add(item: pItem; const name: string);
		procedure Remove(item: pItem);
		function Find(const name: string; e: ThrowBehaviour = Throw): pItem;
	private
		lck: ThreadLock;
		items: array of record
			name: string;
			item: pItem;
		end;
		nItems: SizeInt;
		function UnlockedFind(const name: string): SizeInt;
	end;

	class function ImageRegistry.Item.Create: pItem;
	begin
		new(result);
		result^.im.Invalidate;
		result^.refcount := 1;
		result^.ir := nil;
	end;

	function ImageRegistry.Item.Ref: pItem;
	begin
		InterlockedIncrement(refcount);
		result := @self;
	end;

	procedure ImageRegistry.Item.Release(var item: pItem);
	begin
		if Assigned(item) then
		begin
			item := nil;
			if InterlockedDecrement(refcount) = 0 then
			begin
				im.Done;
				dispose(@self);
			end;
		end;
	end;

	procedure ImageRegistry.Init;
	begin
		lck.Init;
		Assert(nItems = 0);
	end;

	procedure ImageRegistry.Done;
	begin
		while nItems > 0 do
		begin
			items[nItems - 1].item^.Release(items[nItems - 1].item);
			dec(nItems);
		end;
		lck.Done;
	end;

	procedure ImageRegistry.Add(item: pItem; const name: string);
	begin
		lck.Enter;
		try
			if nItems >= length(items) then SetLength(items, Ary.GrowStgy(nItems + 1, length(items)));
			inc(nItems);
			items[nItems - 1].item := item^.Ref;
			items[nItems - 1].name := name;
		finally
			lck.Leave;
		end;
	end;

	procedure ImageRegistry.Remove(item: pItem);
	var
		i, na: SizeInt;
	begin
		lck.Enter;
		try
			for i := nItems - 1 downto 0 do
				if items[i].item = item then
				begin
					items[i].item^.Release(items[i].item);
					items[i] := items[nItems - 1];
					dec(nItems); if Ary.ShrinkStgy(nItems, length(items), SizeUint(na)) then SetLength(items, na);
				end;
		finally
			lck.Leave;
		end;
	end;

	function ImageRegistry.Find(const name: string; e: ThrowBehaviour = Throw): pItem;
	var
		i: SizeInt;
	begin
		lck.Enter;
		try
			i := UnlockedFind(name);
			if i >= 0 then
				result := items[i].item^.Ref
			else
				if e = Throw then
					raise Exception.Create('Картинка "{}" не найдена.'.format([name]))
				else
					result := nil;
		finally
			lck.Leave;
		end;
	end;

	function ImageRegistry.UnlockedFind(const name: string): SizeInt;
	var
		i: SizeInt;
	begin
		Assert(lck.AcquiredAssert);
		for i := 0 to nItems - 1 do
			if items[i].name = name then exit(i);
		result := -1;
	end;

type
	GenericOp = class;

	pGenericOpPayload = ^GenericOpPayload;
	GenericOpPayload = class(TObjectEx)
		op: GenericOp;
		oim: Image;
		destructor Destroy; override;
		procedure Start; virtual;
		procedure GeneratePart(threadIndex, startPixel, endPixel: SizeUint); virtual;
	end;

	GenericOp = class(TObjectEx)
	type
		InputStage = (Ready, Opening, Reading, QueuedForDecoding, Decoding, Completed);
		OutputStage = (Ready, Opening, QueuedForEncoding, Encoding, Writing, Completed);
		GlobalStage = (Ready, Reading, Processing, Saving, Done);
		Status = (Running, Cancelled, Failed, Completed);

		pTaskParam = ^TaskParam;
		TaskParam = record
			op: GenericOp;
			index: SizeInt;
		end;

		pInputRec = ^InputRec;
		InputRec = record
			name: ImageName;
			onlyRead: boolean;
			im: ImageRegistry.pItem;
			param: pTaskParam;
			stage: InputStage;
			task: pTask; // Opening, Reading — OnOpenAndStartReadingInputFile, Decoding — OnDecode
			f: &File;
			dataSize: size_t;
			data: pointer;
			decodingHalfTimeEstimation: seconds;
			startedAt: Ticks; // Decoding или Reading
		end;

		pOutputRec = ^OutputRec;
		OutputRec = record
			stage: OutputStage;
			fn: FilePath;
			f: &File;
			openTask, encodeTask: pTask;
			frame: uint;
			dataSize: size_t;
			data, dataBlock: pointer;
			param: pTaskParam;
			startedAt: Ticks;
		end;
	var
		ir: pImageRegistry;
		lock: ThreadLock;
		hey: ThreadCV;
		stage: GlobalStage;
		inputs: array of InputRec;
		running, decoding, encoding, pendingInputs, pendingOutputs, processing: SizeUint;
		undecoded, fileInputs, unencoded: array of SizeInt;
		stat: Status;
		err: string;
		ctrlC: Console.CtrlCCookie;
		lodeHook: MemoryIsland.HookCookie;
		pl: GenericOpPayload;
		oname: ImageName;
		fileOutputs: array of OutputRec;
		threads: array of record
			task: pTask;
			startPixel, endPixel: SizeUint;
			param: pTaskParam;
			progress: float;
		end;
		lodePreset: lodepng.Preset;

		constructor Create(var ir: ImageRegistry; pl: pGenericOpPayload);
		destructor Destroy; override;
		function AddInput(const name: ImageName; onlyRead: boolean = false): SizeInt;
		procedure Run;
		procedure Cancel(lock: boolean);
		procedure FailFromExcept;
		procedure Intercept(lock: boolean = true);
		procedure Wait;
		function Progress: float;
		procedure NoteProgress(threadIndex: SizeUint; const progress: float); // Должна вызываться из GenericOpPayload.GeneratePart.
		class function InfiniteProgressBar(const time, halfEst: seconds): float; static;
	private
		abortPosted: boolean;
		function CodingThreads: SizeUint;
		procedure Abort;
		procedure StartSubtask(lock: boolean);
		procedure EndSubtask(lock: boolean);
		procedure CleanupInputs;
		class procedure OnCtrlC(param: pointer); static;
		class procedure OnInterceptLodeRealloc(param: pointer); static;
		class procedure OnOpenAndStartReadingInputFile(param: pointer); static;
		procedure OpenAndStartReadingInputFile(var inp: InputRec);
		class procedure OnEndReadingInputFile(const status: &File.IOStatus; param: pointer); static;
		procedure EndReadingInputFile(const status: &File.IOStatus; var inp: InputRec);
		procedure MaybeStartDecoding;
		class procedure OnDecode(param: pointer); static;
		procedure Decode(var inp: InputRec);
		procedure DecodePNG(var inp: InputRec);
		procedure MaybeProceedToPayload(lock: boolean);
		procedure StartProcessing;
		class procedure OnProcessPart(param: pointer); static;
		procedure ProcessPart(threadIndex: SizeUint);
		procedure MaybeProceedToSavingOutputs;
		procedure StartSavingOutputs;
		class procedure OnStartSavingOutput(param: pointer); static;
		procedure StartSavingOutput(var outp: OutputRec);
		procedure MaybeStartEncoding;
		class procedure OnEncodeAndStartWritingOutputFile(param: pointer); static;
		procedure EncodeAndStartWritingOutputFile(var outp: OutputRec);
		procedure EncodePNG(var outp: OutputRec);
		class procedure OnEndWritingOutputFile(const status: &File.IOStatus; param: pointer); static;
		procedure EndWritingOutputFile(const status: &File.IOStatus; var outp: OutputRec);
		procedure MaybeComplete;
	end;

	destructor GenericOpPayload.Destroy;
	begin
		oim.Done;
		inherited Destroy;
	end;

	procedure GenericOpPayload.Start; begin end;
	procedure GenericOpPayload.GeneratePart(threadIndex, startPixel, endPixel: SizeUint); begin {$define args := threadIndex _ startPixel _ endPixel} unused_args end;

	constructor GenericOp.Create(var ir: ImageRegistry; pl: pGenericOpPayload);
	begin
		inherited Create;
		self.ir := @ir;
		if Assigned(pl) then
		begin
			self.pl := pl^; pl^ := nil;
		end;
		if not Assigned(self.pl) then self.pl := GenericOpPayload.Create;
		if Assigned(self.pl) then self.pl.op := self;
		lock.Init;
		hey.Init;
		lodePreset := lodepng.Good;
	end;

	destructor GenericOp.Destroy;
	var
		i: SizeInt;
	begin
		Cancel(true);
		Wait;

		ctrlC.Free(ctrlC);
		lodeHook.Free(lodeHook);

		CleanupInputs;
		for i := 0 to High(inputs) do inputs[i].task^.Close(inputs[i].task);
		for i := 0 to High(threads) do
		begin
			threads[i].task^.Close(threads[i].task);
			if Assigned(threads[i].param) then begin dispose(threads[i].param); threads[i].param := nil; end;
		end;
		for i := 0 to High(fileOutputs) do
		begin
			fileOutputs[i].openTask^.Close(fileOutputs[i].openTask);
			fileOutputs[i].encodeTask^.Close(fileOutputs[i].encodeTask);
			if fileOutputs[i].f.Valid then
			begin
				fileOutputs[i].f.Close;
				if (fileOutputs[i].stage <> OutputStage.Completed) then &File.Erase(fileOutputs[i].fn);
			end;
			fileOutputs[i].f.Close;
			FreeMem(fileOutputs[i].dataBlock);
			if Assigned(fileOutputs[i].param) then dispose(fileOutputs[i].param);
		end;
		pl.Free(pl);
		lock.Done;
		hey.Done;
		inherited Destroy;
	end;

	function GenericOp.AddInput(const name: ImageName; onlyRead: boolean = false): SizeInt;
	begin
		lock.Enter;
		try
			SetLength(inputs, length(inputs) + 1);
			inputs[High(inputs)].name := name;
			inputs[High(inputs)].onlyRead := onlyRead;
			if name.mode = name.Filename then SizeInt(Ary(fileInputs).Grow(TypeInfo(fileInputs))^) := High(inputs);
			result := High(inputs);
		finally
			lock.Leave;
		end;
	end;

	procedure GenericOp.Run;
	var
		i: SizeInt;
	begin
		try
			stage := GlobalStage.Reading;
			ctrlC := Con.RegisterCtrlCHandler(Con.CtrlCHandler(@GenericOp.OnCtrlC), self);
			lodeHook := lodepng.island.RegisterHook(0, lodepng.island.Hook(@GenericOp.OnInterceptLodeRealloc), self);

			for i := 0 to High(inputs) do
				case inputs[i].name.mode of
					ImageName.Alias: inputs[i].im := ir^.Find(inputs[i].name.name);
					ImageName.Filename:
						begin
							if not inputs[i].onlyRead then
								case FilePath(inputs[i].name.name).Extension.Lowercase of
									'png': ;
									else raise Exception.Create('{}: неизвестный формат.'.Format([inputs[i].name.name]));
								end;

							lock.Enter;
							try
								new(inputs[i].param);
								inputs[i].param^.op := self;
								inputs[i].param^.index := i;
								inputs[i].stage := InputStage.Opening;
								StartSubtask(false); inc(pendingInputs);
								try
									Assert(not Assigned(inputs[i].task));
									Task.Post(inputs[i].task, Task.Body(@GenericOp.OnOpenAndStartReadingInputFile), inputs[i].param);
								except
									EndSubtask(false); dec(pendingInputs); raise;
								end;
							finally
								lock.Leave;
							end;
						end;
					else Session.Impossible('mode = {}'.Format([ord(inputs[i].name.mode)]));
				end;

			MaybeProceedToPayload(true);
		except
			FailFromExcept;
		end;
	end;

	procedure GenericOp.Cancel(lock: boolean);
	begin
		if lock then self.lock.Enter else Assert(self.lock.AcquiredAssert);
		try
			if stat = Status.Running then
			begin
				stat := Status.Cancelled;
				Abort;
			end;
		finally
			if lock then self.lock.Leave;
		end;
	end;

	procedure GenericOp.FailFromExcept;
	begin
		lock.Enter;
		try
			if (Exception.Current is Interception) and (stat in [Status.Running, Status.Cancelled, Status.Completed]) then
				if stat <> Status.Completed then stat := Status.Cancelled else
			else
				if stat <> Status.Failed then
				begin
					stat := Status.Failed;
					err := Exception.Message;
				end;
			Abort;
		finally
			lock.Leave;
		end;
	end;

	procedure GenericOp.Intercept(lock: boolean = true);
	begin
		if lock then self.lock.Enter else Assert(self.lock.AcquiredAssert);
		try
			if stat <> Status.Running then raise Interception.Create('Операция прервана.');
		finally
			if lock then self.lock.Leave;
		end;
	end;

	procedure GenericOp.Wait;
	begin
		lock.Enter;
		try
			while (stat = Status.Running) or (running > 0) do hey.Wait(lock);
		finally
			lock.Leave;
		end;
	end;

	function GenericOp.Progress: float;
		function OnceRead: float;
		begin
			if Ary(fileInputs).Empty then result := 0 else result := 0.1;
		end;

		function SingleReadingProgress(const inp: InputRec): float;
		const
			WhenReading = 0.05;
			OnceRead = 0.1;
		begin
			case inp.stage of
				InputStage.Reading: result := WhenReading;
				InputStage.QueuedForDecoding: result := OnceRead;
				InputStage.Decoding: result := OnceRead + (1 - OnceRead) * InfiniteProgressBar(Ticks.Get - inp.startedAt, inp.decodingHalfTimeEstimation);
				InputStage.Completed: result := 1;
				else result := 0;
			end;
		end;

		function ReadingProgress: float;
		var
			i: SizeInt;
		begin
			result := 0; if Ary(fileInputs).Empty then exit;
			for i := 0 to High(fileInputs) do result += SingleReadingProgress(inputs[fileInputs[i]]);
			result := result / length(fileInputs);
		end;

		function ProcessingProgress: float;
		var
			i: SizeInt;
		begin
			result := 0; if Ary(threads).Empty then exit;
			for i := 0 to High(threads) do result += threads[i].progress;
			result /= length(threads);
		end;

		function OnceProcessed: float;
		begin
			if oname.mode = oname.Alias then result := 1 else result := 0.6;
		end;

		function SingleSavingProgress(const outp: OutputRec): float;
		const
			WhenQueued = 0.05;
			WhenWriting = 0.95;
		begin
			case outp.stage of
				OutputStage.QueuedForEncoding: result := WhenQueued;
				// Для оценки в идеале можно было бы выбрать N пикселей оригинальной картинки, попробовать их закодировать, засечь время и экстраполировать.
				OutputStage.Encoding: result := WhenQueued + (WhenWriting - WhenQueued) * InfiniteProgressBar(Ticks.Get - outp.startedAt, 1.0 * (1 + sqr(ord(lodePreset))));
				OutputStage.Writing: result := WhenWriting + (1.0 - WhenWriting) * InfiniteProgressBar(Ticks.Get - outp.startedAt, 1.0);
				OutputStage.Completed: result := 1.0;
				else result := 0;
			end;
		end;

		function SavingProgress: float;
		var
			i: SizeInt;
		begin
			result := 0; if Ary(fileOutputs).Empty then exit;
			for i := 0 to High(fileOutputs) do result += SingleSavingProgress(fileOutputs[i]);
			result /= length(fileOutputs);
		end;

	begin
		Assert(lock.AcquiredAssert);
		case stage of
			GlobalStage.Reading: result := OnceRead * ReadingProgress;
			GlobalStage.Processing: result := OnceRead + (OnceProcessed - OnceRead) * ProcessingProgress;
			GlobalStage.Saving: result := OnceProcessed + (0.99 - OnceProcessed) * SavingProgress;
			GlobalStage.Done: result := 1.0;
			else result := 0.0;
		end;
	end;

	procedure GenericOp.NoteProgress(threadIndex: SizeUint; const progress: float);
	begin
		Intercept;
		lock.Enter;
		threads[threadIndex].progress := progress;
		lock.Leave;
	end;

	class function GenericOp.InfiniteProgressBar(const time, halfEst: seconds): float;
	begin
		result := clamp(1.0 - pow(0.5, time / halfEst), 0.0, 1.0);
	end;

	function GenericOp.CodingThreads: SizeUint;
	begin
		result := CPUCount;
	end;

	procedure GenericOp.Abort;
	var
		i: SizeInt;
	begin
		Assert(lock.AcquiredAssert);
		hey.WakeAll;
		if abortPosted then exit;
		abortPosted := true;
		case stage of
			GlobalStage.Reading:
				for i := 0 to High(inputs) do
					if (inputs[i].stage = InputStage.Reading) and inputs[i].f.Valid then inputs[i].f.CancelPendingIO;
			GlobalStage.Saving:
				for i := 0 to High(fileOutputs) do
					if (fileOutputs[i].stage = OutputStage.Writing) and fileOutputs[i].f.Valid then fileOutputs[i].f.CancelPendingIO;
		end;
	end;

	procedure GenericOp.StartSubtask(lock: boolean);
	begin
		if lock then self.lock.Enter else Assert(self.lock.AcquiredAssert);
		inc(running);
		if lock then self.lock.Leave;
	end;

	procedure GenericOp.EndSubtask(lock: boolean);
	begin
		if lock then self.lock.Enter else Assert(self.lock.AcquiredAssert);
		try
			dec(running); if running = 0 then hey.WakeAll;
		finally
			if lock then self.lock.Leave;
		end;
	end;

	procedure GenericOp.CleanupInputs;
	var
		i: SizeInt;
	begin
		for i := 0 to High(inputs) do
		begin
			// task изредка дедлокается, мне лень разбираться, поэтому очищается в деструкторе отдельно
			inputs[i].im^.Release(inputs[i].im);
			inputs[i].f.Close;
			FreeMem(inputs[i].data);
			if Assigned(inputs[i].param) then begin dispose(inputs[i].param); inputs[i].param := nil; end;
		end;
	end;

	class procedure GenericOp.OnCtrlC(param: pointer);
	begin
		GenericOp(param).Cancel(true);
	end;

	class procedure GenericOp.OnInterceptLodeRealloc(param: pointer);
	begin
		GenericOp(param).Intercept;
	end;

	class procedure GenericOp.OnOpenAndStartReadingInputFile(param: pointer);
	begin
		pTaskParam(param)^.op.OpenAndStartReadingInputFile(pTaskParam(param)^.op.inputs[pTaskParam(param)^.index]);
	end;

	procedure GenericOp.OpenAndStartReadingInputFile(var inp: InputRec);
	begin
		try
			try
				Intercept;
				inp.f.Open(inp.name.name);
				if inp.f.Size > Image.MaxDataSize then raise Exception.Create('{}: слишком большой файл.'.Format([inp.f.Size]));
				inp.dataSize := inp.f.Size;
				inp.data := GetMem(inp.dataSize);
				lock.Enter;
				try
					inp.stage := InputStage.Reading;
					inp.startedAt := Ticks.Get;
					StartSubtask(false);
					try
						inp.f.Read(0, inp.data, inp.dataSize, &File.CompletionHandler(@GenericOp.OnEndReadingInputFile), inp.param);
					except
						EndSubtask(false); raise;
					end;
				finally
					lock.Leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	class procedure GenericOp.OnEndReadingInputFile(const status: &File.IOStatus; param: pointer);
	begin
		pTaskParam(param)^.op.EndReadingInputFile(status, pTaskParam(param)^.op.inputs[pTaskParam(param)^.index]);
	end;

	procedure GenericOp.EndReadingInputFile(const status: &File.IOStatus; var inp: InputRec);
	begin
		try
			try
				Intercept;
				inp.task^.Close(inp.task);
				lock.Enter;
				try
					if not status.OK then
						if status.Cancelled then
						begin
							Cancel(false);
							exit;
						end else
							raise status.ToException;
					inp.f.Close;
					if inp.onlyRead then
					begin
						inp.stage := InputStage.Completed;
						dec(pendingInputs);
						MaybeProceedToPayload(false);
					end else
					begin
						inp.decodingHalfTimeEstimation := clamp(100 * seconds(Ticks.Get - inp.startedAt), 0.1, 10.0);
						inp.stage := InputStage.QueuedForDecoding;
						SizeInt(Ary(undecoded).Grow(TypeInfo(undecoded))^) := @inp - pInputRec(inputs);
						MaybeStartDecoding;
					end;
				finally
					lock.Leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	procedure GenericOp.MaybeStartDecoding;
	var
		index: SizeInt;
	begin
		Assert(lock.AcquiredAssert);
		if not Ary(undecoded).Empty and (decoding < CodingThreads) then
		begin
			index := undecoded[High(undecoded)]; SetLength(undecoded, length(undecoded) - 1);
			StartSubtask(false); inc(decoding);
			try
				Assert(not Assigned(inputs[index].task));
				inputs[index].stage := InputStage.Decoding;
				inputs[index].startedAt := Ticks.Get;
				Task.Post(inputs[index].task, Task.Body(@GenericOp.OnDecode), inputs[index].param);
			except
				EndSubtask(false); dec(decoding); raise;
			end;
		end;
	end;

	class procedure GenericOp.OnDecode(param: pointer);
	begin
		pTaskParam(param)^.op.Decode(pTaskParam(param)^.op.inputs[pTaskParam(param)^.index]);
	end;

	procedure GenericOp.Decode(var inp: InputRec);
	begin
		try
			try
				Intercept;
				case FilePath(inp.name.name).Extension.Lowercase of
					'png': DecodePNG(inp);
					else raise Exception.Create('{}: неизвестный формат.'.Format([inp.name.name]));
				end;
				FreeMem(inp.data);

				lock.Enter;
				try
					inp.stage := InputStage.Completed;
					dec(decoding);
					dec(pendingInputs);
					MaybeStartDecoding;
					MaybeProceedToPayload(false);
				finally
					lock.Leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	procedure GenericOp.DecodePNG(var inp: InputRec);
	const
		PNGHeaderLen = 8;
		IHDR_offset = PNGHeaderLen;

		PLTE_BIT  = 1 shl 0;
		RGB_BIT   = 1 shl 1;
		ALPHA_BIT = 1 shl 2;
	type
		pChunk_t = ^chunk_t;
		Chunk_t = packed record
			chunklen   : uint32;
			chunktype  : packed array[0 .. 3] of char;
		end;

		IHDR_data = packed record
			asChunk    : Chunk_t;
			width      : uint32;
			height     : uint32;
			bitDepth   : uint8;
			colorType  : uint8;
			compression: uint8;
			filter     : uint8;
			interlace  : uint8;
		end;

		function sum(a, b: size_t): size_t;
		begin
			result := a + b;
			if result < a then raise Exception.Create('{}: данные повреждены.'.Format([inp.name.name]));
		end;

		function has_tRNS(data: pChunk_t; size: size_t): boolean;
		var
			len: size_t;
		begin
			result := false;
			repeat
				len := sum(BEtoN(data^.chunklen), sizeof(Chunk_t) + {CRC} sizeof(uint32));
				if sum(len, sizeof(Chunk_t)) > size then exit;

				pointer(data) += len;
				size -= len;
				if data^.chunktype = 'tRNS' then exit(true)
				else if data^.chunktype = 'PLTE' then // продолжить
				else exit(false);
			until false;
		end;

		procedure setup(out fmt: ImageFormat; out lct: cint; nfmt: ImageFormat; nlct: cint);
		begin
			fmt := nfmt;
			lct := nlct;
		end;

	var
		ihdr: ^IHDR_data;
		w, h, lcode: cuint;
		fmt: ImageFormat;
		lct: cint;
		decodedData, decodedBlock: pointer;

	begin
		if inp.dataSize < IHDR_offset + sizeof(((@ihdr)^^)) then raise Exception.Create('Файл повреждён.'.Format([inp.dataSize]));
		ihdr := inp.data + IHDR_offset;
		if ihdr^.asChunk.chunktype <> 'IHDR' then raise Exception.Create('Неверный заголовок PNG.');

		if RGB_BIT and ihdr^.colorType <> 0 then
			if (ALPHA_BIT and ihdr^.colorType <> 0) or ((ihdr^.colorType and PLTE_BIT <> 0) and has_tRNS(@ihdr^.asChunk, inp.dataSize - IHDR_offset)) then
				setup(fmt, lct, ImageFormat.RGBA, lodepng.CT_RGBA)
			else
				setup(fmt, lct, ImageFormat.RGB, lodepng.CT_RGB)
		else
			if (ALPHA_BIT and ihdr^.colorType <> 0) then
				setup(fmt, lct, ImageFormat.GA, lodepng.CT_GREY_ALPHA)
			else
				setup(fmt, lct, ImageFormat.G, lodepng.CT_GREY);

		try
			lcode := lodepng.decode_memory(decodedData, w, h, inp.data, inp.dataSize, lct, bitsizeof(uint8), lodepng.GlobalAllocator);
		except
			lodepng.island.Purge(ThreadID);
			raise;
		end;
		if lcode <> 0 then raise Exception.Create(lodepng.ErrorMessage(lcode));
		lodepng.island.TakeAway(decodedData, decodedBlock);

		try
			inp.im := ImageRegistry.Item.Create;
			inp.im^.im.Init(inp.name.name, decodedData, ImageSpec.Make(w, h, 1, fmt), decodedBlock);
		except
			FreeMem(decodedBlock);
			raise;
		end;
	end;

	procedure GenericOp.MaybeProceedToPayload(lock: boolean);
	begin
		if lock then self.lock.Enter else Assert(self.lock.AcquiredAssert);
		try
			if (stage = GlobalStage.Reading) and (pendingInputs = 0) then
			begin
				stage := GlobalStage.Processing;
				hey.WakeAll;
				StartProcessing;
			end;
		finally
			if lock then self.lock.Leave;
		end;
	end;

	procedure GenericOp.StartProcessing;
	var
		partSize, pixels: SizeUint;
		i: SizeInt;
	begin
		Assert(lock.AcquiredAssert);
		lock.Leave;
		try
			pl.Start;
		finally
			lock.Enter;
		end;
		Intercept(false);
		if Assigned(pl.oim.data) then
		begin
			pixels := SizeUint(pl.oim.w) * pl.oim.h * pl.oim.frames;
			partSize := pixels div CodingThreads;
			partSize := partSize - partSize mod PageSize;
			partSize := max(partSize, PageSize);
			SetLength(threads, max(1, pixels div partSize));
			for i := 0 to High(threads) do
			begin
				new(threads[i].param);
				threads[i].param^.op := self;
				threads[i].param^.index := i;
				threads[i].startPixel := SizeUint(i) * partSize;
				if i < High(threads) then threads[i].endPixel := SizeUint(i + 1) * partSize else threads[i].endPixel := pixels;
				StartSubtask(false); inc(processing);
				try
					Task.Post(threads[i].task, Task.Body(@GenericOp.OnProcessPart), threads[i].param);
				except
					dec(processing); EndSubtask(false); raise;
				end;
			end;
		end;
		MaybeProceedToSavingOutputs;
	end;

	class procedure GenericOp.OnProcessPart(param: pointer);
	begin
		pTaskParam(param)^.op.ProcessPart(pTaskParam(param)^.index);
	end;

	procedure GenericOp.ProcessPart(threadIndex: SizeUint);
	begin
		try
			try
				Intercept;
				pl.GeneratePart(threadIndex, threads[threadIndex].startPixel, threads[threadIndex].endPixel);
				lock.Enter;
				try
					dec(processing);
					MaybeProceedToSavingOutputs;
				finally
					lock.leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	procedure GenericOp.MaybeProceedToSavingOutputs;
	begin
		Assert(lock.AcquiredAssert);
		Assert(stage = GlobalStage.Processing);
		if processing = 0 then
		begin
			stage := GlobalStage.Saving;
			hey.WakeAll;
			CleanupInputs;
			StartSavingOutputs;
			MaybeComplete;
		end;
	end;

	procedure GenericOp.StartSavingOutputs;
		procedure SaveFrame(frame: SizeInt);
		var
			im: ImageRegistry.pItem;
			name: string;
			fo: pOutputRec;
		begin
			name := oname.name;
			if (frame < 0) and (pl.oim.frames > 1) then
				case oname.mode of
					ImageName.Alias:
						begin
							im := ImageRegistry.Item.Create;
							try
								im^.im := pl.oim; pl.oim.Invalidate;
								ir^.Add(im, name);
							finally
								im^.Release(im);
							end;
						end;
					else raise Exception.Create('Нельзя вывести {} кадр{/а/ов} в {}. Используйте псевдоним или %f%.'.Format([pl.oim.frames, name]));
				end
			else
			begin
				if frame < 0 then frame := 0;
				Image.ValidateFrame(frame, pl.oim.frames, name);

				if oname.insertFrameNoAt > 0 then
					name := name.Stuffed(oname.insertFrameNoAt, 0, '{}'.Format([frame]))
				else if pl.oim.frames > 1 then raise Exception.Create('{} содержит {} кадр{/а/ов}, используйте %f%.'.Format([name, pl.oim.frames]));

				case oname.mode of
					ImageName.Alias:
						begin
							im := ImageRegistry.Item.Create;
							try
								im^.im.Init(name, nil, ImageSpec.Make(pl.oim.w, pl.oim.h, 1, pl.oim.format));
								ir^.Add(im, name);
							finally
								im^.Release(im);
							end;
						end;
					ImageName.Filename:
						begin
							case FilePath(name).Extension.Lowercase of
								'png': ;
								else raise Exception.Create('{}: неизвестный формат.'.Format([name]));
							end;

							SetLength(fileOutputs, length(fileOutputs) + 1);
							fo := @fileOutputs[High(fileOutputs)];
							fo^.fn := name;
							fo^.frame := frame;
							new(fo^.param);
							fo^.param^.op := self;
							fo^.param^.index := High(fileOutputs);
						end;
				end;
			end;
		end;
	var
		i: SizeInt;
	begin
		Assert(lock.AcquiredAssert);
		Assert(stage = GlobalStage.Saving);
		if not Assigned(pl.oim.data) then exit;

		if oname.name = '' then raise Exception.Create('Не задан выходной файл.');
		if oname.insertFrameNoAt > 0 then
			for i := 0 to pl.oim.frames - 1 do
				SaveFrame(i)
		else
			SaveFrame(oname.frame);

		for i := 0 to High(fileOutputs) do
		begin
			StartSubtask(false); inc(pendingOutputs);
			try
				fileOutputs[i].stage := OutputStage.Opening;
				Task.Post(fileOutputs[i].openTask, Task.Body(@GenericOp.OnStartSavingOutput), fileOutputs[i].param);
			except
				dec(pendingOutputs); EndSubtask(false); raise;
			end;
		end;
		MaybeComplete;
	end;

	class procedure GenericOp.OnStartSavingOutput(param: pointer);
	begin
		pTaskParam(param)^.op.StartSavingOutput(pTaskParam(param)^.op.fileOutputs[pTaskParam(param)^.index]);
	end;

	procedure GenericOp.StartSavingOutput(var outp: OutputRec);
	begin
		try
			try
				Intercept;
				outp.f.Open(outp.fn, [outp.f.Writeable]);
				lock.Enter;
				try
					outp.stage := OutputStage.QueuedForEncoding;
					SizeInt(Ary(unencoded).Grow(TypeInfo(unencoded))^) := @outp - pOutputRec(fileOutputs);
					MaybeStartEncoding;
				finally
					lock.Leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	procedure GenericOp.MaybeStartEncoding;
	var
		index: SizeInt;
	begin
		Assert(lock.AcquiredAssert);
		if not Ary(unencoded).Empty and (encoding < CodingThreads) then
		begin
			index := unencoded[High(unencoded)]; SetLength(unencoded, length(unencoded) - 1);
			StartSubtask(false); inc(encoding);
			try
				fileOutputs[index].stage := OutputStage.Encoding;
				fileOutputs[index].startedAt := Ticks.Get;
				Task.Post(fileOutputs[index].encodeTask, Task.Body(@GenericOp.OnEncodeAndStartWritingOutputFile), fileOutputs[index].param);
			except
				EndSubtask(false); dec(encoding); raise;
			end;
		end;
	end;

	class procedure GenericOp.OnEncodeAndStartWritingOutputFile(param: pointer);
	begin
		pTaskParam(param)^.op.EncodeAndStartWritingOutputFile(pTaskParam(param)^.op.fileOutputs[pTaskParam(param)^.index]);
	end;

	procedure GenericOp.EncodeAndStartWritingOutputFile(var outp: OutputRec);
	begin
		try
			try
				Intercept;
				case FilePath(outp.fn).Extension.Lowercase of
					'png': EncodePNG(outp);
					else raise Exception.Create('{}: неизвестный формат.'.Format([outp.fn]));
				end;

				lock.Enter;
				try
					outp.stage := OutputStage.Writing;
					outp.startedAt := Ticks.Get;
					dec(encoding);
					MaybeStartEncoding;
					StartSubtask(false);
					try
						outp.f.Write(0, outp.data, outp.dataSize, &File.CompletionHandler(@GenericOp.OnEndWritingOutputFile), outp.param);
					except
						EndSubtask(false); raise;
					end;
				finally
					lock.Leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	procedure GenericOp.EncodePNG(var outp: OutputRec);
	var
		lct, lcode: cuint;
		encodedData, encodedBlock: pointer;
		encodedSize: csize_t;
	begin
		case pl.oim.format of
			ImageFormat.G: lct := lodepng.CT_GREY;
			ImageFormat.GA: lct := lodepng.CT_GREY_ALPHA;
			ImageFormat.RGB: lct := lodepng.CT_RGB;
			ImageFormat.RGBA: lct := lodepng.CT_RGBA;
			else raise Exception.Create('Сохранение {} в PNG не поддерживается.'.Format([pl.oim.format.id]));
		end;

		try
			lcode := lodepng.encode_memory(encodedData, encodedSize,
				pl.oim.data + pl.oim.format.pixelSize * pl.oim.w * pl.oim.h * outp.frame,
				pl.oim.w, pl.oim.h, lct, bitsizeof(uint8), lodepng.Presets[lodepng.Good], lodepng.GlobalAllocator);
		except
			lodepng.island.Purge(ThreadID);
			raise;
		end;
		if lcode <> 0 then raise Exception.Create(lodepng.ErrorMessage(lcode));
		lodepng.island.TakeAway(encodedData, encodedBlock);
		outp.data := encodedData;
		outp.dataBlock := encodedBlock;
		outp.dataSize := encodedSize;
	end;

	class procedure GenericOp.OnEndWritingOutputFile(const status: &File.IOStatus; param: pointer);
	begin
		pTaskParam(param)^.op.EndWritingOutputFile(status, pTaskParam(param)^.op.fileOutputs[pTaskParam(param)^.index]);
	end;

	procedure GenericOp.EndWritingOutputFile(const status: &File.IOStatus; var outp: OutputRec);
	begin
		try
			try
				Intercept;
				lock.Enter;
				try
					if not status.OK then
						if status.Cancelled then
						begin
							Cancel(false);
							exit;
						end else
							raise status.ToException;
					outp.f.Close;
					outp.stage := OutputStage.Completed;
					dec(pendingOutputs);
					MaybeComplete;
				finally
					lock.Leave;
				end;
			except
				FailFromExcept;
			end;
		finally
			EndSubtask(true);
		end;
	end;

	procedure GenericOp.MaybeComplete;
	begin
		Assert(lock.AcquiredAssert);
		if pendingOutputs = 0 then
		begin
			stage := GlobalStage.Done;
			stat := Status.Completed;
		end;
	end;

type
	MixOperation = class(GenericOpPayload)
		inps: array of record
			weight: float;
		end;
		iwsum: float;
		procedure Start; override;
		procedure GeneratePart(threadIndex, startPixel, endPixel: SizeUint); override;
		class procedure ChooseOutputSpec(op: GenericOp; out spec: ImageSpec); static;
	const
		FormatEstimation: array[ImageFormat] of uint = (0, 1, 2, 3);
		ReportPeriodPixels = 16384;
	end;

	procedure MixOperation.Start;
	var
		i: SizeInt;
		rspec: ImageSpec;
		wsum: float;
	begin
		if length(op.inputs) <= 1 then
			raise Exception.Create('Недостаточно входных файлов для смешивания ({}).'.Format([length(op.inputs)]));
		if length(inps) = 0 then
		begin
			SetLength(inps, length(op.inputs));
			for i := 0 to High(inps) do inps[i].weight := 1.0;
		end;
		if length(op.inputs) <> length(inps) then
			raise Exception.Create('Неверно заданы веса для смешивания.');

		wsum := inps[0].weight;
		for i := 1 to High(inps) do wsum += inps[i].weight;
		for i := 0 to High(inps) do inps[i].weight /= wsum;

		ChooseOutputSpec(op, rspec);
		oim.Init(op.oname.name, nil, rspec);
	end;

	class procedure MixOperation.ChooseOutputSpec(op: GenericOp; out spec: ImageSpec);
	var
		refim, nim: pImage;
		fmt: ImageFormat;
		w, h: SizeUint;
		i: SizeInt;
	begin
		if length(op.inputs) = 0 then raise Exception.Create('Нет входных файлов.');
		refim := @op.inputs[0].im^.im;
		fmt := refim^.format;
		for i := 1 to High(op.inputs) do
		begin
			nim := @op.inputs[i].im^.im;
			if (refim^.w <> nim^.w) or (refim^.h <> nim^.h) then
				raise Exception.Create('Размеры изображений {} и {} не совпадают: {}x{} <-> {}x{}.'.Format([op.inputs[0].name.orig, op.inputs[i].name.orig,
					refim^.w, refim^.h, nim^.w, nim^.h]));
			if FormatEstimation[nim^.format] > FormatEstimation[fmt] then fmt := op.inputs[i].im^.im.format;
		end;
		w := refim^.w;
		h := refim^.h;
		spec := ImageSpec.Make(w, h, 1, fmt);
	end;

	procedure MixOperation.GeneratePart(threadIndex, startPixel, endPixel: SizeUint);
	var
		pixel, x, y, f, opsz: SizeUint;
		ofs: pointer;
		linps: array of record
			ofs: pointer;
			fmt: ImageFormat;
			pixelSize: SizeUint;
		end;
		i: SizeInt;
		sum: Vec4;
	begin
		oim.DecodePixelNumber(startPixel, x, y, f, ofs);
		pixel := startPixel;
		opsz := oim.format.pixelSize;
		SetLength(linps, length(inps));
		for i := 0 to High(linps) do
		begin
			linps[i].fmt := op.inputs[i].im^.im.format;
			linps[i].pixelSize := linps[i].fmt.pixelSize;
			linps[i].ofs := op.inputs[i].im^.im.data + linps[i].pixelSize * startPixel;
		end;

		while pixel < endPixel do
		begin
			sum := inps[0].weight * Image.ReadLinearRGBA(linps[0].ofs, linps[0].fmt);
			for i := 1 to High(inps) do
				sum += inps[i].weight * Image.ReadLinearRGBA(linps[i].ofs, linps[i].fmt);
			Image.WriteLinearRGBA(ofs, oim.format, sum);
			inc(pixel);
			ofs += opsz;
			for i := 0 to High(linps) do linps[i].ofs += linps[i].pixelSize;
			if pixel mod ReportPeriodPixels = 0 then op.NoteProgress(threadIndex, (pixel - startPixel) / (endPixel - startPixel));
		end;
	end;

type
	TweenOperation = class(GenericOpPayload)
		inps: array of record
			extraFrames: SizeUint;
		end;
		procedure Start; override;
		procedure GeneratePart(threadIndex, startPixel, endPixel: SizeUint); override;
		class procedure Tween(n: SizeUint; ap: pointer; af: ImageFormat; bp: pointer; bf: ImageFormat; outp: pointer; outf: ImageFormat; const w: float; op: GenericOpPayload; threadIndex: SizeUint; const progressBase, progressK: float); static;
		class procedure Blit(n: SizeUint; inp: pointer; inf: ImageFormat; outp: pointer; outf: ImageFormat; op: GenericOpPayload; threadIndex: SizeUint; const progressBase, progressK: float); static;
	end;

	procedure TweenOperation.Start;
	var
		spec: ImageSpec;
		frames: SizeUint;
		i: SizeInt;
	begin
		if length(op.inputs) <= 1 then
			raise Exception.Create('Недостаточно входных файлов для смешивания ({}).'.Format([length(op.inputs)]));
		if length(inps) + 1 <> length(op.inputs) then
			raise Exception.Create('Неверно заданы переходы: ожидается {}-1, получено {}.'.Format([length(op.inputs), length(inps)]));
		MixOperation.ChooseOutputSpec(op, spec);
		frames := 1;
		for i := 0 to High(inps) do frames += 1 + inps[i].extraFrames;
		oim.Init(op.oname.name, nil, ImageSpec.Make(spec.w, spec.h, frames, spec.format));
	end;

	procedure TweenOperation.GeneratePart(threadIndex, startPixel, endPixel: SizeUint);
	var
		pixel, x, y, f, endX, endY, endF, iframe, curA, curAFrame, batchPixels: SizeUint;
		aOfs, bOfs, outOfs, endOfs: pointer;
		progressBase, progressK: float;
		procedure NextA;
		begin
			inc(curAFrame);
			if curA = SizeUint(length(inps)) then
				Assert(curAFrame = 1)
			else if curAFrame > inps[curA].extraFrames then
			begin
				inc(curA);
				curAFrame := 0;
			end;
		end;
	begin
		oim.DecodePixelNumber(startPixel, x, y, f, outOfs);
		oim.DecodePixelNumber(endPixel, endX, endY, endF, endOfs);
		curA := 0; curAFrame := 0;
		for iframe := 1 to f do NextA;

		pixel := startPixel;
		while pixel < endPixel do
		begin
			batchPixels := oim.w * oim.h;
			if pixel = startPixel then
			begin
				batchPixels -= pixel mod batchPixels; // первая картинка может начаться с середины
				aOfs := op.inputs[curA].im^.im.PixelPtr(x, y, 0);
				if curAFrame > 0 then bOfs := op.inputs[curA + 1].im^.im.PixelPtr(x, y, 0) else bOfs := nil;
			end else
			begin
				aOfs := op.inputs[curA].im^.im.data;
				if curAFrame > 0 then bOfs := op.inputs[curA + 1].im^.im.data else bOfs := nil;
			end;

			batchPixels := min(batchPixels, endPixel - pixel); // последняя картинка может оборваться на середине
			progressBase := (pixel - startPixel) / (endPixel - startPixel);
			progressK := batchPixels / (endPixel - startPixel);

			if curAFrame = 0 then
				Blit(batchPixels, aOfs, op.inputs[curA].im^.im.format, outOfs, oim.format, self, threadIndex, progressBase, progressK)
			else
				Tween(batchPixels, aOfs, op.inputs[curA].im^.im.format, bOfs, op.inputs[curA + 1].im^.im.format, outOfs, oim.format, curAFrame / (1 + inps[curA].extraFrames),
					self, threadIndex, progressBase, progressK);

			pixel += batchPixels;
			outOfs += batchPixels * oim.format.pixelSize;
			NextA;
		end;
	end;

	class procedure TweenOperation.Tween(n: SizeUint; ap: pointer; af: ImageFormat; bp: pointer; bf: ImageFormat; outp: pointer; outf: ImageFormat;
		const w: float; op: GenericOpPayload; threadIndex: SizeUint; const progressBase, progressK: float);
	var
		apsz, bpsz, outpsz, startn: SizeUint;
		w2: float;

		procedure RGBShortcut(n: SizeUint; ap: pointer; apsz: SizeUint; bp: pointer; bpsz: SizeUint; outp: pointer; outpsz: SizeUint;
			const w, w2: float; const progressBase, progressK: float);
		begin
			while n > 0 do
			begin
				p4x8(outp)^[0] := round(Image.ApplyGamma(w2 * Image.UnapplyGamma(p4x8(ap)^[0]) + w * Image.UnapplyGamma(p4x8(bp)^[0])));
				p4x8(outp)^[1] := round(Image.ApplyGamma(w2 * Image.UnapplyGamma(p4x8(ap)^[1]) + w * Image.UnapplyGamma(p4x8(bp)^[1])));
				p4x8(outp)^[2] := round(Image.ApplyGamma(w2 * Image.UnapplyGamma(p4x8(ap)^[2]) + w * Image.UnapplyGamma(p4x8(bp)^[2])));
				ap += apsz; bp += bpsz; outp += outpsz; dec(n);
				if n mod MixOperation.ReportPeriodPixels = 0 then op.op.NoteProgress(threadIndex, progressBase + (1 - n/startn) * progressK);
			end;
		end;

		procedure RGBA_AlphaShortcut_Tween(n: SizeUint; ap: pointer; bp: pointer; outp: pointer;
			const w, w2: float; const progressBase, progressK: float);
		begin
			while n > 0 do
			begin
				p4x8(outp)^[3] := Image.Denorm8(w2 * p4x8(ap)^[3] * Image.Norm8 + w * Image.Denorm8(p4x8(bp)^[3]) * Image.Norm8);
				ap += sizeof(_4x8); bp += sizeof(_4x8); outp += sizeof(_4x8); dec(n);
				if n mod MixOperation.ReportPeriodPixels = 0 then op.op.NoteProgress(threadIndex, progressBase + (1 - n/startn) * progressK);
			end;
		end;

		procedure RGBA_AlphaShortcut_TweenTo1(n: SizeUint; ap: pointer; outp: pointer;
			const w, w2: float; const progressBase, progressK: float);
		begin
			while n > 0 do
			begin
				p4x8(outp)^[3] := Image.Denorm8(w2 * p4x8(ap)^[3] * Image.Norm8 + w);
				ap += sizeof(_4x8); outp += sizeof(_4x8); dec(n);
				if n mod MixOperation.ReportPeriodPixels = 0 then op.op.NoteProgress(threadIndex, progressBase + (1 - n/startn) * progressK);
			end;
		end;

		procedure RGBA_AlphaShortcut_Set1(n: SizeUint; outp: pointer; const progressBase, progressK: float);
		begin
			while n > 0 do
			begin
				p4x8(outp)^[3] := High(uint8);
				outp += sizeof(_4x8); dec(n);
				if n mod MixOperation.ReportPeriodPixels = 0 then op.op.NoteProgress(threadIndex, progressBase + (1 - n/startn) * progressK);
			end;
		end;

	begin
		apsz := ImageFormatHelper.Info[af].pixelSize; bpsz := ImageFormatHelper.Info[bf].pixelSize; outpsz := ImageFormatHelper.Info[outf].pixelSize; w2 := 1 - w; startn := n;
		if ([af, bf, outf] <= [ImageFormat.RGB, ImageFormat.RGBA]) then
		begin
			RGBShortcut(n, ap, apsz, bp, bpsz, outp, outpsz, w, w2, progressBase, progressK * IfThen(outf = ImageFormat.RGBA, 3/4, 1));
			if outf = ImageFormat.RGBA then
			begin
				if (af = ImageFormat.RGBA) and (bf = ImageFormat.RGBA) then RGBA_AlphaShortcut_Tween(n, ap, bp, outp, w, w2, progressBase + 3/4/progressK, 1/4*progressK)
				else if af = ImageFormat.RGBA then RGBA_AlphaShortcut_TweenTo1(n, ap, outp, w, w2, progressBase + 3/4*progressK, 1/4*progressK)
				else if bf = ImageFormat.RGBA then RGBA_AlphaShortcut_TweenTo1(n, bp, outp, w2, w, progressBase + 3/4*progressK, 1/4*progressK)
				else RGBA_AlphaShortcut_Set1(n, outp, progressBase + 3/4/progressK, 1/4*progressK);
			end;
			exit;
		end;

		while n > 0 do
		begin
			Image.WriteLinearRGBA(outp, outf, w2 * Image.ReadLinearRGBA(ap, af) + w * Image.ReadLinearRGBA(bp, bf));
			ap += apsz; bp += bpsz; outp += outpsz; dec(n);
			if n mod MixOperation.ReportPeriodPixels = 0 then op.op.NoteProgress(threadIndex, progressBase + (1 - n/startn) * progressK);
		end;
	end;

	class procedure TweenOperation.Blit(n: SizeUint; inp: pointer; inf: ImageFormat; outp: pointer; outf: ImageFormat; op: GenericOpPayload; threadIndex: SizeUint; const progressBase, progressK: float);
	var
		inpsz, outpsz, startn: SizeUint;
	begin
		inpsz := ImageFormatHelper.Info[inf].pixelSize; outpsz := ImageFormatHelper.Info[outf].pixelSize; startn := n;
		if inf = outf then
		begin
			Move(inp^, outp^, n * inpsz);
			exit;
		end;

		while n > 0 do
		begin
			Image.WriteLinearRGBA(outp, outf, Image.ReadLinearRGBA(inp, inf));
			inp += inpsz; outp += outpsz; dec(n);
			if n mod MixOperation.ReportPeriodPixels = 0 then op.op.NoteProgress(threadIndex, progressBase + (1 - n/startn) * progressK);
		end;
	end;

type
	lua = object
	const
		OK = 0; YIELDED = 1; ERRRUN = 2; ERRSYNTAX = 3; ERRMEM = 4; ERRGCMM = 5; ERRERR = 6;

		MULTRET = -1;
		FIRSTPSEUDOIDX = -1001000;
		REGISTRYINDEX = FIRSTPSEUDOIDX;
		RIDX_MAINTHREAD = 1; RIDX_GLOBALS = 2; RIDX_LAST = RIDX_GLOBALS;

		TNONE = -1; TNIL = 0; TBOOLEAN = 1; TLIGHTUSERDATA = 2; TNUMBER = 3; TSTRING = 4; TTABLE = 5; TFUNCTION = 6; TUSERDATA = 7; TTHREAD = 8;
		MASKCALL = 1 shl 0; MASKRET = 1 shl 1; MASKLINE = 1 shl 2; MASKCOUNT = 1 shl 3; MASKTAILCALL = 1 shl 4;

		IDSIZE = 60;

	type
		State = ^State_; State_ = record end;
		Number = type double; pNumber = ^Number;
		Integer = {$ifdef CPU32} cint {$else} clonglong {$endif};
		CFunction = function(L: State): cint; cdecl;
		KContext = PtrInt;
		KFunction = function(L: State; status: cint; ctx: KContext): cint; cdecl;
		ChunkReader = function(L: State; ud: pointer; out sz: csize_t): PChar; cdecl;
		ChunkWriter = function(L: State; p: pointer; sz: csize_t; ud: pointer): cint; cdecl;
		Alloc = function(ud: pointer; ptr: pointer; osize, nsize: csize_t): pointer; cdecl;

		Debug = record
			event: cint;
			name: PChar; // (n)
			namewhat: PChar; // (n) 'global', 'local', 'field', 'method'
			what: PChar; // (S) 'Lua', 'C', 'main', 'tail'
			source: PChar; // (S)
			currentline: cint; // (l)
			linedefined: cint; // (S)
			lastlinedefined: cint; // (S)
			nups: cuchar; // (u) number of upvalues
			nparams: cuchar; // (u) number of parameters
			isvararg: cschar; // (u)
			istailcall: cuchar; // (t)
			short_src: array[0 .. IDSIZE-1] of ansichar; // (S)
			&private: pointer;
		end;
		Hook = procedure(L: State; var ar: Debug); cdecl;

		// модификации: пользовательские функции для error и pcall
		Throwf = procedure; cdecl;
		PFunc = procedure(L: State; ud: pointer); cdecl;
		PCallf = function(f: PFunc; L: State; ud: pointer): cint; cdecl;

	class var
		lib: DLL;
		newstate: function(f: Alloc; ud: pointer): State; cdecl;
		close: procedure(L: State); cdecl;
		atpanic: function(L: State; panicf: CFunction): CFunction; cdecl;
		onthrow: procedure(L: State; throwf: Throwf; pcallf: PCallf); cdecl;
		sethook: function(L: State; func: Hook; mask, count: cint): cint; cdecl;

		gettop: function(L: State): cint; cdecl;
		settop: procedure(L: State; idx: cint); cdecl;
		pushvalue: procedure(L: State; idx: cint); cdecl;
		rotate: procedure(L: State; idx, n: cint); cdecl;
		copy: procedure(L: State; fromidx, toidx: cint); cdecl;
		absindex: function(L: State; idx: cint): cint; cdecl;

		isnumber: function(L: State; idx: cint): LongBool; cdecl;
		isinteger: function(L: State; idx: cint): LongBool; cdecl;
		isuserdata: function(L: State; idx: cint): LongBool; cdecl;
		iscfunction: function(L: State; idx: cint): LongBool; cdecl;
		&type: function(L: State; idx: cint): cint; cdecl;
		typename: function(L: State; tp: cint): PChar; cdecl;
		tonumberx: function(L: State; idx: cint; isnum: pcint): Number; cdecl;
		tointegerx: function(L: State; idx: cint; isnum: pcint): cint; cdecl;
		toboolean: function(L: State; idx: cint): LongBool; cdecl;
		tolstring: function(L: State; idx: cint; len: pcsize_t): PChar; cdecl;
		touserdata: function(L: State; idx: cint): pointer; cdecl;
		rawlen: function(L: State; idx: cint): csize_t; cdecl;
		rawequal: function(l: State; index1, index2: cint): LongBool; cdecl;

		pushnil: procedure(L: State); cdecl;
		pushnumber: procedure(L: State; n: Number); cdecl;
		pushinteger: procedure(L: State; n: cint); cdecl;
		pushlstring: procedure(L: State; s: PChar; ls: csize_t); cdecl;
		pushcclosure: procedure(L: State; fn: CFunction; n: cint); cdecl;
		pushboolean: procedure(L: State; b: LongBool); cdecl;
		pushlightuserdata: procedure(L: State; p: pointer); cdecl;
		createtable: procedure(l: State; narr, nrec: cint); cdecl;
		newuserdata: function(L: State; sz: csize_t): pointer; cdecl;

		getfield: procedure(l: State; index: cint; k: pChar); cdecl;
		rawget: procedure(L: State; idx: cint); cdecl;
		rawgeti: procedure(L: State; idx, n: cint); cdecl;
		getmetatable: function(L: State; objindex: cint): cint; cdecl;
		getuservalue: procedure(L: State; index: cint); cdecl;

		setfield: procedure(l: State; index: cint; k: pChar); cdecl;
		rawset: procedure(L: State; idx: cint); cdecl;
		rawseti: procedure(L: State; idx, n: cint); cdecl;
		setmetatable: function(L: State; objindex: cint): LongBool; cdecl;
		setuservalue: procedure(L: State; index: cint); cdecl;
		setupvalue: function(L: State; funcindex, n: cint): PChar; cdecl;

		callk: procedure(L: State; nargs, nresults: cint; ctx: KContext; k: KFunction); cdecl;
		pcallk: function(L: State; nargs, nresults, errfunc: cint; ctx: KContext; k: KFunction): cint; cdecl;
		error: function(L: State): cint; cdecl;

		load_: function(L: State; reader: Chunkreader; dt: pointer; chunkname, mode: PChar): cint; cdecl;

		class procedure Load(const fn: string); static;
		class procedure Unload; static;

		class procedure pop(L: State; n: cint = 1); static;
		class procedure remove(L: State; idx: cint); static;
		class procedure insert(L: State; idx: cint); static;
		class procedure replace(L: State; idx: cint); static;

		class function topchar(L: State; idx: cint): pChar; static;
		class function tostring(L: State; idx: cint): string; reintroduce; static;
		class function tonumber(L: State; idx: cint): Number; static;
		class function isfunction(L: State; idx: cint): boolean; static;
		class function istable(L: State; idx: cint): boolean; static;
		class function islightuserdata(L: State; idx: cint): boolean; static;
		class function isnil(L: State; idx: cint): boolean; static;
		class function isboolean(L: State; idx: cint): boolean; static;

		class procedure newtable(L: State); static;

		class procedure call(L: State; nargs, nresults: cint); static;
		class function pcall(L: State; nargs, nresults, errfunc: cint): cint; static;
		class function userparamptr(L: State): pPointer; static;

		class procedure pushstring(L: State; const s: string); static;
		class procedure pushcfunction(L: State; f: CFunction); static;
		class procedure loadstringE(L: State; const parts: array of string; const name: string); static;
		class function striplinenumber(const msg, chunkName: string): string; static;
		class procedure throw(L: State; const msg: string); noreturn; static;

		class function default_alloc(ud: pointer; ptr: pointer; osize, nsize: csize_t): pointer; cdecl; static;
		class procedure default_throw; cdecl; static;
		class function default_pcall(f: PFunc; L: State; ud: pointer): cint; cdecl; static;
		class function default_panic(L: State): cint; cdecl; static;
		class function adjustidx(index, pushed: cint): cint; static;

	strict private type
		InternalThrow = class end;

		loadstring_ReaderParam = record
			parts: pString;
			next, total: SizeInt;
		end;
		class function loadstring_reader(L: lua.State; ud: pointer; out sz: csize_t): pChar; cdecl; static;
	end;

	class procedure lua.Load(const fn: string);
	begin
		try
			lib.Load(fn).Prefix('lua_').Func('newstate', newstate).Func('close', close).Func('atpanic', atpanic).Func('onthrow', onthrow).Func('sethook', sethook)
				.Func('gettop', gettop).Func('settop', settop).Func('pushvalue', pushvalue).Func('rotate', rotate).Func('copy', copy).Func('absindex', absindex)
				.Func('isnumber', isnumber).Func('isinteger', isinteger).Func('isuserdata', isuserdata).Func('iscfunction', iscfunction)
				.Func('type', &type).Func('typename', typename)
				.Func('tonumberx', tonumberx).Func('tointegerx', tointegerx).Func('toboolean', toboolean).Func('tolstring', tolstring).Func('touserdata', touserdata)
				.Func('rawlen', rawlen).Func('rawequal', rawequal)
				.Func('pushnil', pushnil).Func('pushnumber', pushnumber).Func('pushinteger', pushinteger).Func('pushlstring', pushlstring).Func('pushcclosure', pushcclosure)
				.Func('pushboolean', pushboolean).Func('pushlightuserdata', pushlightuserdata).Func('createtable', createtable).Func('newuserdata', newuserdata)
				.Func('getfield', getfield).Func('rawget', rawget).Func('rawgeti', rawgeti).Func('getmetatable', getmetatable).Func('getuservalue', getuservalue)
				.Func('setfield', setfield).Func('rawset', rawset).Func('rawseti', rawseti).Func('setmetatable', setmetatable).Func('setuservalue', setuservalue).Func('setupvalue', setupvalue)
				.Func('callk', callk).Func('pcallk', pcallk).Func('error', error)
				.Func('load', load_);
		except
			Unload;
			raise;
		end;
	end;

	class procedure lua.Unload;
	begin
		lib.Unload;
	end;

	class procedure lua.pop(L: State; n: cint = 1);
	begin
		settop(L, -n - 1);
	end;

	class procedure lua.remove(L: State; idx: cint);
	begin
		rotate(L, idx, -1);
		settop(L, -2);
	end;

	class procedure lua.insert(L: State; idx: cint);
	begin
		rotate(L, idx, 1);
	end;

	class procedure lua.replace(L: State; idx: cint);
	begin
		copy(L, -1, idx);
		settop(L, -2);
	end;

	class function lua.topchar(L: State; idx: cint): pChar;
	begin
		result := tolstring(L, idx, nil);
	end;

	class function lua.tostring(L: State; idx: cint): string;
	var
		ch: pchar;
		len: csize_t;
	begin
		ch := tolstring(L, idx, @len); Assert(Assigned(ch));
		SetLength(result, len);
		Move(ch^, pointer(result)^, len * sizeof(char));
	end;

	class function lua.tonumber(L: State; idx: cint): Number;
	begin
		result := tonumberx(L, idx, nil);
	end;

{$define isimpl := begin result := &type(L, idx) = tag; end; {$undef tag}}
	class function lua.isfunction(L: State; idx: cint): boolean; {$define tag := TFUNCTION} isimpl
	class function lua.istable(L: State; idx: cint): boolean; {$define tag := TTABLE} isimpl
	class function lua.islightuserdata(L: State; idx: cint): boolean; {$define tag := TLIGHTUSERDATA} isimpl
	class function lua.isnil(L: State; idx: cint): boolean; static; {$define tag := TNIL} isimpl
	class function lua.isboolean(L: State; idx: cint): boolean; static; {$define tag := TBOOLEAN} isimpl
{$undef isimpl}

	class procedure lua.newtable(L: State);
	begin
		createtable(L, 0, 0);
	end;

	class procedure lua.call(L: State; nargs, nresults: cint);
	begin
		callk(L, nargs, nresults, 0, nil);
	end;

	class function lua.pcall(L: State; nargs, nresults, errfunc: cint): cint;
	begin
		result := pcallk(L, nargs, nresults, errfunc, 0, nil);
	end;

	class function lua.userparamptr(L: State): pPointer;
	begin
		result := pPointer(L) - 1;
	end;

	class procedure lua.pushstring(L: State; const s: string);
	begin
		pushlstring(L, pChar(s), length(s));
	end;

	class procedure lua.pushcfunction(L: State; f: CFunction);
	begin
		pushcclosure(L, f, 0);
	end;

	class function lua.loadstring_Reader(L: lua.State; ud: pointer; out sz: csize_t): PChar; cdecl;
	var
		r: ^loadstring_ReaderParam absolute ud;
		cur: SizeInt;
	begin {$define args := L} unused_args
		while r^.next < r^.total do
		begin
			cur := r^.next;
			inc(r^.next);
			if length(r^.parts[cur]) > 0 then
			begin
				sz := length(r^.parts[cur]) * sizeof(r^.parts[cur, 1]);
				exit(pointer(r^.parts[cur]));
			end;
		end;
		sz := 0; result := nil;
	end;

	class procedure lua.loadstringE(L: State; const parts: array of string; const name: string);
	var
		rr: loadstring_ReaderParam;
		msg: string;
	begin
		rr.parts := pString(parts);
		rr.next := 0;
		rr.total := length(parts);
		if load_(L, ChunkReader(@lua.loadstring_reader), @rr, pChar('=' + name), nil) <> OK then
		begin
			msg := tostring(L, -1);
			pop(L);
			raise Exception.Create(msg);
		end;
	end;

	class function lua.striplinenumber(const msg, chunkName: string): string;
	var
		p: SizeInt;
	begin
		if msg.Prefixed(chunkName) and msg.Consume([':'], length(chunkName) + 1, p) and msg.Consume(['0' .. '9'], p, p) and (msg.Consume([':'], p) > p) then
		begin
			// сейчас в GenerateByScriptOperation.ScriptState имя чанка (совпадающее с исходником) заканчивается переводом строки,
			// чтобы сообщение об ошибке выводилось как
			// исходник <EOL>
			// комментарий от Lua

			// так вот: если имя блока заканчивается таким переводом строки, убрать последнюю : вместе с пробелом, а то будет
			// исходник <EOL>
			// : комментарий от Lua          <- лишние двоеточик и пробел в начале
			if chunkName.ConsumeRev(StringHelper.AsciiSpaces, length(chunkName)) < length(chunkName) then
				msg.Consume([':', ' '], p, p);
			result := msg.Head(length(chunkName)) + msg.Tail(p);
		end else
			result := msg;
	end;

	class procedure lua.throw(L: State; const msg: string);
	begin
		pushstring(L, msg);
		error(L);
	end;

{$ifdef suppress_false_dfa_alarms} {$warn 5058 off} {$endif} // 'ptr' does not seem to be initialized
	class function lua.default_alloc(ud: pointer; ptr: pointer; osize, nsize: csize_t): pointer; cdecl;
	begin {$define args := ud _ osize} unused_args
		result := ReallocMem(ptr, nsize);
	end;
{$ifdef suppress_false_dfa_alarms} {$warn 5058 on} {$endif}

	class procedure lua.default_throw; cdecl;
	begin
		raise InternalThrow.Create;
	end;

	class function lua.default_pcall(f: PFunc; L: State; ud: pointer): cint; cdecl;
	begin
		try
			f(L, ud);
			result := 1;
		except
			on InternalThrow do result := 0;
		end;
	end;

	class function lua.default_panic(L: lua.State): cint; cdecl;
	begin {$define args := result} unused_args
		raise Exception.Create(tostring(L, -1));
	end;

	class function lua.adjustidx(index, pushed: cint): cint;
	begin
		if (index > lua.FIRSTPSEUDOIDX) and (index < 0) then result := index - pushed else result := index;
	end;

{$define all_script_vectors :=
	{$if defined(vec) or defined(vecn) or defined(pvec) or defined(vecMT) or defined(vecname) or
		defined(l_vecctr) or defined(pushvec) or defined(argvec) or defined(pushargvec)}
		{$error all_script_vectors would hide defines}
	{$endif}

	{$define vec := Vec2} {$define vecn := 2} {$define pvec := pVec2} {$define vecMT := Reg_Vec2MT} {$define vecname := 'vec2'}
	{$define l_vecctr := l_vec2} {$define pushvec := PushVec2} {$define argvec := ArgVec2} {$define pushargvec := PushArgVec2} vecf

	{$define vec := Vec3} {$define vecn := 3} {$define pvec := pVec3} {$define vecMT := Reg_Vec3MT} {$define vecname := 'vec3'}
	{$define l_vecctr := l_vec3} {$define pushvec := PushVec3} {$define argvec := ArgVec3} {$define pushargvec := PushArgVec3} vecf

	{$define vec := Vec4} {$define vecn := 4} {$define pvec := pVec4} {$define vecMT := Reg_Vec4MT} {$define vecname := 'vec4'}
	{$define l_vecctr := l_vec4} {$define pushvec := PushVec4} {$define argvec := ArgVec4} {$define pushargvec := PushArgVec4} vecf

	{$undef vec} {$undef vecn} {$undef pvec} {$undef vecMT} {$undef vecname}
	{$undef l_vecctr} {$undef pushvec} {$undef argvec} {$undef pushargvec}
	{$undef vecf}}

{$define all_script_lookups :=
	{$if defined(chans) or defined(storagetype) or defined(imagereadfunc) or defined(lookupfunc) or defined(bindinglookupfunc) or
		defined(scriptlookupname) or defined(storagedefault)}
		{$error all_script_lookups would hide defines}
	{$endif}

	{$define chans := 1} {$define storagetype := float} {$define imagereadfunc := ReadG} {$define lookupfunc := LookupG}
	{$define bindinglookupfunc := l_image_g} {$define scriptlookupname := 'g'} {$define storagedefault := 0} lookupf

	{$define chans := 2} {$define storagetype := Vec2} {$define imagereadfunc := ReadGA} {$define lookupfunc := LookupGA}
	{$define bindinglookupfunc := l_image_ga} {$define scriptlookupname := 'ga'} {$define storagedefault := Vec2.Make(0, 1)} lookupf

	{$define chans := 3} {$define storagetype := Vec3} {$define imagereadfunc := ReadRGB} {$define lookupfunc := LookupRGB}
	{$define bindinglookupfunc := l_image_rgb} {$define scriptlookupname := 'rgb'} {$define storagedefault := Vec3.Make(0, 0, 0)} lookupf

	{$define chans := 4} {$define storagetype := Vec4} {$define imagereadfunc := ReadRGBA} {$define lookupfunc := LookupRGBA}
	{$define bindinglookupfunc := l_image_rgba} {$define scriptlookupname := 'rgba'} {$define storagedefault := Vec4.Make(0, 0, 0, 1)} lookupf

	{$undef chans} {$undef storagetype} {$undef imagereadfunc} {$undef lookupfunc}
	{$undef bindinglookupfunc} {$undef scriptlookupname} {$undef storagedefault}
	{$undef lookupf}}

type
	GenerateByScriptOperation = class(GenericOpPayload)
		lock: ThreadLock;
		source, chunkName: string;
		spec: ImageSpec;
		forceSize, forceFormat: boolean;

		constructor Create;
		destructor Destroy; override;
		procedure Start; override;
		procedure GeneratePart(threadIndex, startPixel, endPixel: SizeUint); override;
	private const
		Reg_Vec2MT = lua.RIDX_LAST + 1;
		Reg_Vec3MT = Reg_Vec2MT + 1;
		Reg_Vec4MT = Reg_Vec3MT + 1;
		Reg_VecMT2VecLen = Reg_Vec4MT + 1;
		Reg_ImageMT = Reg_VecMT2VecLen + 1;

	type
		ScriptState = class(TObjectEx)
			L: lua.State; // userparamptr^ = @self
			op: GenerateByScriptOperation;
			x, y, f: SizeUint;
			intercepted: boolean;
			constructor Create(op: GenerateByScriptOperation);
			destructor Destroy; override;
			function CallGetPixel(var r: Vec4): uint;
		private
			procedure Setup; // экспозит все возможности в _G
			class function HumanValue(L: lua.State; index: cint): string; static;
			class function HumanArgs(L: lua.State; first, last: cint): string; static;
			class procedure ArgError(L: lua.State; const funcName: string; argIndex, first, last: cint; const extra: string = ''); noreturn; static;
			class procedure ArgError(L: lua.State; const funcName: string; argIndex: cint; const extra: string = ''); noreturn; static;

			class procedure Hook(L: lua.State; var ar: lua.Debug); cdecl; static;
			class function l_indexenv(L: lua.State): cint; cdecl; static;

			class function VecLen(L: lua.State; index: cint): uint; static;
		{$define vecf :=
			class function l_vecctr(L: lua.State): cint; cdecl; static;
			class procedure pushvec(L: lua.State; const v: vec); static;
			class function argvec(L: lua.State; index: cint; out args: uint; const func: string): vec; static;
			class function pushargvec(L: lua.State; const v: vec; scatter: boolean): cint; static;} all_script_vectors
			class function l_vecindex(L: lua.State): cint; cdecl; static;
			class function l_vecadd(L: lua.State): cint; cdecl; static;
			class function l_vecsub(L: lua.State): cint; cdecl; static;
			class function l_vecmul(L: lua.State): cint; cdecl; static;
			class function l_vecdiv(L: lua.State): cint; cdecl; static;
			class function l_vecunm(L: lua.State): cint; cdecl; static;
			class procedure BadBinOp(L: lua.State; const op: string); static;
			class function l_min(L: lua.State): cint; cdecl; static;
			class function l_max(L: lua.State): cint; cdecl; static;
			class function l_abs(L: lua.State): cint; cdecl; static;
			class function l_clamp(L: lua.State): cint; cdecl; static;
			class function l_lerp(L: lua.State): cint; cdecl; static;
			class function l_sin(L: lua.State): cint; cdecl; static;
			class function l_cos(L: lua.State): cint; cdecl; static;
			class function l_smoothstep(L: lua.State): cint; cdecl; static;
			class function l_hsv2rgb(L: lua.State): cint; cdecl; static;
			class function l_rgb2hsv(L: lua.State): cint; cdecl; static;
			class function SelfToImage(L: lua.State; const func: string): pImage; static;
			class function SelfToImageUnchecked(L: lua.State): pImage; static;
			class function MaybePixelPtr(var im: Image; const v: Vec2): pointer; static;
		{$define lookupf :=
			class function lookupfunc(var im: Image; const v: Vec2): storagetype; static;
			class function bindinglookupfunc(L: lua.State): cint; cdecl; static;} all_script_lookups
			class function l_image_index(L: lua.State): cint; cdecl; static;
		end;

	var
		// в этом стейте вызывается функция для первого пикселя, чтобы по тому, что она вернёт, определить формат результата.
		// В дальнейшем этот стейт используется потоком 0, остальные создают себе отдельные.
		ss0: ScriptState;
	end;

	constructor GenerateByScriptOperation.Create;
	begin
		inherited Create;
		lock.Init;
	end;

	destructor GenerateByScriptOperation.Destroy;
	begin
		ss0.Free(ss0);
		lock.Done;
		inherited Destroy;
	end;

	procedure GenerateByScriptOperation.Start;
	var
		r: Vec4;
		acceptLen, cpLen: SizeInt;
	begin {$define args := r} unused_args
		if source = '' then raise Exception.Create('Формула не задана.');

		// ScriptState.Create вызывает Setup. Setup выставляет oim.w/oim.h в глобальные переменные.
		// Даже если бы они читались в _G.__index, здесь чуть ниже вызывается GetPixel, которая её дёрнет.
		Image.ValidateSize(spec, op.oname.name);
		if not forceSize and not Ary(op.inputs).Empty and Assigned(op.inputs[0].im) then
		begin
			spec.w := op.inputs[0].im^.im.w;
			spec.h := op.inputs[0].im^.im.h;
		end;

		oim.spec := spec;

		ss0 := ScriptState.Create(self);
		if chunkName = '' then chunkName := source + EOL;

		// Lua отрежет название, если оно слишком длинное. Сделать это самому, красивее.
		if length(chunkName) > lua.IDSIZE - 10 then
		begin
			acceptLen := 0;
			while (1 + acceptLen <= length(chunkName)) do
			begin
				cpLen := chunkName.CodepointLen(1 + acceptLen);
				if acceptLen + cpLen <= lua.IDSIZE - 10 then acceptLen += cpLen else break;
			end;
			chunkName := chunkName.Head(acceptLen) + '(...)' + IfThen(chunkName.ConsumeRev([#13, #10], length(chunkName)) < length(chunkName), EOL);
		end;

		try
			lua.loadstringE(ss0.L, [source], chunkName);
		except
			on e: Exception do
			begin
				e.msg := lua.striplinenumber(e.msg, chunkName);
				raise;
			end;
		end;

		if not forceFormat then
			case ss0.CallGetPixel(r) of
				1: spec.format := ImageFormat.G;
				2: spec.format := ImageFormat.GA;
				3: spec.format := ImageFormat.RGB;
				4: spec.format := ImageFormat.RGBA;
			end;
		oim.Init(op.oname.name, nil, spec);
	end;

	procedure GenerateByScriptOperation.GeneratePart(threadIndex, startPixel, endPixel: SizeUint);
		function Mismatch(nc: uint): Exception;
		begin
			result := Exception.Create('Формула вернула {} значени{е/я/й}, ожидается 1-4.'.Format([VarRec.uint(nc), oim.format.id]));
		end;
	var
		ss: ScriptState;
		pixel, psz: SizeUint;
		r: Vec4;
		nc: uint;
		ofs: pointer;
	begin {$define args := r} unused_args
		pixel := startPixel;
		psz := oim.format.pixelSize;

		ss := nil;
		try
			if threadIndex = 0 then ss := ss0 else
			begin
				ss := ScriptState.Create(self);
				lua.loadstringE(ss.L, [source], chunkName);
			end;
			oim.DecodePixelNumber(pixel, ss.x, ss.y, ss.f, ofs);

			while pixel < endPixel do
			begin
				nc := ss.CallGetPixel(r);
				case nc of
					1: Image.WriteG(ofs, oim.format, r.data[0]);
					2: Image.WriteGA(ofs, oim.format, pVec2(@r)^);
					3: Image.WriteRGB(ofs, oim.format, pVec3(@r)^);
					4: Image.WriteRGBA(ofs, oim.format, r);
				end;
				oim.NextPixel(pixel, ss.x, ss.y, ss.f);
				ofs += psz;
				if pixel mod MixOperation.ReportPeriodPixels = 0 then op.NoteProgress(threadIndex, (pixel - startPixel) / (endPixel - startPixel));
			end;
		finally
			if ss <> ss0 then ss.Free(ss);
		end;
	end;

	constructor GenerateByScriptOperation.ScriptState.Create(op: GenerateByScriptOperation);
	begin
		inherited Create;
		self.op := op;
		L := lua.newstate(lua.Alloc(@lua.default_alloc), nil);
		lua.userparamptr(L)^ := self;
		lua.atpanic(L, lua.CFunction(@lua.default_panic));
		lua.onthrow(L, lua.Throwf(@lua.default_throw), lua.Pcallf(@lua.default_pcall));
		lua.sethook(L, lua.Hook(@ScriptState.Hook), lua.MASKCOUNT, 100000);
		Setup;
	end;

	destructor GenerateByScriptOperation.ScriptState.Destroy;
	begin
		if Assigned(L) then lua.close(L);
		inherited Destroy;
	end;

	// на вершине стека ожидается функция; она НЕ снимается со стека
	function GenerateByScriptOperation.ScriptState.CallGetPixel(var r: Vec4): uint;
	var
		top, first, nr, i: cint;
	begin
		top := lua.gettop(L);
		lua.pushvalue(L, -1); // (top)func func
		if lua.pcall(L, 0, lua.MULTRET, 0) <> lua.OK then
		begin
			// Lua-хук, чтобы не бросать исключение сквозь Lua-фреймы, преобразует его lua_error с простым сообщением об ошибке, т. е. тип теряется.
			// Для Interception он запоминается ad-hoc, чтобы отличить эту ситуацию.
			if intercepted then op.op.Intercept;
			raise Exception.Create(lua.striplinenumber(lua.tostring(L, -1), op.chunkName));
		end;
		first := top + 1;
		// func (first)...результаты...

		nr := lua.gettop(L) - top;
		case nr of
			1:
				case lua.&type(L, first) of
					lua.TNUMBER: // градация серого
						begin
							r.data[0] := lua.tonumberx(L, first, nil);
							result := 1;
						end;
					lua.TUSERDATA: // вектор
						case VecLen(L, first) of
							2: begin pVec2(@r)^ := pVec2(lua.touserdata(L, first))^; result := 2; end;
							3: begin pVec3(@r)^ := pVec3(lua.touserdata(L, first))^; result := 3; end;
							4: begin r := pVec4(lua.touserdata(L, first))^; result := 4; end;
							else result := 0;
						end;
					else result := 0;
				end;
			2, 3, 4: // вектор как N чисел.
				begin
					result := nr;
					for i := first to first + nr - 1 do
						if lua.&type(L, i) = lua.TNUMBER then r.data[i-first] := lua.tonumberx(L, i, nil) else result := 0;
				end;
			else result := 0;
		end;

		if result = 0 then
			raise Exception.Create('Формула {}; ожидается 1 вектор или от 1 до 4 чисел.'.Format([
				IfThen(nr > 0, 'вернула ({})'.Format([HumanArgs(L, first, first + nr - 1)]), 'ничего не вернула')]));
		lua.settop(L, top);
	end;

	procedure GenerateByScriptOperation.ScriptState.Setup;
	var
		i: SizeInt;
	begin
	{$define vecf :=
		lua.newtable(L);
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecindex)); lua.setfield(L, -2, '__index');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecadd)); lua.setfield(L, -2, '__add');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecsub)); lua.setfield(L, -2, '__sub');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecmul)); lua.setfield(L, -2, '__mul');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecdiv)); lua.setfield(L, -2, '__div');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecunm)); lua.setfield(L, -2, '__unm');
		lua.rawseti(L, lua.REGISTRYINDEX, vecMT);} all_script_vectors
		lua.newtable(L);
		{$define vecf :=
			lua.rawgeti(L, lua.REGISTRYINDEX, vecMT); lua.pushinteger(L, vecn); lua.rawset(L, -3);} all_script_vectors
		lua.rawseti(L, lua.REGISTRYINDEX, Reg_VecMT2VecLen);
		lua.newtable(L);
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_image_index)); lua.setfield(L, -2, '__index');
		lua.rawseti(L, lua.REGISTRYINDEX, Reg_ImageMT);

		lua.rawgeti(L, lua.REGISTRYINDEX, lua.RIDX_GLOBALS); // _G
			lua.pushinteger(L, op.oim.w); lua.setfield(L, -2, 'w');
			lua.pushinteger(L, op.oim.h); lua.setfield(L, -2, 'h');
			lua.pushinteger(L, op.oim.frames); lua.setfield(L, -2, 'frames');
			PushVec2(L, Vec2.Make(op.oim.w, op.oim.h)); lua.setfield(L, -2, 'wh');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_min)); lua.setfield(L, -2, 'min');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_max)); lua.setfield(L, -2, 'max');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_abs)); lua.setfield(L, -2, 'abs');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_clamp)); lua.setfield(L, -2, 'clamp');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_lerp)); lua.setfield(L, -2, 'lerp');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_sin)); lua.setfield(L, -2, 'sin');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_cos)); lua.setfield(L, -2, 'cos');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_smoothstep)); lua.setfield(L, -2, 'smoothstep');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_hsv2rgb)); lua.setfield(L, -2, 'hsv2rgb');
			lua.pushcfunction(L, lua.CFunction(@ScriptState.l_rgb2hsv)); lua.setfield(L, -2, 'rgb2hsv');
			for i := 0 to High(op.op.inputs) do
				if Assigned(op.op.inputs[i].im) then
				begin
					pPointer(lua.newuserdata(L, sizeof(pointer)))^ := @op.op.inputs[i].im^.im;
					lua.rawgeti(L, lua.REGISTRYINDEX, Reg_ImageMT); lua.setmetatable(L, -2);
					if i = 0 then begin lua.pushvalue(L, -1); lua.setfield(L, -3, 'im'); end;
					lua.setfield(L, -2, pChar('im' + im.ToString(1 + i)));
				end;
		{$define vecf := lua.pushcfunction(L, lua.CFunction(@ScriptState.l_vecctr)); lua.setfield(L, -2, vecname);} all_script_vectors
			lua.newtable(L); // _G gMT
				lua.pushcfunction(L, lua.CFunction(@ScriptState.l_indexenv)); lua.setfield(L, -2, '__index');
			lua.setmetatable(L, -2); // _G
		lua.pop(L);
	end;

	class function GenerateByScriptOperation.ScriptState.HumanValue(L: lua.State; index: cint): string;
	begin
		case lua.&type(L, index) of
			lua.TBOOLEAN: result := IfThen(lua.toboolean(L, index), 'true', 'false');
			lua.TNUMBER: if lua.isinteger(L, index) then result := im.ToString(lua.tointegerx(L, index, nil)) else result := im.ToString(lua.tonumberx(L, index, nil));
			lua.TSTRING: result := '"' + lua.tostring(L, index) + '"';
			lua.TUSERDATA:
				case VecLen(L, index) of
				{$define vecf :=
					vecn: result := '{}({})'.Format([vecname, pvec(lua.touserdata(L, index))^.ToString]);} all_script_vectors
					else
					begin
						result := '';
						if lua.getmetatable(L, 1) <> 0 then
						begin
							lua.rawgeti(L, lua.REGISTRYINDEX, Reg_ImageMT); if lua.rawequal(L, -2, -1) then result := 'im'; lua.pop(L);
							lua.pop(L);
						end;
						if result = '' then result := '<{}>'.Format([lua.typename(L, lua.&type(L, index))]);
					end;
				end;
			else result := lua.typename(L, lua.&type(L, index));
		end;
	end;

	class function GenerateByScriptOperation.ScriptState.HumanArgs(L: lua.State; first, last: cint): string;
	var
		index: cint;
	begin
		for index := first to last do
			result += IfThen(index > first, ', ') + HumanValue(L, index);
	end;

	class procedure GenerateByScriptOperation.ScriptState.ArgError(L: lua.State; const funcName: string; argIndex, first, last: cint; const extra: string = '');
	var
		args: string;
		index: cint;
	begin
		args := '';
		for index := first to last do
			args += IfThen(index > first, ', ') + IfThen(argIndex = index, '>') + HumanValue(L, index);
		if argIndex > last then args += IfThen(args <> '', ', ') + '..?';
		lua.throw(L, '{}({}){}{}'.Format([funcName, args, IfThen(extra <> '', ': '), extra]));
	end;

	class procedure GenerateByScriptOperation.ScriptState.ArgError(L: lua.State; const funcName: string; argIndex: cint; const extra: string = '');
	begin
		ArgError(L, funcName, argIndex, 1, lua.gettop(L), extra);
	end;

	class procedure GenerateByScriptOperation.ScriptState.Hook(L: lua.State; var ar: lua.Debug); cdecl;
	var
		ss: ScriptState;
	begin {$define args := ar} unused_args
		ss := ScriptState(lua.userparamptr(L)^);
		try
			ss.op.op.Intercept;
		except
			on e: TObject do
			begin
				if e is Interception then ss.intercepted := true;
				lua.throw(L, Exception.Message);
			end;
		end;
	end;

	class function GenerateByScriptOperation.ScriptState.l_indexenv(L: lua.State): cint; cdecl;
		function WhatImage(L: lua.State; p: pChar; out ss: ScriptState; out im: pImage): boolean;
		var
			index: uint;
		begin
			ss := ScriptState(lua.userparamptr(L)^);
			index := 0;
			if p^ <> #0 then
			begin
				repeat
					if (p^ >= '0') and (p^ <= '9') then
					begin
						index := index * 10 + uint(ord(p^) - ord('0'));
						if index > SizeUint(length(ss.op.op.inputs)) then exit(false);
					end else
						if p^ = #0 then break else exit(false);
					inc(p);
				until false;
				if index = 0 then exit(false);
				dec(index);
			end;

			result := (index < SizeUint(length(ss.op.op.inputs))) and Assigned(ss.op.op.inputs[index].im);
			if result then im := @ss.op.op.inputs[index].im^.im;
		end;
	var
		p: pChar;
		ss: ScriptState;
		im: pImage;
	begin
		result := 0;
		p := lua.topchar(L, 2);
		if Assigned(p) then
			case p[0] of
				'x':
					case p[1] of
						#0: begin ss := ScriptState(lua.userparamptr(L)^); lua.pushinteger(L, ss.x); result := 1; end;
						'y': if p[2] = #0 then begin ss := ScriptState(lua.userparamptr(L)^); PushVec2(L, Vec2.Make(ss.x, ss.y)); result := 1; end;
					end;
				'y': if p[1] = #0 then begin ss := ScriptState(lua.userparamptr(L)^); lua.pushinteger(L, ss.y); result := 1; end;
				'f': if p[1] = #0 then begin ss := ScriptState(lua.userparamptr(L)^); lua.pushinteger(L, ss.f); result := 1; end;
				'n':
					case p[1] of
						'x':
							case p[2] of
								#0: begin ss := ScriptState(lua.userparamptr(L)^); lua.pushnumber(L, ss.x/ss.op.oim.w); result := 1; end;
								'y': if p[3] = #0 then begin ss := ScriptState(lua.userparamptr(L)^); PushVec2(L, Vec2.Make(ss.x/ss.op.oim.w, ss.y/ss.op.oim.h)); result := 1; end;
							end;
						'y': if p[2] = #0 then begin ss := ScriptState(lua.userparamptr(L)^); lua.pushnumber(L, ss.y/ss.op.oim.h); result := 1; end;
						'f': if p[2] = #0 then begin ss := ScriptState(lua.userparamptr(L)^); lua.pushnumber(L, ss.f/ss.op.oim.frames); result := 1; end;
					end;
				'r':
					if (p[1] = 'g') and (p[2] = 'b') then
						if p[3] = 'a' then
							if WhatImage(L, p + 4, ss, im) then begin PushVec4(L, LookupRGBA(im^, Vec2.Make(ss.x, ss.y))); result := 1; end else
						else if WhatImage(L, p + 3, ss, im) then begin PushVec3(L, LookupRGB(im^, Vec2.Make(ss.x, ss.y))); result := 1; end else
					else if WhatImage(L, p + 1, ss, im) then begin lua.pushnumber(L, LookupRGB(im^, Vec2.Make(ss.x, ss.y)).x); result := 1; end;
				'g':
					if (p[1] = 'r') and (p[2] = 'a') and (p[3] = 'y') then
						if WhatImage(L, p + 4, ss, im) then begin lua.pushnumber(L, LookupG(im^, Vec2.Make(ss.x, ss.y))); result := 1; end else
					else if (p[1] = 'a') and WhatImage(L, p + 2, ss, im) then begin PushVec2(L, LookupGA(im^, Vec2.Make(ss.x, ss.y))); result := 1; end
					else if WhatImage(L, p + 1, ss, im) then begin lua.pushnumber(L, LookupRGB(im^, Vec2.Make(ss.x, ss.y)).y); result := 1; end;
				'b': if WhatImage(L, p + 1, ss, im) then begin lua.pushnumber(L, LookupRGB(im^, Vec2.Make(ss.x, ss.y)).z); result := 1; end;
				'a': if WhatImage(L, p + 1, ss, im) then begin lua.pushnumber(L, LookupRGBA(im^, Vec2.Make(ss.x, ss.y)).w); result := 1; end;
			end;
		if result = 0 then lua.throw(L, 'Переменная {} не определена.'.Format([HumanValue(L, 2)]));
	end;

	class function GenerateByScriptOperation.ScriptState.VecLen(L: lua.State; index: cint): uint;
	begin
		if lua.getmetatable(L, index) = 0 then exit(0); // mt
		lua.rawgeti(L, lua.REGISTRYINDEX, Reg_VecMT2VecLen); // mt mt2len
		lua.pushvalue(L, -2); // mt mt2len mt
		lua.rawget(L, -2); // mt mt2len len
		result := lua.tointegerx(L, -1, nil);
		lua.pop(L, 3);
	end;

{$define vecf :=
	class function GenerateByScriptOperation.ScriptState.l_vecctr(L: lua.State): cint; cdecl;
	var
		args, iarg, icomp: cint;
		i, nv: uint;
		v: vec;
		procedure AE; begin ArgError(L, vecname, iarg); end;
	begin
		args := lua.gettop(L);
		iarg := 1;
		icomp := 0;
		while (iarg <= args) and (icomp < length(v.data)) do
		begin
			case lua.&type(L, iarg) of
				lua.TNUMBER:
					begin
						v.data[icomp] := lua.tonumberx(L, iarg, nil); inc(icomp);
						if args = 1 then
							while icomp < length(v.data) do begin v.data[icomp] := v.data[0]; inc(icomp); end;
					end;
				lua.TUSERDATA:
					begin
						nv := VecLen(L, iarg); if nv = 0 then AE;
						i := 0;
						while (i < nv) and (icomp < length(v.data)) do
						begin
							v.data[icomp] := Vec4.LinearData(lua.touserdata(L, iarg)^)[i];
							inc(i); inc(icomp);
						end;
					end;
				else AE;
			end;
			inc(iarg);
		end;
		if iarg < args then AE;

		while icomp < length(v.data) do
		begin
			if icomp < 3 then v.data[icomp] := 0 else v.data[icomp] := 1;
			inc(icomp);
		end;
		pushvec(L, v);
		result := 1;
	end;

	class procedure GenerateByScriptOperation.ScriptState.pushvec(L: lua.State; const v: vec);
	begin
		vec(lua.newuserdata(L, sizeof(v))^) := v;
		lua.rawgeti(L, lua.REGISTRYINDEX, vecMT); lua.setmetatable(L, -2);
	end;

	class function GenerateByScriptOperation.ScriptState.argvec(L: lua.State; index: cint; out args: uint; const func: string): vec;
		procedure AE(index: cint); noreturn; begin ArgError(L, func, index); end;
	var
		i: cint;
	begin
		case lua.&type(L, index) of
			lua.TNUMBER:
				begin
					result.data[0] := lua.tonumberx(L, index, nil);
					for i := 1 to High(result.data) do
						if lua.&type(L, index + i) = lua.TNUMBER then
							result.data[i] := lua.tonumberx(L, index + i, nil)
						else
							AE(index + i);
					args := length(result.data);
				end;
			lua.TUSERDATA:
				if VecLen(L, index) = vecn then
				begin
					result := pvec(lua.touserdata(L, index))^;
					args := 1;
				end else
					AE(index);
			else AE(index);
		end;
	end;

	class function GenerateByScriptOperation.ScriptState.pushargvec(L: lua.State; const v: vec; scatter: boolean): cint;
	var
		i: uint;
	begin
		if scatter then
		begin
			for i := 0 to High(v.data) do lua.pushnumber(L, v.data[i]);
			result := length(v.data);
		end else
		begin
			pushvec(L, v);
			result := 1;
		end;
	end;} all_script_vectors

	class function GenerateByScriptOperation.ScriptState.l_vecindex(L: lua.State): cint; cdecl;
		function Swizzle(L: lua.State; p: pChar; v: pointer; len: uint): cint;
		var
			i, n: csize_t;
			cidx: uint;
			r: Vec4;
		begin
			n := lua.rawlen(L, 2);
			if (n < 1) or (n > 4) then exit(0);
			i := 0;
			while i < n do
			begin
				case p[i] of
					'x', 'r': cidx := 0;
					'y': cidx := 1;
					'z', 'b': cidx := 2;
					'w': cidx := 3;
					'g': if len = 2 then cidx := 0 else cidx := 1;
					'a': if len = 2 then cidx := 1 else cidx := 3;
					'0': begin r.data[i] := 0; inc(i); continue; end;
					'1': begin r.data[i] := 1; inc(i); continue; end;
					else exit(0);
				end;
				if cidx >= len then exit(0);
				r.data[i] := pVec4(v)^.data[cidx];
				inc(i);
			end;
			case n of
				1: begin lua.pushnumber(L, r.data[0]); result := 1; end;
			{$define vecf := vecn: begin pushvec(L, pvec(@r)^); result := 1; end;} all_script_vectors else result := 0;
			end;
		end;

		function IndexByString(L: lua.State; v: pointer; len: uint): cint;
		var
			p: pChar;
		begin
			result := 0;
			p := lua.topchar(L, 2);
			case p[0] of
				'l':
					if (p[1] = 'e') and (p[2] = 'n') and (p[3] = #0) then
						case len of
						{$define vecf := vecn: begin lua.pushnumber(L, vec(v^).Length); result := 1; end;} all_script_vectors
						end;
				's':
					if (p[1] = 'q') and (p[2] = 'l') and (p[3] = 'e') and (p[4] = 'n') and (p[5] = #0) then
						case len of
						{$define vecf := vecn: begin lua.pushnumber(L, vec(v^).SquareLength); result := 1; end;} all_script_vectors
						end;
				'n':
					if (p[1] = 'n') and (p[2] = #0) then
						case len of
						{$define vecf := vecn: begin pushvec(L, vec(v^).Normalized); result := 1; end;} all_script_vectors
						end;
				else result := Swizzle(L, p, v, len);
			end;
		end;

		function IndexByNumber(L: lua.State; v: pointer; len: uint): cint;
		var
			lint: cint;
			isnum: cint;
		begin
			lint := lua.tointegerx(L, 2, @isnum);
			if (isnum <> 0) and (lint >= 1) and (uint(lint) <= len) then
			begin
				lua.pushnumber(L, pVec4(v)^.data[lint-1]);
				result := 1;
			end else
				result := 0;
		end;

	var
		len: uint;
		v: pointer;

	begin
		v := lua.touserdata(L, 1);
		len := VecLen(L, 1);
		case lua.&type(L, 2) of
			lua.TSTRING: result := IndexByString(L, v, len);
			lua.TNUMBER: result := IndexByNumber(L, v, len);
			else result := 0;
		end;
		if result <> 1 then lua.throw(L, 'vec{}.{}'.Format([len, HumanValue(L, 2)]));
	end;

	class function GenerateByScriptOperation.ScriptState.l_vecadd(L: lua.State): cint; cdecl;
	var
		len: uint;
	begin
		len := VecLen(L, 1);
		if len <> VecLen(L, 2) then lua.throw(L, '{} + {}'.Format([HumanValue(L, 1), HumanValue(L, 2)]));
		case len of
		{$define vecf := vecn: pushvec(L, pvec(lua.touserdata(L, 1))^ + pvec(lua.touserdata(L, 2))^);} all_script_vectors else BadBinOp(L, '+');
		end;
		result := 1;
	end;

	class function GenerateByScriptOperation.ScriptState.l_vecsub(L: lua.State): cint; cdecl;
	var
		len: uint;
	begin
		len := VecLen(L, 1);
		if len <> VecLen(L, 2) then lua.throw(L, '{} - {}'.Format([HumanValue(L, 1), HumanValue(L, 2)]));
		case len of
		{$define vecf := vecn: pushvec(L, pvec(lua.touserdata(L, 1))^ - pvec(lua.touserdata(L, 2))^);} all_script_vectors else BadBinOp(L, '-');
		end;
		result := 1;
	end;

	class function GenerateByScriptOperation.ScriptState.l_vecmul(L: lua.State): cint; cdecl;
		procedure bynum(L: lua.State; nidx, vidx: cint);
		begin
			case VecLen(L, vidx) of
			{$define vecf := vecn: pushvec(L, lua.tonumberx(L, nidx, nil) * pvec(lua.touserdata(L, vidx))^);} all_script_vectors else BadBinOp(L, '*');
			end;
		end;
	var
		len: uint;
	begin
		if lua.&type(L, 1) = lua.TNUMBER then bynum(L, 1, 2)
		else if lua.&type(L, 2) = lua.TNUMBER then bynum(L, 2, 1)
		else
		begin
			len := VecLen(L, 1);
			if len <> VecLen(L, 2) then lua.throw(L, '{} * {}'.Format([HumanValue(L, 1), HumanValue(L, 2)]));
			case len of
			{$define vecf := vecn: pushvec(L, pvec(lua.touserdata(L, 1))^ * pvec(lua.touserdata(L, 2))^);} all_script_vectors else BadBinOp(L, '*');
			end;
		end;
		result := 1;
	end;

	class function GenerateByScriptOperation.ScriptState.l_vecdiv(L: lua.State): cint; cdecl;
	var
		len: uint;
	begin
		if lua.&type(L, 1) = lua.TNUMBER then
			case VecLen(L, 2) of
			{$define vecf := vecn: pushvec(L, lua.tonumberx(L, 1, nil) / pvec(lua.touserdata(L, 2))^);} all_script_vectors else BadBinOp(L, '/');
			end
		else if lua.&type(L, 2) = lua.TNUMBER then
			case VecLen(L, 1) of
			{$define vecf := vecn: pushvec(L, pvec(lua.touserdata(L, 1))^ / lua.tonumberx(L, 2, nil));} all_script_vectors else BadBinOp(L, '/');
			end
		else
		begin
			len := VecLen(L, 1);
			if len <> VecLen(L, 2) then lua.throw(L, '{} / {}'.Format([HumanValue(L, 1), HumanValue(L, 2)]));
			case len of
			{$define vecf := vecn: pushvec(L, pvec(lua.touserdata(L, 1))^ / pvec(lua.touserdata(L, 2))^);} all_script_vectors else BadBinOp(L, '/');
			end;
		end;
		result := 1;
	end;

	class function GenerateByScriptOperation.ScriptState.l_vecunm(L: lua.State): cint; cdecl;
	begin
		case VecLen(L, 1) of
		{$define vecf := vecn: pushvec(L, -pvec(lua.touserdata(L, 1))^);} all_script_vectors else lua.throw(L, '-{}'.Format([HumanValue(L, 1)]));
		end;
		result := 1;
	end;

	class procedure GenerateByScriptOperation.ScriptState.BadBinOp(L: lua.State; const op: string);
	begin
		lua.throw(L, '{} {} {}'.Format([HumanValue(L, 1), op, HumanValue(L, 2)]));
	end;

	// https://ru.wikipedia.org/wiki/HSV_(цветовая_модель)#Преобразования_цветовых_компонентов_между_моделями
	// Я не уверен, нужна ли здесь по-хорошему гамма-коррекция для V. На всякий случай ничего не трогал.
	function HSVToRGB(const hsv: Vec3): Vec3;
	var
		h, v, vMin, a: float;
	begin
		h := clamp(frac(hsv.x), 0, 1) * 6;
		v := clamp(hsv.z, 0, 1);
		vMin := (1 - clamp(hsv.y, 0, 1)) * v;
		a := (v - vMin) * frac(h);

		case trunc(h) of
			0: result := Vec3.Make(v, vMin + a, vMin);
			1: result := Vec3.Make(v - a, v, vMin);
			2: result := Vec3.Make(vMin, v, vMin + a);
			3: result := Vec3.Make(vMin, v - a, v);
			4: result := Vec3.Make(vMin + a, vMin, v);
			else result := Vec3.Make(v, vMin, v - a);
		end;
	end;

	function RGBToHSV(const rgb: Vec3): Vec3;
	var
		cmax, cmin: float;
	begin
		cmax := max(max(rgb.x, rgb.y), rgb.z);
		cmin := min(min(rgb.x, rgb.y), rgb.z);
		if cmax = cmin then result.x := 0
		else if cmax = rgb.x then
			if rgb.y >= rgb.z then result.x := (rgb.y - rgb.z) / (cmax - cmin) / 6 else result.x := 1 + (rgb.y - rgb.z) / (cmax - cmin) / 6
		else if cmax = rgb.y then result.x := (2/6) + (rgb.z - rgb.x) / (cmax - cmin) / 6
		else result.x := (4/6) + (rgb.x - rgb.y) / (cmax - cmin) / 6;
		if cmax = 0 then result.y := 0 else result.y := 1 - cmin/cmax;
		result.z := cmax;
	end;

{$define opimpl :=
		procedure AE(index: cint); noreturn; begin ArgError(L, funcname, index); end;
	var
	{$if not defined(per_component)} iarg: cint; {$endif}
		r: array[0 .. 3] of lua.Number;
		iv, vlen: uint;
		v: {$if defined(ternary)} array[1 .. 3] of {$elseif defined(x_erp)} array[1 .. 2] of {$endif} pointer;
	begin
		case lua.&type(L, 1) of
			lua.TNUMBER:
				begin
				{$if defined(minmax)}
					r[0] := lua.tonumberx(L, 1, nil);
					for iarg := 2 to lua.gettop(L) do
					begin
						if lua.&type(L, iarg) <> lua.TNUMBER then AE(iarg);
						r[0] := func(r[0], lua.tonumberx(L, iarg, nil));
					end;
				{$elseif defined(ternary) or defined(x_erp)}
					for iarg := 2 to 3 do
						if lua.&type(L, iarg) <> lua.TNUMBER then AE(iarg);
					r[0] := func(lua.tonumberx(L, 1, nil), lua.tonumberx(L, 2, nil), lua.tonumberx(L, 3, nil));
				{$elseif defined(per_component)}
					r[0] := func(lua.tonumberx(L, 1, nil));
				{$else} {$error not minmax, not ternary, not interpolation, not per-component operation, so what is it?} {$endif}
					lua.pushnumber(L, r[0]); result := 1;
				end;

			lua.TUSERDATA:
				begin
					vlen := VecLen(L, 1); if vlen = 0 then AE(1);
					v {$if defined(ternary) or defined(x_erp)} [1] {$endif} := lua.touserdata(L, 1);
				{$if defined(minmax)}
					for iv := 0 to vlen - 1 do
						r[iv] := pVec4(v)^.data[iv];

					for iarg := 2 to lua.gettop(L) do
					begin
						if VecLen(L, iarg) <> vlen then AE(iarg);
						v := lua.touserdata(L, iarg);
						for iv := 0 to vlen - 1 do
							r[iv] := func(r[iv], pVec4(v)^.data[iv]);
					end;
				{$elseif defined(ternary)}
					for iarg := 2 to 3 do
					begin
						if VecLen(L, iarg) <> vlen then AE(iarg);
						v[iarg] := lua.touserdata(L, iarg);
					end;
					for iv := 0 to vlen - 1 do
						r[iv] := func(pVec4(v[1])^.data[iv], pVec4(v[2])^.data[iv], pVec4(v[3])^.data[iv]);
				{$elseif defined(x_erp)}
					if VecLen(L, 2) <> vlen then AE(2); v[2] := lua.touserdata(L, 2);
					if lua.&type(L, 3) <> lua.TNUMBER then AE(3);
					for iv := 0 to vlen - 1 do
						r[iv] := func(pVec4(v[1])^.data[iv], pVec4(v[2])^.data[iv], lua.tonumberx(L, 3, nil));
				{$elseif defined(per_component)}
					for iv := 0 to vlen - 1 do
						r[iv] := func(pVec4(v)^.data[iv]);
				{$else} {$error not minmax, not ternary, not interpolation, not per-component operation, so what is it?} {$endif}

					case vlen of
					{$define vecf :=
						vecn: begin pushvec(L, vec.Make(r[0], r[1] {$if vecn >= 3}, r[2] {$endif} {$if vecn >= 4}, r[3] {$endif})); result := 1; end;}
						all_script_vectors else lua.throw(L, '?!');
					end;
					result := 1;
				end;
			else AE(1);
		end;
{$ifdef suppress_false_dfa_alarms} {$warn 5036 off} {$endif}
	end;
{$ifdef suppress_false_dfa_alarms} {$warn 5036 on} {$endif} // 'r' does not seem to be initialized
	{$undef funcname} {$undef func} {$undef minmax} {$undef ternary} {$undef x_erp} {$undef per_component}}

	class function GenerateByScriptOperation.ScriptState.l_min(L: lua.State): cint; cdecl; {$define funcname := 'min'} {$define func := min} {$define minmax} opimpl
	class function GenerateByScriptOperation.ScriptState.l_max(L: lua.State): cint; cdecl; {$define funcname := 'max'} {$define func := max} {$define minmax} opimpl
	class function GenerateByScriptOperation.ScriptState.l_abs(L: lua.State): cint; cdecl; {$define funcname := 'abs'} {$define func := abs} {$define per_component} opimpl
	class function GenerateByScriptOperation.ScriptState.l_clamp(L: lua.State): cint; cdecl; {$define funcname := 'clamp'} {$define func := clamp} {$define ternary} opimpl
	class function GenerateByScriptOperation.ScriptState.l_lerp(L: lua.State): cint; cdecl; {$define funcname := 'lerp'} {$define func := lerp} {$define x_erp} opimpl
	class function GenerateByScriptOperation.ScriptState.l_sin(L: lua.State): cint; cdecl; {$define funcname := 'sin'} {$define func := sin} {$define per_component} opimpl
	class function GenerateByScriptOperation.ScriptState.l_cos(L: lua.State): cint; cdecl; {$define funcname := 'cos'} {$define func := cos} {$define per_component} opimpl
	class function GenerateByScriptOperation.ScriptState.l_smoothstep(L: lua.State): cint; cdecl; {$define funcname := 'smoothstep'} {$define func := smoothstep} {$define x_erp} opimpl
{$undef opimpl}

	class function GenerateByScriptOperation.ScriptState.l_hsv2rgb(L: lua.State): cint; cdecl;
	var
		hsv: Vec3;
		vArgs: uint;
	begin
		hsv := ArgVec3(L, 1, vArgs, 'hsv2rgb');
		result := PushArgVec3(L, HSVToRGB(hsv), vArgs > 1);
	end;

	class function GenerateByScriptOperation.ScriptState.l_rgb2hsv(L: lua.State): cint; cdecl;
	var
		rgb: Vec3;
		vArgs: uint;
	begin
		rgb := ArgVec3(L, 1, vArgs, 'rgb2hsv');
		result := PushArgVec3(L, RGBToHSV(rgb), vArgs > 1);
	end;

	class function GenerateByScriptOperation.ScriptState.SelfToImage(L: lua.State; const func: string): pImage;
	var
		top: cint;
	begin
		top := lua.gettop(L);
		lua.rawgeti(L, lua.REGISTRYINDEX, Reg_ImageMT);
		if (lua.getmetatable(L, 1) = 0) or not lua.rawequal(L, -2, -1) then ArgError(L, func, 1, 1, top, 'где self? пропущена «:»?');
		lua.settop(L, top);
		result := SelfToImageUnchecked(L);
	end;

	class function GenerateByScriptOperation.ScriptState.SelfToImageUnchecked(L: lua.State): pImage;
	begin
		result := pPointer(lua.touserdata(L, 1))^;
	end;

	class function GenerateByScriptOperation.ScriptState.MaybePixelPtr(var im: Image; const v: Vec2): pointer;
	begin
		if (v.x >= 0) and (v.x < im.w) and (v.y >= 0) and (v.y < im.h) then
			result := im.data + im.format.pixelSize * (im.w * trunc(v.y) + trunc(v.x))
		else
			result := nil;
	end;

{$define lookupf :=
	class function GenerateByScriptOperation.ScriptState.lookupfunc(var im: Image; const v: Vec2): storagetype;
	var
		p: pointer;
	begin
		p := MaybePixelPtr(im, v);
		if Assigned(p) then result := Image.imagereadfunc(p, im.format) else result := storagedefault;
	end;} all_script_lookups

	class function GenerateByScriptOperation.ScriptState.l_image_index(L: lua.State): cint; cdecl;
	var
		p: pChar;
		im: pImage;
	begin
		p := lua.topchar(L, 2);
		result := 0;
		if Assigned(p) then
			case p[0] of
				'r':
					if (p[1] = 'g') and (p[2] = 'b') then
						case p[3] of
							#0: begin lua.pushcfunction(L, lua.CFunction(@ScriptState.l_image_rgb)); result := 1; end;
							'a': if p[4] = #0 then begin lua.pushcfunction(L, lua.CFunction(@ScriptState.l_image_rgba)); result := 1; end;
						end;
				'g':
					case p[1] of
						#0: begin lua.pushcfunction(L, lua.CFunction(@ScriptState.l_image_g)); result := 1; end;
						'a': if p[2] = #0 then begin lua.pushcfunction(L, lua.CFunction(@ScriptState.l_image_ga)); result := 1; end;
					end;
				'w':
					case p[1] of
						'h': if p[2] = #0 then begin im := SelfToImageUnchecked(L); PushVec2(L, Vec2.Make(im^.w, im^.h)); result := 1; end;
					end;
				'h': if p[1] = #0 then begin lua.pushnumber(L, SelfToImageUnchecked(L)^.h); result := 1; end;
			end;
		if result = 0 then lua.throw(L, 'image.{}'.Format([HumanValue(L, 2)]));
	end;

{$define lookupf :=
	class function GenerateByScriptOperation.ScriptState.bindinglookupfunc(L: lua.State): cint; cdecl;
	var
		vArgs: uint;
		v: Vec2;
	begin
		v := ArgVec2(L, 2, vArgs, 'image::' + scriptlookupname);
		result := {$if chans = 1} 1; lua.pushnumber {$elseif chans = 2} PushArgVec2 {$elseif chans = 3} PushArgVec3 {$else} PushArgVec4 {$endif} (L,
			lookupfunc(SelfToImage(L, 'image::' + scriptlookupname)^, v)
			{$if chans > 1}, vArgs > 1 {$endif});
	end;} all_script_lookups

type
	Application = object
		ir: ImageRegistry;
		tasks: array of GenericOp;
		lastSpec: ImageSpec;
		repl: boolean;

		procedure Init;
		procedure Done;
		function Execute(const input: string): boolean;
	end;

	procedure Application.Init;
	begin
		try
			lodepng.Load('{}lib\{}\lodepng.dll'.Format([Executable.Path, CPUArch]));
			lua.Load('{}lib\{}\lua.dll'.Format([Executable.Path, CPUArch]));
			ir.Init;
			lastSpec := ImageSpec.Make(768, 768, 1, ImageFormat.RGB);
		except
			Done;
			raise;
		end;
	end;

	procedure Application.Done;
	var
		i: SizeInt;
	begin
		for i := 0 to High(tasks) do tasks[i].Free(tasks[i]);
		tasks := nil;
		ir.Done;
		lua.Unload;
		lodepng.Unload;
	end;

	function Application.Execute(const input: string): boolean;
	begin
		result := true;
	end;

var
	app: Application;
	input: string;

begin
	try
		try
			app.Init;
			input := Win32.CommandLineTail;
			app.repl := input = '';
			if app.repl then Con.ColoredLine('<gb>Справка: ?');
			repeat
				if app.repl then
				begin
					Con.Colored('<.3>> ');
					input := Con.ReadLine;
				end;
			until not app.Execute(input) or not app.repl;
		except
			Con.ResetCtrlC;
			if Exception.Current is Interception then
				if app.repl then begin Con.Colored('<gb>' + Exception.Message); if app.repl then Con.ReadLine; end else
			else begin Con.Colored('<R>' + Con.Escape(Exception.Message)); if app.repl then Con.ReadLine; end;
		end;
	finally
		app.Done;
	end;
end.
