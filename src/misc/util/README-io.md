# Experimental output routing

`ABC_USE_STDIO_REDIRECT` evaluates a small alternative to changing every ABC
printing call. It is OFF by default. The implementation uses C and the existing
optional pthread support; it adds no external runtime dependency.

Build in a separate directory (do not mix enabled/disabled Make objects):

```
cmake -S . -B build/io-route -DABC_USE_STDIO_REDIRECT=ON -DABC_SKIP_TESTS=ON
cmake --build build/io-route --parallel 4
```

For a fresh Make build, use `make -j4 ABC_USE_STDIO_REDIRECT=1`.
On Windows, the MSBuild project templates accept
`/p:ABC_USE_STDIO_REDIRECT=1`; omitting it keeps capture disabled. This applies
MSVC's `/FI` to ABC's source files. Windows uses the existing thread-local
frame support and bundled pthread library for worker inheritance.
Native Windows and macOS CI results must still be reviewed before merging;
implementing support and configuring a workflow do not establish validation.

## Integration

The build force-includes `abc_stdio.h` only for ABC's translation units.
CMake marks the option PRIVATE, including for the static and PIC libraries.
Neither `abc_global.h` nor standalone headers include this private header.
The host application retains its own libc calls. `abc_io.h` declares the small
routing interface without redefining standard names.
The forced header reads the Windows CRT's extra declarations and the C++ file
stream definitions before installing macros. This leaves standard-library
declarations and qualified stdio calls inside file streams untouched.
Each routed print resolves its destination with a thread-local frame lookup;
it does not cache a frame across commands or nested entry scopes.

`utilIo.c` selects the current frame's output without creating a frame. With no
frame, it uses inherited worker streams, then the real standard streams. It
wraps printf/fprintf, their va_list forms, string/character/block output,
perror, and fflush. A NULL fflush argument keeps libc's flush-all semantics.
Ordinary FILE arguments pass through. Function-like macros leave format
attributes alone, and wrappers retain compiler format checking.

Small compatibility adjustments are needed: SN's existing POSIX feature
selection is also passed on the compile command, ahead of the forced header;
the fret package explicitly undefines vprintf before installing its unrelated
legacy verbosity shorthand (which still calls the routed printf). Six bundled
BDD printing calls keep conditional directives outside the argument lists so
MSVC can expand the interception macros. Their formats and arguments are unchanged.

The standard stream macros themselves are unchanged. In ordinary frames, bridge
mode bypasses routing: protocol headers and direct descriptor writes must use
the same channel. An instance created with a private log cannot enable bridge
mode or replace its output streams. A rejected bridge-mode request writes a
diagnostic to the captured frame's error stream.

For an embedded invocation:

```c
Abc_Frame_t * p = Abc_FrameCreateWithLog();
Abc_Frame_t * pPrevious;
if ( p == NULL )
    return;  // Capture is unavailable, or the temporary file could not be opened.
pPrevious = Abc_FrameEnter( p );
Cmd_CommandExecute( p, "read_blif example.blif; strash; print_stats" );
Abc_FrameLeave( pPrevious );
// Optional: save the combined stdout/stderr log; check the return value.
if ( !Abc_FrameCopyLog( p, output_file ) )
{
    // Handle an I/O error in the host.
}
Abc_FrameDestroy( p );
```

Each captured frame owns a temporary binary file from initialization through
destruction. POSIX uses `tmpfile()`. Windows uses its temporary directory and
opens the file with delete-on-close and no-inherit flags, avoiding the CRT's
drive-root temporary-file permission requirement. Normal output and errors share
this file. The host may copy it,
using `Abc_FrameCopyLog`, or simply discard it by destroying the frame. Copying
preserves the log's write position, so more commands can run afterward. It copies
bytes to the supplied FILE without routing them back into ABC. It returns 1 on
success and 0 on failure. Call it only after commands and workers have finished.
The output file used for the copy belongs to the host. Open that destination in
binary mode on Windows if exact byte preservation is required.

Capture is explicit: `Abc_FrameCreate()` and the normal CLI still print normally,
including when commands use worker threads. `Abc_FrameCreateWithLog()` returns
NULL with `errno == ENOSYS` in a build without routing or thread-local storage.
Log-creation failures set errno without creating a frame; CRT errors are
preserved, and Windows path-creation errors use EIO. It never silently creates a
partially captured instance. `Abc_FrameHasLog()` tests this property.

Create/destroy frames serially and leave every entered scope before destroying
its frame. Run at most one command at a time on a given frame. Independent
frames can have independent logs, and nested entry restores the previous
destination. This change does not establish concurrent safety of all of ABC's
initialization or algorithms.

The new `Abc_FrameSetOutputStreams(p, out, err)` interface accepts borrowed
streams for ordinary frames; keep them open until
commands and workers finish. NULL restores the corresponding standard stream.
The setter returns 0 with `errno == EBUSY` for a captured frame, and 1 otherwise.
Likewise, `set abcout` and `set abcerr` cannot redirect a captured frame's log.

The set command opens its replacement before releasing the previous stream, so
failure diagnostics never use a closed FILE. Frame ownership fields distinguish
command-opened files from host-owned files. Replaced command files are closed,
retained/shared files remain open, and final frame destruction closes command
files. These cleanup fixes also apply with interception disabled.

The pthread_create wrapper copies only the resolved output/error pointers into
the new worker. It does not share the parent's frame. eSLIM and RRR's
`std::thread` launch sites explicitly inherit the same destinations through
`Abc_IoSetWorkerStreams`. A worker's default console streams retain inherited
capture even if it creates a lazy default frame; an explicitly selected file
or captured frame takes precedence. Streams must remain open and unchanged
until these workers have joined. Long-lived pools need explicit per-task
propagation if reused across output contexts.

## C++ diagnostics

Existing C++ console output now ends in the same C stdio path. Simple output
uses unqualified printf/fprintf calls. `abc_print.h` provides a small helper for
container, bitset and manipulator formatting: a local `ostringstream` builds
the message, then one fwrite emits its bytes. This preserves typed formatting
and embedded zero bytes without using shared cout/cerr state. Formatting into
ordinary files or caller-supplied C++ streams remains unchanged.

This covers eSLIM/eSLIM2, RRR, transduction, prefix generation, ACD, UFAR/UNTK
and their logging helpers. There are no new runtime dependencies; C++ remains
needed only for the packages already implemented in C++. Development scripts
are local test aids and are not required to build or run ABC.

## Regression tests and native platform validation

The standalone C/C++ tests in `test/io/` need no Python, GoogleTest or downloaded
test framework. They use CTest and the existing pthread support. Enable
them explicitly; normal builds do not compile them:

```
cmake -S . -B build/io-test -DCMAKE_BUILD_TYPE=Release \
  -DREADLINE_FOUND=FALSE -DABC_SKIP_TESTS=ON \
  -DABC_BUILD_IO_TESTS=ON -DABC_USE_STDIO_REDIRECT=ON
cmake --build build/io-test --target abc_io_test --parallel 4
ctest --test-dir build/io-test --output-on-failure -R '^io_routing$'
```

Use a separate build directory and `-DABC_USE_STDIO_REDIRECT=OFF` to test ordinary
output and explicit refusal of unsupported capture. Add
`-DABC_USE_NAMESPACE=abc_io_test_namespace` to test the namespace C++ build.
Builds without pthreads skip this test target.

Windows CI builds ABC using the existing MSBuild solution, then builds these
same tests against its library. From an x86 MSVC developer command prompt, after generating
the solution/project files as in `.github/workflows/build-windows.yml`:

```
msbuild abcspace.sln /m:4 /p:Configuration=Release /p:Platform=Win32 /p:ABC_USE_STDIO_REDIRECT=1
cmake -S test/io -B build-io -A Win32 -T v143 -DABC_IO_LIBRARY="%CD%/lib/abcr.lib" -DABC_USE_STDIO_REDIRECT=ON
cmake --build build-io --config Release --parallel 4
ctest --test-dir build-io -C Release --output-on-failure -R "^io_routing$"
```

Use matching capture settings in the library and test configurations. The tests
check the library's reported capability, so a mismatch fails. The standalone
configuration links the bundled pthread library and copies its DLL beside the
test executable. It does not force-include the interception header in the host
driver; only the C/C++ emitters receive it.

The tests check independent concurrent logs, C and C++ worker inheritance,
RRR/eSLIM/eSLIM2 worker commands, nested frame scopes, combined normal/error
output, host printf isolation, ordinary file destinations, binary-safe copying,
copy-then-append, rejected log replacement, and log closure on destruction.
An uncaptured frame and its workers must print normally with capture ON or OFF.
Both modes also check that borrowed files remain open and command-owned files
close on replacement or frame destruction.
Windows additionally checks failed temporary-file creation and non-inherited
private log handles. Binary tests cover embedded zero, CRLF and Ctrl-Z bytes;
only the console transcript normalizes Windows line endings.
CTest checks the entire host stdout/stderr streams, so escaping captured output
fails the test. All checks remain active with `NDEBUG`.

`.github/workflows/io-routing.yml` runs these tests on native macOS and Ubuntu,
with capture ON/OFF and ordinary/namespace builds (eight configurations).
`.github/workflows/build-windows.yml` runs the existing x86 MSVC build and CLI
checks plus the logging tests, with capture OFF and ON (two configurations).
The existing POSIX build workflows are unchanged. Native results must be
reviewed before merging; adding workflows is not itself a successful native
platform validation.
The Ubuntu capture-ON, ordinary-build leg also builds with
`make -j4 ABC_USE_STDIO_REDIRECT=1 ABC_USE_NO_READLINE=1 abc` and checks that
`set abcout` redirects `print_stats` to a file in that executable.

## Limits of transparent interception

- New code must use the routed C stdio path or the C++ formatting helper.
  Direct cout/cerr/clog writes would bypass capture. Use unqualified printf,
  not `std::printf`, inside ABC: the private macros do not work with a `std::`
  prefix. Host calls are unaffected. System C/C++ stdio headers are included
  before macros are installed.
- A FILE equal to stdout or stderr denotes the corresponding logical channel.
  This is ambiguous when explicitly cross-assigning native streams, for example
  setting a frame's Err to stdout while Out points to a file: printf and an
  fprintf using that Err cannot both infer the original intent. Use nonstandard
  FILE destinations for borrowed capture. Owned private logs avoid this
  ambiguity. This remains a compatibility issue for legacy stream redirection,
  including `set abcerr -` combined with redirected abcout.
- A parenthesized `(fprintf)(...)` explicitly calls libc without redirection;
  taking a libc function's address also bypasses the function-like macro.
- Raw descriptor writes, externally compiled plugins, subprocesses and new
  thread launch sites without inheritance are not automatically captured.
  A host thread can enter its own ABC frame normally.
- This is output routing, not a guarantee that all synthesis packages can run
  concurrently. Shared destinations can interleave complete printing calls.

The portable regression suite above is included for reviewers and CI. Additional
local evaluation harnesses and build logs are in `temp/io-routing/` (initial
prototype), `temp/io-owned/` (owned logs and C++ conversion), and `temp/io-pr/`
(portable tests and PR preparation); these directories are not part of the
proposed PR. `temp/io-windows/` records the earlier Windows-disabled experiment;
`temp/io-win-support/` records the subsequent Windows implementation and local
checks. Native MSVC/Windows and macOS results remain pending until CI runs.
