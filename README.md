[![.github/workflows/build-posix.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-posix.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-posix.yml)
[![.github/workflows/build-windows.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-windows.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-windows.yml)
[![.github/workflows/build-posix-cmake.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-posix-cmake.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-posix-cmake.yml)

# ABC: System for Sequential Logic Synthesis and Formal Verification

ABC is always changing but the current snapshot is believed to be stable.

## Compiling

To compile the ABC executable, run `make`. To compile ABC as a static library,
run `make libabc.a`.

When ABC is used as a static library, `Abc_Start()` and `Abc_Stop()` are
provided for starting and quitting a single ABC session in the calling
application. A simple demo program (file src/demo.c) shows how to
create a stand-alone program performing DAG-aware AIG rewriting, by calling 
APIs of ABC compiled as a static library.

Independent ABC sessions can run concurrently in different threads on Linux
and macOS. Existing single-threaded applications using `Abc_Start()` and
`Abc_Stop()` continue to work unchanged. Concurrent applications should create
one `Abc_Frame_t` per session with `Abc_FrameCreate()`, execute commands using
that frame, and release it with `Abc_FrameDestroy()`; the same frame must not be
used concurrently by multiple threads. Scoped calls to
`Abc_FrameEnter()`/`Abc_FrameLeave()` establish the current frame when invoking
APIs outside command execution that depend on it. See `src/runabc.c` for
single-threaded and concurrent embedding examples. Some obsolete commands still
use shared process state and are not safe to run in concurrent sessions.

Build and run the single-threaded demo from the repository root with:

```sh
gcc -Wall -O2 -c src/demo.c -o demo.o
g++ -o demo demo.o libabc.a -lm -ldl -lreadline -lpthread
./demo i10.aig
```

Build and run the MiniAIG/MiniLUT embedding example with:

```sh
gcc -Wall -O2 -Isrc -c src/runabc.c -o runabc.o
g++ -o runabc runabc.o libabc.a -lm -ldl -lreadline -lpthread
./runabc i10.aig
./runabc -t 4 i10.aig
```

The last command compares four concurrent sessions with a single-threaded
baseline. If ABC is built with `ABC_USE_NO_READLINE=1`, omit `-lreadline`.
Explicitly single-threaded configurations may disable thread-local frame
selection with `ABC_USE_NO_THREAD_LOCAL=1`.

To run the demo program, give it a file with the logic network in AIGER or BLIF. For example:

    [...] ~/abc> demo i10.aig
    i10          : i/o =  257/  224  lat =    0  and =   2396  lev = 37
    i10          : i/o =  257/  224  lat =    0  and =   1851  lev = 35
    Networks are equivalent.
    Reading =   0.00 sec   Rewriting =   0.18 sec   Verification =   0.41 sec

The same can be produced by running the binary in the command-line mode:

    [...] ~/abc> ./abc
    UC Berkeley, ABC 1.01 (compiled Oct  6 2012 19:05:18)
    abc 01> r i10.aig; b; ps; b; rw -l; rw -lz; b; rw -lz; b; ps; cec
    i10          : i/o =  257/  224  lat =    0  and =   2396  lev = 37
    i10          : i/o =  257/  224  lat =    0  and =   1851  lev = 35
    Networks are equivalent.

or in the batch mode:

    [...] ~/abc> ./abc -c "r i10.aig; b; ps; b; rw -l; rw -lz; b; rw -lz; b; ps; cec"
    ABC command line: "r i10.aig; b; ps; b; rw -l; rw -lz; b; rw -lz; b; ps; cec".
    i10          : i/o =  257/  224  lat =    0  and =   2396  lev = 37
    i10          : i/o =  257/  224  lat =    0  and =   1851  lev = 35
    Networks are equivalent.

### Compiling as C or C++

ABC can be compiled with a C or C++ compiler.

- To compile as C code, use the default Make configuration.
- To compile as C++ in a namespace, run `make ABC_USE_NAMESPACE=xxx`.

### Building a shared library

Build the shared library as position-independent code with:

```sh
make ABC_USE_PIC=1 libabc.so
```

### Building with CMake

ABC also supports CMake builds. The default CMake configuration builds the
executable and regression tests:

```sh
cmake -S . -B build
cmake --build build
ctest --test-dir build --output-on-failure
```

## Bug Reporting

Please reproduce bugs and unexpected behavior using the latest version of ABC
available from https://github.com/berkeley-abc/abc.

If the problem persists, provide the following information:

1. ABC version or Git commit.
2. Operating system, distribution, architecture, and compiler version.
3. The exact command line and complete error message.
4. The output of `ldd abc` on Linux, or the corresponding dependency report
   on another platform, when relevant.
5. Versions of relevant tools and libraries.

## Troubleshooting

1. If compilation does not start because of the cyclic dependency check, run
   `find . -type f -exec touch "{}" \;` and rebuild.
2. If readline is unavailable, install its development package or build with
   `make ABC_USE_NO_READLINE=1`.
3. If pthreads are unavailable, build without pthread support using
   `make ABC_USE_NO_PTHREADS=1`. Concurrent embedding requires pthread support.
4. On systems where readline depends on curses, include the appropriate curses
   library in `ABC_READLINE_LIBRARIES`.

The following tutorial is kindly offered by Ana Petkovska from EPFL:
https://www.dropbox.com/s/qrl9svlf0ylxy8p/ABC_GettingStarted.pdf

## Placement-aware synthesis

This branch includes the adaptive geometric restructuring (AGR) flow and the prior PA flow as separate
extensions. See [the physical synthesis guide](examples/physical/README.md) for
build instructions, both reproduction recipes, source organization, and checks.
AGR uses `agr`; PA retains its `pa_place`, `pa_rw`, `pa_rf`, `pa_rs`, and `pa_strash`
commands. Ordinary ABC synthesis and mapping commands remain unchanged.

## Final Remarks

ABC includes CMake-based regression tests, which run in continuous integration
on supported configurations. The suite is not exhaustive, so bug reports
should include a small reproducer whenever possible.

This system is maintained by Alan Mishchenko <alanmi@berkeley.edu>. Consider also 
using ZZ framework developed by Niklas Een: https://bitbucket.org/niklaseen/abc-zz (or https://github.com/berkeley-abc/abc-zz)
