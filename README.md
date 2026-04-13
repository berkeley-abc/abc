# ABC: System for Sequential Logic Synthesis and Formal Verification

[![ci](https://github.com/sarnold/abc-fork/actions/workflows/ci.yml/badge.svg)](https://github.com/sarnold/abc-fork/actions/workflows/ci.yml)
[![msystem](https://github.com/sarnold/abc-fork/actions/workflows/win.yml/badge.svg)](https://github.com/sarnold/abc-fork/actions/workflows/win.yml)
[![CondaDev](https://github.com/sarnold/abc-fork/actions/workflows/conda-dev.yml/badge.svg)](https://github.com/sarnold/abc-fork/actions/workflows/conda-dev.yml)

[![.github/workflows/build-posix.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-posix.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-posix.yml)
[![.github/workflows/build-windows.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-windows.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-windows.yml)
[![.github/workflows/build-posix-cmake.yml](https://github.com/berkeley-abc/abc/actions/workflows/build-posix-cmake.yml/badge.svg)](https://github.com/berkeley-abc/abc/actions/workflows/build-posix-cmake.yml)

## Requirements:

ABC is always changing but the current snapshot is believed to be stable.

## ABC fork with new features

Here is a [fork](https://github.com/yongshiwo/abc.git) of ABC containing Agdmap, a novel technology mapper for LUT-based FPGAs.  Agdmap is based on a technology mapping algorithm with adaptive gate decomposition [1]. It is a cut enumeration based mapping algorithm with bin packing for simultaneous wide gate decomposition, which is a patent pending technology.

The mapper is developed and maintained by Longfei Fan and Prof. Chang Wu at Fudan University in Shanghai, China.  The experimental results presented in [1] indicate that Agdmap can substantially improve area (by 10% or more) when compared against the best LUT mapping solutions in ABC, such as command "if".

The source code is provided for research and evaluation only. For commercial usage, please contact Prof. Chang Wu at wuchang@fudan.edu.cn.

References:

[1] L. Fan and C. Wu, "FPGA technology mapping with adaptive gate decompostion", ACM/SIGDA FPGA International Symposium on FPGAs, 2023.

Minimum desktop tools needed:

 * A recent toolchain for your platform: GNU/Clang/Xcode, MSVC/MSYS
 * Make and/or CMake/Ninja: the latter can be installed via Tox

Optional:

 * libstdc++
 * readline/ncurses
 * pthreads
 * If using Tox, a recent Python for your platform
 * If using Conda, install `conda-devenv` and use the `environment.devenv.yml` file

ABC can be built in multiple ways on each platform; see the github workflow
files for specific build methods and tools/packages. The easiest (local) build
workflow is to install a toolchain, make utilities, and Tox using your system
package manager; you *can* build from source on MacOS/Windows using the usual
developer tools, ie, Apple Xcode or Windows Visual Studio tools (as shown in
the `ci.yml` workflow and `tox.ini` files).

For non-Linux platforms, if you don't have tools installed yet, an (extra)
package manager should be used to install GNU tools and dependencies. Note
this is exactly what the Github workflow runners use:

 * Windows: `Chocolatey` or `MSYS2`
 * MacOS: `brew`

### Build and test with Tox

With at least Python 3.6 installed, install [![tox](tox)](https://github.com/tox-dev/tox)

After cloning the repository, you can run the current tests using either
cmake or (just) make with the `tox` command.  Tox will build a virtual
python environment with most of the build dependencies (except the shared
libraries above) and then run the tests. For cmake plus a simple unittest,
run something like the following:

    $ git clone https://github.com/berkeley-abc/abc.git
    $ cd abc/
    $ tox -e ctest

Note for some Tox targets, eg `demo` and `clang`, both `CC` and `CXX` should
either be set in the shell environment or passed on the command line, eg:

    $ CC=gcc CXX=g++ tox -e abc,demo  --or--
    $ CC=clang CXX=clang++ tox -e clang

There are several `tox -e` environment commands available in the current tox file:

* Make-based args:
  * `abc` - run make build => abc executable and static lib
  * `soname` - run make build => shared lib with soname
  * `tests` - build/run abc executable as simple test
  * `demo` - build/run demo executable against static lib using make
* CMake-based args:
  * `base` - run cmake Release build with namespace and staging dir install
  * `build` - run cmake Debug build with shared libs, namespace, soname, LTO
  * `clang` - run cmake RelWithDebInfo build with clang/LLVM source coverage, namespace, static lib
  * `ctest` - build/run tests using ctest => static lib and "test" executable
  * `grind` - run cmake Debug build with valgrind
* Misc utility commands:
  * `clean` - clean the automake/autoconf build byproducts
  * `cclean` - clean the cmake build/ directory/files
  * `lint` - run cpplint style checks

### Compiling manually:

To compile ABC as a binary, clone/download and unzip the code, then type `make`.
To compile ABC as a static library, type `make libabc.a`.
To compile ABC as a shared library, type `make lib`.
To compile ABC as a shared library with soname, type `ABC_USE_SONAME=1 make lib`.

When ABC is used as a static library, two additional procedures, `Abc_Start()`
and `Abc_Stop()`, are provided for starting and quitting the ABC framework in
the calling application. A simple demo program (file src/demo.c) shows how to
create a stand-alone program performing DAG-aware AIG rewriting, by calling
APIs of ABC compiled as a static library.

To build the demo program

 * Copy demo.c and libabc.a to the working directory
 * Run `gcc -Wall -g -c demo.c -o demo.o`
 * Run `g++ -g -o demo demo.o libabc.a -lm -ldl -lreadline -lpthread`

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

## Compiling as C or C++

The current version of ABC can be compiled with C compiler or C++ compiler.

 * To compile as C code (default): make sure that `CC=gcc` and `ABC_NAMESPACE` is not defined.
 * To compile as C++ code without namespaces: make sure that `CC=g++` and `ABC_NAMESPACE` is not
   defined (deprecated).
 * To compile as C++ code with namespaces: make sure that `CC=g++` and `ABC_NAMESPACE` is set to
   the name of the requested namespace. For example, add `-DABC_NAMESPACE=xxx` to OPTFLAGS.

## Building a shared library

 * Compile the code as position-independent by adding `ABC_USE_PIC=1`.
 * Build the `libabc.so` target:

     make ABC_USE_PIC=1 lib

## Adding new source files

For each module with new sources:

 * Add new source files to the corresponding `module.make` file
 * Run `tools/mk-cmakelists.py` and then `git diff` to review changes
 * Make sure new object files exist in your build

## Bug reporting:

Please try to reproduce all the reported bugs and unexpected features using the latest
version of ABC available from https://github.com/berkeley-abc/abc

If the bug still persists, please provide the following information:

 1. ABC version (when it was downloaded from GitHub)
 1. Linux distribution and version (32-bit or 64-bit)
 1. The exact command-line and error message when trying to run the tool
 1. The output of the `ldd` command run on the exeutable (e.g. `ldd abc`).
 1. Versions of relevant tools or packages used.


## Troubleshooting:

 1. If compilation does not start because of the cyclic dependency check,
try touching all files as follows: `find ./ -type f -exec touch "{}" \;`
 1. If compilation fails because readline is missing, install 'readline' library or
compile with `make ABC_USE_NO_READLINE=1`
 1. If compilation fails because pthreads are missing, install 'pthread' library or
compile with `make ABC_USE_NO_PTHREADS=1`
    * See http://sourceware.org/pthreads-win32/ for pthreads on Windows
    * Precompiled DLLs are available from ftp://sourceware.org/pub/pthreads-win32/dll-latest
 1. If compilation fails in file "src/base/main/libSupport.c", try the following:
    * Remove "src/base/main/libSupport.c" from "src/base/main/module.make"
    * Comment out calls to `Libs_Init()` and `Libs_End()` in "src/base/main/mainInit.c"
 1. On some systems, readline requires adding '-lcurses' to Makefile.

The following comment was added by Krish Sundaresan:

"I found that the code does compile correctly on Solaris if gcc is used (instead of
g++ that I was using for some reason). Also readline which is not available by default
on most Sol10 systems, needs to be installed. I downloaded the readline-5.2 package
from sunfreeware.com and installed it locally. Also modified CFLAGS to add the local
include files for readline and LIBS to add the local libreadline.a. Perhaps you can
add these steps in the readme to help folks compiling this on Solaris."

The following tutorial is kindly offered by Ana Petkovska from EPFL:
https://www.dropbox.com/s/qrl9svlf0ylxy8p/ABC_GettingStarted.pdf

## Final remarks:

Unfortunately, there is no comprehensive regression test. Good luck!

This system is maintained by Alan Mishchenko <alanmi@berkeley.edu>. Consider also
using ZZ framework developed by Niklas Een: https://bitbucket.org/niklaseen/abc-zz (or https://github.com/berkeley-abc/abc-zz)
