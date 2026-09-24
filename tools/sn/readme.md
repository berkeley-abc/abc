# Optional SystemVerilog frontend

ABC can build a companion `sn` executable without linking Slang into ABC. Ordinary `make` builds are unchanged.
The companion is currently supported on Linux and macOS and requires Git, CMake 3.28 or newer, and a C++20 compiler.
ABC retains its existing compiler and platform requirements.

```sh
git clone https://github.com/berkeley-abc/abc.git
cd abc
make -j10 ABC_USE_SLANG=1
./abc -c "@slang counter.v; @check; @ps -v"
```

The first optional build downloads the pinned Slang revision and its dependencies. Both executables are placed in
the ABC working directory. Later builds are incremental. Building begins with ABC, then runs the companion build
using the Make job count. `SLANG_JOBS=10` explicitly sets the companion's parallelism.
The Make companion cache is under `build/sn-slang-make/`; it is separate from the CMake companion cache.

An existing Slang checkout can be supplied, and the companion can use a different compiler:

```sh
make -j10 ABC_USE_SLANG=1 SLANG_SOURCE_DIR=../slang SLANG_CXX=clang++
```

The default Slang revision is pinned in `tools/sn/CMakeLists.txt`. An existing checkout is used as supplied.
Slang may still download its own dependencies unless these are already cached or provided locally.

The CMake build also supports the companion. It is built independently after ABC, without changing ABC's language
standard or compiler flags. Both executables are placed beside each other in the ABC build output directory.

```sh
cmake -S . -B build-bundle -DABC_USE_SLANG=ON -DSLANG_JOBS=10 -DCMAKE_BUILD_TYPE=Release
cmake --build build-bundle -j10
./build-bundle/abc -c "@slang counter.v; @check; @ps -v"
```

Use `-DSLANG_SOURCE_DIR=/path/to/slang` and `-DSLANG_CXX_COMPILER=/path/to/c++` to override dependencies/compiler.
Windows builds compile the Slang-independent SN package as part of ABC but do not build the optional companion.
They can read and process `.sn` files produced on a supported host. `ABC_USE_SLANG=ON` is rejected explicitly on Windows.
HDL loading through `@slang`, `&cec`, or `&sec` reports an unsupported-platform error there without launching a companion.

The checked-in `counter.v` is a compact smoke test. Its sequential 4-bit `counter` top instantiates the
combinational 4-bit `adder`, exercising arithmetic lowering, register inference, instance connectivity and hierarchy.
The unique top is inferred automatically; use `-M module` when sources contain multiple possible tops. The command
above checks the imported SN design and prints the `counter` -> `adder` hierarchy.

The standalone companion accepts one-letter options (`./sn -h` prints its full usage). For example,
`./sn -M counter -p -o counter.sn counter.v` writes a binary while retaining otherwise removable state.
Its argument options are `-M` top, repeatable `-D` define, `-B` declared black box, `-L` Liberty model,
`-I` include directory, `-F` library source, `-C` Liberty cache directory, `-P` output port-layout JSON,
and `-o` output SN file. Boolean options are `-e` (empty modules are black boxes), `-a` (infer memory only
from attributes), `-g` (metadata), `-i`/`-r` (ignore/reject assertions), `-s`/`-u` (reject/allow unknown
modules), `-p` (preserve state), and `-t` (timing). In the companion, `-I` now means include directory;
the former ignore-assertions meaning is `-i`. ABC's `&cec -I` is a separate instance-cut option.

`@slang` looks for the frontend in this order:

1. An explicit `set sn /path/to/sn` setting.
2. An executable named `sn` beside the running ABC executable.
3. An executable of that name in `PATH`.

The companion is found independently of the current working directory. An explicit setting takes precedence; a
failed frontend invocation is reported rather than retried with another version. To distribute a binary bundle,
keep both executables together and include the applicable license notices. Build binaries for the target OS and ABI.

The frontend uses Mike Popoloski's [Slang](https://github.com/MikePopoloski/slang), whose SystemVerilog parsing and
elaboration provide the foundation for this work. We gratefully acknowledge Mike and the Slang contributors.

Several semantic abstractions and improvement priorities in this implementation were inspired by Martin Povišer's
[sv-elab](https://github.com/povik/sv-elab) project, which provided valuable ideas for lvalue analysis, procedural
state, timing-pattern recognition, memory eligibility, addressing, resolved nets, and diagnostics. Warm thanks to
Martin for saving us from discovering many of SystemVerilog's sharp edges the hard way. The SN representation and
lowering implementation are developed independently.

We also thank [Yosys](https://github.com/YosysHQ/yosys) and its contributors for an exemplary synthesis flow.
Its approaches to elaboration, technology mapping, and other synthesis problems have been valuable examples
from which we have learned while developing SN.
