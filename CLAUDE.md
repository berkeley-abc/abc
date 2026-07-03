# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Berkeley ABC — a system for sequential logic synthesis and formal verification (EDA tool). Written in C (also compilable as C++17 with `-fno-exceptions`), maintained by Alan Mishchenko at UC Berkeley.

## Build

```bash
make -j$(nproc)              # builds the ./abc binary (ccache auto-detected)
make libabc.a                # static library (all objects minus src/base/main/main.o)
make ABC_USE_PIC=1 libabc.so # shared library
make clean
```

Useful make switches: `ABC_USE_NO_READLINE=1`, `ABC_USE_NO_PTHREADS=1`, `ABC_USE_NO_CUDD` (drops the BDD/CUDD modules), `ABC_USE_NAMESPACE=xxx` (compiles everything as C++ inside namespace `xxx`), `ABC_MAKE_VERBOSE=1`.

CMake build (this is the one that includes unit tests; generates `compile_commands.json`):

```bash
cmake -S . -B build -G Ninja
cmake --build build
```

Note: CMake shells out to `make cmake_info` to extract the source list and flags, so the Makefile is the source of truth for both builds.

## Run / smoke test

```bash
./abc                        # interactive shell
./abc -c "r i10.aig; b; ps; b; rw -l; rw -lz; b; rw -lz; b; ps; cec"   # batch mode; this is the CI smoke test
```

`cec` at the end proves the rewritten network is equivalent to the original — this is the standard way to sanity-check a synthesis change (there is no comprehensive regression suite).

## Tests

Unit tests exist only in the CMake build (GoogleTest, fetched automatically):

```bash
cd build && ctest                    # all tests
ctest -R gia_test --verbose          # single test binary
```

Test sources live in `test/` (currently just `test/gia/gia_test.cc`). New tests: add a subdirectory under `test/` with a `CMakeLists.txt`, link against `libabc` + `gtest_main`, use `gtest_discover_tests`.

## Architecture

### Two coexisting network representations

1. **"Old" ABC network** — `Abc_Ntk_t` / `Abc_Obj_t` (`src/base/abc/abc.h`). Feature-rich general graph; type is a combination of `Abc_NtkType_t` (netlist/logic/strash) × `Abc_NtkFunc_t` (SOP/BDD/AIG/MAP...). Used by classic commands (`b`, `rw`, `if`, ...), which operate on the frame's `pNtkCur`.
2. **GIA** — `Gia_Man_t` / `Gia_Obj_t` (`src/aig/gia/gia.h`). The modern lightweight array-based AIG built for scalability; `src/aig/gia/` is the largest package and hosts most modern algorithms.

Commands prefixed with `&` (the "ABC9" group, the largest command group) operate on the frame's current GIA (`pAbc->pGia`) instead of `pNtkCur`. Convert between the two with `&get` / `&put`. There is also the classic `Aig_Man_t` (`src/aig/aig/aig.h`) still used by many `src/opt` and `src/proof` engines.

### Command framework

- Global state lives in `Abc_Frame_t` (`src/base/main/mainInt.h`) — current network, current GIA and saved copies, flags.
- Entry point: `src/base/main/main.c` → `Abc_RealMain()` in `mainReal.c` → command loop via `Cmd_CommandExecute()` (`src/base/cmd/`).
- Every command handler has the signature `int Abc_CommandXxx(Abc_Frame_t *pAbc, int argc, char **argv)` and is registered with `Cmd_CommandAdd(pAbc, "<Group>", "<name>", Abc_CommandXxx, fChanges)` (`src/base/cmd/cmdApi.c`); `fChanges=1` means the command modifies the network (enables undo/backup).
- The central registry is `Abc_Init()` in `src/base/abci/abc.c` (~41k lines, ~570 commands). To add a command: write the handler (in `abc.c` or another `src/base/abci/*.c`), add its forward declaration near the top of `abc.c`, and add a `Cmd_CommandAdd` call in `Abc_Init`. `&`-command handlers typically read `pAbc->pGia`, run a `src/aig/gia/` algorithm, and install the result via `Abc_FrameUpdateGia()`.
- Packages can also self-register via init hooks called from `src/base/main/mainInit.c` (`Io_Init`, `If_Init`, ...) or the `Abc_FrameAddInitializer` mechanism.

### Source tree map

| Directory | Purpose |
|---|---|
| `src/base` | Old network core (`abc`), command implementations (`abci`), command interpreter (`cmd`), file I/O (`io`), frame/entry (`main`), Verilog parser (`ver`), word-level networks (`wlc`, `wln`) |
| `src/aig` | AIG packages: `gia` (modern), `aig` (classic), `saig`, `hop`, `ivy`, `ioa` (AIGER I/O), `miniaig` |
| `src/opt` | Synthesis engines: `rwr`/`rwt`/`dar` (rewriting), `res`/`mfs`/`sfm` (resubstitution/don't-cares), `ret`/`fret` (retiming), `cut`, `fxu`/`fxch`, ... |
| `src/map` | Technology mapping: `if` (priority-cut LUT mapper), `mio` (genlib), `scl` (liberty standard cells), `super`, `amap`, ... |
| `src/sat` | Embedded SAT solvers: `bsat` (default, MiniSAT-derived), `glucose`/`glucose2`, `kissat`, `cadical`, `satoko`, plus `cnf` (AIG→CNF) and `bmc` |
| `src/proof` | Verification: `pdr` (IC3), `cec`/`acec` (equivalence checking), `fra`/`fraig`, `ssw`, `abs`, `int`, `live` |
| `src/bool` | Boolean function manipulation: `kit` (truth tables), `bdc`, `dec`, `lucky`, ... |
| `src/bdd` | CUDD and BDD-based engines (optional, `ABC_USE_NO_CUDD` to exclude) |
| `src/misc` | Containers/utilities: `vec` (dynamic arrays used everywhere), `st`/`nm` (hash/name tables), `tim`, `mem`, bundled `zlib`/`bzlib` |

### Module system

Every leaf package directory has a `module.make` that appends its sources to `SRC`; the root `Makefile`'s `MODULES` list decides which packages are compiled. Adding a source file to an existing package = edit that package's `module.make`. Adding a new package = create `module.make` and add the directory to `MODULES` in the root `Makefile`.
