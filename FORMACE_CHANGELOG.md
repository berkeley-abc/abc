# ForMACE Change Log

This file records ForMACE-specific changes made in this ABC fork.

## 2026-07-27

- Recreated the ForMACE extension setup in `abc_formace_ext`.
- Added project rules in `FORMACE_RULES.md`.
- Added this change log in `FORMACE_CHANGELOG.md`.
- Added experimental extension directory `src/extformace_ext/`.
- Added `src/extformace_ext/module.make` so ABC's Makefile can build the extension module.
- Added `src/extformace_ext/formace.c` with a self-registering `fm_summary` command.
- The extension registers through `Abc_FrameAddInitializer()` from inside `src/extformace_ext/formace.c`, avoiding direct edits to original ABC source files.
- Added `upstream` remote pointing to `https://github.com/berkeley-abc/abc.git`; kept `origin` as `git@github.com:elvis517/abc_formace_ext.git`.
- Set `upstream` push URL to `DISABLED` to avoid accidental pushes to Berkeley ABC.
- Built ABC successfully with `make -j4 ABC_USE_NO_READLINE=1`.
- Verified the extension command with `./abc -c "read i10.aig; fm_summary -v"`.
- Verified command usage with `./abc -c "fm_summary -h"`.

## Build And Verification Notes

- First full ABC builds can take several minutes.
- Prefer incremental builds after editing only `src/extformace_ext/`.
- Suggested build command:

```bash
make -j4 ABC_USE_NO_READLINE=1
```

- Latest successful sample output:

```text
ForMACE summary for "i10":
  pi      = 257
  po      = 224
  latches = 0
  nodes   = 2675
  levels  = 50
  objects = 3157
  type    = strashed AIG
  seq     = combinational
```
