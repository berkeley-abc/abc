# ForMACE ABC Extension Rules

This repository is the working ABC fork for ForMACE experiments. The GitHub
project is `abc_formace_ext`.

## Development Rules

- Prefer adding ForMACE work under `src/formace_ext/`.
- Avoid changing upstream ABC source files when an extension-only approach is possible.
- The top-level `Makefile` intentionally includes `src/formace_ext` in `MODULES` so the extension directory can be tracked normally by Git.
- Keep extension commands read-only unless the intended behavior is explicitly a network transform.
- Record every added file, modified file, build step, and verification result in `FORMACE_CHANGELOG.md`.
- Before committing, review `git status --short` and make sure unrelated local files are not included.
- Avoid putting ForMACE work under `src/ext*`; upstream ABC's `.gitignore` ignores that pattern.
- Keep the Berkeley ABC remote available as `upstream`.
- Keep the GitHub ForMACE fork as `origin`.

## Remote Layout

Recommended remotes:

```text
origin   git@github.com:elvis517/abc_formace_ext.git
upstream https://github.com/berkeley-abc/abc.git
```

The local `upstream` push URL should be set to `DISABLED` to avoid accidental
pushes to Berkeley ABC.

Useful commands:

```bash
git push origin master
git fetch upstream
```
