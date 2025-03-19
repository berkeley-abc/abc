#!/usr/bin/env python
import os
from pathlib import Path

s = """abc_libabc_add_sources(
    NAME {NAME}
    SOURCES
{SOURCES}
)
"""
for root, _, files in os.walk("src"):
    if "module.make" not in files:
        continue
    if "main" in root:
        continue
    r = Path(root).relative_to("src")
    makefile = open(Path(root)/"module.make").read()
    target = str(r).replace("/","_")
    sources = list(filter(lambda s: s in makefile, files))
    if sources:
        sources_str = "\n".join("        {}".format(source) for source in sources)
        txt = s.format(NAME=target, SOURCES=sources_str)
    else:
        txt = ""
    cmake = Path(root) / "CMakeLists.txt"
    cmake.open("w").write(txt)
