# Integration validation

Base: upstream ABC `0aabbb13f4a10cd8dc9c96ae3c743ec8fc3045a7`.
The integration was checked on macOS arm64 with Apple Clang, using both the
CMake Release build and the normal Make build (`-O2 -g`, assertions enabled).
Readline was disabled for these builds.

| Check | Result |
|---|---:|
| Final compact TG, step 0.28, retained EPFL endpoints | 20/20 identical AIG payloads |
| Two-round PA recipe, step 0.28, retained EPFL endpoints | 20/20 identical AIG payloads |
| TG step sensitivity, 0.26 and 0.30 | 12/12 identical AIG payloads |
| Direct endpoint CEC, eight designs per flow | 16/16 equivalent |
| Integration regression script, Release build | 35/35 passed |
| Integration regression script, assertion-enabled Make build | 35/35 passed |
| Ordinary ABC synthesis versus unmodified upstream | Identical AIG payload |
| Retained PA regression | 30 CEC, 24 edge, 20 input/state cases passed |
| PA private AIG manager and copied helpers | Layout and seven helpers match upstream |

The 20-design endpoint checks include `hyp`. The sensitivity checks use the same
six designs at both steps: `ctrl`, `int2float`, `log2`, `router`, `sqrt`, and
`voter`. Direct CEC covers `adder`, `ctrl`, `int2float`, `log2`, `router`, `sin`,
`sqrt`, and `voter` for each flow. The remaining endpoints were checked for exact
payload reproduction, not independently re-proved in this cleanup pass.

`test/physical/endpoint_manifest.json` records the input, library, and canonical
endpoint hashes. A payload comparison includes the AIGER header, outputs,
and AND encoding, while excluding symbol/comment trailers. TG includes the
paper flow's final `strash`; applying another `strash` can change serialization
order and is not the endpoint recipe used here. The PA recipe includes its
explicit final normalization. The maintained PA timing-dependency fixes were
retained and still reproduce all 20 saved PA endpoints.

The regression script exercises repeated calls, rereading networks, undo,
TG-to-native and TG/PA handoffs, immediate mapping, mapped PA placement transfer,
cluster-aware PA rewriting/refactoring, invalid arguments, and CEC of each
successful endpoint. It requires only Python's standard library and ABC's
included demonstration Liberty file.

These checks validate source cleanup, functional handoff, and reproduction of
the retained AIGs. Build/test timings collected during integration are not
performance measurements. Mapped QoR and physical-backend results were not
rerun against the newer upstream mapper; reproducing historical PPA additionally
requires the archived mapping/backend versions and physical setup.
