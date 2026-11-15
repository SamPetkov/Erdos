# Self-contained Lean build

`Erdos625SelfContained.lean` is generated deterministically from the complete
local import closure of `Erdos625.lean`. It contains no local import commands;
the only remaining imports are external Mathlib modules supplied by the pinned
toolchain. Thus the artifact is standalone with respect to this project, not
with respect to Lean or Mathlib.

```text
lake exe cache get
python scripts/generate_self_contained.py --check
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

Generated source metrics:

- local source modules: 483;
- external Mathlib imports: 86;
- lines: 91,243;
- normalized-LF SHA-256: `bbbfd1867af9996e2aa058defc5bbc020319a5967e5e8b86e693c60f01ee3368`.

The top-level theorem is
`Erdos625.erdos625 : Erdos625.Erdos625Statement`. Its printed axiom closure
contains only `propext`, `Classical.choice`, and `Quot.sound`.
The file also contains the three five-size phase-gain modules described in
`README.md`. Apart from those modules and the root module's added imports and
documentation, it is identical to the standalone file at source commit
`824e4b609466d2e26b216a76ecf103184dac2663`.
