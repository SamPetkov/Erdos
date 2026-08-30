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

- local source modules: 480;
- external Mathlib imports: 86;
- lines: 89,528;
- normalized-LF SHA-256: `53060b9563330f20a5f2133ffdf8f56e5a41eae6d0f772487193d9c54133e837`.

The top-level theorem is `Erdos625.erdos625 : Erdos625Statement`. Its printed
axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`.
The current file is byte-identical to the standalone file at source commit
`824e4b609466d2e26b216a76ecf103184dac2663`.
