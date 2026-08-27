# Self-contained Lean build

`Erdos625SelfContained.lean` is generated deterministically from the local
import closure of `Erdos625.lean`.

```text
lake exe cache get
python scripts/generate_self_contained.py --check
lake env lean -DwarningAsError=true Erdos625SelfContained.lean
```

Generated source metrics:

- local source modules: 475;
- external Mathlib imports: 86;
- logical lines: 88,563;
- normalized-LF SHA-256: `0f54ac26285e5a1631ed62f0258ba0836cc3a2cd28cc35df3b2f737cfaffac30`.

The top-level theorem is `Erdos625.erdos625 : Erdos625Statement`. Its printed
axiom closure contains only `propext`, `Classical.choice`, and `Quot.sound`.
