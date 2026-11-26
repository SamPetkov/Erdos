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

## `Erdos625HPSelfContained.lean` (v3 auxiliary closure)

`Erdos625HPSelfContained.lean` is generated deterministically from the complete
local import closure of `Erdos625HP.lean` (which includes `Erdos625.lean`, the
two `Erdos625/HPRoute*` modules, and all 26 modules in `Erdos625HP/`, ending
with `Erdos625HP/AxiomAudit.lean`):

```text
lake exe cache get
python scripts/generate_hp_self_contained.py --check
lake env lean -DwarningAsError=true Erdos625HPSelfContained.lean
```

Generated source metrics:

- local source modules: 512 (485 under `Erdos625` + 27 under `Erdos625HP`, i.e. 26 in `Erdos625HP/` + root `Erdos625HP.lean`);
- external Lean/Mathlib imports: 89 (`Lean.LibrarySuggestions.Basic` + 88 `Mathlib` modules);
- lines: 148,633 (`7,256,871` bytes);
- normalized-LF SHA-256: `1db40bfe653ca42ef3d91640ed0eb748433e8958dc61276586af99aaa7a3e2ad`;
- from-scratch verification transcripts: `STANDALONE_512_CLEAN_LEANPATH.log` (local single-threaded standalone compile of all 512 modules exiting `0` in `1217.7s` under `lean -DwarningAsError=true` with external-only `LEAN_PATH` — `9` `.lake/packages` entries, zero project `.olean` directories — `0` warnings/errors, and unclipped `251`-declaration `Erdos625HP/AxiomAudit.lean` `#print axioms` output out of `1,954` total `#print axioms` outputs across the file (`1,950` `depends on axioms` + `4` constructive `does not depend on any axioms`), including zero-hypothesis `Erdos625HP.erdos625_phaseRefinement_unconditional` and `Erdos625HP.erdos625_mainTheorem_unconditional`; stdout also includes informational `ring_nf` hints from upstream `Erdos625` modules and nonfatal `Linarith.normalizeDenominatorsLHS` preprocessor trace lines) and `PROCIDA_STANDALONE_69570.log` (earlier `510`-module `procida` SLURM `Job 69570` wiped-`.lake/build` check).

Around `Erdos625.Section9MinimalEvenCycleTour` (the sole module using
`grind +suggestions`), the generator scopes
`set_library_suggestions open Lean.LibrarySuggestions in sineQuaNonSelector.filterGrindAnnotated`
so multi-module concatenation does not inject unrelated current-file theorems
from `env.constants.map₂`. Every exported theorem in both `Erdos625` and
`Erdos625HP` depends solely on `propext`, `Classical.choice`, and `Quot.sound`.
