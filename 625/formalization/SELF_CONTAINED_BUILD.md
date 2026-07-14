# Self-contained Lean checkpoint

`Erdos625SelfContained.lean` is generated from the complete transitive local
import closure of `Erdos625.lean`. It contains each project module's source in
dependency order, with a marked and section-scoped source boundary, and has no
`import Erdos625...` command. Its imports are only the external Mathlib modules
used by that closure.

This is a packaging of the current verified **partial formalization**, not a
claim that Problem 625 is completely formalized.  In Section VIII the exact
fixed-witness residual sample-space law, cell decomposition, and cellwise
zero/cap translations are proved, but canonical-skeleton selection,
uniqueness/incidence, global conditioned-event packaging, and the skeleton
estimates remain open.  In Section IX generic restriction and support-cardinality
bounds and the injective parity-matrix encoding are proved, but the manuscript's
actual residual-family support theorem, cycle/traversal estimates, and
second-moment assembly remain open.  Section X's quarter-density high-degree
step and exact neighbourhood recurrence are proved, but its simultaneous
leftover-colouring event and full seed-amplification assembly remain open.
Section XI's deterministic threshold-event inclusion is proved, but the actual
parameter sequences, probability-one inputs, final limit assembly, and the
final probabilistic theorem remain open.

## Regeneration

From `625/formalization`:

```powershell
python scripts/generate_self_contained.py
python scripts/generate_self_contained.py --check
```

The first command generates the file. The second is a byte-for-byte
reproducibility check and exits nonzero if the generated file is stale.

## Independent single-file build

```powershell
New-Item -ItemType Directory -Force .lake/build/lib/lean | Out-Null
lake env lean -DwarningAsError=true Erdos625SelfContained.lean `
  -o .lake/build/lib/lean/Erdos625SelfContained.olean
```

Verification performed on 2026-07-14 with the pinned Lean 4.31.0 toolchain and
Mathlib v4.31.0:

- result: success, exit code 0;
- wall time: 102.9 seconds in the current warmed dependency environment;
- local source modules included: 112;
- external Mathlib imports: 60;
- central `#print axioms` commands included: 410;
- physical lines: 23,793;
- generated source SHA-256:
  `271199E5C232B29C863CD270F732D3856430928D896F7EC37B9BAD0298FB72A8`;
- generated `.olean` size: 19,715,568 bytes.

The included central `#print axioms` audit reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies (or subsets of
these, and no axioms for some declarations). Text scans found no `sorry`,
`admit`, `sorryAx`, project `axiom`/`constant` declarations, `unsafe`,
`native_decide`, `run_tac`, `exact?`, suggestion-enabled `grind`, or
`maxHeartbeats`/`maxRecDepth` override.

The ordered module manifest is embedded in the generated file as 112
`BEGIN SOURCE MODULE` records. It can be displayed with:

```powershell
rg "^BEGIN SOURCE MODULE:" Erdos625SelfContained.lean
```
