# Self-contained Lean checkpoint

`Erdos625SelfContained.lean` is generated from the complete transitive local
import closure of `Erdos625.lean`. It contains each project module's source in
dependency order, with a marked and section-scoped source boundary, and has no
`import Erdos625...` command. Its imports are only the external Mathlib modules
used by that closure.

This is a packaging of the current verified **partial formalization**, not a
claim that Problem 625 is completely formalized.  In Section VIII the exact
fixed-witness residual sample-space law, cell decomposition, and cellwise
zero/cap translations are proved.  The canonical cutoff demand, its
partial-matching and exact on/off-support values, conditional selected-fibre and
compatible-pairing uniqueness, and the support-indexed full/residual constraint
equivalence are also proved.  The actual labelled canonical witness and event,
the incidence formula (8.3), its probability/count, and the skeleton estimates
remain open.  In Section IX the generic restriction and support-cardinality
bounds, injective parity-matrix encoding, literal residual even-edge family and
its `2 ^ |R|` bound, and the division-free form of (9.21) are proved.  The
cycle-space identity/decomposition, traversal estimates, attachment bound, and
second-moment assembly remain open.  Section X's quarter-density high-degree
step, exact neighbourhood recurrence, growing amplification radius, and all
four deterministic little-`o` contributions in (10.11)--(10.12) are proved,
but its simultaneous leftover-colouring event and concrete seed-amplification
assembly remain open.  Section XI's deterministic event inclusion, generic
probability-one intersection, eventual threshold reduction, and exact scale
divergence are proved, but the actual parameter sequences, probability-one
inputs, final instantiation, and the final probabilistic theorem remain open.

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
- wall time: 503.9 seconds in the current warmed dependency environment;
- local source modules included: 120;
- external Mathlib imports: 61;
- central `#print axioms` commands included: 442;
- physical lines: 25,194;
- generated source SHA-256:
  `D841A258A15B7AA3D9675DADC8B12EDD2507610B65EF8FA7DFA2DA145C4090E2`;
- generated `.olean` size: 20,560,680 bytes.

The included central `#print axioms` audit reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies (or subsets of
these, and no axioms for some declarations). Text scans found no `sorry`,
`admit`, `sorryAx`, project `axiom`/`constant` declarations, `unsafe`,
`native_decide`, `run_tac`, `exact?`, suggestion-enabled `grind`, or
`maxHeartbeats`/`maxRecDepth` override.

The ordered module manifest is embedded in the generated file as 120
`BEGIN SOURCE MODULE` records. It can be displayed with:

```powershell
rg "^BEGIN SOURCE MODULE:" Erdos625SelfContained.lean
```
