# Self-contained Lean checkpoint

`Erdos625SelfContained.lean` is generated from the complete transitive local
import closure of `Erdos625.lean`. It contains each project module's source in
dependency order, with a marked and section-scoped source boundary, and has no
`import Erdos625...` command. Its imports are only the external Mathlib modules
used by that closure.

This is a packaging of the current verified **partial formalization**, not a
claim that Problem 625 is completely formalized. In Section VIII the exact
fixed-witness residual sample-space law, cell decomposition, and cellwise
zero/cap translations are proved. The canonical cutoff demand, its
partial-matching and exact on/off-support values, conditional selected-fibre and
compatible-pairing uniqueness, the support-indexed full/residual constraint
equivalence, and deterministic existence and uniqueness of the labelled
canonical witness for one supplied matching are also proved. The normalized
labelled-witness incidence identity and the distinguishable near-skeleton
product expansion are checked as finite algebra. Counting and identifying the
global canonical event, its conditioned law, the remaining incidence
specialization, and the endpoint/near/middle skeleton estimates remain open.

In Section IX the generic restriction and support-cardinality bounds,
injective parity-matrix encoding, literal residual even-edge family and its
`2 ^ |R|` bound, division-free form of (9.21), full finite cycle-rank chain
through literal support and `m₀ / 2`, exact binary cycle-space cardinality,
fixed-`F` capped expansion, finite analytic endpoint bounds, and deterministic
small-residual estimate are proved. The file also contains a recoverable
disjoint decomposition into minimal nonempty even sets with a real-valued
polymer bound, plus abstract and matching-aware finite geometric traversal
bounds. The canonical-skeleton instantiation, actual residual-family and
`ENNReal` weight specialization, positive residual kernel from `q`, injective
weight-preserving cycle-to-walk encoding, conditioned attachment estimate, and
second-moment assembly remain open.

Section X's quarter-density high-degree step, exact neighbourhood recurrence,
quarter-union decay, deterministic simultaneous greedy-colouring implication,
growing amplification radius, and all four deterministic little-`o`
contributions in (10.11)--(10.12) are proved. The graph-probability transport
giving the required one simultaneous event and the concrete seed-amplification
assembly remain open. Section XI's deterministic event inclusion, generic
probability-one intersection, eventual threshold reduction, exact scale
divergence, and final conditional seam are proved, but the seam's concrete tail
inputs and threshold instantiation—and therefore the final probabilistic
theorem—remain open.

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

Verification performed on 2026-07-15 with the pinned Lean 4.31.0 toolchain and
Mathlib v4.31.0:

- result: success, exit code 0;
- wall time: 332.304 seconds in the current warmed dependency environment;
- local source modules included: 137;
- external Mathlib imports: 71;
- central `#print axioms` commands included: 503;
- physical lines: 28,874;
- generated source SHA-256:
  `E2BEE24D196309FAB3500CC361DA57605AC24905F1A337858477EC90C8B7C29B`;
- generated `.olean` size: 26,860,200 bytes;
- generated `.olean` SHA-256:
  `AE68AE47EC242E6048F635A870C3B35E3BA930270F34999D5C8B105E97171DFD`.

The included central `#print axioms` audit reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies (or subsets of
these, and no axioms for some declarations). Text scans found no `sorry`,
`admit`, `sorryAx`, project `axiom`/`constant` declarations, `unsafe`,
`native_decide`, `run_tac`, `exact?`, suggestion-enabled `grind`, or
`maxHeartbeats`/`maxRecDepth` override.

The ordered module manifest is embedded in the generated file as 137
`BEGIN SOURCE MODULE` records. It can be displayed with:

```powershell
rg "^BEGIN SOURCE MODULE:" Erdos625SelfContained.lean
```
