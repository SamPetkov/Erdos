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
canonical witness for one supplied matching are also proved. Existence of a
labelled demand witness forces total demand below the ambient row-stub mass,
and for one fixed witness the full canonical event transports exactly to the
residual half-cap/no-return event. Total residual row and column degrees agree,
and the full canonical-demand event has a named exact support/cap
characterization. The normalized
labelled-witness incidence identity and the distinguishable near-skeleton
product expansion are checked as finite algebra. The literal global canonical
event for one fixed demand is also counted exactly through its labelled-witness
fibres.
Its ambient probability normalization and fixed-demand factorization into
labelled-witness incidence times a residual-event probability are also proved.
Under the strict high-demand premise and explicit nonemptiness, its ambient
conditional law is a uniform joint witness/residual sigma law; after choosing
a reference witness it is a uniform product with one standardized
residual-event fibre, whose residual coordinate has the uniform finite
marginal. These finite identities do not prove event nonemptiness or a
quantitative probability bound, and the manuscript-specific skeleton
parameterization and endpoint/near/middle estimates remain open.

In Section IX the generic restriction and support-cardinality bounds,
injective parity-matrix encoding, literal residual even-edge family and its
`2 ^ |R|` bound, division-free form of (9.21), full finite cycle-rank chain
through literal support and `m₀ / 2`, exact binary cycle-space cardinality,
fixed-`F` capped expansion, finite analytic endpoint bounds, and deterministic
small-residual estimate are proved. The file also contains a recoverable
disjoint decomposition into minimal nonempty even sets with a real-valued
polymer bound, plus abstract and matching-aware finite geometric traversal
bounds. It now also contains the endpoint-resolved positive kernel, pointwise
explicit-path/chain summand bounds, and the generic row/column norm consequence
of a supplied degree-square `q` estimate. The canonical-skeleton
instantiation, actual residual-family and `ENNReal` weight specialization,
concrete pointwise `q` estimate, injective weight-preserving cycle-to-walk
encoding, conditioned attachment estimate, and second-moment assembly remain
open.

Section X's quarter-density high-degree step, exact neighbourhood recurrence,
quarter-union decay, deterministic simultaneous greedy-colouring implication,
growing amplification radius, and all four deterministic little-`o`
contributions in (10.11)--(10.12) are proved. The exact finite binomial
edge-count law, equality of the half-binomial graph law with the uniform law,
and the no-independence quantitative two-event failure seam are also checked.
The graph-probability transport giving the required one
simultaneous event and the concrete seed-amplification assembly remain open.
Section XI's deterministic event inclusion, generic probability-one
intersection, strict-lower complement bridge, eventual threshold reduction,
exact scale divergence, and final conditional seam are proved, but the seam's
concrete tail inputs and threshold instantiation—and therefore the final
probabilistic theorem—remain open.

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

The source checkpoint generated on 2026-07-15 has the following reproducible
metrics:

- regeneration check: success, exit code 0;
- local source modules included: 151;
- external Mathlib imports: 75;
- central `#print axioms` commands included: 531;
- newline count: 30,257;
- generated source SHA-256:
  `46BE3575A917F3F2AFCED5DB21AD91B185106DD97166AE5CBEC1CA4B3436C0E7`.

The warning-fatal compilation of this exact checkpoint is performed by the
repository's GitHub Actions workflow, after the modular `lake build --wfail`
gate.  This deliberately moves the memory-intensive whole-project acceptance
run off the development workstation.  A checkpoint is accepted only when both
remote compilation gates and the placeholder scan succeed.

The included central `#print axioms` audit reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies (or subsets of
these, and no axioms for some declarations). Text scans found no `sorry`,
`admit`, `sorryAx`, project `axiom`/`constant` declarations, `unsafe`,
`native_decide`, `run_tac`, `exact?`, suggestion-enabled `grind`, or
`maxHeartbeats`/`maxRecDepth` override.

The ordered module manifest is embedded in the generated file as 151
`BEGIN SOURCE MODULE` records. It can be displayed with:

```powershell
rg "^BEGIN SOURCE MODULE:" Erdos625SelfContained.lean
```
