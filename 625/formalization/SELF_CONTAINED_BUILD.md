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
marginal. Globally, every configuration matching is also equivalent to its
attained canonical demand, its labelled witness, and its demand-dependent
residual event; the transported uniform law has the exact fibre-cardinality
demand marginal, and each such fibre factors into its labelled-witness count
times one explicit demand-specific residual-fibre count. These finite
identities do not claim a common residual law across demands, event
nonemptiness, or a quantitative probability bound, and the manuscript-specific
skeleton parameterization and endpoint/near/middle estimates remain open.

In Section IX the generic restriction and support-cardinality bounds,
injective parity-matrix encoding, literal residual even-edge family and its
`2 ^ |R|` bound, division-free form of (9.21), full finite cycle-rank chain
through literal support and `m₀ / 2`, exact binary cycle-space cardinality,
fixed-`F` capped expansion, finite analytic endpoint bounds, and deterministic
small-residual estimate are proved. Every tagged state in the global Section
VIII canonical-demand disintegration is retyped by its own literal Section IX
cap/no-return event, and the ambient uniform PMF transports exactly to the
uniform law on that tagged sigma family. This does not create an untagged
residual law or an expectation bound. The file also contains a recoverable
disjoint decomposition into minimal nonempty even sets with a real-valued
polymer bound. The actual residual even-edge family has an exact one-sided
weighted `ENNReal` inclusion into the all-even finite sum and a finite
simple-cycle polymer product bound and an `EReal` exponential endpoint, including infinite weights. The file also contains abstract and matching-aware finite geometric traversal
bounds. It now also contains the endpoint-resolved positive kernel, pointwise
explicit-path/chain summand bounds, and the generic row/column norm consequence
of a supplied degree-square `q` estimate. The literal residual `q` has a
degree-cap row/column bound and its symmetric bipartite kernel inherits that
row norm. The canonical-skeleton
instantiation, concrete pointwise `q` estimate, injective weight-preserving cycle-to-walk
encoding, conditioned attachment estimate, and second-moment assembly remain
open.

Section X's fixed-size-to-larger quarter-density lift, high-degree step,
exact neighbourhood recurrence, quarter-union decay, deterministic simultaneous
greedy-colouring implication, growing amplification radius, and all four
deterministic little-`o` contributions in (10.11)--(10.12) are proved. The
exact finite binomial edge-count law, equality of the half-binomial graph law
with the uniform law, ambient complement invariance, native fixed induced
pushforward laws, their fixed-set lower-quarter tails, and the quantitative
two-event seam are also checked. The literal finite cutoff-subset event has
its exact union bound and a full-sequence probability-one limit. One
deterministic complement-neighbourhood step and a finite chain under explicit
density and shifted-potential survival hypotheses are checked as well. The literal cutoff event now also has deterministic event-to-density and larger-subset consequences (with an explicit cutoff-at-least-two hypothesis). The concrete survival/rounding estimates and complete simultaneous probability transport
and concrete seed-amplification assembly remain open.
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

The source checkpoint generated on 2026-07-16 has the following reproducible
metrics:

- regeneration check: success, exit code 0;
- local source modules included: 178;
- external Mathlib imports: 78;
- central `#print axioms` commands included: 683;
- newline count: 34,069;
- generated source SHA-256:
  `1D521C1F09A649645A3D168635C840B9A5E4FCABC9B4C3435C3667337DD03357`.

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

The ordered module manifest is embedded in the generated file as 176
`BEGIN SOURCE MODULE` records. It can be displayed with:

```powershell
rg "^BEGIN SOURCE MODULE:" Erdos625SelfContained.lean
```
