# Sections X--XI Aristotle target ledger

Audit date: 2026-07-15.

This directory records the remaining faithful Lean targets in manuscript
Sections X and XI.  It is a proposal ledger, not accepted proof source.  The
authoritative Lean modules already prove the deterministic recurrence,
analytic union-cost decay, greedy-colouring recursion, amplification-scale
limits, event intersection, moving-to-fixed threshold bridge, and the
conditional final assembly.

The remaining work separates into three layers:

1. deterministic and asymptotic leaves that can be proved without a random
   graph law;
2. graph-probability transport, where the exact `G(n,1/2)` measure must be
   connected to a fixed-subset tail and then to one simultaneous event;
3. concrete manuscript-sequence instantiation, which consumes the upstream
   chromatic and signed-cocolouring theorems.

## Dependency order

| ID | Target | Kind | Immediate dependencies | Aristotle status |
|---|---|---|---|---|
| X01 | fixed-subset complement-edge lower-quarter tail | graph probability | binomial random graph law | send now |
| X02 | exact-size density implies all-larger density | deterministic | finite double counting | send now |
| X03 | quarter-neighbourhood chain yields an independent set | deterministic | X02-style density hypothesis; accepted degree/recurrence atoms | send now |
| X04 | concrete cutoff/step survival | asymptotic | real powers, floor and ceiling bounds | send now |
| X05 | one simultaneous leftover-colouring event has probability tending to one | graph probability transport | X01--X04; accepted union decay and greedy recursion | stage after X01--X04 |
| X06 | quantitative two-success-event failure bound | generic probability transport | finite probability measure | send now |
| X07 | quantifier-correct rare-seed amplification bound | graph probability assembly | X05, X06, accepted capacity concentration and concatenation | stage after X05/X06 |
| XI01 | at-most tail zero gives strict-lower tail one | generic probability transport | complement identity | send now |
| XI02 | concrete manuscript threshold separation | sequence instantiation | Sections IV--V, X07, and Sections VIII--IX | blocked upstream |

The corresponding specifications are in the sibling files named by ID.

## Live proof-search checkpoint

On 2026-07-15 X01 completed at the service and remains quarantined while its
uniform-graph formulation is ported to the repository's
`randomGraphMeasure`; X02 was submitted and is in progress.  X03, X03a, X04,
and the finer X05/X07 packages remain source-only proposals.  X06 and XI01
have independent local Lean 4.31 warning-fatal proofs in
`Section10CapacityLeftoverQuantitative.lean` and
`Section11ChromaticLowerTailBridge.lean`, so their isolated service packages
are now only redundant fallbacks.  None of these scheduling facts changes the
open status of Lemma 10.1, Lemma 10.2, or the final theorem.

## Isolated Lean 4.28 packages

The six send-now targets are packaged under the ignored local directory
`.aristotle/pending-next`.  Each package pins Lean 4.28.0 and Mathlib revision
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`, and contains exactly one target
proof hole.

| ID | Local package |
|---|---|
| X01 | `.aristotle/pending-next/x01_fixed_subset_quarter_tail` |
| X02 | `.aristotle/pending-next/x02_density_lift` |
| X03 | `.aristotle/pending-next/x03_quarter_chain` |
| X03a fallback | `.aristotle/pending-next/x03a_quarter_neighborhood_step` |
| X04 | `.aristotle/pending-next/x04_survival_asymptotics` |
| X06 | `.aristotle/pending-next/x06_capacity_leftover_quantitative` |
| XI01 | `.aristotle/pending-next/xi01_chromatic_lower_bridge` |

X03a is a smaller one-step fallback preserving the exact quarter constant; it
does not replace the chain/clique invariant required by X03.  X05 and X07 have
since been split into faithful generic leaves recorded in
`X05_X07_NEXT_WAVE.md`; those leaves may be used for proof search before all
concrete inputs exist, but no concrete X07 instantiation is legitimate until
its Section IX seed is available.  XI02 remains blocked.  Submitting the final
theorem as a single goal would merely conceal the unresolved probability
transport and sequence instantiation.

## Lean 4.28 skeleton replay

Each packaged declaration was elaborated with the cached toolchain and the
exact pinned Mathlib revision.  These runs validate imports and statement
typing only; they do not validate the missing target proof.

| ID | Result | Elapsed seconds | Note |
|---|---:|---:|---|
| X01 | pass | 456.399 | uses the exactly equivalent uniform law because this Mathlib revision predates `SimpleGraph.binomialRandom` |
| X02 | pass | 60.185 | exact density-lift statement |
| X03 | pass | 60.931 | replayed after adding the required `SimpleGraph.Clique` import; statement unchanged |
| X03a | pass | 64.937 | smaller exact-quarter one-step fallback |
| X04 | pass | 137.266 | full-sequence floor/ceiling statement |
| X06 | pass | 95.092 | generic quantitative probability statement |
| XI01 | pass | 156.660 | varying finite sample-space statement |

## Upstream boundary

- X01--X06 and XI01 do not depend on Sections VIII--IX.
- The generic X07 theorem does not need the signed second-moment proof, but
  applying it to the manuscript's `k_co` and `Lambda` requires the Section IX
  seed.  That seed in turn consumes the Section VIII--IX machinery.
- XI01 is generic.  Its concrete input, the chromatic at-most tail, comes from
  Sections IV--V rather than Sections VIII--IX.
- XI02 needs both branches: the chromatic threshold/tail from IV--V and the
  cochromatic seed/threshold from VIII--X.

## Acceptance gates

Every returned proof must preserve the displayed quantifiers and full
`atTop` limits.  X05 must be one event containing an internal universal
quantifier over all vertex subsets; pointwise-in-subset probabilities are not
interchangeable with it.  X07 must choose its absolute constant and failure
sequence before the deterministic seed and radius sequences.  Returned code
is quarantined until it is source-scanned, replayed in the repository's Lean
version with warnings fatal, assumption-audited, and reviewed for statement
identity.
