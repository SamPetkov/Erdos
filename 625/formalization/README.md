# Lean formalization

This directory contains the incremental Lean 4 formalization of the proposed
resolution of Erdős Problem 625.

**Authors:** Samuil Petkov & ChatGPT 5.6

The confirmed scope, conventions, validation criteria, failure modes, and
checkpoint policy are recorded in [`FORMALIZATION_BRIEF.md`](FORMALIZATION_BRIEF.md).
The comparison with DeepMind's statement-only Problem 625 draft is recorded in
[`EXTERNAL_FORMALIZATION_AUDIT.md`](EXTERNAL_FORMALIZATION_AUDIT.md); no code
was copied and no dependency was added.
The explicit import, toolchain, transitive lockfile, and reproducible-build policy is
recorded in
[`DEPENDENCY_REPRODUCIBILITY.md`](DEPENDENCY_REPRODUCIBILITY.md).

## Reproducible toolchain

- Lean: `v4.31.0`
- mathlib: `v4.31.0`
- Aristotle: optional isolated proof search on its fixed Lean `v4.28.0`
  service toolchain; no returned file is accepted without a local Lean 4.31
  port and the full repository gates.  See
  [`ARISTOTLE_WORKFLOW.md`](ARISTOTLE_WORKFLOW.md).

Run the standard cache-assisted build from this directory with:

```powershell
lake exe cache get
lake build --wfail
```

Do not run `lake update` for an ordinary reproduction: the tracked manifest
already fixes every dependency commit.  Use it only for an intentional,
reviewed dependency refresh.

## Integrity policy

A milestone is called complete only when its imported modules compile without
`sorry`, `admit`, project-defined axioms, or hidden generated proof objects.
Finite computations may test definitions but are never substituted for an
asymptotic proof.  `FORMALIZATION_LEDGER.md` maps the public declarations to
the authoritative manuscript and records all remaining obligations explicitly.

## Current scope

Milestone M0 formalizes the finite labelled-graph model, chromatic and
cochromatic invariants and minimum semantics, the inequality `ζ(G) ≤ χ(G)`,
induced-set cocolouring concatenation, the exact `G(n, 1/2)` probability law
and uniform singleton mass, event measurability, and the full-sequence target
proposition. The independent M0 results are in
[`M0_AUDIT_2026-07-13.md`](M0_AUDIT_2026-07-13.md).

The verified post-M0 bricks now include exact phase/floor arithmetic and
adjacent first-moment ratios; Markov, Paley--Zygmund, and binomial-tail tools;
the complete finite independent-set first moment; the endpoint-uniform phase
expansion and its genuine consequences (2.3), (2.4), and (2.9); and exact
Boolean-cube and arbitrary finite-block bounded differences.  The uniform
vertex-block product law is proved equivalent to `G(n,1/2)`, including event
and expectation transport.  The largest induced `k`-cocolourable subgraph is
defined, shown one-vertex Lipschitz, characterized at full capacity, and given
one- and two-sided graph-law tails with the `(n-1)/4` block profile.  The
capacity maximum is attained by an explicit induced core whose complement has
exact size `n-capacity`; concatenating its cocolouring with an ordinary
colouring of the complement proves the deterministic manuscript inequality
(10.9).  A generic probability lemma also converts an endpoint seed of mass
`exp(-Λ)` and a positive-proxy one-sided sub-Gaussian tail into the exact
endpoint-to-expectation cost `sqrt(2vΛ)`; its graph-specific specialization
proves `n-E[capacity]≤sqrt((n-1)Λ/2)` for `n≥2`.  The matching one-sided
lower tail now yields the exact (10.8) failure probability `exp(-r)` at the
additional radius `sqrt((n-1)r/2)`, without a two-sided factor.  The
finite-support `{2,3,4,5}` exponential family also has kernel-checked mean
inversion, a zero-safe entropy variational optimizer, and a sharp
coordinatewise score-stability theorem for the optimized value at each fixed
interior target, together with an explicit uniform-in-target convergence
corollary on `(2,5)`.  Joint score-and-target continuity now gives moving-target
convergence of the unique tilt and all four optimizer coordinates.  On every
compact subset of `(2,5)`, these convergences are uniform, one index controls
all four coordinates, and the optimizer is eventually bounded uniformly away
from zero.
The finite Section 4 profile foundation now models unordered nonempty colour
classes as `Finpartition`s, proves their exact internal-edge count and fixed-
partition probability, and derives the exact first moment as the actual number
of profile partitions times its energy factor.  The enumeration layer proves
the exact factorial decoration count, maps every decorated partition to a canonical slot
equivalence, and reconstructs from every slot equivalence the correct profile
partition, labels, and within-part orders.  Coordinate recovery proves the
forgetful map both injective and surjective, so these constructions are now an
actual total equivalence.  The exact unordered factorial cardinality formula
and the displayed first-moment formula (4.2) are consequently proved under
the necessary mass equation, without assuming a counting interpretation from
mathlib.  All mass-`n`, exactly-`k`, size-bounded profiles are also collected
in a finite coordinate box, their number is at most `(n+1)^b`, and the
aggregate expectation is proved to be exactly the sum of the per-profile
expectations.  Explicit zero-safe factorial bounds identify the exact
per-profile logarithmic weight, convert it to an exponential upper bound, and
sum it with the rigorous `(n+1)^b` profile-box multiplicity.  The finite
exponent is proved exactly equal to the manuscript's expanded discrete
objective, including zero coordinates and the empty profile.  Natural
profiles embed into an explicit nonnegative real feasible space with exact
part-count and vertex-mass constraints and exactly preserved objective.  A
generic variational-envelope theorem then packages any proved continuous
 upper relaxation into the required finite expectation bound.  For positive
 support and part count, a finite zero-safe Gibbs argument provides a concrete
 one-parameter log-partition dual upper bound.  The Gibbs mean tends to the two
 support endpoints, is strictly increasing when `b≥2`, and therefore has a
 unique tilt for every target in `(1,b)`.  The matching Gibbs profile is
 feasible and attains the exact greatest value of the fixed finite real-profile
 relaxation.  Reindexing the support by deficits is exact: the manuscript's
 normalized deficit tilt is `λ=B_α-t`, and its target is `α-n/parts`.  On the
 interior target domain, the inverse derivative is the reciprocal variance,
 the normalized entropy derivative is `-t`, and the attained value has exact
 part-count derivative `log Z_b(t)-log parts`.  Finally, the exceptional top
 deficit has its exact logarithmic correction, while every support coordinate
 satisfies the pointwise Gaussian residual-score upper bound.  Exact support
 reversal and finite tilted-Gaussian tails now give uniform partition,
 first-moment, and second-moment envelopes on the growing support whenever a
 common absolute tilt bound is supplied; the deficit-zero atom simultaneously
 gives a uniform denominator lower bound.  The limiting law on deficits
 `{-1,0,1,…}` is defined with summable zeroth, first, and second moments and a
 strictly positive partition.  Its partition and first numerator can be
 differentiated termwise, its normalized mean has derivative equal to a
 strictly positive raw variance, and hence the limiting mean is strictly
 increasing.  Its endpoint limits are `-1` at negative infinite tilt and
 `+∞` at positive infinite tilt; every target above `-1` therefore has a
 unique limiting tilt, and compact target intervals have fixed finite
 bracketing tilts.  Every fixed natural weight, the exceptional
 `-1` weight, and their fixed first/second-moment terms converge to the
 corresponding limiting atoms.  Uniform Gaussian domination now upgrades
 these coordinate limits to pointwise and compact-uniform convergence of the
 full growing-support partition, first numerator, second numerator, and
 normalized mean.  The selected finite deficit tilt is eventually bounded by
 one constant simultaneously for every target in a supplied compact interval
 above `-1`; it converges uniformly there to the unique selected limiting
 tilt.  The finite deficit variance is the derivative of the finite mean and
 converges uniformly on bounded tilt intervals to the positive limiting raw
 variance.  Continuity supplies a positive compact variance floor, integration
 gives a quantitative lower separation, and a generic inverse-error theorem
 completes the selected-inverse transfer without assuming its conclusion.  The
 dual bound is already
composed with the finite chromatic probability reduction, producing the exact
`box·exp(dual+error)+μ(n,b+1)` inequality for every parameter `t`.  A coloring is
also converted to its nonempty kernel partition, refined to exactly `k`
nonempty parts, and extracted into a bounded profile.  This proves the
deterministic event containment behind (4.5), with the excessive-independence-
number event as the only alternative.  A direct finite-space Markov and union
argument then proves `P(χ≤k)≤E[bounded count]+P(α>b)`, as well as its sharp
 box-exponential-plus-`μ(n,b+1)` form.  The remaining part of (4.3)--(4.5) is
 analytic and asymptotic: insert the now-controlled phase-dependent deficit
 optimizer into the part-count objective, establish the scalar root corridor
 and slope, justify the integer rounding decrement, and prove that the
 assembled upper bound tends to zero.
An explicit phase-cap squeeze theorem already performs the last implication
once convergence of the displayed dual main term is supplied.

The early reproduced build, source, axiom, and independent statement checks
are recorded in
[`M1A_M2_SETUP_AUDIT_2026-07-13.md`](M1A_M2_SETUP_AUDIT_2026-07-13.md).
The subsequent cross-audit of the Boolean-cube bounded-differences theorem
and the explicit phase estimates is in
[`M1B_M2_ESTIMATES_AUDIT_2026-07-13.md`](M1B_M2_ESTIMATES_AUDIT_2026-07-13.md).
The current declaration-by-declaration hashes and remaining obligations are
kept in the formalization ledger.  The combined phase, vertex-block, capacity,
and rare-seed checkpoint is reproduced in
[`M3_PHASE_BLOCK_AMPLIFICATION_AUDIT_2026-07-13.md`](M3_PHASE_BLOCK_AMPLIFICATION_AUDIT_2026-07-13.md).
The compact-uniform profile, exact (10.8), complete finite enumeration and
first-moment formula (4.2), and finite aggregation checkpoint is reproduced in
[`M4_PROFILE_SECTION4_AUDIT_2026-07-13.md`](M4_PROFILE_SECTION4_AUDIT_2026-07-13.md).
The finite Stirling/log-weight, coloring-to-profile, sharp probability,
Gibbs-dual, local dual-calculus, and conditional phase-cap checkpoint is in
[`M5_SECTION4_FINITE_DUAL_AUDIT_2026-07-13.md`](M5_SECTION4_FINITE_DUAL_AUDIT_2026-07-13.md).
The fixed finite-support inversion, exact Gibbs attainment, deficit
normalization, envelope calculus, and pointwise Gaussian-score checkpoint is in
[`M6_FINITE_DUAL_ATTAINMENT_DEFICIT_AUDIT_2026-07-14.md`](M6_FINITE_DUAL_ATTAINMENT_DEFICIT_AUDIT_2026-07-14.md).
The growing-support moments, limiting-law calculus, compact selected-tilt
convergence, variance stability, and generic root/rounding checkpoint is in
[`M7_GROWING_SUPPORT_TILT_CORRIDOR_AUDIT_2026-07-14.md`](M7_GROWING_SUPPORT_TILT_CORRIDOR_AUDIT_2026-07-14.md).
The active overlap/skeleton/residual decomposition and quarantined Aristotle
task map are recorded in
[`SECTIONS_6_9_BREAKDOWN_2026-07-14.md`](SECTIONS_6_9_BREAKDOWN_2026-07-14.md).

The latest exact finite checkpoint proves the fixed-row ordered overlap law
(6.1)--(6.2), the configuration-model prescribed-cell estimates
(6.8)--(6.10), the partial-diagonal and full-corner
identities (7.1)--(7.6), the exact configuration-cell row and column margins,
and the resulting high-cell matching assertion before (8.2).  Each accepted
module has an isolated warnings-fatal build and focused standard-axiom audit.
The deterministic equivalence between witness-extending matchings and
bijections of the unused stubs is also proved, without overclaiming the still
open residual degree-fibre probability law.  External proof-search output
remains advisory until independently replayed.

The remaining phase-objective root/rounding, unrestricted chromatic lower-location,
signed-moment/overlap assembly, asymptotic diagonal ranges, canonical residual
law, residual attachment, and complete amplification layers remain open.  The
project therefore does **not** claim Lemma 3.1 or
`Erdos625Statement`. The
[`formalization ledger`](FORMALIZATION_LEDGER.md) is the authoritative
declaration-by-declaration status record.

CI also performs a source gate for placeholders, explicit placeholder-axiom
terms, project `axiom`/`constant` declarations, and `unsafe`, and invokes
Lean with `--wfail`, so Lean's own warning for a proof placeholder is fatal.
The optional external `nanoda` path is disabled; no mutable proof-checker
helper is part of the milestone claim.

## License and citation

The original formalization is covered by the repository's
[CC BY 4.0 license](../../LICENSE) and [scope notice](../../LICENSE_SCOPE.md).
Please cite Samuil Petkov using the repository's
[`CITATION.cff`](../../CITATION.cff) when using this work academically.
