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
  service toolchain.  Raw returned files remain quarantined; a candidate is
  accepted only after manual review, a local Lean 4.31 port or reconstruction,
  and the full repository gates.  See
  [`ARISTOTLE_WORKFLOW.md`](ARISTOTLE_WORKFLOW.md).

Run the standard cache-assisted build from this directory with:

```powershell
lake exe cache get
lake build --wfail
```

Do not run `lake update` for an ordinary reproduction: the tracked manifest
already fixes every dependency commit.  Use it only for an intentional,
reviewed dependency refresh.

## One-file checkpoint

[`Erdos625SelfContained.lean`](Erdos625SelfContained.lean) is a generated,
single-file packaging of the transitive local import closure of
`Erdos625.lean`.  It retains only external Mathlib imports and embeds the
project modules in dependency order.  Regenerate it with
[`scripts/generate_self_contained.py`](scripts/generate_self_contained.py) and
see [`SELF_CONTAINED_BUILD.md`](SELF_CONTAINED_BUILD.md) for the independent
compile and source/axiom audit.

This convenience artifact contains the current verified **partial**
formalization.  It is not a completed formal proof of Sections 8--9 or of
Problem 625: in particular, `Erdos625Statement` remains an unproved target.

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
bijections of the unused stubs is also proved.  The unused row and column
fibres are now identified class-preservingly with dependent sums having the
exact residual degrees, and the fixed-witness extension subtype is equivalent
to the corresponding residual `ConfigurationMatching` space.  Uniformity is
transported across that equivalence.  A separate generic theorem identifies
conditioning a finite uniform law on a nonempty event with the pushforward of
the uniform law on the event subtype.  The supporting target-fibre split,
class-preserving equivalence, and exact used-cell identification now culminate
in the per-cell fixed-witness identity
`configurationCellCount = demand + residual configurationCellCount`.  The
accepted constraint module separately proves the cap-free zero equivalence.
Its packaged configuration theorem has the explicit hypothesis
`hcap : demand a b <= cap` and returns that zero equivalence together with the
identification of the full cap and the truncated residual cap
`residual <= cap - demand a b`.  The high-skeleton cell condition uses the
zero branch.  Before using the unshifted cap off the skeleton, one must first
prove `demand a b = 0`; without this, only the shifted `cap - demand a b`
conclusion is available.  These are exact fixed-witness results; they do not
by themselves choose the canonical high skeleton or package these constraints
as the full canonical conditional event in Section 8.

[`Section8FixedWitnessAssembly.lean`](Erdos625/Section8FixedWitnessAssembly.lean)
now composes these accepted leaves for one fixed labelled witness.  Its bundle
conditions the ambient uniform law on the witness-extension event, transports
that conditional law to the residual configuration, records the exact
full-count/demand/residual split, and imposes all cap/no-additional-pair
constraints simultaneously.  The hypotheses explicitly include nonempty
finite sample spaces and `demand a b <= cap a b`.  This fixed-witness bundle
does not choose the canonical skeleton or bound the canonical skeleton event.

[`Section8CanonicalSkeleton.lean`](Erdos625/Section8CanonicalSkeleton.lean)
adds the deterministic canonical-support layer: the selected high demand has
partial-matching support and exact on/off values; fixed selected fibres admit
only one compatible pairing; zero residual mass forces a selected fibre to be
the full fibre; and the support-indexed full/residual cap/no-return conditions
are equivalent.  This does not construct or count the labelled canonical
witness, prove manuscript incidence (8.3), identify the global conditioned
event, or prove the endpoint/near/middle skeleton estimates.

The six Section 8 source units are
[`UniformConditionalLaw.lean`](Erdos625/UniformConditionalLaw.lean),
[`ResidualDegreeMatching.lean`](Erdos625/ResidualDegreeMatching.lean), and
[`ConfigurationResidualCellCounts.lean`](Erdos625/ConfigurationResidualCellCounts.lean),
together with
[`ConfigurationResidualCellConstraints.lean`](Erdos625/ConfigurationResidualCellConstraints.lean)
[`Section8FixedWitnessAssembly.lean`](Erdos625/Section8FixedWitnessAssembly.lean),
and [`Section8CanonicalSkeleton.lean`](Erdos625/Section8CanonicalSkeleton.lean).

The accepted Section 9 atoms now also include the following deterministic
facts.  Restriction to a residual relation is injective for even `ZMod 2`
bipartite matrices supported on its union with a row matching, giving the
generic cardinal bound `2 ^ |R|`.  A finite bipartite edge set is now encoded
injectively by its zero-one `ZMod 2` incidence matrix, and zero row and column
sums are equivalent to even row and column fibres.  The number of cells of an
actual configuration matching that contain at least two paired stubs is at
most the total row-stub count divided by two.  The actual residual even-edge
family has now been defined and its literal incidence encoding is proved to
meet the row-matching-plus-residual support condition, so it inherits the exact
`2 ^ |R|` bound.  The finite division-free choose-two mass estimate (9.21) is
also proved.  The finite graph-theoretic inequality in (9.20) is checked as
well: adding an arbitrary residual relation to a genuine bipartite matching
raises cycle rank by at most the number of residual cells.  Its literal
configuration-support specialization proves that this is at most half the
residual row-stub mass, including the explicit `m₀ / 2` form.  These results do
not identify the residual cycle space or prove any traversal, attachment, or
asymptotic estimate.  The earlier high-cell mass bound, weighted finite
Cauchy inequality, local sign-exponent arithmetic, and matching-support parity
kernel remain available as independent leaves.  Accepted Lean 4.31 source is
the proof authority; any Aristotle output is only redundant candidate
generation and remains quarantined until it passes the local acceptance gates.
The corresponding source units are
[`ResidualSupportMass.lean`](Erdos625/ResidualSupportMass.lean),
[`BipartiteEdgeMatrix.lean`](Erdos625/BipartiteEdgeMatrix.lean),
[`EvenMatchingRestriction.lean`](Erdos625/EvenMatchingRestriction.lean), and
[`ConfigurationResidualSupport.lean`](Erdos625/ConfigurationResidualSupport.lean),
together with [`Section9ActualResidualFamily.lean`](Erdos625/Section9ActualResidualFamily.lean)
and [`Section9ChooseTwoMass.lean`](Erdos625/Section9ChooseTwoMass.lean), plus
[`Section9CycleRankResidual.lean`](Erdos625/Section9CycleRankResidual.lean) and
[`Section9CycleRankConfigurationAssembly.lean`](Erdos625/Section9CycleRankConfigurationAssembly.lean).
The finite capped degree moments, exact theta factorizations, normalized bounds
in (9.13)--(9.14), and the total-zero branch are kernel-checked as a separate
Section 9 arithmetic module.

[`Section9EncodingAssembly.lean`](Erdos625/Section9EncodingAssembly.lean)
composes the generic Section 9 encoding/counting seam.  Given an explicit
injective encoding whose images are even matrices supported on a row matching
plus a residual relation, it proves the family bound `2 ^ |R|`.  Specializing
the residual relation to the actual configuration support bounds that exponent
by half the row-stub count.  This is a cardinality exponent bound under the
stated encoding/evenness/support hypotheses; it is not a mass-occupancy claim.
`Section9ActualResidualFamily.lean` verifies those hypotheses for the literal
finite even-edge family used here.  The recoverable edge-disjoint simple-cycle
decomposition, concrete cycle-to-walk enumeration and weight/kernel transfer
(including eventual `tau < 1`), attachment estimates, and full Lemma 9.1/
Proposition 9.2 assembly remain open.  The separate cycle-rank module proves
the finite forest-plus-residual-edge bound required in the small-residual
regime, and its configuration assembly supplies both inequalities displayed
in (9.20); the exact binary cycle-space cardinality and abstract traversal
kernel are proved in the two modules below.

[`Section9CycleSpaceCardinality.lean`](Erdos625/Section9CycleSpaceCardinality.lean)
now constructs the vertex-edge incidence map over `ZMod 2`, computes its
kernel dimension by rank-nullity and connected-component indicators, identifies
that kernel with literal finite edge subsets of even degree at every vertex,
and proves their exact cardinality `2 ^ cycleRank`.  This is the finite binary
cycle-space identity used in (6.7).  It does not choose a recoverable
edge-disjoint simple-cycle decomposition or encode cycles as weighted walks.

[`Section9TraversalKernel.lean`](Erdos625/Section9TraversalKernel.lean) defines
finite `ENNReal` kernel-walk mass and proves propagation by the row norm,
bipartite row/column specialization, a one-time marked-start cardinality cost,
and the positive/even-length geometric bounds used analytically in
(9.16)--(9.18).  These bounds become top for `tau >= 1`; the concrete
application must still prove eventual `tau < 1`, construct the cycle-to-walk
encodings, and transfer the manuscript weights into the kernel.

Three accepted deterministic modules now begin the Sections 10--11 layer.
[`QuarterDensityDegree.lean`](Erdos625/QuarterDensityDegree.lean) proves the
denominator-cleared quarter-density averaging step, and
[`QuarterRecurrence.lean`](Erdos625/QuarterRecurrence.lean) proves the exact
recurrence lower bound in (10.3a).
[`Section11EventAssembly.lean`](Erdos625/Section11EventAssembly.lean) defines
the two threshold events and proves both the abstract and explicit-constant
pointwise inclusions of their intersection in `gapEvent`.  It does not prove
that either event has probability tending to one.

[`Section10AmplificationScales.lean`](Erdos625/Section10AmplificationScales.lean)
defines the manuscript's base and radius, proves that the radius tends to
infinity, and proves the seed square-root, transformed-radius, real cube-root,
and additive-constant little-o statements, each relative to
`n/(log n)^3`.  These deterministic limits do not supply the probabilistic
seed, the simultaneous leftover-colouring event, or Lemma 10.2.
[`Section11AsymptoticAssembly.lean`](Erdos625/Section11AsymptoticAssembly.lean)
proves the generic full-sequence intersection theorem without independence,
the eventual explicit threshold from abstract root/little-o hypotheses, and
divergence of the explicit gap scale.  The actual manuscript parameter
sequences and their chromatic/cochromatic tails are not instantiated.

The missing Section 10 statement must use one high-probability event with an
internal `∀ U`; pointwise events chosen separately for each leftover set
have the wrong quantifiers.  In Lemma 10.2, the absolute `C` and deterministic
`epsilon_n -> 0` must be chosen before the deterministic sequences `k_n`,
`Lambda_n`, and `r_n`, and the result must hold along the full sequence.  The
Section 11 set inclusion must still be instantiated with the actual parameter
sequences and probability tails.  See
[`SECTIONS_10_11_BREAKDOWN_2026-07-14.md`](SECTIONS_10_11_BREAKDOWN_2026-07-14.md)
for the exact DAG and the ten completed/quarantined Aristotle requests.

[`Section10_11ConditionalAssembly.lean`](Erdos625/Section10_11ConditionalAssembly.lean)
now packages the rounded capacity-deficit tail from explicit seed, rounding,
and radius hypotheses, defines the quantifier-correct one-event leftover
interface with an internal `∀ W`, and proves the conditional implication
`erdos625Statement_of_capacity_leftover_thresholds`.  That implication takes
`hCapacityTail`, `hLeftoverTail`, `hChromaticTail`,
`hCochromaticThreshold`, and `hGapThreshold` as hypotheses.  It does **not**
prove `Erdos625Statement`; those probabilistic and asymptotic inputs remain to
be supplied for the manuscript's concrete sequences.

The remaining phase-objective root/rounding, unrestricted chromatic lower-location,
signed-moment/overlap assembly, asymptotic diagonal ranges, canonical residual
conditioned-event packaging, labelled canonical-witness/incidence (8.3),
skeleton estimates, and full Section 8 assembly,
cycle-space decomposition and traversal enumeration, residual attachment and full Section 9 assembly,
Section 10's simultaneous leftover tail and concrete seed-amplification
instantiation, and Section 11's actual chromatic tail and threshold/limit
instantiation remain open.  The new seam theorems do not discharge these
inputs or prove any manuscript section theorem.  The project
therefore does **not** claim Lemma 3.1 or
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
