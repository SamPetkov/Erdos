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
are equivalent.  Its new theorem
`canonicalHighDemand_eq_iff_exact_support_and_capped_off` also characterizes
the canonical cutoff by exact support values and the off-support `U/2` cap.
This module alone does not identify the labelled witness.  The accepted
[`Section8CanonicalLabelledWitness.lean`](Erdos625/Section8CanonicalLabelledWitness.lean)
now proves `existsUnique_canonicalHighDemandWitness`: for each one fixed
configuration matching, the literal canonical high-cell demand determines a
unique labelled prescribed-demand witness extended by that matching.  This is
a deterministic `exists unique` theorem, not itself a probability estimate.
The later fixed-demand conditional-law and factorization bridges below use
additional displayed hypotheses.  The manuscript-specific skeleton
specialization and the endpoint/near/middle skeleton estimates remain open.

[`Section8CanonicalEventResidual.lean`](Erdos625/Section8CanonicalEventResidual.lean)
now proves the exact next deterministic seam for one fixed witness: the full
canonical-demand event transports through the residual equivalence precisely
to the half-cap/no-return event.  It does not count the union over canonical
witnesses by itself; the later conditional-law module uses the resulting
fixed-demand equivalence.

[`Section8CanonicalEventCharacterization.lean`](Erdos625/Section8CanonicalEventCharacterization.lean)
names the corresponding full-event support/cap characterization, while
[`Section8ResidualDegreeTotal.lean`](Erdos625/Section8ResidualDegreeTotal.lean)
records equality of total residual row and column degrees.  Both are finite
deterministic bridges; neither by itself supplies event nonemptiness, a
quantitative canonical-event probability estimate, or a skeleton estimate.

[`Section8CanonicalEventCardinality.lean`](Erdos625/Section8CanonicalEventCardinality.lean)
decomposes one fixed-demand literal canonical event by its unique labelled
witness and proves the exact product of witness count and residual-event count. It passed
the remote warning-fatal Lean 4.31 gates.  This finite decomposition supplies
the sigma-space transport used below; it does not prove event nonemptiness or
any quantitative skeleton estimate.

[`Section8CanonicalConditionalLaw.lean`](Erdos625/Section8CanonicalConditionalLaw.lean)
formalizes the exact finite conditional-law transport for a *fixed* demand.
Under the strict high-demand premise and explicit nonemptiness of the literal
canonical-demand event, conditioning the ambient uniform configuration law on
that event is reconstruction from the uniform joint sigma law of a labelled
witness and its residual event.  After choosing a reference witness, this
joint space is equivalent to a product with one standardized residual-event
fibre, and the residual coordinate has the uniform finite marginal.  This
does not prove the event nonempty or likely, instantiate the manuscript's
skeleton parameters, or establish any quantitative skeleton bound.

[`Section8CanonicalDemandGlobalResidual.lean`](Erdos625/Section8CanonicalDemandGlobalResidual.lean)
adds the ambient finite counterpart without extending a fixed residual fibre
outside its natural scope.  Every configuration matching is equivalent to the
dependent sigma family of its attained canonical demand, its unique labelled
witness, and the residual event for that demand.  Under equal total stub mass,
the ambient uniform PMF transports to the uniform sigma PMF, and the demand
marginal is its literal fibre cardinality divided by the total cardinality.
That fibre has the exact labelled-witness times standardized-residual
cardinality factorization for any explicitly supplied witness. This is not a
common residual law across demands, a nonemptiness estimate, or a quantitative
skeleton statement.

Its marginal corollary gives the corresponding pushed-forward demand mass as
the labelled-witness cardinality times the specified demand-specific residual
fibre cardinality, divided by the ambient matching-space cardinality.

[`Section9GlobalCanonicalResidualBridge.lean`](Erdos625/Section9GlobalCanonicalResidualBridge.lean)
adds the precise downstream handoff: each element of that dependent global
sigma family is retyped as `ResidualCapNoReturnEvent` for its own support and
residual degrees, and the ambient uniform matching PMF transports exactly to
the uniform PMF on this still-tagged Section 9 sigma family. It does not turn
the dependent family into one residual PMF or establish an expectation or an
asymptotic bound.

[`Section8CanonicalEventProbabilityNormalization.lean`](Erdos625/Section8CanonicalEventProbabilityNormalization.lean)
adds the independent ambient-law normalization: under equal total row and
column stub mass, the probability of the literal canonical event is its finite
cardinality divided by the total matching factorial. It passed the remote
warning-fatal Lean 4.31 gates.  The companion
[`Section8CanonicalEventProbabilityFactorization.lean`](Erdos625/Section8CanonicalEventProbabilityFactorization.lean)
combines this normalization with the fixed-demand cardinality and incidence
identities to factor that exact probability into labelled-witness incidence
times the fixed residual-event probability.  These finite identities do not
prove nonemptiness, a quantitative probability bound, or a high-skeleton
estimate.

[`Section8LabelledIncidence.lean`](Erdos625/Section8LabelledIncidence.lean)
proves `labelledWitnessIncidence_eq`, the exact normalized descending-factorial
identity for labelled prescribed-demand witnesses.  It is the finite incidence
factor used by the fixed-demand probability factorization above; the
manuscript-specific skeleton parameterization and estimates remain separate.
[`Section8WitnessDemandFeasibility.lean`](Erdos625/Section8WitnessDemandFeasibility.lean)
proves the separate finite side condition that existence of such a labelled
witness forces its total demand to be at most the ambient row-stub mass.
[`Section8NearSkeletonExpansion.lean`](Erdos625/Section8NearSkeletonExpansion.lean)
proves `sum_nearSkeletonChoiceWeight_eq_product` for distinguishable optional
deficit choices.  The unlabelled typed-skeleton quotient, multiplicity bridge,
ratio estimates, and (8.25a) remain open.

The six earlier Section 8 source units are
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
also proved.  For arbitrary `ENNReal` cell weights, its finite weighted sum
has an exact one-sided inclusion into the sum over all even bipartite edge
sets. This inclusion is promoted by `Section9ActualResidualENNRealPolymerBridge.lean`
to a finite `ENNReal` simple-cycle polymer product. `Section9ActualResidualENNRealExpBridge.lean` then turns that actual-family product bound into an `EReal` exponential endpoint, including infinite weights. Separately, for pointwise
nonnegative real cell weights and a literal matching high-cell set, the same
actual residual family now inherits the established real polymer-product and
exponential bounds.  That real bridge does not identify the weights with
`residualQ` or prove a conditioned residual law, a cycle encoding, or an
attachment estimate.  The finite graph-theoretic
inequality in (9.20) is checked as
well: adding an arbitrary residual relation to a genuine bipartite matching
raises cycle rank by at most the number of residual cells.  Its literal
configuration-support specialization proves that this is at most half the
residual row-stub mass, including the explicit `m₀ / 2` form.  The exact
binary cycle-space identity, recoverable real-valued polymer decomposition,
and abstract traversal bounds are proved separately below.  The exact
one-sided weighted inclusion does not specialize the polymer decomposition to
`ENNReal`; that strengthening, the cycle-to-walk transfer, and the attachment
estimate remain open.  The earlier high-cell mass bound, weighted finite
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
[`Section9ActualResidualWeightedEmbedding.lean`](Erdos625/Section9ActualResidualWeightedEmbedding.lean),
[`Section9ActualResidualENNRealPolymerBridge.lean`](Erdos625/Section9ActualResidualENNRealPolymerBridge.lean),
[`Section9ActualResidualENNRealExpBridge.lean`](Erdos625/Section9ActualResidualENNRealExpBridge.lean),
[`Section9ActualResidualRealPolymerBridge.lean`](Erdos625/Section9ActualResidualRealPolymerBridge.lean),
and [`Section9ChooseTwoMass.lean`](Erdos625/Section9ChooseTwoMass.lean), plus
[`Section9CycleRankResidual.lean`](Erdos625/Section9CycleRankResidual.lean) and
[`Section9CycleRankConfigurationAssembly.lean`](Erdos625/Section9CycleRankConfigurationAssembly.lean).
[`Section9SmallResidualDeterministic.lean`](Erdos625/Section9SmallResidualDeterministic.lean)
then proves the exact finite integrand estimate (9.22): under the literal
cap/no-return table event, residual-mass identity, and separated cycle-rank
bound, the component factor times all local sign rewards is at most
`2^(U*m₀/2)`.  This remains a deterministic leaf; the conditioned random-law
instantiation and complete attachment expectation are still open.
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
finite even-edge family used here.  `Section9ActualResidualWeightedEmbedding.lean`
also proves the exact one-sided finite `ENNReal` weighted inclusion into the
all-even sum.  `Section9ActualResidualRealPolymerBridge.lean` adds the distinct
real-weight bridge from that literal actual family to the accepted polymer
product and exponential endpoint, under a matching premise and pointwise
nonnegative weights.  A separate accepted real-valued polymer theorem
constructs a recoverable disjoint minimal-even decomposition.
`Section9ActualResidualENNRealPolymerBridge.lean` additionally proves the
finite actual-residual `ENNReal` sum is at most the finite simple-cycle polymer
product. `Section9ActualResidualENNRealExpBridge.lean` turns that actual-family product bound into an `EReal` exponential endpoint, including infinite weights. Concrete cycle-to-walk
enumeration and weight/kernel transfer, instantiation of the accepted
eventual-`tau` bridge, the upstream finite attachment estimates, and full
Lemma 9.1/
Proposition 9.2 assembly remain open.  The separate cycle-rank module proves
the finite forest-plus-residual-edge bound required in the small-residual
regime, and its configuration assembly supplies both inequalities displayed
in (9.20).  The new deterministic small-residual module combines that explicit
cycle-rank input with the local reward product to prove (9.22); the exact binary
cycle-space cardinality and abstract traversal kernel are proved in the two
modules below.

[`Section9CycleSpaceCardinality.lean`](Erdos625/Section9CycleSpaceCardinality.lean)
now constructs the vertex-edge incidence map over `ZMod 2`, computes its
kernel dimension by rank-nullity and connected-component indicators, identifies
that kernel with literal finite edge subsets of even degree at every vertex,
and proves their exact cardinality `2 ^ cycleRank`.  This is the finite binary
cycle-space identity used in (6.7). The separate accepted polymer theorem
constructs a recoverable disjoint minimal-even decomposition. The new finite
`ENNReal` bridge gives the actual residual family a simple-cycle product bound,
and its `EReal` exponential endpoint; the required weighted-walk encoding remains open.

[`Section9TraversalKernel.lean`](Erdos625/Section9TraversalKernel.lean) defines
finite `ENNReal` kernel-walk mass and proves propagation by the row norm,
bipartite row/column specialization, a one-time marked-start cardinality cost,
and the positive/even-length geometric bounds used analytically in
(9.16)--(9.18).  These bounds become top for `tau >= 1`; the concrete
application must still instantiate the accepted eventual-`tau` bridge from
the actual profile inequalities, construct the cycle-to-walk encodings, and
transfer the manuscript weights into the kernel.  The accepted
[`Section9MatchingTraversalBridge.lean`](Erdos625/Section9MatchingTraversalBridge.lean)
proves the relaxed finite matching-operator/geometric bridge: matching
traversal keeps the residual row bound, there are exactly `2 * |M|` oriented
starts, and their finite block-walk mass is bounded by the geometric series.
It does not construct the positive residual kernel from `q`, nor an injective,
weight-preserving code from the minimal even sets or cycles to those walks.

Three accepted Section 9 modules now discharge further faithful finite leaves.
[`Section9CappedFixedFExpansion.lean`](Erdos625/Section9CappedFixedFExpansion.lean)
proves `capped_fixedF_prescribedDemand_expansion`, retaining the literal
cap/no-return event and uniform configuration law for one fixed `F`; summing
over the even family remains separate.
[`Section9CyclePolymerBound.lean`](Erdos625/Section9CyclePolymerBound.lean)
proves `weighted_evenSubgraph_polymer_bound`, including a recoverable
pairwise-disjoint decomposition into inclusion-minimal nonempty even sets and
the real subset-product/exponential bound. The separate `ENNReal` bridges now give the actual residual family a finite simple-cycle product and its corresponding `EReal` exponential endpoint, including infinite weights.
[`Section9FiniteAnalyticEndpoint.lean`](Erdos625/Section9FiniteAnalyticEndpoint.lean)
proves `existsAbsoluteFiniteEndpointConstant`, the uniform finite real bounds
`lambda <= C * theta^3` and `q <= C * theta^2` under the exact displayed
hypotheses.  It does not supply the upstream probabilistic event or parameter
identification.
[`Section9ResidualQQuadratic.lean`](Erdos625/Section9ResidualQQuadratic.lean)
proves `existsAbsoluteResidualQQuadraticBound`, transporting that real
endpoint estimate to the literal `ENNReal` `residualQ`, including its
exposed-skeleton zero branch and the finite/top cell-parameter split. It does
not identify a conditioned residual table, prove an attachment estimate, or
establish Lemma 9.1.
[`Section9ResidualQDegreeAssembly.lean`](Erdos625/Section9ResidualQDegreeAssembly.lean)
then composes that pointwise estimate with Euler rescaling and the proved
degree-square summation bound. Its degree-cap corollary supplies one finite
positive absolute constant for both residual-q row and column sums at scale
`U^3 / m`, but still does not identify a conditioned residual family or prove
an attachment estimate.
[`Section9ResidualQTraversalBridge.lean`](Erdos625/Section9ResidualQTraversalBridge.lean)
then lifts those two bounds to the symmetric `bipartiteCellKernel` of the
literal residual `q`, so the existing finite kernel-walk estimates apply under
the same degree-cap hypotheses. It still does not encode cycles as walks or
prove an attachment estimate.

Three further accepted Section 9 leaves isolate exact downstream algebra.
[`Section9RewardTelescoping.lean`](Erdos625/Section9RewardTelescoping.lean)
proves `cappedReward_telescoping`, the capped identities (9.10)--(9.11) under
the necessary `r <= R` hypothesis.
[`Section9FiniteFamilyAlgebra.lean`](Erdos625/Section9FiniteFamilyAlgebra.lean)
proves `finiteInjectiveFamily_product_exp_bound` from explicit injectivity,
pointwise product bounds, and nonnegative atom weights.
[`Section9AttachmentAsymptotics.lean`](Erdos625/Section9AttachmentAsymptotics.lean)
proves `eventually_tau_lt_one_third` from the displayed large-residual profile
bounds and `exists_uniform_twoRegime_error` from assumed large-/small-residual
attachment estimates.  These leaves do not construct the required
cycle-to-walk encoding or weight transfer, prove those upstream finite attachment
estimates, identify the conditioned probability law, or assemble Section 9.

Three additional warning-fatal Section 9 leaves sharpen the still-incomplete
cycle-to-walk interface.  [`Section9EndpointKernel.lean`](Erdos625/Section9EndpointKernel.lean)
defines the endpoint-resolved positive-walk kernel, proves that its row sum
recovers the scalar walk mass, and inherits the finite geometric row bound.
[`Section9ExplicitPathTerms.lean`](Erdos625/Section9ExplicitPathTerms.lean)
proves that each explicitly supplied path or chain is one nonnegative summand
of the corresponding endpoint or scalar kernel mass.
[`Section9QDegreeBound.lean`](Erdos625/Section9QDegreeBound.lean) turns a
pointwise quadratic `q` estimate, the exact degree totals, and degree caps into
the required row and column bounds `kappa * U^3 / m`.  These results do not
construct a covering-cycle decomposition, an injective weight-preserving
cycle code, or the concrete manuscript kernel, and therefore do not prove
Lemma 9.1 or Proposition 9.2.

Three further warning-fatal modules close the finite enumeration layer without
claiming the remaining physical encoding.  [`Section9KernelPathEnumeration.lean`](Erdos625/Section9KernelPathEnumeration.lean)
retains every internal vertex sequence and proves exact weighted-sum identities
for endpoint and scalar kernel masses.  [`Section9BlockChainEnumeration.lean`](Erdos625/Section9BlockChainEnumeration.lean)
iterates full positive-path codes and matching-transition states, giving the
exact endpoint mass of the relaxed composed-kernel chain.
[`Section9MinimalEvenCycleTour.lean`](Erdos625/Section9MinimalEvenCycleTour.lean)
proves that every inclusion-minimal nonempty even bipartite edge set is covered
exactly by a simple cycle walk.  Thus exact path multiplicity, relaxed
block-chain enumeration, and minimal cycle coverage are proved.  The physical
marked/oriented cycle-cut reconstruction and injective weight-preserving map
into those codes, the attachment bound, and the final theorem remain open.

Three accepted deterministic modules now begin the Sections 10--11 layer.
[`QuarterDensityDegree.lean`](Erdos625/QuarterDensityDegree.lean) proves the
fixed-size-to-larger density lift and the denominator-cleared quarter-density
averaging step, and
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
`n/(log n)^3`.  It now also defines `gapBase` and `amplificationError` and proves
`amplificationError_isLittleO_gapBase` by assembling those four accepted
components.  These deterministic limits do not supply the concrete
probabilistic seed or its Section IX `Lambda` asymptotics; the
quantifier-correct uniform amplification theorem is supplied separately
below.
[`Section11AsymptoticAssembly.lean`](Erdos625/Section11AsymptoticAssembly.lean)
proves the generic full-sequence intersection theorem without independence,
the eventual explicit threshold from abstract root/little-o hypotheses, and
divergence of the explicit gap scale.  Its
`fixedThreshold_tail_of_movingThreshold` additionally turns an assumed moving
tail with diverging threshold into every fixed-threshold tail, even for
`n`-dependent sample spaces.  The actual statistic, manuscript parameter
sequences, and chromatic/cochromatic tails are not instantiated.

[`Section10QuarterUnionDecay.lean`](Erdos625/Section10QuarterUnionDecay.lean)
proves `quarterDensity_unionBound_tendsto_zero`, the deterministic full-sequence
decay of `choose(n,u₀) * exp(-c*u₀^2)` at `u₀ = ceil(n^(1/4))`.
[`Section10SimultaneousGreedyColoring.lean`](Erdos625/Section10SimultaneousGreedyColoring.lean)
proves `simultaneous_induced_chromatic_bound`: one graph-uniform independent-
block hypothesis implies the required internal `forall U` chromatic bound with
ceiling division.  The first theorem does not build the graph event, and the
second does not prove its uniform hypothesis with high probability or perform
the concrete manuscript parameter arithmetic.

[`Section10BinomialEdgeCount.lean`](Erdos625/Section10BinomialEdgeCount.lean)
proves the exact singleton law for the number of edges in Mathlib's finite
binomial random graph.  The native fixed-set transport and its scalar
lower-quarter tail are now completed in
[`Section10InducedRestriction.lean`](Erdos625/Section10InducedRestriction.lean):
for every deterministic `S : Set (Fin n)`, the induced graph and the induced
complement both have the exact `G(S,1/2)` law, and their edge counts satisfy
the corresponding fixed-set exponential lower-quarter bound.  This does not
form a union bound, a simultaneous event over `S`, or the quarter-density
event of Lemma 10.1.
[`Section10QuarterDensityEvent.lean`](Erdos625/Section10QuarterDensityEvent.lean)
forms the literal finite event over all cutoff-size subsets, proves its
measurability, and derives the exact finite union bound
`choose(n,u0) * exp(-choose(u0,2)/16)`.
[`Section10QuarterDensityLimit.lean`](Erdos625/Section10QuarterDensityLimit.lean) proves that this literal cutoff event has probability tending to one. [`Section10QuarterDensityLift.lean`](Erdos625/Section10QuarterDensityLift.lean) converts event membership into quarter density on every cutoff-size complement set and, when the cutoff is at least two, on every larger subset. [`Section10UniformQuarterDensityEvent.lean`](Erdos625/Section10UniformQuarterDensityEvent.lean) packages those facts into one all-larger-subsets complement-density event with probability tending to one. [`Section10QuarterChainSurvival.lean`](Erdos625/Section10QuarterChainSurvival.lean), [`Section10QuarterChainParameters.lean`](Erdos625/Section10QuarterChainParameters.lean), and [`Section10QuarterChainSurvivalTransport.lean`](Erdos625/Section10QuarterChainSurvivalTransport.lean) prove the chosen-scale shifted-potential survival inequality, cutoff/start and step-count facts, its explicit logarithmic lower bound, and transport to every larger initial set.
[`Section10NeighborhoodDeletionStep.lean`](Erdos625/Section10NeighborhoodDeletionStep.lean)
proves one deterministic complement-neighbourhood step with the exact
denominator-cleared recurrence inequality. [`Section10QuarterDenseChain.lean`](Erdos625/Section10QuarterDenseChain.lean)
then assembles a finite clique and common-neighbour residual chain under
explicit quarter-density and shifted-potential survival hypotheses.
[`Section10QuarterChainAdapters.lean`](Erdos625/Section10QuarterChainAdapters.lean)
provides the exact complement-clique-to-independent-set bridge, and
[`Section10QuarterChainIndependentBlock.lean`](Erdos625/Section10QuarterChainIndependentBlock.lean)
assembles all of these inputs into one probability-one event supplying a
uniform independent block in every sufficiently large vertex set.  It also
instantiates the accepted greedy theorem with the exact ceiling-division
bound.
[`Section10QuarterChainGreedyNumeric.lean`](Erdos625/Section10QuarterChainGreedyNumeric.lean)
performs the remaining piecewise numerical conversion and gives the explicit
positive constant `C = 14 * log 4 + 2`.
[`Section10QuarterChainFailure.lean`](Erdos625/Section10QuarterChainFailure.lean)
defines the complement probability of the one independent-block event as a
deterministic, parameter-independent error sequence and proves that it tends
to zero.
[`Section10QuarterChainLinearEvent.lean`](Erdos625/Section10QuarterChainLinearEvent.lean)
then packages the exact manuscript-form event: for one positive absolute
constant, every induced set satisfies
`χ(G[U]) ≤ C |U| / log n + n^(1/3)` on one event whose probability tends to
one.  This closes the exact statement of Lemma 10.1.
[`Section10QuarterChainLeftoverEvent.lean`](Erdos625/Section10QuarterChainLeftoverEvent.lean)
specializes the same event to every deterministic deficit sequence, with
leftover bound
`ceilDivNat d (quarterChainSteps n) + quarterChainStart n`, proves the
simultaneous leftover-event probability tends to one, and bounds each fixed
failure probability by the same parameter-independent error.

[`Section10ComplementInvariance.lean`](Erdos625/Section10ComplementInvariance.lean)
proves that complementation exactly preserves the ambient labelled
`G(n,1/2)` measure; the new restriction module combines that symmetry with
the native restriction pushforward only for fixed deterministic subsets.
[`RandomGraphUniformLaw.lean`](Erdos625/RandomGraphUniformLaw.lean) proves that
the repository's half-binomial graph measure is exactly `uniformOn univ`, from
its equal singleton masses and probability normalization.  This removes the
measure mismatch for uniform finite counting arguments; the fixed-induced-set
transport is supplied separately by `Section10InducedRestriction.lean`.
[`Section10CapacityLeftoverQuantitative.lean`](Erdos625/Section10CapacityLeftoverQuantitative.lean)
locally proves the two-event quantitative union seam: if two success events
imply a good event, its failure probability is at most the sum of the two
failure bounds, without independence.
[`Section10UniformAmplification.lean`](Erdos625/Section10UniformAmplification.lean)
assembles that seam with the accepted capacity lower tail, an attaining core,
deterministic concatenation, and the parameter-independent simultaneous
colouring event.  Its theorem
`exists_uniform_cochromatic_amplification` is the exact quantifier-correct
form of Lemma 10.2: one constant `C ≥ 1` and one nonnegative deterministic
sequence `epsilon_n → 0` are chosen before all deterministic `k_n`,
`Lambda_n`, and `r_n`, and the fixed-index failure is at most
`exp(-r_n) + epsilon_n` whenever the displayed seed inequality holds.  No
independence is assumed.  The concrete Section IX seed estimate and its
`Lambda` asymptotics are not proved by this module.
[`Section11ChromaticLowerTailBridge.lean`](Erdos625/Section11ChromaticLowerTailBridge.lean)
locally converts a full-sequence probability-zero bound for `X n <= k n` into
probability one for the complementary strict event `k n < X n`, allowing the
sample space to depend on `n`.  The actual chromatic at-most tail and its
manuscript threshold remain open.

The named Section 8--11 leaves above have local Lean 4.31 warning-fatal builds.
That acceptance is declaration-scoped: it verifies their displayed algebraic,
deterministic, or conditional implications and does not promote any enclosing
manuscript lemma or section to complete.

The exact one-event Lemma 10.1 and the exact quantifier-correct uniform
Lemma 10.2 are now formalized.  In the latter, the absolute `C ≥ 1` and
nonnegative deterministic `epsilon_n → 0` are chosen before the deterministic
sequences `k_n`, `Lambda_n`, and `r_n`, and the conclusion holds along the full
sequence under its displayed seed hypothesis.  The concrete Section IX seed
and `Lambda` asymptotics, and the Section 11 parameter sequences and
probability tails, must still be supplied.  See
[`SECTIONS_10_11_BREAKDOWN_2026-07-14.md`](SECTIONS_10_11_BREAKDOWN_2026-07-14.md)
for the exact DAG and the declaration-scoped Aristotle request ledger.
The complete remaining-work and model-allocation plan is recorded in
[`REMAINING_FORMALIZATION_PLAN_2026-07-16.md`](REMAINING_FORMALIZATION_PLAN_2026-07-16.md).

[`Section10_11ConditionalAssembly.lean`](Erdos625/Section10_11ConditionalAssembly.lean)
now packages the rounded capacity-deficit tail from explicit seed, rounding,
and radius hypotheses, defines the quantifier-correct one-event leftover
interface with an internal `∀ W`, and proves the conditional implication
`erdos625Statement_of_capacity_leftover_thresholds`.  That implication takes
`hCapacityTail`, `hLeftoverTail`, `hChromaticTail`,
`hCochromaticThreshold`, and `hGapThreshold` as hypotheses.  It does **not**
prove `Erdos625Statement`; those probabilistic and asymptotic inputs remain to
be supplied for the manuscript's concrete sequences.  The quarter-chain
specialization
`erdos625Statement_of_capacity_quarterChainLeftover_thresholds` discharges
`hLeftoverTail`, reducing this route to four remaining inputs: capacity tail,
chromatic tail, cochromatic threshold, and gap threshold.  Uniform Lemma 10.2
is now available as a proved upstream interface, but its concrete Section IX
capacity seed and the remaining Section XI inputs are open.

The remaining phase-objective root/rounding, unrestricted chromatic lower-location,
signed-moment/overlap assembly, asymptotic diagonal ranges, manuscript-specific
specialization of the exact fixed-demand canonical conditional law and
probability factorization, skeleton quotient/estimates, and full Section 8
assembly, concrete cycle-to-walk enumeration and weight
transfer,
finite residual attachment bounds, conditioned
probability control, and full Section 9 assembly,
Section 10's concrete Section IX capacity seed and `Lambda` asymptotics, and
Section 11's actual chromatic tail and threshold/limit instantiation remain
open.  The proved uniform Lemma 10.2 interface does not supply those inputs or
the final theorem.  The project
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
