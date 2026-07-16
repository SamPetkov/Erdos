# Erdős Problem 625 research dossier

## Complete proof

**[Open the complete proof PDF](COMPLETE_PROOF_SELF_CONTAINED.pdf)**

**[Open the publication-layout preprint PDF](arxiv_625.pdf)**

The publication-layout PDF is dated 12 July 2026 and lists Samuil Petkov as
the sole author, with explicit AI-assistance, Aristotle-use, funding, and
competing-interests disclosures.  It remains a candidate preprint while the
full Lean target is open.

Its editable source, author--year bibliography, arXiv-ready `.bbl`, build
notes, and byte-identical PDF are collected in the [`arxiv/`](arxiv/) folder.

The editable canonical manuscript is
[`proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](proofs/COMPLETE_PROOF_SELF_CONTAINED.md),
and the generated TeX is
[`output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex`](output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex).

## Supplementary exact example

An [MP4 animation](assets/animations/erdos625-coloring-example.mp4) shows an
exact coloring and cochromatic partition of a fixed 12-vertex graph.  It is an
illustrative example, not statistical or asymptotic proof evidence.

## Lean formalization

[`formalization/`](formalization/) contains the pinned Lean 4 formalization,
authored by **Samuil Petkov & ChatGPT 5.6**.  The accepted project is checked
locally with Lean/mathlib `v4.31.0`.  Raw Aristotle outputs remain quarantined;
only manually reviewed Lean 4.31 ports or reconstructions that pass the local
repository gates enter the accepted project.  The verified closure includes
the labelled finite-graph and `G(n,1/2)` model, chromatic/cochromatic semantics,
exact phase and independent-set asymptotics, Boolean-cube and variable-block
bounded differences, induced-capacity amplification bricks, and finite
four-support entropy/optimizer continuity.

For audit convenience, the generated
[`Erdos625SelfContained.lean`](formalization/Erdos625SelfContained.lean)
packages the current transitive local import closure into one Lean source
file; its regeneration and independent compile record are in
[`SELF_CONTAINED_BUILD.md`](formalization/SELF_CONTAINED_BUILD.md).  This is a
single-file **partial checkpoint**, not a full formal proof of Sections 8--9
or of `Erdos625Statement`.

The Section 4 layer now proves the exact unordered profile enumeration and
first-moment formula (4.2), zero-safe factorial/log-weight bounds, the finite
`(n+1)^b` aggregate exponential estimate, and exact equivalence with the
expanded discrete profile objective.  Natural profiles now embed exactly in
the constrained real profile space, and an abstract variational-envelope
theorem supplies the finite expectation interface.  A zero-safe Gibbs
inequality gives an explicit one-parameter dual domination for positive
support and part count and is composed with the sharp shifted finite
 probability bound.  The Gibbs mean now has its two endpoint limits and a
 unique interior target tilt; its positive optimizer exactly attains the fixed
 finite real-profile maximum.  The support is reindexed exactly by deficits
 with normalized tilt `λ=B_α-t`, and the inverse, entropy, and part-count
 envelope derivatives are kernel-checked.  The exceptional top residual is
 evaluated exactly and the full finite support has a pointwise Gaussian score
 bound.  Exact support reversal plus finite Gaussian-tail lemmas now give
 explicit growing-support partition, first-moment, and second-moment envelopes
 on every supplied bounded tilt interval, with a uniform denominator lower
 bound from the zero-deficit atom.  The limiting deficit Gaussian is defined
 with summable moments through order two and a strictly positive partition;
 its normalized mean has derivative equal to a strictly positive variance and
 has endpoint limits `-1` and `+∞`.  Hence every limiting target above `-1`
 has a unique finite tilt and compact target intervals admit fixed brackets.
The final phase-cap squeeze interface is also kernel-checked.  The layer
also constructs a nonempty kernel
partition from a coloring, refines it to exactly `k` parts, extracts the
bounded profile, and proves the deterministic event containment used in
(4.5), including all zero endpoints.  Finite-space Markov and union bounds
then give the exact probability reduction and its conditional
`(n+1)^b exp(L)+μ(n,b+1)` form.

The current Sections 6--8 checkpoint now includes the exact fixed-row ordered
overlap law (6.1)--(6.2), the uniform configuration-model prescribed-cell bound
(6.8), the effective
falling-factorial estimate (6.10), and the all-cases cellwise product bound
(6.9), including a proof that the excessive-total event is empty.  The exact
partial-diagonal algebra, endpoint factorization, and recurrences (7.1)--(7.6)
are kernel-checked.  Exact row and column margins of the configuration cell
table also instantiate the concrete high-cell matching assertion before
(8.2).  Extending a fixed exposed witness is moreover equivalent to a bijection
of its unused stubs, with exact remaining cardinalities.  The unused fibres
are now identified class-preservingly with standard residual stub types having
the exact residual degrees, so the fixed-witness extension subtype is
equivalent to the corresponding residual `ConfigurationMatching` space and
its uniform law pushes forward to the residual uniform law.  Generic finite
uniform conditioning is also proved.  The target-fibre and class-preservation
lemmas culminate in the exact per-cell fixed-witness identity
`full configurationCellCount = demand + residual configurationCellCount`.
The accepted cell-constraint module separately identifies `full = demand`
with residual count zero through a cap-free arithmetic lemma.  Its packaged
configuration theorem assumes `hcap : demand a b <= cap` and returns that
equivalence together with `full <= cap` iff
`residual <= cap - demand`.  High-skeleton cells use the zero branch; an
off-skeleton application of the unshifted residual cap first needs
`demand a b = 0`.  These fixed-witness results do not by themselves select the
canonical high skeleton or package the constraints as the full Section 8
conditional event.

[`Section8FixedWitnessAssembly.lean`](formalization/Erdos625/Section8FixedWitnessAssembly.lean)
now composes those leaves for one fixed labelled witness: conditioning the
ambient uniform law on its extension event, transporting that law to the
residual configuration, splitting every full cell count as demand plus
residual count, and imposing the cap/no-additional-pair constraints
simultaneously.  This is a fixed-witness seam theorem under its explicit
nonemptiness and `demand <= cap` hypotheses.  It still does not select the
canonical high skeleton or estimate the probability of the canonical skeleton
event.

[`Section8CanonicalSkeleton.lean`](formalization/Erdos625/Section8CanonicalSkeleton.lean)
now defines the deterministic canonical high demand and proves that its support
is a partial matching with exact on- and off-support values.  It also proves
compatibility uniqueness after the selected fibres are fixed, that zero
residual mass makes a selected fibre the whole fibre, and an exact generic
translation of support-indexed cap/no-return constraints.  The added theorem
`canonicalHighDemand_eq_iff_exact_support_and_capped_off` characterizes the
same cutoff by exact support values and the off-support `U/2` cap.
[`Section8CanonicalLabelledWitness.lean`](formalization/Erdos625/Section8CanonicalLabelledWitness.lean)
then proves `existsUnique_canonicalHighDemandWitness`: for one fixed
configuration matching, its literal canonical high-cell demand has a unique
labelled prescribed-demand witness extended by that matching.  This is a
deterministic fixed-matching identification, not a count or probability for
the global canonical event.
[`Section8LabelledIncidence.lean`](formalization/Erdos625/Section8LabelledIncidence.lean)
proves `labelledWitnessIncidence_eq`, the normalized labelled-witness
descending-factorial identity, while
[`Section8NearSkeletonExpansion.lean`](formalization/Erdos625/Section8NearSkeletonExpansion.lean)
proves `sum_nearSkeletonChoiceWeight_eq_product` for distinguishable optional
deficit choices.  These are deterministic/counting leaves.  For a fixed demand,
the formalization also proves the exact finite canonical conditional-law
transport: under its strict high-demand and nonemptiness hypotheses, the
ambient conditional law is the uniform joint law of a labelled witness and a
residual-event fibre.  With a reference witness this becomes a product law,
and the standardized residual coordinate has the uniform finite marginal.
The corresponding exact event-probability factorization is also proved as
labelled-witness incidence times the fixed residual-event probability.  None
of these facts proves event nonemptiness or a quantitative skeleton estimate;
the unlabelled typed-skeleton multiplicity bridge, ratio bounds, and the
endpoint/near/middle estimates of Lemma 8.3 remain open.

At the ambient level,
[`Section8CanonicalDemandGlobalResidual.lean`](formalization/Erdos625/Section8CanonicalDemandGlobalResidual.lean)
now decomposes every configuration matching by its attained canonical-demand
table, its labelled witness, and its demand-dependent residual event.  It
transports the ambient uniform law to this dependent sigma space and proves
that a demand table has mass proportional to its exact fibre cardinality.  It
also factors that fibre into its labelled-witness cardinality times one
demand-specific residual-fibre cardinality.  It does not claim that demands
are uniformly distributed, that one residual law works across all demands, or
that any canonical event is likely.

The companion marginal theorem states this directly as the labelled-witness
cardinality times that demand-specific residual-fibre cardinality, divided by
the ambient matching-space cardinality.

[`Section9GlobalCanonicalResidualBridge.lean`](formalization/Erdos625/Section9GlobalCanonicalResidualBridge.lean)
then retypes every residual fibre by its literal Section 9 cap/no-return
event and transports the ambient uniform matching PMF exactly to the uniform
PMF on that tagged Section 9 sigma family. The attained demand and labelled
witness remain explicit tags, so this is not an untagged residual
distribution, conditioning statement, expectation bound, or asymptotic
estimate.

For Section 9, restriction to the residual relation is proved injective for
even matrices supported on the union of that relation with a row matching,
giving a generic `2 ^ |R|` cardinal bound.  Finite bipartite edge sets now have
an injective zero-one incidence-matrix encoding over `ZMod 2`, with matrix
parity equivalent to even row and column fibres.  The number of cells of an
actual configuration matching with multiplicity at least two is at most the
total row-stub count divided by two.  The explicitly defined actual residual
even-edge family is now connected to the generic restriction theorem, giving
the precise `2 ^ |R|` support bound, and the division-free finite choose-two
mass estimate (9.21) is proved.  It also has an exact one-sided `ENNReal`
weighted embedding into the finite sum over all even bipartite edge sets, for
arbitrary cell weights.  This is a subfamily comparison, not an `ENNReal`
polymer estimate.  The finite forest-plus-residual-edge
cycle-rank inequality in (9.20) is also kernel-checked, including its literal
configuration-support and `m₀ / 2` forms.  The exact finite binary cycle-space
cardinality, a recoverable real-valued minimal-even polymer decomposition, and
the abstract row-norm/geometric traversal kernel are also proved.  The accepted
[`Section9MatchingTraversalBridge.lean`](formalization/Erdos625/Section9MatchingTraversalBridge.lean)
adds the relaxed finite matching-operator/walk-mass bridge: matching traversal
preserves the residual row bound, oriented starts cost exactly `2 * |M|`, and
the finite block-walk sum has the stated geometric bound.  It does not build
the positive residual kernel from `q` or an injective, weight-preserving
cycle-to-walk encoding.  The exact finite subfamily embedding is checked, but
an `ENNReal` polymer bound, the cycle-to-walk weight transfer, instantiation
of the accepted eventual-`tau` bridge,
the finite attachment estimates, and the global Lemma
9.1/Proposition 9.2
assembly remain open.  Aristotle is used only for redundant
isolated candidate generation; reviewed local Lean 4.31 source is
authoritative.
The capped degree moments and exact theta factorizations/bounds behind
(9.13)--(9.14) are also kernel-checked.  The literal residual `q` now has a
finite degree-cap row/column norm bound, and hence its symmetric bipartite
cell kernel has the corresponding row norm; this still supplies neither a
conditioned residual law nor a cycle-to-walk encoding.

[`Section9EncodingAssembly.lean`](formalization/Erdos625/Section9EncodingAssembly.lean)
packages the generic counting seam.  An explicit injective even-matrix
encoding supported on a row matching together with a residual relation gives
the bound `2 ^ |R|`; when that residual relation is the actual configuration
support already bounded above, the exponent is at most half the row-stub
count.  These are conditional cardinality theorems under the displayed
encoding, evenness, and support hypotheses.
[`Section9ActualResidualFamily.lean`](formalization/Erdos625/Section9ActualResidualFamily.lean)
discharges those encoding/evenness/support hypotheses for the literal finite
family of even edge sets supported on the high matching or multiplicity-at-
least-two cells.  [`Section9ActualResidualWeightedEmbedding.lean`](formalization/Erdos625/Section9ActualResidualWeightedEmbedding.lean)
then proves its exact one-sided weighted `ENNReal` inclusion into the all-even
finite sum; it does not turn the separate real polymer theorem into an
`ENNReal` theorem.  [`Section9ChooseTwoMass.lean`](formalization/Erdos625/Section9ChooseTwoMass.lean)
proves (9.21) in a division-free form, while
[`Section9CycleRankResidual.lean`](formalization/Erdos625/Section9CycleRankResidual.lean)
proves that a matching plus a residual relation has cycle rank at most the
number of residual cells.
[`Section9CycleRankConfigurationAssembly.lean`](formalization/Erdos625/Section9CycleRankConfigurationAssembly.lean)
identifies the literal residual-support finset and proves the full finite chain
`cycleRank ≤ |E(H_res)| ≤ m₀ / 2`.  A separate accepted real-valued polymer
theorem constructs a recoverable disjoint minimal-even decomposition.  The
actual family has the one-sided finite weighted embedding above, but an
`ENNReal` polymer specialization, concrete cycle-to-walk encoding and
weight/kernel transfer, instantiation of the accepted eventual-`tau` bridge,
attachment bound, and final Section 9 assembly
remain open; the exact binary cycle-space count and abstract traversal kernel
are proved below.

[`Section9SmallResidualDeterministic.lean`](formalization/Erdos625/Section9SmallResidualDeterministic.lean)
proves the finite arithmetic conclusion (9.22).  Given the literal
cap/no-return table event, the exact demand-plus-residual split, residual mass,
and the separated cycle-rank estimate, it bounds the component factor times
the complete local sign-reward product by `2^(U*m₀/2)`.  It does not yet
identify the conditioned random residual table or close the full attachment
expectation in Lemma 9.1.

[`Section9CycleSpaceCardinality.lean`](formalization/Erdos625/Section9CycleSpaceCardinality.lean)
proves the exact binary cycle-space count: finite even edge subsets are
equivalent to the `ZMod 2` incidence kernel and number exactly
`2 ^ cycleRank`.  [`Section9TraversalKernel.lean`](formalization/Erdos625/Section9TraversalKernel.lean)
proves the finite row-norm walk estimate, the one-time marked-start factor, and
the positive/even geometric tails behind (9.16)--(9.18).  What remains is the
actual-family specialization and cycle-to-walk encoding, the concrete
weight/kernel transfer and attachment assembly.

[`Section9CappedFixedFExpansion.lean`](formalization/Erdos625/Section9CappedFixedFExpansion.lean)
proves the faithful capped/no-return prescribed-demand expansion for one fixed
`F`.  [`Section9CyclePolymerBound.lean`](formalization/Erdos625/Section9CyclePolymerBound.lean)
constructs the recoverable disjoint minimal-even decomposition and proves the
finite real polymer product/exponential bound.
[`Section9FiniteAnalyticEndpoint.lean`](formalization/Erdos625/Section9FiniteAnalyticEndpoint.lean)
proves one absolute-constant finite real endpoint bound for `lambda` and `q`
under its exact hypotheses.  These modules do not themselves supply an
`ENNReal` polymer bound for the actual residual family, build the required
cycle-to-walk code, or supply the upstream random event.

[`Section9RewardTelescoping.lean`](formalization/Erdos625/Section9RewardTelescoping.lean)
proves `cappedReward_telescoping`, the exact capped reward identities under
`r <= R`.  [`Section9FiniteFamilyAlgebra.lean`](formalization/Erdos625/Section9FiniteFamilyAlgebra.lean)
proves `finiteInjectiveFamily_product_exp_bound` under explicit injectivity and
pointwise nonnegative product bounds.
[`Section9AttachmentAsymptotics.lean`](formalization/Erdos625/Section9AttachmentAsymptotics.lean)
proves `eventually_tau_lt_one_third` from the stated large-residual profile
inequalities and `exists_uniform_twoRegime_error` from assumed large-/small-
residual attachment estimates.  It does not supply the required cycle-to-walk
and weight encodings, those upstream finite estimates, the conditioned probability
bound, or the global Section 9 assembly.

The newest Sections 10--11 checkpoint adds eight accepted source units.
[`QuarterDensityDegree.lean`](formalization/Erdos625/QuarterDensityDegree.lean)
proves both the fixed-size-to-larger quarter-density lift and the high-degree
vertex step, and
[`QuarterRecurrence.lean`](formalization/Erdos625/QuarterRecurrence.lean)
proves the exact real recurrence (10.3a).
[`Section11EventAssembly.lean`](formalization/Erdos625/Section11EventAssembly.lean)
proves two pointwise threshold-intersection inclusions, including the explicit
constant and strict-event `+1`.
[`Section10AmplificationScales.lean`](formalization/Erdos625/Section10AmplificationScales.lean)
proves growth of the chosen radius together with the seed, transformed-radius,
real cube-root, and additive-constant little-o terms on the
`n/(log n)^3` scale.  Its `amplificationError_isLittleO_gapBase` now assembles
the exact displayed deterministic error from those four components.
[`Section11AsymptoticAssembly.lean`](formalization/Erdos625/Section11AsymptoticAssembly.lean)
proves the generic full-sequence intersection, eventual threshold, and scale-
divergence lemmas.  Its `fixedThreshold_tail_of_movingThreshold` proves the
generic implication from an assumed diverging moving tail to every fixed
threshold, including for `n`-dependent sample spaces.
[`Section10QuarterUnionDecay.lean`](formalization/Erdos625/Section10QuarterUnionDecay.lean)
proves `quarterDensity_unionBound_tendsto_zero`, the full-sequence deterministic
union-cost decay at
`u₀ = ceil(n^(1/4))`, while
[`Section10ComplementInvariance.lean`](formalization/Erdos625/Section10ComplementInvariance.lean)
proves that graph complementation preserves the ambient finite `G(n,1/2)` law
exactly.  This symmetry does not provide the still-missing fixed induced-
restriction pushforward.
[`Section10SimultaneousGreedyColoring.lean`](formalization/Erdos625/Section10SimultaneousGreedyColoring.lean)
proves `simultaneous_induced_chromatic_bound`, the internal-`forall U` greedy
chromatic bound from one graph-uniform independent-block hypothesis.  These
atoms do not prove the random event
supplying that hypothesis, Lemma 10.1, Lemma 10.2, the actual Section 11
sequence/tail instantiation, or the final theorem.  The exact remaining DAG,
quantifier order, and the declaration-scoped Aristotle request ledger are
recorded in the
[`Sections X--XI breakdown`](formalization/SECTIONS_10_11_BREAKDOWN_2026-07-14.md).

The newly named Section 8--11 leaves have local Lean 4.31 warning-fatal builds.
This is statement-scoped acceptance of their deterministic, algebraic, or
conditional content, not completion of a manuscript section or the target.

[`Section10_11ConditionalAssembly.lean`](formalization/Erdos625/Section10_11ConditionalAssembly.lean)
adds three auditable seams: the rounded capacity-deficit tail from explicit
seed, rounding, and radius hypotheses; a single leftover-colouring event whose
definition contains the required internal `forall W`; and the conditional
implication `erdos625Statement_of_capacity_leftover_thresholds`.  The latter
assumes `hCapacityTail`, `hLeftoverTail`, `hChromaticTail`,
`hCochromaticThreshold`, and `hGapThreshold`.  It is therefore **not** a proof
of `Erdos625Statement`; the corresponding probabilistic tails and concrete
threshold comparisons must still be established.

The asymptotic target is deliberately recorded as an **unproved proposition**;
the current development is a verified partial formalization, not a completed
Lean proof of the manuscript.  Growing-support moments, compact-uniform
optimizer-tilt convergence, variance stability, and generic root/rounding
interfaces are kernel-checked.  In Section 4, the concrete phase objective,
its center/slope corridor, its integer decrement, and the resulting probability
limit remain open; the
signed first-moment certificate, unordered/sign-summed overlap assembly, asymptotic
partial-diagonal ranges, manuscript-specific specialization of the exact
fixed-demand canonical conditional law and probability factorization, the
skeleton quotient/estimates, and full Section 8 assembly, actual-family and
`ENNReal` polymer/weight specialization beyond the proved one-sided subfamily
inclusion, concrete
cycle-to-walk encoding and weight transfer, finite residual attachment and
conditioned probability control, and full Section 9 assembly, Section 10's
simultaneous leftover tail and concrete
seed-amplification instantiation, and Section 11's actual chromatic tail and
threshold/limit instantiation also remain open.
See the [`formalization ledger`](formalization/FORMALIZATION_LEDGER.md) for the
declaration-by-declaration status and remaining dependency graph.  Reproduced
milestone evidence is recorded in the audit files under
[`formalization/`](formalization/); the latest growing-support, compact-tilt,
variance, and root-interface checkpoint is the
[`M7 audit`](formalization/M7_GROWING_SUPPORT_TILT_CORRIDOR_AUDIT_2026-07-14.md).  The
complete dependency/import policy is in
[`DEPENDENCY_REPRODUCIBILITY.md`](formalization/DEPENDENCY_REPRODUCIBILITY.md).
The current Sections 6--9 atomization, Aristotle quarantine status, and exact
non-atomic obligations are tracked in the
[`Sections 6--9 breakdown`](formalization/SECTIONS_6_9_BREAKDOWN_2026-07-14.md).
The simultaneous-leftover, amplification, and final event/limit obligations
are tracked separately in the
[`Sections X--XI breakdown`](formalization/SECTIONS_10_11_BREAKDOWN_2026-07-14.md).

## Current status

`proofs/COMPLETE_PROOF_SELF_CONTAINED.md` contains a proposed all-`n` positive
resolution with the explicit bound

\[
 \chi(G(n,1/2))-\zeta(G(n,1/2))
 \ge \frac{(\ln2)^2\ln(200/153)}{32}
       \frac{n}{(\ln n)^3}
 \quad\text{with high probability}.
\]

The decisive overlap components passed focused independent audits, and four
independent end-to-end reconstructions each returned PASS.  A fresh
severity-ranked adversarial review on 2026-07-13 then found a circular signed-
root localization in the written proof, an unstated globalization step in the
high-skeleton sum, and a one-sided/two-sided overclaim in the residual lemma.
All three were repaired without changing the theorem or constant, and three
independent regression reviews returned PASS on the corrected passages.  See
[`audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md`](audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md).
The concise draft and the focused first-moment, dense-overlap, residual, and
amplification notes were subsequently synchronized to those repairs.  Their
cross-document mapping is recorded in
[`audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md`](audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md).
This is internal validation of a new argument, not external peer review,
publication, priority confirmation, or community acceptance.

A further user-supplied review dated 2026-07-12 reports **provisional internal
verification: PASS** and no blocking mathematical error.  Its separately
written checker reproduces five groups of finite diagnostic tests from
Sections 6 and 8.  The report, checker, reproduced output, provenance, and
limitations are indexed in [`verification/`](verification/).  This is
additional internal evidence, not external peer review or machine
verification, and the finite tests do not prove the asymptotic theorem.

As of 2026-07-12, the [public Problem 625 page](https://www.erdosproblems.com/625)
still labels the problem `OPEN`.  This repository presents a proposed
resolution for scrutiny and does not claim an official status change.

The current complete packaged dossier is available at
[`releases/Erdos-625-complete-dossier-2026-07-14.zip`](releases/Erdos-625-complete-dossier-2026-07-14.zip).
It includes the arXiv source library and the pinned Lean source project while
excluding local build/service caches and copyrighted historical-source PDFs.

## Publication artifacts

The canonical dossier manuscript attributes co-authorship to **Samuil Petkov
& ChatGPT 5.6**.  The separate publication-layout preprint lists **Samuil
Petkov** as author and gives explicit AI-assistance and ethics disclosures.

- [`COMPLETE_PROOF_SELF_CONTAINED.pdf`](COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - top-level convenience copy for immediate viewing on GitHub; byte-identical
    to the compiled PDF under `output/pdf/`.
- [`proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](proofs/COMPLETE_PROOF_SELF_CONTAINED.md)
  - canonical self-contained Markdown manuscript.
- [`output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex`](output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex)
  - generated standalone TeX source with color-coded lemma/proposition boxes.
- [`output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf`](output/pdf/COMPLETE_PROOF_SELF_CONTAINED.pdf)
  - compiled 30-page A4 PDF with proofs kept outside the statement boxes.
- [`output/README.md`](output/README.md) - build versions, hashes, and PDF QA.
- [`arxiv/`](arxiv/) - publication-layout TeX, bibliography, `.bbl`, build
  notes, and compiled 35-page preprint.
- [`arxiv_625.pdf`](arxiv_625.pdf) - top-level convenience copy of the
  publication-layout preprint.

## Proof authority and synchronized support

`proofs/COMPLETE_PROOF_SELF_CONTAINED.md` is the sole authoritative proof.
The TeX and PDF are generated publication forms of that manuscript.  The
component notes below retain focused derivations and route history; they have
been synchronized to the 2026-07-13 repairs but are supporting explanations,
not a second proof whose wording overrides the canonical manuscript.  If a
future discrepancy appears, the canonical manuscript controls and the
discrepancy must be logged.

- `proofs/COMPLETE_PROOF_DRAFT.md` — concise synchronized map of the theorem
  and its proof obligations.
- `proofs/ALPHA_MINUS_TWO_ROUTE.md` — synchronized support for the uniform
  root corridor, first-moment comparison, explicit constants, unrestricted
  chromatic lower location, and tangent-rounded integer profile.
- `proofs/FOUR_SIZE_PARTIAL_RATES.md` — exact common-diagonal sum `1+o(1)`.
- `proofs/DENSE_FOUR_TYPE_MATCHING.md` — synchronized support for all
  unequal-type containments, near-containments, the mixed middle strip, and
  the conditioned global sum over high skeletons.
- `proofs/RESIDUAL_ATTACHMENT.md` — synchronized one-sided upper bound for
  residual local and even-subgraph attachments after the large-cell matching
  is exposed.
- `proofs/ALON_CONCENTRATION_EXTENSION.md` — synchronized rare-event-to-whp
  transfer with the growing deterministic error/failure sequence used in the
  final event intersection.

## Independent audits

- `audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` — severity-ranked fresh
  audit, repair register, and independent regression results; internal pass
  after revision.
- `audits/PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md` — traceability
  matrix confirming that the focused component notes reflect those repairs;
  no change to the canonical TeX/PDF content.
- `audits/RARE_EVENT_AMPLIFICATION_AUDIT.md` — pass.
- `audits/RESIDUAL_ATTACHMENT_AUDIT.md` and
  `audits/DENSE_FOUR_TYPE_MATCHING_AUDIT.md` — preserved internal 2026-07-12
  verdicts on the earlier component bytes; their top notices delimit scope.
- `audits/FULL_PROOF_AUDIT_1.md` through `_4.md` — preserved independent
  2026-07-12 reconstructions; all four passed the bytes then reviewed, and
  their top notices make clear that they are not reviews of later bytes.
- `verification/erdos625_verification_report.md` — additional provisional
  internal verification; pass, with formalization targets identified.
- `verification/erdos625_independent_checks.py` — separately written finite
  diagnostic checker; all five supplied check groups pass.

## Literature and known results

- `sources/SOURCE_LEDGER.md`
- `sources/RECENT_WORK_AUDIT.md`
- `sources/HISTORICAL_SOURCE_AUDIT.md`
- `sources/ERDOS625_REFERENCES.bib` -- reusable BibTeX for every reference
  cited in the canonical manuscript.
- `proofs/KNOWN_RESULTS_RECONSTRUCTION.md`
- `proofs/EXCEPTIONAL_REGIME.md`

The ledger records every source version and probability quantifier.  Every
historical Problem 625 source cited in the manuscript has been checked directly
for the claim attributed to it, with pages and SHA-256 identifiers recorded in
the historical audit.  Bibliographic metadata for the standard bounded-
differences and concentration references was verified against the publisher
and arXiv records.  The copyrighted PDFs remain local and are not redistributed
in this repository or its release archives.

## Reproducibility

- `experiments/alpha_minus_two_route.py` — phase-uniform entropy losses and
  certified constants.
- `experiments/dense_transport_scan.py` — exact finite falling-factorial
  diagnostics for dense typed transports.
- `experiments/constrained_profile_certify.py` and
  `experiments/finite_slack_profile.py` — exceptional-profile calculations.
- `experiments/exact_chi_zeta.py`, CSV, and report — certified finite graph
  computations (diagnostic only).
- `experiments/render_erdos625_animation.py` — deterministic GIF/MP4 renderer
  that revalidates the fixed graph and its exact partition witnesses before
  producing the supplementary animation artifacts.

`WORK_LOG.md` and `MECHANISM_REGISTRY.md` record the investigation history,
failed routes, redirections, and precise remaining status.
`FINAL_VERIFICATION.md` records the full audit history, the 2026-07-13
adversarial repairs and regression results, the 2026-07-14 publication and
Lean-checkpoint refresh, the additional user-supplied verification,
reproducibility checks, final hashes, and the completed historical-source
audit.

## Citation and license

The original repository material is licensed under
[CC BY 4.0](../LICENSE). When the license requires attribution, credit
**Samuil Petkov** and follow the repository-level
[scope and attribution notice](../LICENSE_SCOPE.md). Scholarly citation
metadata are provided in [`CITATION.cff`](../CITATION.cff).
