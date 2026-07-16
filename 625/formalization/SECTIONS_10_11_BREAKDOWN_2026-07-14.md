# Sections X--XI formalization breakdown -- 2026-07-14

## Scope and status rule

### Status reconciliation (updated 2026-07-16)

This reconciliation supersedes older submission-time labels below without
changing module-count, hash, or full-build metrics.  The exact returned
statements N, O, P, and Q were independently audited for statement identity,
source policy, axioms, and mathematical dependency boundary, ported into
tracked source, and replayed successfully in local Lean 4.31 warning-fatal
builds.  Acceptance is strictly limited to the atomic theorem and displayed
hypotheses in each row: these leaves do not supply omitted graph-law transport
or probabilistic inputs, do not turn a pointwise event into a simultaneous
one, and do not by themselves complete Section X, Section XI, or the final
Erdős 625 theorem.

This document records the accepted deterministic Lean atoms and the exact
remaining proof obligations for manuscript Sections 10 and 11.  A declaration
marked **local proved** is accepted Lean 4.31 source.  Aristotle service output
is quarantined provenance only; the request ledger below records the completed
isolated builds and standard-axiom reports, but accepted local Lean 4.31 source
remains authoritative and no service source was imported directly.

The exact one-event statement of Lemma 10.1 and the exact quantifier-correct
uniform statement of Lemma 10.2 are now complete.  The concrete Section IX
seed/`Lambda` asymptotics, Section 11, and `Erdos625Statement` remain open.

The X01--X02 graph-law and probability lane is now closed locally:
`Section10InducedRestriction.lean`, `Section10QuarterDensityEvent.lean`,
`Section10QuarterDensityLimit.lean`, `Section10QuarterDensityLift.lean`, and
`Section10UniformQuarterDensityEvent.lean` prove one full-sequence event whose
probability tends to one and which controls every subset at least as large as
the cutoff.  `Section10QuarterDenseChain.lean` proves the exact finite clique
chain under its displayed survival hypothesis, and
`Section10QuarterChainSurvival.lean` proves that hypothesis eventually at the
chosen manuscript scales.  The parameter, survival-transport, complement, and
chain adapters are now assembled further in
`Section10QuarterChainIndependentBlock.lean`: one event of probability tending
to one supplies an independent block of the same deterministic size in every
sufficiently large vertex set, and the accepted greedy theorem gives its exact
ceiling-division chromatic bound.  The numerical conversion, exact
manuscript-form linear event, parameter-independent failure sequence, and
deficit-indexed leftover-event packaging are now accepted in the four
quarter-chain continuation modules.  `Section10UniformAmplification.lean`
then closes X04 under the displayed seed hypothesis.  The current frontier is
the concrete Section IX capacity seed and `Lambda` asymptotics needed to
instantiate that theorem, followed by the Section XI inputs.

## Accepted local atoms

| Declaration | Manuscript role | Status | Exact limitation |
|---|---|---:|---|
| `exists_vertex_quarter_degree`, `quarterDense_all_larger_of_all_exact` | deterministic density lift and averaging steps in Lemma 10.1 | local proved | Quarter density on every set of one fixed size lifts to every larger set, and the denominator-cleared quarter-density premise then yields one vertex with `card - 1 <= 4 * degree`.  These theorems do not prove the random simultaneous-density event or construct the full greedy colouring. |
| `quarterRecurrence_lowerBound` | recurrence (10.3a) | local proved | From `(s t - 1) / 4 <= s (t+1)` it proves `4^(-t) * s 0 - 1/3 <= s t`.  The required number of iterations and independent-set extraction are not included. |
| `cutoffComplementAllLargerQuarterDenseEvent`, `cutoffComplementAllLargerQuarterDenseEvent_probability_tendsto_one` | one simultaneous random quarter-density event | defined; local proved | Along the full sequence, one event of probability tending to one asserts quarter density in the complement graph for every subset at least as large as the cutoff.  It does not itself initialize the clique chain, convert a complement clique to an independent set, or invoke greedy colouring. |
| `exists_quarterDense_clique_chain`, `quarterChain_shifted_survival_eventually` | finite quarter-density chain and chosen-scale survival | local proved | Under the uniform density premise, the finite theorem produces a clique of the requested length and a common-neighbour residual; the chosen manuscript start and step scales eventually satisfy its shifted-potential survival premise.  The exact-start subset, cutoff/start comparison, complement-to-independent conversion, and uniform greedy instantiation remain open. |
| `quarterDensityCutoff_le_quarterChainStart_eventually`, `one_le_quarterDensityCutoff_eventually`, `quarterChainSteps_tendsto_atTop`, `one_le_quarterChainSteps_eventually`, `quarterChainSteps_real_lower_bound_eventually` | X03 parameter package | local proved | The cutoff/start and positivity facts are explicit, the step count tends to infinity, and its floor retains the lower bound `log n/(14 log 4)`. |
| `quarterChain_shifted_survival_of_start_le_card`, `quarterChain_shifted_survival_all_larger_eventually`, `isIndepSet_of_compl_isClique` | X03 transport and complement adapters | local proved | The exact shifted potential transports to every larger initial set, and a complement clique is converted to an original-graph independent set without changing the vertex set. |
| `quarterChainIndependentBlockEvent`, `cutoffComplementAllLargerQuarterDenseEvent_subset_independentBlockEvent_eventually`, `quarterChainIndependentBlockEvent_probability_tendsto_one`, `chromaticNumberNat_induce_le_of_independentBlockEvent` | X03 uniform independent-block/greedy package | defined; local proved | On one event of probability tending to one, every set above the cube-root start contains a logarithmic independent block, and every induced graph satisfies the exact ceiling-division greedy bound. |
| `quarterChain_greedy_count_real_upper_bound_eventually`, `quarterChainGreedyColorCost`, `quarterChainGreedyColorCost_eventually_le_linear_log_plus_cubeRoot` | X03 manuscript-constant numerical conversion | defined; local proved | The exact piecewise greedy cost is eventually bounded uniformly by `C * u / log n + n^(1/3)` with the explicit positive choice `C = 14 * log 4 + 2`. |
| `quarterChainIndependentBlockFailure`, `quarterChainIndependentBlockFailure_tendsto_zero` | parameter-independent Lemma 10.1 error | defined; local proved | The complement probability of the single independent-block event depends only on `n` and tends to zero, so it is independent of all later seed, radius, and deficit choices. |
| `quarterChainLinearColoringEvent`, `exists_quarterChainLinearColoringEvent_probability_tendsto_one`, `exists_quarterChainLinearColoringEvent_full_control` | exact manuscript Lemma 10.1 | defined; local proved | One positive absolute constant gives the simultaneous induced-colouring inequality on one event of probability tending to one, together with the quantitative complement bound.  This closes Lemma 10.1 and supplies the colouring input to the downstream Lemma 10.2 theorem. |
| `quarterChainLeftoverBound`, `quarterChainIndependentBlockEvent_subset_simultaneousLeftoverColoringEvent`, `quarterChainLeftoverBound_probability_tendsto_one`, `quarterChainLeftoverBound_compl_probability_le`, `erdos625Statement_of_capacity_quarterChainLeftover_thresholds` | deficit-indexed leftover event and reduced final seam | defined; local proved | Every deterministic deficit sequence has the required simultaneous leftover tail, with the same failure sequence.  The conditional target seam is thereby reduced from five inputs to four; capacity, chromatic, and threshold inputs remain open. |
| `amplificationBase`, `amplificationRadius`, `gapBase`, `amplificationError`, `amplificationRadius_tendsto_atTop`, `sqrt_seedTerm_isLittleO`, `sqrt_radiusTerm_isLittleO`, `realCubeRoot_isLittleO`, `one_isLittleO_gapScale`, `amplificationError_isLittleO_gapBase` | scales (10.10)--(10.12) | defined; local proved | `r_n = sqrt(n/(log n)^4)` tends to infinity.  The seed implication, transformed-radius term, real cube-root term, and additive constant are all little-o of `n/(log n)^3`; their displayed sum is assembled into one little-o statement under the exact hypotheses.  The concrete Section IX seed and its `Lambda` asymptotics remain open. |
| `quarterDensity_unionBound_tendsto_zero` | analytic union bound in Lemma 10.1 | local proved | For each fixed positive lower-tail constant, the union cost at `u0 = ceil(n^(1/4))` tends to zero along the full sequence.  No graph-law transport or simultaneous random event is proved. |
| `simultaneous_induced_chromatic_bound` | deterministic greedy seam in Lemma 10.1 | local proved | One graph-uniform hypothesis, quantified over every sufficiently large induced subset, yields the advertised chromatic bound for every requested leftover set.  The downstream quarter-chain event now supplies that internal universal hypothesis. |
| `binomialRandom_map_ncard_edgeSet_singleton` | fixed finite binomial edge-count law before Lemma 10.1 | local proved | The pushforward edge-count measure has the exact binomial singleton mass for Mathlib's finite binomial random graph.  Transport to each fixed induced complement graph, the lower-quarter tail, and the simultaneous event remain open. |
| `randomGraphMeasure_map_compl` | ambient complement symmetry before Lemma 10.1 | local proved | The finite labelled `G(n,1/2)` law is exactly invariant under graph complementation. This does not provide the native pushforward through a fixed induced restriction, the lower-quarter tail, or the simultaneous event. |
| `failure_probability_le_add_of_two_success_events` | quantitative capacity/leftover intersection in Lemma 10.2 | local proved | If two supplied success events imply `Good`, its failure probability is at most the sum of their supplied failure bounds, without independence.  The downstream uniform theorem instantiates this seam under the displayed seed inequality. |
| `uniformAmplificationError`, `quarterChainLinearColoringEvent_mono_constant`, `cochromaticCapacityDeficitRadius_lt_displayed`, `capacityAmplification_inter_linear_subset_cochromaticUpperEvent`, `cochromaticUpperEvent_compl_probability_le_exp_add`, `exists_uniform_cochromatic_amplification` | exact quantifier-correct manuscript Lemma 10.2 | defined; local proved | One absolute `C ≥ 1` and one nonnegative deterministic `epsilon_n → 0` are chosen before all deterministic `k_n`, `Lambda_n`, and `r_n`.  Under eventual `Lambda_n ≥ 0`, `r_n > 0`, and the displayed seed inequality, the cochromatic-upper-event failure is eventually bounded by `exp(-r_n) + epsilon_n`.  No independence is assumed.  The concrete Section IX seed/`Lambda` asymptotics, Section XI inputs, and final target remain open. |
| `chromaticLowerEvent`, `cochromaticUpperEvent` | threshold events in Section 11 | defined | These are the strict natural chromatic lower event and real cochromatic upper event with deterministic error. |
| `thresholdIntersection_subset_gapEvent` | deterministic Section 11 event inclusion | local proved | Given the exact threshold separation, the intersection is contained in `gapEvent`; the strict chromatic event contributes the necessary `+1`. |
| `explicitThresholdIntersection_subset_gapEvent` | expanded form of (11.2) | local proved | The same inclusion displays the constant explicitly.  It supplies no sequence choice, probability limit, or eventual separation theorem. |
| `tendsto_measure_inter_one` | probability intersection in Section 11 | local proved | Two measurable event families whose probabilities tend to one have intersection probability tending to one, with no independence hypothesis and with sample spaces allowed to depend on `n`. |
| `baseScale`, `eventually_explicit_gap_threshold` | eventual threshold (11.2) | defined; local proved | Abstract root separation with vanishing `rho` and `a = o(baseScale)` eventually gives the explicit separated thresholds, including the strict-event `+1`.  The actual manuscript sequences and upstream hypotheses are not instantiated. |
| `tendsto_explicit_gap_scale_atTop` | divergence used for (11.3) | local proved | The explicit positive scale tends to infinity along the full sequence.  The actual fixed-`M` probability-tail implication is not yet assembled. |
| `fixedThreshold_tail_of_movingThreshold` | moving-to-fixed threshold implication in (11.3) | local proved | An assumed probability-one tail above a deterministic threshold tending to infinity implies every fixed-threshold tail, even for `n`-dependent finite sample spaces.  The concrete moving-threshold tail remains open. |
| `strictLower_probability_tendsto_one_of_atMost_tendsto_zero` | strict chromatic lower-event bridge | local proved | A full-sequence probability-zero tail for `X n <= k n` gives probability one for `k n < X n`, with `n`-dependent sample spaces.  The actual chromatic at-most tail and threshold are not supplied. |
| `capacityDeficitEvent`, `simultaneousLeftoverColoringEvent`, `capacityDeficitEvent_probability_tendsto_one`, `cochromaticNumber_le_of_capacityDeficit_and_leftover`, `tendsto_measure_one_of_eventually_subset`, `erdos625Statement_of_capacity_leftover_thresholds` | conditional Sections 10--11 closure | defined; local proved under explicit hypotheses | The capacity and simultaneous-leftover events have the correct internal quantifiers; a rounded capacity tail is derived from the displayed seed/radius assumptions; and five named full-sequence inputs imply `Erdos625Statement`.  The quarter-chain specialization above discharges the leftover-tail input, but the result remains conditional rather than an unconditional target proof. |

The previously accepted amplification infrastructure also includes the induced
`k`-cocolourable capacity, its full-capacity event, one-vertex block
oscillation, graph-law tails, rare-seed expectation inversion (10.7), the
one-sided lower-tail estimate (10.8), a maximizing core with exact complement
size, and deterministic concatenation (10.9).  The new uniform-amplification
module assembles those interfaces with Lemma 10.1 under the displayed seed
hypothesis; it does not prove that concrete seed.

## Section X dependency DAG

```text
fixed-set lower-quarter binomial tail
  -> union bound over all u0-subsets
  -> one quarter-density event for every set of size at least u0
  -> quarter-degree vertex + quarter recurrence
  -> an independent set of size c log n in every set of size at least n^(1/3)
  -> greedy colouring on every U, on the same event
  -> Lemma 10.1 (simultaneous leftover colouring)

rare cochromatic seed
  + induced-capacity concentration (10.7)--(10.8)
  + maximizing core and concatenation (10.9)
  + Lemma 10.1's one simultaneous event
  -> Lemma 10.2 with one universal C and epsilon_n
  -> seed/radius scale estimates (10.10)--(10.12)
  -> cochromatic upper tail (10.13)
```

## Next execution wave -- 2026-07-16

The X01--X04 wave, including exact Lemmas 10.1 and 10.2, is now accepted.
The active checkpoint is the concrete Section IX seed/`Lambda` asymptotics
needed to instantiate the uniform theorem and then supply the Section XI
inputs.  The historical X01--X04 request breakdown below is retained as
provenance, not as current open work.

### Execution ownership: Terra Max with Aristotle

Terra Max is the designated primary implementation agent for this wave.
Aristotle is its theorem-scoped proof-search assistant, not a second source of
truth.  Terra Max owns the complete loop:

1. read the current local declarations and preserve their exact quantifiers;
2. prepare the full-theorem and leaf Aristotle payloads listed below;
3. poll requests and keep every return quarantined until review;
4. reconstruct or port useful arguments into the repository's Lean 4.31
   source instead of importing service workspaces;
5. compile focused declarations warning-fatally, inspect their mathematics,
   scan trust boundaries, and audit axioms;
6. integrate accepted leaves into the modular import tree, generated
   self-contained proof, ledger, and user-facing documentation;
7. require green branch and `main` CI before calling a batch accepted.

Terra Max may send both a whole target and its independent leaves to Aristotle
at the same time.  It should use returned compiler diagnostics to refine only
the failing leaf, while continuing local work on other leaves.  It must not
replace a hard theorem by an assumption, strengthen a hypothesis silently,
weaken a conclusion, change a full-sequence limit to a subsequence, or turn a
fixed-set result into a simultaneous event.  If a service return proves a
nearby statement, Terra Max records that nearby statement honestly or rejects
the return.

At the historical handoff, Terra Max was to begin with X01 below; X02--X04
were downstream work packages, not licenses to assume X01.  All four are now
accepted locally.  arXiv packaging remains secondary until the exact final
target is fully represented in Lean or is still described explicitly as a
candidate partial formalization.

### X01 -- fixed induced-restriction law and fixed-set tail

1. Define the fixed restriction map on the subtype carried by
   `S : Finset (Fin n)` and prove the native pushforward
   ```text
   (randomGraphMeasure n).map
       (fun G : LabeledGraph n => G.induce (S : Set (Fin n)))
     = SimpleGraph.binomialRandom (↥(S : Set (Fin n))) halfProbability.
   ```
   Prove the complement version by composing this restriction law with the
   accepted `randomGraphMeasure_map_compl`; do not hide the restriction law
   behind complement invariance.
2. Push the restricted graph law through edge-set cardinality and identify the
   scalar law with the half-binomial law on `S.card.choose 2` trials.  Keep the
   natural-valued law and the real-cast law as separate declarations if that
   avoids coercion-heavy proofs.
3. Derive the exact fixed-`S` lower-quarter estimate from
   `binomialHalf_lowerQuarter_le_exp`.  The theorem must quantify over one
   deterministic `S`; it must not be named or documented as a simultaneous
   event.

Planned Aristotle calls for X01 will be submitted in parallel as redundant
proof search, with the current repository imports and exact target
declarations:

- `AX-X01-FULL`: the complete fixed induced-restriction pushforward;
- `AX-X01-FIBRE`: the finite fibre-cardinality/bijection lemma for one target
  induced graph;
- `AX-X01-MAP`: the measure-extensionality assembly from the fibre count;
- `AX-X01-SCALAR`: the edge-count pushforward and natural/real cast bridge;
- `AX-X01-TAIL`: the fixed-set lower-quarter bound assuming the scalar
  pushforward equality.

The already submitted X01 service task remains status-only until it reaches a
terminal state.  Completion percentage, a dashboard badge, or a returned file
is not acceptance.  If a full-theorem request fails, its exact Lean diagnostic
is fed only to the smallest corresponding leaf request; repeated blind retries
are not part of the workflow.

### X02 -- one simultaneous quarter-density event

1. Define the measurable event saying that every cutoff-size subset has the
   required quarter-density property in the complement graph.
2. Union-bound its failure event over the literal finite family of
   `quarterDensityCutoff n`-subsets, using the X01 fixed-set tail.
3. Combine the finite probability bound with
   `quarterDensity_unionBound_tendsto_zero` to obtain one full-sequence
   probability-one event.
4. Reuse the already proved `quarterDense_all_larger_of_all_exact` on that one
   event to obtain the internal statement for every larger subset.  No new
   Aristotle request is needed for this deterministic lift.

Planned Aristotle calls:

- `AX-X02-EVENT`: measurability and exact complement-of-intersection/union
  identities for the simultaneous event;
- `AX-X02-UNION`: the finite measure union bound with the cutoff-subset count;
- `AX-X02-LIMIT`: the short limit assembly from the explicit failure bound.

### X03 -- recurrence chain and uniform greedy instantiation

1. Combine `exists_vertex_quarter_degree`,
   `quarterDense_all_larger_of_all_exact`, and
   `quarterRecurrence_lowerBound` into an explicit neighbourhood-deletion
   chain.
2. Prove the chain survives for the required integer number of steps and
   extracts an independent set of size at least `c * log n` whenever the
   current induced set has size at least the manuscript cutoff.
3. Instantiate `simultaneous_induced_chromatic_bound` on the X02 event, with
   all rounding and positivity obligations explicit, to close the simultaneous
   leftover-colouring input to Lemma 10.2.

Planned Aristotle calls:

- `AX-X03-CHAIN`: finite chain construction and pairwise nonadjacency;
- `AX-X03-SURVIVE`: real/natural rounding and survival inequality;
- `AX-X03-INSTANTIATE`: parameter arithmetic for the accepted greedy theorem;
- `AX-X03-FULL`: the combined deterministic implication, submitted in parallel
  as a cross-check rather than trusted as a monolithic replacement.

### X04 -- Lemma 10.2 and Sections X--XI seam

Accepted in `Section10UniformAmplification.lean`.  The theorem assembles the
already proved capacity seed inversion, one-sided lower tail, maximizing core,
deterministic concatenation, simultaneous colouring event, and two-event
failure bound.  It chooses one absolute `C ≥ 1` and one nonnegative
deterministic `epsilon_n -> 0` before quantifying over `k_n`, `Lambda_n`, and
`r_n`, and gives the eventual failure bound `exp(-r_n) + epsilon_n` under the
displayed seed hypothesis.

The earlier planned Aristotle calls are retained as request-design provenance:

- `AX-X04-QUANTIFIERS`: a statement-only audit of the required quantifier
  order and uniformity;
- `AX-X04-ASSEMBLY`: the finite probability inequality under the already
  accepted input tails;
- `AX-X04-LIMIT`: the full-sequence `exp (-r_n) + epsilon_n -> 0` closure.

The remaining work is not another abstract Lemma 10.2 assembly: it is the
concrete Section IX seed and `Lambda` asymptotics, followed by the concrete
radius/error specialization and Section XI tail/threshold inputs.

### Parallel Section IX lane

While X01 service calls run, use separate requests for the next Section IX
bridges without allowing them to block Section X:

- `AIX-01-REAL`: actual-residual real-weight sum bounded by the accepted real
  polymer product;
- `AIX-02-ENNREAL`: a genuine `ENNReal` polymer analogue, kept separate from
  the already proved one-sided subfamily inclusion;
- `AIX-03-CYCLE-CODE`: an injective, weight-preserving minimal-cycle-to-walk
  encoding;
- `AIX-04-CONDITIONED-LAW`: the exact conditioned residual-table law, without
  assuming the attachment estimate it is meant to support.

These four targets are logically distinct.  In particular, the accepted
one-sided `ENNReal` subfamily inequality is not an `ENNReal` polymer bound, and
no request may conflate the actual residual family with the potential
`residualQ` kernel.

### Acceptance and compute checkpoint

Every Aristotle payload contains one exact target placeholder and no project
axiom.  Returned source stays in the ignored candidate area and is never
committed directly.  A candidate becomes repository source only after:

1. statement and quantifier comparison against the local target;
2. manual proof review and adaptation to Lean 4.31/current Mathlib;
3. warning-fatal focused compilation, placeholder/project-axiom scan, and
   `#print axioms` showing only standard foundational axioms;
4. root import, `AxiomAudit.lean`, ledger, README, and generated
   `Erdos625SelfContained.lean` synchronization;
5. fresh branch CI passing the modular build, generated-file freshness, and
   warning-fatal self-contained build before any promotion to `main`;
6. green `main` CI after promotion.

X01--X04, including the exact manuscript-form Lemmas 10.1 and 10.2, are now
accepted.  The active decision checkpoint is their concrete Section IX
seed/`Lambda` instantiation.

The remaining Section X obligations, in dependency order, are:

1. **Completed locally:** the fixed induced complement law, lower-quarter
   tail, finite subset union bound, and full-sequence probability-one event are
   assembled in `cutoffComplementAllLargerQuarterDenseEvent`.
2. **Completed locally:** the exact-size-to-all-larger deterministic lift is
   used inside that one event with an internal `∀ U`.
3. **Completed locally:** the cutoff/start arithmetic,
   survival transport, finite-chain instantiation, complement conversion, and
   one-event uniform independent-block theorem are proved.  The explicit
   logarithmic lower bound on the block length is also proved.
4. **Completed locally:** the exact ceiling-division conclusion is converted
   to the displayed bound (10.3), simultaneously for every `U` on one event,
   with `C = 14 * log 4 + 2`.  The deficit-indexed leftover event and one
   deterministic failure sequence tending to zero are formalized.
5. **Completed locally:** Lemma 10.2 is assembled from the proved capacity
   expectation and lower-tail bounds, the maximizing core, deterministic
   concatenation, and the simultaneous event.  The theorem chooses `C ≥ 1`
   and a nonnegative deterministic `epsilon_n -> 0` before quantifying over
   deterministic `k_n`, `Lambda_n`, and `r_n`; the error sequence does not
   depend on any of those choices.  Its conclusion is uniform for every
   deterministic eventually positive `r_n`, under the displayed seed
   inequality.
6. **Completed locally as deterministic scale facts:**
   `r_n = sqrt(n/(log n)^4)` tends to infinity; the seed hypothesis
   `Lambda_n = o(n/(log n)^4)` gives the required seed square-root term; and
   `sqrt(n*r_n)/log n`, the real cube-root term, and the additive constant are
   each `o(n/(log n)^3)`.  These limits do not supply the probabilistic seed
   or its concrete `Lambda_n`.
7. Prove the concrete Section IX seed and `Lambda_n` asymptotics, define the
   actual deterministic error `a_n`, and instantiate the proved Lemma 10.2 to
   obtain (10.13), including `exp(-r_n) + epsilon_n -> 0` on the full sequence.

No pointwise-in-`U` probability statement can replace steps 2--4: the
capacity-attaining complement is chosen from the random graph and therefore
must be controlled by the same simultaneous event.

## Section XI dependency DAG

```text
Section 4 chromatic lower tail
  + Section 10 cochromatic upper tail
  + eventual root separation minus a_n
  -> probabilities of both threshold events tend to one
  -> probability of their intersection tends to one (no independence)
  + deterministic threshold-intersection inclusion
  -> probability of gapEvent tends to one
  -> Erdos625Statement

explicit gap-scale divergence
  + gapEvent tail
  -> every fixed-M gap tail (11.3)
```

The accepted `Section11EventAssembly.lean` module supplies the pointwise set
inclusion.  `Section11AsymptoticAssembly.lean` now supplies the generic
full-sequence intersection theorem without independence, the abstract eventual
threshold theorem, and explicit scale divergence.
`Section10_11ConditionalAssembly.lean` packages the rounded capacity tail,
quantifier-correct simultaneous-leftover interface, deterministic
cochromatic bound, measure monotonicity, and the conditional five-input target
closure.  `Section10QuarterChainLeftoverEvent.lean` supplies the leftover tail
and a four-input specialization.  The remaining actual sequence/tail
instantiation is:

1. Define the manuscript sequences `kChi n`, `kCo n`, and `a n`, and connect
   their Lean definitions to the Section 4, Section 5, Section 9, and Section
   10 outputs without replacing an eventual statement by a subsequence.
2. Instantiate the proved eventual threshold theorem, including the strict-
   event `+1`, by proving its root-separation, `rho_n -> 0`, and
   `a_n = o(baseScale)` hypotheses for the actual sequences.
3. Prove measurability and full-sequence convergence to one for the actual
   chromatic-lower and cochromatic-upper event probabilities.  For the
   chromatic side, the accepted strict-lower bridge reduces this to proving
   the corresponding at-most probability tends to zero at the actual
   threshold.
4. Use the proved uniform Lemma 10.2 with the concrete Section IX seed to
   obtain the actual cochromatic upper tail and prove the eventual
   cochromatic threshold comparison.  Then supply those, the chromatic tail,
   and the gap threshold to the proved conditional theorem
   `erdos625Statement_of_capacity_leftover_thresholds`.  Its internal
   intersection step uses no independence assumption and its measure-
   monotonicity closure need not be reproved.
5. Use the proved explicit scale divergence together with the actual gap-event
   tail to derive the fixed-`M` probability tail (11.3).

Every limit above is an `atTop` statement along all natural `n`.  Phase
uniformity near independence-number jumps must therefore be inherited from the
upstream full-sequence theorems, not added as a density-one or subsequence
qualification.

## Aristotle request ledger

The initial ten requests completed successfully and are quarantined.  Their isolated
service projects reported successful builds and only standard axioms.  The
corresponding Lean 4.31 declarations were replayed and accepted locally; those
local files are authoritative and no service source was imported directly.

| Section | Isolated task | Request ID | Service/repository status |
|---|---|---|---|
| X | quarter recurrence | `6b7ec5a6-6bfc-4926-b699-bc20977f66fd` | completed; quarantined; local `QuarterRecurrence.lean` accepted |
| X | quarter-density high-degree vertex | `b275f7c1-dfba-4c1c-9ead-0112c4e54020` | completed; quarantined; local `QuarterDensityDegree.lean` accepted |
| X | growing amplification radius | `ff666a22-b192-489c-8c66-ef0da63a0daa` | completed; quarantined; local `Section10AmplificationScales.lean` accepted |
| X | seed square-root scale | `288de3bd-372f-4802-8070-60c0eef7f3c2` | completed; quarantined; local `Section10AmplificationScales.lean` accepted |
| X | transformed-radius scale | `47457fc6-f6ff-4702-81de-6b5956bb5db9` | completed; quarantined; locally replayed and accepted in `Section10AmplificationScales.lean` |
| X | real cube-root scale | `5000978b-34fd-4d94-bbe7-f2a13b4b05bc` | completed; quarantined; locally replayed and accepted in `Section10AmplificationScales.lean` |
| X | additive constant scale | `67ac866d-2bd9-4cb8-a19f-a0f57ee7ffeb` | completed; quarantined; locally replayed and accepted in `Section10AmplificationScales.lean` |
| XI | probability intersection | `cb039d44-1e81-4b0b-a0e2-481eeb8fc8a0` | completed; quarantined; local `Section11AsymptoticAssembly.lean` accepted |
| XI | eventual parameter threshold | `e451963a-2f93-407c-aa0e-28467d87642e` | completed; quarantined; local `Section11AsymptoticAssembly.lean` accepted |
| XI | explicit gap-scale divergence | `764866b6-c929-48fb-b476-ec61925d250c` | completed; quarantined; local `Section11AsymptoticAssembly.lean` accepted |
| X | exact binomial edge-count singleton law | `f3ca6d6a-200a-42bc-810e-9799b721f7e7` | completed; returned revision differed; audited and replayed warning-fatally on the repository revision as `Section10BinomialEdgeCount.lean` |

The service tasks are redundant candidate generation only.  A returned proof
must still be reviewed, reconstructed or ported to Lean 4.31, source-scanned,
built with warnings fatal, axiom-audited, and integrated without changing its
quantifiers before it can become accepted repository source.

### Wave-two requests submitted 2026-07-15

These four additional projects were independently statement-audited and
elaborated under the service's exact Lean 4.28/Mathlib revision before
submission.  Each source-only payload contained exactly one intentional
target `sorry` and no cache or binary artifacts.  Their exact returned
statements have now passed independent review and the local Lean 4.31
acceptance gates; the tracked ports named below, not the quarantined service
workspaces, are authoritative.  The scope column remains a strict limitation.

| Section | Isolated target | Request ID | Status at submission | Scope |
|---|---|---|---:|---|
| X | `quarterDensity_unionBound_tendsto_zero` | `e569e37b-3486-4909-b5dd-3ebbbbe64049` | `COMPLETE`; audited, ported, Lean 4.31 warning-fatal accepted | full-sequence analytic union-bound decay only; graph-law transport remains separate; local authority is `Section10QuarterUnionDecay.lean` |
| X | `simultaneous_induced_chromatic_bound` | `78638bbc-5941-4275-9ea3-b0022cc640dc` | `COMPLETE`; audited, ported, Lean 4.31 warning-fatal accepted | deterministic greedy colouring under one supplied uniform internal-`∀ U` hypothesis; it does not prove that random event; local authority is `Section10SimultaneousGreedyColoring.lean` |
| X | `amplificationError_isLittleO_gapBase` | `3fcd655d-a5cd-42b8-bcb0-85767126b3a7` | `COMPLETE`; audited, ported, Lean 4.31 warning-fatal accepted | exact deterministic (10.10)--(10.12) error assembly under its displayed little-o hypotheses; local authority is `Section10AmplificationScales.lean` |
| XI | `fixedThreshold_tail_of_movingThreshold` | `20da6297-c83e-4800-8724-cc2551a31409` | `COMPLETE`; audited, ported, Lean 4.31 warning-fatal accepted | moving-threshold tail implies every fixed-threshold tail only; intentionally redundant with accepted measure monotonicity; local authority is `Section11AsymptoticAssembly.lean` |

The quantitative two-event failure seam and strict-lower complement bridge
were proved locally in `Section10CapacityLeftoverQuantitative.lean` and
`Section11ChromaticLowerTailBridge.lean`; they are not attributed to an
Aristotle completion.  The former is now consumed by the locally accepted
`Section10UniformAmplification.lean`; its concrete Section IX seed input is
still open.  Historical source-only proposal packages split the Section X
chain into fixed-subset quarter tail, density lift, recurrence-chain,
survival-asymptotic, uniform leftover-event, and final amplification atoms.
They remain scheduling/proof-search provenance only: queued, running, failed,
or completed service status does not make any target accepted until the local
Lean 4.31 warning-fatal, trust-scan, axiom, and scope gates pass.
