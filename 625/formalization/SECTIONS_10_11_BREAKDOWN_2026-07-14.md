# Sections X--XI formalization breakdown -- 2026-07-14

## Scope and status rule

### Status reconciliation (2026-07-15)

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

Neither Lemma 10.1, Lemma 10.2, Section 11, nor `Erdos625Statement` is complete.

## Accepted local atoms

| Declaration | Manuscript role | Status | Exact limitation |
|---|---|---:|---|
| `exists_vertex_quarter_degree` | deterministic averaging step in Lemma 10.1 | local proved | The denominator-cleared quarter-density premise yields one vertex with `card - 1 <= 4 * degree`.  It does not prove the random simultaneous-density event or construct the full greedy colouring. |
| `quarterRecurrence_lowerBound` | recurrence (10.3a) | local proved | From `(s t - 1) / 4 <= s (t+1)` it proves `4^(-t) * s 0 - 1/3 <= s t`.  The required number of iterations and independent-set extraction are not included. |
| `amplificationBase`, `amplificationRadius`, `gapBase`, `amplificationError`, `amplificationRadius_tendsto_atTop`, `sqrt_seedTerm_isLittleO`, `sqrt_radiusTerm_isLittleO`, `realCubeRoot_isLittleO`, `one_isLittleO_gapScale`, `amplificationError_isLittleO_gapBase` | scales (10.10)--(10.12) | defined; local proved | `r_n = sqrt(n/(log n)^4)` tends to infinity.  The seed implication, transformed-radius term, real cube-root term, and additive constant are all little-o of `n/(log n)^3`; their displayed sum is assembled into one little-o statement under the exact hypotheses.  The probabilistic seed and Lemma 10.2 remain open. |
| `quarterDensity_unionBound_tendsto_zero` | analytic union bound in Lemma 10.1 | local proved | For each fixed positive lower-tail constant, the union cost at `u0 = ceil(n^(1/4))` tends to zero along the full sequence.  No graph-law transport or simultaneous random event is proved. |
| `simultaneous_induced_chromatic_bound` | deterministic greedy seam in Lemma 10.1 | local proved | One graph-uniform hypothesis, quantified over every sufficiently large induced subset, yields the advertised chromatic bound for every requested leftover set.  The random event supplying that internal universal hypothesis remains open. |
| `binomialRandom_map_ncard_edgeSet_singleton` | fixed finite binomial edge-count law before Lemma 10.1 | local proved | The pushforward edge-count measure has the exact binomial singleton mass for Mathlib's finite binomial random graph.  Transport to each fixed induced complement graph, the lower-quarter tail, and the simultaneous event remain open. |
| `randomGraphMeasure_map_compl` | ambient complement symmetry before Lemma 10.1 | local proved | The finite labelled `G(n,1/2)` law is exactly invariant under graph complementation. This does not provide the native pushforward through a fixed induced restriction, the lower-quarter tail, or the simultaneous event. |
| `failure_probability_le_add_of_two_success_events` | quantitative capacity/leftover intersection in Lemma 10.2 | local proved | If two supplied success events imply `Good`, its failure probability is at most the sum of their supplied failure bounds, without independence.  Neither probabilistic input is proved here. |
| `chromaticLowerEvent`, `cochromaticUpperEvent` | threshold events in Section 11 | defined | These are the strict natural chromatic lower event and real cochromatic upper event with deterministic error. |
| `thresholdIntersection_subset_gapEvent` | deterministic Section 11 event inclusion | local proved | Given the exact threshold separation, the intersection is contained in `gapEvent`; the strict chromatic event contributes the necessary `+1`. |
| `explicitThresholdIntersection_subset_gapEvent` | expanded form of (11.2) | local proved | The same inclusion displays the constant explicitly.  It supplies no sequence choice, probability limit, or eventual separation theorem. |
| `tendsto_measure_inter_one` | probability intersection in Section 11 | local proved | Two measurable event families whose probabilities tend to one have intersection probability tending to one, with no independence hypothesis and with sample spaces allowed to depend on `n`. |
| `baseScale`, `eventually_explicit_gap_threshold` | eventual threshold (11.2) | defined; local proved | Abstract root separation with vanishing `rho` and `a = o(baseScale)` eventually gives the explicit separated thresholds, including the strict-event `+1`.  The actual manuscript sequences and upstream hypotheses are not instantiated. |
| `tendsto_explicit_gap_scale_atTop` | divergence used for (11.3) | local proved | The explicit positive scale tends to infinity along the full sequence.  The actual fixed-`M` probability-tail implication is not yet assembled. |
| `fixedThreshold_tail_of_movingThreshold` | moving-to-fixed threshold implication in (11.3) | local proved | An assumed probability-one tail above a deterministic threshold tending to infinity implies every fixed-threshold tail, even for `n`-dependent finite sample spaces.  The concrete moving-threshold tail remains open. |
| `strictLower_probability_tendsto_one_of_atMost_tendsto_zero` | strict chromatic lower-event bridge | local proved | A full-sequence probability-zero tail for `X n <= k n` gives probability one for `k n < X n`, with `n`-dependent sample spaces.  The actual chromatic at-most tail and threshold are not supplied. |
| `capacityDeficitEvent`, `simultaneousLeftoverColoringEvent`, `capacityDeficitEvent_probability_tendsto_one`, `cochromaticNumber_le_of_capacityDeficit_and_leftover`, `tendsto_measure_one_of_eventually_subset`, `erdos625Statement_of_capacity_leftover_thresholds` | conditional Sections 10--11 closure | defined; local proved under explicit hypotheses | The capacity and simultaneous-leftover events have the correct internal quantifiers; a rounded capacity tail is derived from the displayed seed/radius assumptions; and five named full-sequence inputs imply `Erdos625Statement`.  The theorem does not prove any of those concrete manuscript inputs and is not an unconditional target proof. |

The previously accepted amplification infrastructure also includes the induced
`k`-cocolourable capacity, its full-capacity event, one-vertex block
oscillation, graph-law tails, rare-seed expectation inversion (10.7), the
one-sided lower-tail estimate (10.8), a maximizing core with exact complement
size, and deterministic concatenation (10.9).  Those interfaces do not by
themselves prove Lemma 10.2.

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

The remaining Section X obligations, in dependency order, are:

1. Define the complement-graph quarter-density event at
   `u0 = ceil(n^(1/4))`.  The exact singleton edge-count law for Mathlib's
   finite binomial random graph is proved.  Transport it to the fixed induced
   complement graph and then to the
   lower-quarter binomial tail, count all `u0`-subsets, and prove that its
   failure probability tends to zero along the full sequence.
   The currently isolated fixed-subset task has a strict boundary: its hard
   missing step is the native pushforward law for restriction of
   `randomGraphMeasure n` to one fixed induced set.  Complement invariance is
   now a checked finite-uniform bijection leaf, and the binomial lower-quarter
   tail follows after the restriction law.  A fixed-set tail alone must not
   be recorded as the simultaneous quarter-density event: the latter still
   needs the subset union bound and the internal universal quantifier.
2. Prove by averaging that the same event gives quarter density in every
   larger vertex set.  This must be one event with an internal `∀ U`, not
   a separately chosen event or exceptional set for each `U`.
3. Combine that event with `exists_vertex_quarter_degree` and
   `quarterRecurrence_lowerBound`.  Prove that a chain starting above
   `n^(1/3)` survives for the required order-`log n` number of steps and yields
   an independent set of size at least `c * log n`, for one absolute `c > 0`.
4. Formalize the greedy deletion/colouring recursion for an arbitrary `U` and
   prove the displayed bound (10.3) simultaneously for every `U` on the one
   event.  Extract one absolute constant `C` and one deterministic failure
   sequence tending to zero.
5. Assemble Lemma 10.2 from the already proved capacity expectation and lower-
   tail bounds, the maximizing core, deterministic concatenation, and the
   simultaneous event.  The quantifiers must choose `C` and a deterministic
   `epsilon_n -> 0` before quantifying over deterministic `k_n`, `Lambda_n`,
   and `r_n`; the error sequence may not depend on any of those three choices.
   The conclusion must be uniform for every deterministic `r_n > 0`.  The
   local two-success-event failure bound supplies only the final union seam;
   both quantitative input tails still have to be constructed.
6. **Completed locally as deterministic scale facts:**
   `r_n = sqrt(n/(log n)^4)` tends to infinity; the seed hypothesis
   `Lambda_n = o(n/(log n)^4)` gives the required seed square-root term; and
   `sqrt(n*r_n)/log n`, the real cube-root term, and the additive constant are
   each `o(n/(log n)^3)`.  These limits do not supply the probabilistic seed,
   the simultaneous leftover theorem, or Lemma 10.2.
7. Define the actual deterministic error `a_n` and instantiate Lemma 10.2 to
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
closure.  The remaining actual sequence/tail instantiation is:

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
4. Prove the actual capacity and simultaneous-leftover tails and the eventual
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
Aristotle completion.  Current source-only proposal packages split the open
Section X chain into fixed-subset quarter tail, density lift, recurrence-chain,
survival-asymptotic, uniform leftover-event, and final amplification atoms.
They are scheduling/proof-search payloads only: queued, running, failed, or
completed service status does not make any target accepted until the local
Lean 4.31 warning-fatal, trust-scan, axiom, and scope gates pass.
