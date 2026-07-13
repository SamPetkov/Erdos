# Erdős Problem 625 Lean formalization ledger

This ledger separates kernel-checked Lean results from the remaining claims in
the candidate manuscript.  Its manuscript anchor is
[`../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](../proofs/COMPLETE_PROOF_SELF_CONTAINED.md).

## Status vocabulary

- **proved**: Lean accepts the declaration without `sorry`, `admit`, or a
  project-defined axiom;
- **defined**: Lean accepts a definition of an object or proposition, but no
  proof of the mathematical claim is asserted;
- **open**: the manuscript argument has not yet been translated into Lean;
- **audit only**: numerical or prose evidence, never a substitute for proof.

## Milestone M0: model and target

| Lean declaration | Manuscript anchor | Status | Meaning |
|---|---|---:|---|
| `gapConstant`, `gapConstant_pos`, `gapScale` | (0.1), (1.1) | defined; positivity proved | Natural-log scale and exact positive constant. Small-`n` totalization is irrelevant at `atTop`. |
| `LabeledGraph n` | §1 | defined | Labelled simple graphs on `Fin n`. |
| `CoColoring`, `CoColorable` | Abstract and §1 | defined | At most `k` clique-or-independent vertex classes; empty palette classes are allowed. |
| `cochromaticNumber` | Abstract and §1 | defined | Minimum `k` admitting a cocolouring on a finite vertex type. |
| `chromaticNumberNat` | Abstract and §1 | defined | Natural-valued wrapper around mathlib's chromatic number, restricted to finite vertex types. |
| `cochromaticNumber_le_chromaticNumber` | elementary observation before (0.1) | proved | Every proper colouring is a cocolouring. |
| `CoColoring.relabel` | proof infrastructure | proved by construction | Palette renaming preserves validity. |
| `CoColoring.addEmptyColors`, `coColorable_mono` | proof infrastructure | proved by construction / proved | Unused palette entries preserve cocolourability. |
| `CoColoring.sumInduce` | §§9–11 interface | proved by construction | Cocolourings on an induced set and its complement glue with disjoint palettes. |
| `coColorable_of_induce_and_compl` | §§9–11 interface | proved | `k + ℓ` cocolours suffice after induced-set concatenation. |
| `coColorable_of_induce_and_colorable_compl` | leftover step in §§10–11 | proved | The leftover may use an ordinary colouring. |
| `coColorable_iff_cochromaticNumber_le` | definition audit | proved | Confirms that `cochromaticNumber` has the intended minimum semantics. |
| `randomGraphMeasure` | (0.1) | defined | Mathlib's binomial random graph law at edge probability `1/2`. |
| `randomGraphMeasure_singleton`, `randomGraphMeasure_singleton_uniform` | model validation | proved | Records the exact singleton formula and proves uniform mass `(1/2)^(n choose 2)`. |
| `measurableSet_gapEvent` | (0.1) | proved | The finite-space event is measurable, not merely assigned an outer measure. |
| `gapProbability_le_one` | probability sanity check | proved | The event mass is at most one. |
| `Erdos625Statement` | (0.1) | defined, **unproved** | Exact full-sequence convergence of the displayed event probability to one. |
| `erdos625Statement_iff_real` | (0.1) | proved | The `ENNReal` target is equivalent to the manuscript's real-valued probability limit. |

## Verified post-M0 bricks

These declarations have passed direct warning-free compilation, placeholder
and project-axiom scans, representative `#print axioms` checks, and independent
statement audits. They do not by themselves prove Lemma 2.1 or the final
target.

| Lean declaration | Manuscript anchor | Status | Meaning |
|---|---|---:|---|
| `q`, `logOrder`, `logLogOrder`, `logBaseTwo`, `alphaZero`, `phaseInt`, `phaseNat`, `phaseDelta` | (2.1) | defined | Exact phase quantities, with integer and natural floor semantics kept separate. |
| `phaseDelta_mem_Ico`, `phaseNat_cast_real` | (2.1) | proved | `0 ≤ δ < 1`; the guarded natural phase equals the integer floor. |
| `mu`, `mu_succ_div_identity`, `mu_pred_div_identity` | (1.2), (2.8) | defined; exact ratios proved | Real first moment and both adjacent-size identities, including explicit denominator hypotheses. |
| `markov_measureReal_le` | (1.4) first-moment use | proved | Real Markov inequality with AE nonnegativity and integrability hypotheses. |
| `paleyZygmund_zero` | (1.5) | proved | Zero-threshold Paley--Zygmund in `ENNReal`, including zero/infinite second-moment cases. |
| `subgaussian_two_sided`, `mcdiarmid_two_sided_of_subgaussian` | analytic tail core for (1.4) | proved **conditional on a sub-Gaussian MGF** | The constants are exact once the centered variable has variance proxy `r/4`; the independent-block-to-MGF bridge remains open. |
| `binomialHalf_lowerQuarter_le_exp` | (1.6) | proved | Exact lower-quarter tail for mathlib's real-valued `Bin(m,1/2)`, with bound `exp(-m/16)`. |
| `randomGraphMeasure_independentEvent` | (1.2) | proved | A fixed labelled `s`-set is independent with probability `2^{-choose(s,2)}`. |
| `independentSetExpectation_eq`, `independentSetExpectation_eq_ofReal_mu` | (1.2) | proved | Exact finite expectation and exact bridge to `ENNReal.ofReal (mu n s)`. |
| `independentSetCount_pos_iff_le_indepNum` | first-moment semantics | proved | Positive count is equivalent to `s ≤ G.indepNum`, including `s=0` and `s>n`. |
| `randomGraphMeasure_independenceNumberExceeds_le_mu_succ` | Markov step toward (2.9) | proved | Sharp shifted bound `P(α(G)>s) ≤ μ_{s+1}`. |
| `phaseC`, `phaseS`, `phaseB`, `phaseK` | (2.5)--(2.7) setup | defined | Exact constants and endpoint-uniform phase offset. |
| `alphaZero_eq_two_phaseS_div_q_add_one`, `phaseNat_cast_eq_two_phaseS_div_q_add_phaseB` | algebra before (2.5) | proved | Exact non-asymptotic normal forms for `α₀` and the guarded natural phase. |
| `continuous_phaseK`, `exists_phaseK_abs_bound` | (2.7) | proved | `K` is continuous and uniformly bounded on the full closed phase interval `[0,1]`. |
| `eventually_phaseRangeDomain` | finite-index bookkeeping for §2 | proved | Eventually `PhaseDomain n`, `2 ≤ phaseNat n`, and `phaseNat n + 2 ≤ n`, without using Lemma 2.1. |
| `phaseNat_isEquivalent_scaled_logOrder`, `eventually_two_mul_phaseNat_le` | range control before (2.5) | proved | The guarded integer phase is asymptotic to `(2/q) log n`; eventually two phase-sized blocks fit inside `n`. |
| `log_descFactorial_linear_error_le` | falling-factorial part of (2.5) | proved | Under `2s ≤ n`, the exact logarithmic linearization error is at most `2s³/n²`. |
| `stirlingLogRemainder_mem_Icc` | (1.3), factorial part of (2.5) | proved | For every positive integer `s`, the exact Robbins remainder lies in `[0,1/(12s)]`. |
| `log_mu_sub_phaseStirlingMain_abs_le`, `phaseStirlingResidual_isBigO_inv_logOrder` | finite and full-sequence (2.5) | proved | The exact falling-factorial and Robbins corrections have the manuscript signs and give the genuine residual `O(1/logOrder)` at the guarded floor phase. |
| `phaseBracket_sub_main_abs_le`, `phaseBracket_sub_main_isBigO` | finite and full-sequence endpoint-uniform (2.6) | proved | The exact bracket residual is bounded through the Taylor shift and is `O(logLogOrder²/logOrder²)` on the full sequence. |
| `phaseMain_algebra_identity`, `phaseExpansionResidual_isBigO` | (2.2), with `K` from (2.7) | proved | Exact algebra plus the finite estimates gives `log μ(n,phaseNat n) - phaseExpansionMain n = O(logLogOrder²/logOrder)` along all natural `n`; consequences (2.3), (2.4), and (2.9) are not claimed here. |
| `log_mu_phaseNat_add_two_div_logOrder_sub_phaseDelta_add_two_tendsto_zero`, `mu_phaseNat_add_two_tendsto_zero` | (2.3) | proved | Exact adjacent-size ratios give the refined exponent at the actual floor phase plus two and hence `μ(n,phaseNat n + 2) → 0` on the full sequence. |
| `exists_pos_eventually_mu_phaseNat_sub_two_lower_bound`, `randomGraphMeasure_independenceNumberExceeds_phaseNat_add_one_tendsto_zero` | (2.4) and (2.9) | proved | There is an absolute `c > 0` with the literal real-power lower bound at the floor phase minus two, and the sharp shifted Markov event tends to zero in `ENNReal`. |
| `cubeMean_exp_center_le`, `boundedDifferences_hasSubgaussianMGF` | fair-bit case of (1.4) | proved | Coordinate oscillation on the uniform finite Boolean cube implies the centered MGF bound with exact proxy `Σcᵢ²/4`; no MGF premise is assumed. |
| `integral_boolCubePMF_eq_cubeMean`, `boundedDifferences_twoSidedTail` | fair-bit measure bridge and tail | proved | Recursive cube averaging is the actual uniform-PMF expectation, giving the exact two-sided fair-bit tail. |
| `blockMean_succ`, `blockMean_exp_center_le` | finite-block form of (1.4) | proved | Exact dependent-product averaging and the bounded-differences MGF induction for arbitrary nonempty finite uniform block types. No equal-cardinality or Boolean-block assumption is used. |
| `integral_blockUniformPMF_eq_blockMean`, `blockBoundedDifferences_hasSubgaussianMGF`, `blockBoundedDifferences_twoSidedTail` | finite-block measure bridge and tails | proved | The product-uniform PMF has the normalized block mean as its actual expectation and satisfies the exact proxy `Σ(cᵢ/2)²`; this is generic concentration infrastructure, not yet the random-graph transport. |
| `gap_le_sqrt_two_mul_of_exp_neg_le_exp_neg_sq_div`, `rareSeed_gap_le`, `rareSeed_gap_le_of_hasSubgaussianMGF` | analytic inversion in (10.7) | proved | An endpoint seed of mass at least `exp(-Λ)` and a centered one-sided sub-Gaussian upper tail with positive proxy `v` imply endpoint minus expectation at most `sqrt(2vΛ)`.  The zero-proxy case remains a separate degeneracy argument. |
| `vertexBlocksEquiv`, `card_vertexBlocks`, `map_vertexBlockMeasure_eq_randomGraphMeasure` | exact vertex-block model | proved | Vertex blocks encode every unordered edge once, have cardinality `2^(n choose 2)`, and push the uniform block law exactly to `G(n,1/2)`, including `n=0`. |
| `blocksToGraph_induce_away_eq`, `randomGraph_vertexBlock_twoSidedTail`, `integral_randomGraphMeasure_eq_randomGraphBlockExpectation` | deletion oscillation and graph-law concentration | proved | Agreement off one block gives literal equality after deleting its vertex; generic deletion oscillation yields the exact McDiarmid constant, centered at the actual random-graph integral. |
| `CoColoring.pullback`, `coColorable_induce_mono`, `coColorable_erase_of_induce_away_eq` | hereditary cocolourability used in (10.6) | proved | Cocolourings pull back along injective adjacency equivalences; feasibility survives restriction and transfers after deleting the one changed exposure vertex. |
| `cochromaticInducedCapacity`, `cochromaticInducedCapacity_eq_card_iff`, `cochromaticInducedCapacity_hasBlockOscillation` | (10.6) and the event before (10.7) | defined; extremal event and oscillation proved | The largest induced `k`-cocolourable vertex set is at most `n`, equals `n` exactly when the whole graph is `k`-cocolourable, and has universal block profile `0,1,…,1`. |
| `blockVariance_noninitialUnitOscillation`, `randomGraph_cochromaticInducedCapacity_upperTail`, `randomGraph_cochromaticInducedCapacity_twoSidedTail` | concentration input to (10.7)–(10.8) | proved | The chosen profile has exact value `(n-1)/4`; both graph-law tails use the actual `G(n,1/2)` expectation.  For `n≤1` the totalized bound is valid but vacuous. |
| `exists_cochromaticInducedCapacity_witness`, `capacity_witness_compl_card`, `cochromaticNumber_le_add_chromaticNumber_compl` | deterministic core of (10.9) | proved | One induced core attains the capacity, its complement has exactly `n-capacity` vertices, and concatenating its `k`-cocolouring with an optimal ordinary colouring of the complement gives `ζ(G) ≤ k + χ(G[Wᶜ])`. |
| `cochromaticInducedCapacity_levelSet_eq`, `cochromaticVarianceProxy_pos`, `cochromaticSeedGap_le_simplified` | graph-specific (10.7) | proved | For `n≥2`, a seed `P{CoColorable G k}≥exp(-Λ)` gives the exact bound `n-E[capacity]≤sqrt(((n-1)Λ)/2)` under the actual random-graph law.  The endpoint event, integrability, proxy positivity, and algebraic simplification are explicit. |
| `randomGraph_cochromaticInducedCapacity_lowerTail`, `randomGraph_cochromaticInducedCapacity_failureProbability_le`, `randomGraph_cochromaticInducedCapacity_strictFailureProbability_le` | graph-specific (10.8) | proved | Negating the exact vertex-block MGF gives the one-sided lower tail centered at the actual graph-law integral.  Combining it with (10.7) yields failure probability at most `exp(-r)` at deficit `sqrt(((n-1)Λ)/2)+sqrt(((n-1)r)/2)`, with no two-sided factor and with both non-strict and strict failure-event spellings. |
| `ProfileEntropyS4.partition`, `ProfileEntropyS4.weight`, `ProfileEntropyS4.mean`, `ProfileEntropyS4.variance` | finite-support analytic infrastructure for Lemma 3.1 | defined; normalization and positivity proved | Exact exponential-family objects on support `{2,3,4,5}` with positive normalized weights. |
| `ProfileEntropyS4.hasDerivAt_mean`, `ProfileEntropyS4.variance_pos`, `ProfileEntropyS4.existsUnique_mean_eq_of_mem_Ioo` | finite-support analytic infrastructure for Lemma 3.1 | proved | The mean derivative is the strictly positive variance, its endpoint limits are `2` and `5`, and every target in `(2,5)` has a unique real tilt parameter. This file explicitly does not claim manuscript Lemma 3.1. |
| `ProfileEntropyS4.optimizer_isFeasible`, `ProfileEntropyS4.entropy_score_le_log_partition_sub_tilt_mul_target`, `ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target` | finite-support entropy optimizer | proved | `ProfileOptimizerS4.lean` extends the common `ProfileEntropyS4` namespace: the unique target-mean tilt gives the exact positive optimizer; a zero-safe relative-entropy argument proves the variational inequality for every feasible competitor and exact equality at the optimizer. |
| `ProfileEntropyS4.optimizedValue`, `ProfileEntropyS4.abs_optimizedValue_sub_optimizedValue_le`, `ProfileEntropyS4.tendsto_optimizedValue_of_uniform_scores` | finite-support value part of (3.9) | defined; stability and fixed-target convergence proved | At every fixed `T∈(2,5)`, the optimized value is 1-Lipschitz in the coordinatewise score norm; uniform convergence over the four coordinates implies sequential value convergence.  These declarations alone make no tilt or optimizer claim; those are recorded below. |
| `ProfileEntropyS4.eventually_uniformOn_optimizedValue_of_uniform_scores`, `ProfileEntropyS4.eventually_uniform_optimizedValue_on_Ioo_of_uniform_scores` | uniform finite-support value part of (3.9) | proved | The same score bound is independent of `T`, so one eventual index works simultaneously on any `K⊆(2,5)`, including the full interior interval.  This file is value-only; the subsequent continuity modules supply tilt, optimizer, and compact positivity results. |
| `ProfileEntropyS4.tendsto_mean_of_scores_and_parameter`, `ProfileEntropyS4.tendsto_tilt_of_scores_and_target`, `ProfileEntropyS4.tendsto_optimizer_of_scores_and_target` | joint finite-support continuity behind (3.9b) | proved | Coordinatewise score convergence and a moving target converging to any `T∈(2,5)` imply mean, unique tilt, and every optimizer coordinate converge.  The inverse proof traps the moving tilt between fixed strict mean brackets and assumes no a priori tilt bound. |
| `ProfileEntropyS4.eventually_uniformOn_tilt_of_uniform_scores`, `ProfileEntropyS4.eventually_uniformOn_optimizer_of_uniform_scores`, `ProfileEntropyS4.eventually_uniform_optimizer_pos_on_compact` | compact-target finite-four-support (3.9b) | proved | Joint continuity plus Heine--Cantor gives explicit `∀ε∃N∀n≥N∀T∈K` tilt convergence and one index for all four optimizer coordinates on every compact `K⊆(2,5)`.  Minimizing the positive limiting optimizer on `K×Fin 4` and transferring the bound proves genuine eventual uniform positivity, including the empty-`K` edge case. |
| `ColoringProfile.sizes`, `ColoringProfile.vertexMass`, `ColoringProfile.forbiddenEdges`, `ColoringProfile.enumerativeCoefficient` | finite profile setup for (4.2) | defined; coefficient identities proved | A coordinate `i : Fin b` records nonempty classes of size `i+1`.  The mass, forbidden-edge count, and both multiset and coordinate factorial denominators are proved exactly, including zero coordinates. |
| `partitionInternalGraph`, `ProfilePartition.ncard_partitionInternalGraph`, `randomGraphMeasure_partitionColoringEvent` | fixed-partition probability in (4.2) | proved | Unordered colour classes are represented by `Finpartition`s.  Their internal clique edge sets are pairwise disjoint, have the profile's exact forbidden-edge count, and are simultaneously absent with probability `(1/2)^forbiddenEdges`. |
| `profileColoringExpectation_eq_card_mul`, `profileColoringExpectation_eq_zero_of_vertexMass_ne` | finite first moment behind (4.2) | proved | The actual finite expectation is the cardinality of the unordered profile-partition type times the exact energy factor; if the vertex-mass constraint fails, it is zero. |
| `card_shapeSlot`, `card_profileDecoration`, `decoratedProfileEquiv` | decorated finite enumeration for (4.2) | proved | Canonical `(size,label,position)` slots have the profile's exact mass.  Every fixed unordered profile partition has exactly `∏(s!)^{k_s}∏k_s!` decorations, and each decoration gives a genuine bijection from the vertex set to those slots. |
| `shapeBlockIndexEquivKernelParts`, `card_slotBlockPart`, `partitionShape_slotKernelPartition`, `slotProfileDecoration` | inverse reconstruction for (4.2) | proved through the reconstructed decoration | Every vertex-to-slot equivalence induces a kernel `Finpartition`; its parts are in exact bijection with `(size,label)` indices, each part has the advertised size, the whole shape multiset is the prescribed profile, and canonical labels and within-part orders are reconstructed. |
| `coloringProfileBox`, `boundedColoringProfiles`, `card_boundedColoringProfiles_le` | profile aggregation before (4.3) | defined; coverage and cardinal bound proved | The otherwise infinite type `Fin b → ℕ` is restricted to the coordinate box `0,…,n`; mass `n` forces every coordinate into that box.  Filtering by mass and part count loses no profile and leaves at most `(n+1)^b` possibilities. |
| `boundedProfileColoringCount`, `boundedProfileColoringExpectation`, `boundedProfileColoringExpectation_eq_sum` | exact finite aggregation before (4.3) | defined; sum interchange proved | The total count over mass-`n`, exactly-`k`, size-at-most-`b` profiles has an exact finite weighted expectation, equal to the sum of the already proved per-profile expectations.  The sum interchange does not depend on the enumeration theorem and makes no asymptotic (4.3) claim. |
| `decoratedProfileEquiv_slotProfileDecoration`, `slotKernelPartition_decoratedProfileEquiv`, `profileDecoration_eq_of_equiv_eq` | inverse laws for the finite enumeration | proved | Reading the explicitly reconstructed decoration returns the original slot equivalence pointwise.  Conversely, the first two slot coordinates recover the original kernel partition, while uniform natural-valued projections of the second and third coordinates recover every label and within-part order. |
| `totalProfileDecorationEquiv`, `profileDecorationBijectionStatement`, `profileEnumerationStatement`, `profileColoringExpectation_eq_formula` | factorial enumeration bridge and first-moment formula (4.2) | proved under the necessary mass equation | The total decorated-partition map is proved injective and surjective and packaged as an actual type equivalence.  Positive Bell-denominator cancellation proves `Nat.card (ProfilePartition n k) = enumerativeCoefficient k` whenever `vertexMass k = n`, including the empty-profile `n=0` case; substituting this into the fixed-partition probability gives the public formula (4.2).  No counting interpretation is assumed from mathlib. |
| `factorialEntropyMain`, `abs_log_factorial_sub_factorialEntropyMain_le`, `abs_profileLogFactorialSum_sub_main_le` | zero-safe Stirling input to (4.3) | proved | Explicit two-sided logarithmic factorial errors hold for every natural input, including zero, and sum uniformly over a bounded profile. |
| `profileLogWeight`, `log_profileColoringExpectation_toReal_eq_profileLogWeight`, `profileColoringExpectation_le_of_stirlingUpperMain_add_error_le` | logarithmic/exponential profile bound in (4.3) | proved under the mass equation where required | The exact ENNReal first moment is positive, its `toReal` logarithm is identified with the enumerative log weight, and a finite log upper bound is converted back to an ENNReal exponential bound with positivity and `ne_top` obligations explicit. |
| `boundedProfileColoringExpectation_le_box_mul`, `boundedProfileColoringExpectation_le_box_mul_exp` | profile multiplicity and aggregate finite bound before (4.3) | proved | A uniform per-profile estimate is summed over the actual constrained profile family and then bounded by `(n+1)^b`; no asymptotic big-O or continuous optimizer is assumed. |
| `profileDiscreteObjective_eq_profileManuscriptObjective`, `profileStirlingUpperMain_eq_profileDiscreteObjective`, `profileLogWeight_le_discreteObjective_add_error` | discrete finite objective in (4.3) | proved | The zero-safe factorial main term and exact forbidden-edge energy are algebraically identical to the manuscript's expanded finite profile objective, including zero coordinates and the empty profile.  Reindexing to deficit coordinates and comparison with the continuous maximum `L_+` remain open. |
| `RealColoringProfile.IsFeasible`, `RealColoringProfile.isFeasible_ofNat`, `profileRealObjective_ofNat` | real relaxation underlying (4.3) | defined; exact embedding proved | Nonnegativity, part count, and vertex mass are explicit affine constraints on `Fin b→ℝ`.  Coordinatewise casting sends every exact natural profile to a feasible real profile and preserves the discrete objective exactly, including all zero endpoints.  No optimizer or maximum is assumed. |
| `IsUniformProfileDiscreteObjectiveUpperBound`, `boundedProfileColoringExpectation_le_variationalEnvelope`, `boundedProfileColoringExpectation_le_of_continuousRelaxation` | abstract variational envelope in (4.3) | proved conditionally on the stated upper-bound witness | Any real `L` dominating all admissible discrete objectives gives the exact `ofReal((n+1)^b)·ofReal(exp(L+error_n))` aggregate bound.  A generic continuous relaxation can supply that domination, but the concrete `L_+` relaxation and its upper-bound proof remain open. |
| `profileDualPartition`, `sum_profile_relativeEntropy_le_zero`, `profileRealObjective_le_profileDualUpper`, `boundedProfileColoringExpectation_le_profileDualUpper` | concrete Gibbs-dual bound toward `L_+` in (4.3) | proved for `b>0` and `parts>0` | The positive log-partition reference vector has total mass `parts`; a zero-safe relative-entropy inequality bounds every feasible real profile by every one-parameter dual value.  Exact casting transfers this to all admissible natural profiles and the aggregate expectation.  The minimizing tilt, equality/attainment, root/slope estimates, and asymptotics remain open. |
| `hasDerivAt_log_profileDualPartition`, `hasDerivAt_profileDualUpper`, `hasDerivAt_profileDualMean`, `profileDualVariance_pos`, `strictMono_deriv_profileDualUpper` | local calculus of the concrete `L_+` dual | proved | The log-partition derivative is the support mean; the mean derivative is the variance; and the dual derivative is `parts·mean−n`.  For `b≥2` the variance is strictly positive, so the derivative is strictly increasing when `parts>0`.  Endpoint limits and the target-matching tilt remain open. |
| `exists_finpartition_refinement_card_eq`, `exists_bounded_proper_refinement_card_eq` | exact nonempty refinement in (4.5) | proved | Every finite partition with at most `k` parts can be refined to exactly `k` nonempty parts when `k` is at most the ground-set cardinality.  Properness and upper block-size bounds pass to the refinement, including the empty endpoint. |
| `boundedProfileColoringCount_pos_of_partition`, `exists_exact_proper_partition_of_chromaticNumberNat_le`, `boundedProfileColoringCount_pos_of_chromaticNumberNat_le` | deterministic profile witness in (4.5) | proved | A `Fin k` coloring gives a kernel partition with at most `k` nonempty fibers, exact refinement gives `k` parts, and the resulting bounded partition is extracted into a positive profile count.  No `n>0`, `k>0`, or `b>0` hypothesis is inserted. |
| `chromaticNumberNat_le_set_subset_boundedProfileColoringCount_pos_union` | deterministic event containment in (4.5) | proved | For `k≤n`, every graph with `χ≤k` either has a positive exactly-`k`, size-`b` bounded profile count or has independence number greater than `b`.  The continuous-root estimate and final probability limit remain open. |
| `randomGraphMeasure_boundedProfileColoringCountPositive_le_expectation`, `randomGraphMeasure_chromaticNumberAtMost_le_expectation_add_independence`, `randomGraphMeasure_chromaticNumberAtMost_le_box_mul_exp_add_mu` | finite probability reduction in (4.5) | proved | Threshold-one Markov on the actual finite graph space and the deterministic containment give `P(χ≤k)≤E[bounded count]+P(α>b)`.  Supplying any common finite logarithmic profile bound gives the sharp shifted estimate `(n+1)^b exp(L)+μ(n,b+1)`, matching the already formalized full-sequence independence tail.  Only the continuous-root/asymptotic input and limit remain. |
| `randomGraphMeasure_chromaticNumberAtMost_le_profileDual_add_mu` | concrete dual probability inequality joining (4.3)–(4.5) | proved for `b>0`, `parts>0`, and `parts≤n` | Every real dual parameter `t` gives the explicit finite bound `ofReal((n+1)^b)·ofReal(exp(dual(t)+error_n))+ofReal(μ(n,b+1))`.  The remaining task is a phase-uniform parameter choice/root estimate making the first term vanish. |
| `randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_dual` | asymptotic assembly of (4.3)–(4.5) | proved conditionally on the explicit dual main-term limit | At cap `b=phaseNat n+1`, eventual positivity and `parts n≤n` plus convergence of the displayed dual main term to zero imply the unrestricted chromatic event probability tends to zero.  The shifted `μ(n,phaseNat n+2)` term is discharged by the already proved (2.3)/(2.9) limit; no root is assumed. |

## Remaining proof dependency graph

The following items are open.  Names here are work-package labels, not hidden
Lean axioms or claimed theorems.

1. Prove existence, uniqueness, derivative bounds, and support comparison for the
   continuous profile roots (Lemma 3.1).  Roots will not be introduced by
   choice until existence and uniqueness are proved.
2. Complete the analytic/asymptotic part of the unrestricted chromatic
   lower-location argument (§4): compare the proved discrete objective with
   the continuous maximum `L_+`, formalize its root/slope estimate, and prove
   that the already assembled finite probability bound tends to zero.  The
   exact enumeration, finite Stirling/multiplicity
   bound, nonempty refinement, profile extraction, event containment, finite
   Markov/union reduction, and conditional box-exponential probability bound are proved.
3. The four-size signed first-moment calculation and uniform entropy
   certificate (Lemma 5.1).
4. Exact sign-summed second-moment and prescribed-cell bounds (Lemmas 6.1–6.2).
5. All partial-diagonal ranges, with empty, central, and full corners kept
   explicit (Lemma 7.1).
6. Canonical high cells, endpoint transportation, and all nonendpoint high
   multiplicities (Lemmas 8.1–8.3).
7. Residual local/cycle attachment bound and normalized signed second moment
   (Lemma 9.1 and Proposition 9.2).  The residual estimate must remain
   one-sided; no equality is to be inferred from an upper bound.
8. Complete the simultaneous leftover-colouring and seed-amplification layer
   (Lemmas 10.1–10.2).  The induced-capacity statistic, event equivalence,
   block-count concentration input, generic rare-seed inversion, maximizing
   core, exact leftover size, graph-specific expectation bound (10.7),
   deterministic concatenation inequality (10.9), and the exact one-sided
   lower-tail step (10.8) are now proved.  The simultaneous
   leftover-colouring event and final intersection remain.
9. Assembly of the preceding results into `Erdos625Statement` (§11).

The central high-risk corridor is items 4–7.  A reduction that merely restates
their global overlap bound will not count as progress; each profile family,
quantifier, endpoint, and uniform error term must be explicit.

## Trust and validation policy

- Toolchain: Lean `v4.31.0`; mathlib tag `v4.31.0`, pinned transitively by
  `lake-manifest.json`.
- Aristotle is used only on isolated, ignored compatibility copies as an
  optional proof-search assistant. Its fixed Lean `v4.28.0` output is never
  imported automatically: every candidate is ported to this project's
  `v4.31.0`, scanned, rebuilt, axiom-audited, and independently reviewed.
- The first isolated Aristotle task (2026-07-13) solved the three
  vertex-block/graph inverse obligations on the service toolchain. Its archive
  remains quarantined and ignored. Because its automation-heavy final inverse
  did not finish within a 184-second direct v4.31 replay, none of the returned
  source was imported; the explicit local proofs remain authoritative. The
  one-run API key used for retrieval was then revoked.
- The second isolated task checked an abstract finite-capacity maximum and
  one-element deletion argument.  Its explicit
  `Finset.Nonempty.image` elaboration fix was ported to Lean 4.31; the
  graph-specific heredity, event, variance, measure-transport, and tail proofs
  were checked locally.  The downloaded result remains quarantined and its
  temporary key was revoked.
- CI rejects placeholders/project axioms with a source gate and runs
  `lake build --wfail`, making Lean's own placeholder warning fatal.  The
  optional external `nanoda` helper path is disabled.
- Before each published milestone: run `lake build`, scan all project `.lean`
  files for `sorry`, `admit`, and project axioms, inspect `#print axioms` for
  public theorems, and obtain an independent statement/dependency audit.
- Python experiments and manuscript audits remain evidence and diagnostics;
  they are not imported as proof certificates.

## Next checkpoint

The user has confirmed the full-proof-first campaign.  The phase expansion,
its stated consequences, exact vertex-block graph law, induced-capacity
oscillation, full-capacity event, and corresponding graph-law concentration
are complete.  The next high-level checkpoint is the continuous profile-root
and support-comparison layer, while deterministic leftover and rare-seed
amplification interfaces may be formalized independently.  The private arXiv
package remains paused until `Erdos625Statement` itself is proved and the final
kernel/source audit passes.
