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
| `profileDiscreteObjective_eq_profileManuscriptObjective`, `profileStirlingUpperMain_eq_profileDiscreteObjective`, `profileLogWeight_le_discreteObjective_add_error` | discrete finite objective in (4.3) | proved | The zero-safe factorial main term and exact forbidden-edge energy are algebraically identical to the manuscript's expanded finite profile objective, including zero coordinates and the empty profile.  Its exact finite Gibbs maximum and deficit reindexing are recorded below; the phase-uniform asymptotics remain open. |
| `RealColoringProfile.IsFeasible`, `RealColoringProfile.isFeasible_ofNat`, `profileRealObjective_ofNat` | real relaxation underlying (4.3) | defined; exact embedding proved | Nonnegativity, part count, and vertex mass are explicit affine constraints on `Fin b→ℝ`.  Coordinatewise casting sends every exact natural profile to a feasible real profile and preserves the discrete objective exactly, including all zero endpoints. |
| `IsUniformProfileDiscreteObjectiveUpperBound`, `boundedProfileColoringExpectation_le_variationalEnvelope`, `boundedProfileColoringExpectation_le_of_continuousRelaxation` | abstract variational envelope in (4.3) | proved conditionally on the stated upper-bound witness | Any real `L` dominating all admissible discrete objectives gives the exact `ofReal((n+1)^b)·ofReal(exp(L+error_n))` aggregate bound.  The concrete fixed finite relaxation is attained below; its phase-uniform root choice and asymptotic estimate remain open. |
| `profileDualPartition`, `sum_profile_relativeEntropy_le_zero`, `profileRealObjective_le_profileDualUpper`, `boundedProfileColoringExpectation_le_profileDualUpper` | concrete Gibbs-dual bound toward `L_+` in (4.3) | proved for `b>0` and `parts>0` | The positive log-partition reference vector has total mass `parts`; a zero-safe relative-entropy inequality bounds every feasible real profile by every one-parameter dual value.  Exact casting transfers this to all admissible natural profiles and the aggregate expectation. |
| `hasDerivAt_log_profileDualPartition`, `hasDerivAt_profileDualUpper`, `hasDerivAt_profileDualMean`, `profileDualVariance_pos`, `strictMono_deriv_profileDualUpper` | local calculus of the concrete `L_+` dual | proved | The log-partition derivative is the support mean; the mean derivative is the variance; and the dual derivative is `parts·mean−n`.  For `b≥2` the variance is strictly positive, so the derivative is strictly increasing when `parts>0`. |
| `tendsto_profileDualMean_atBot`, `tendsto_profileDualMean_atTop`, `existsUnique_profileDualMean_eq_of_mem_Ioo` | finite mean inversion | proved for `b≥2` and target in `(1,b)` | The mean has endpoint limits `1` and `b`, is strictly increasing, and therefore has a unique target-matching tilt.  The total selected tilt used later falls back to zero outside this interior domain; no endpoint optimizer is claimed. |
| `profileDualOptimizer_isFeasible`, `profileDualUpper_eq_profileRealObjective_of_mean_eq`, `profileDualUpper_isGreatest_profileRealObjective` | exact finite Gibbs optimizer and maximum | proved | When `parts>0` and `parts·mean=n`, the positive Gibbs profile has exactly the required mass and part count, attains the dual value, and is the greatest value of the real finite-profile relaxation. |
| `profileDualScore_eq_deficitAffine_add_residual`, `profileDualWeight_eq_profileDeficitWeight`, `profileDualMean_eq_iff_profileDeficitMean_eq`, `profileDualUpper_eq_deficitCentered` | exact deficit normalization on support `b=α+1` | proved | With deficit `d=α-size`, the normalized manuscript tilt is exactly `λ=B_α-t`, normalized weights are unchanged, the target is `α-n/parts`, and the dual value has the exact centered form. |
| `hasDerivAt_profileDualTilt`, `hasDerivAt_profileDualEntropyValue`, `profileDualOptimalValue_isGreatest_profileRealObjective`, `hasDerivAt_profileDualOptimalValue_parts` | selected optimum and envelope calculus | proved on the strict interior domain | The inverse derivative is `1/variance`, normalized entropy has derivative `-tilt`, and the attained finite optimum has part-count derivative `log Z_b(t)-log parts`.  These are exact finite derivatives, not phase-uniform slope asymptotics. |
| `profileDeficitResidualScore_last`, `profileDeficitResidualScore_eq_descFactorial`, `log_descFactorial_le_mul_log`, `profileDeficitResidualScore_le_gaussian` | pointwise deficit-score control | proved | For `α>0` the unique deficit `-1` coordinate has its exact correction `-q/2+log(α/(α+1))`; interior coordinates have the exact descending-factorial decomposition, and every support coordinate satisfies residual `≤-(q/2)d²`.  This row is pointwise; its bounded-tilt sum consequence is recorded next. |
| `gaussian_abs_tilt_domination`, `finiteTiltedGaussianTail_le`, `finiteTiltedGaussianFirstMomentTail_le`, `finiteTiltedGaussianSecondMomentTail_le`, `summable_tiltedGaussian_moments`, `one_le_profileDeficitPartition`, `profileDeficitPartition_le_gaussianEnvelope`, `abs_profileDeficitMean_le_gaussianEnvelope`, `profileDeficitSecondMoment_le_gaussianEnvelope` | growing-support zeroth-, first-, and second-moment control on a bounded tilt interval | proved conditional on `|λ|≤M` | Exact support reversal isolates the deficit `-1` atom and enumerates all natural deficits.  The zero-deficit atom gives `Z_α(λ)≥1`; explicit Gaussian tails give partition, unnormalized first/second-moment, normalized-mean, and normalized raw second-moment bounds independent of `α` whenever a common `M` is supplied.  The selected-tilt theorem below now supplies one eventual common `M` simultaneously on each compact target interval. |
| `extendedGaussianNaturalTerm`, `extendedGaussianPartition`, `extendedGaussianFirstNumerator`, `extendedGaussianSecondNumerator`, `extendedGaussianMean`, `extendedGaussianRawVariance`, `summable_extendedGaussianNaturalTerm`, `summable_extendedGaussianFirstMoment`, `summable_extendedGaussianSecondMoment`, `one_lt_extendedGaussianPartition`, `hasDerivAt_extendedGaussianPartition`, `hasDerivAt_extendedGaussianFirstNumerator`, `hasDerivAt_extendedGaussianMean`, `extendedGaussianNatural_cauchySchwarz`, `extendedGaussianRawVariance_pos`, `strictMono_extendedGaussianMean`, `tendsto_extendedGaussianMean_atBot`, `tendsto_extendedGaussianMean_atTop` | limiting deficit law, calculus, and endpoint geometry on `{-1,0,1,…}` | proved for `a>0` | The exceptional atom has weight `exp(-λ-a/2)` and every natural deficit `d` has weight `exp(λ d-a d²/2)`.  Moments through order two are summable and the partition is strictly positive.  Locally dominated termwise differentiation proves `Z'=N₁`, `N₁'=N₂`, and `mean'=variance`; countable Cauchy–Schwarz plus positive mass at deficits `-1` and `0` makes the variance strictly positive.  The mean is differentiable, continuous, and strictly increasing, tends to `-1` at negative infinite tilt, and diverges to `+∞` at positive infinite tilt.  Full finite-profile moment convergence and compact selected-inverse transfer are recorded below. |
| `exists_ordered_mean_bracket`, `existsUnique_eq_of_strictMono_endpoint_limits`, `exists_ordered_extendedGaussianMean_bracket`, `existsUnique_extendedGaussianMean_eq` | limiting compact brackets and unique tilt inversion | proved | Endpoint filters produce ordered finite tilt parameters bracketing any compact target interval above `-1`; continuity and strict monotonicity then give a unique limiting tilt for every target `T>-1`.  The total limiting selector, finite selector, compact traps, and uniform transfer are recorded below. |
| `profileDeficitNaturalTerm`, `profileDeficitExceptionalTerm`, `tendsto_profileDeficitNaturalTerm`, `tendsto_profileDeficitExceptionalTerm`, `tendsto_profileDeficitNaturalFirstMomentTerm`, `tendsto_profileDeficitNaturalSecondMomentTerm` | fixed-coordinate finite-to-limiting deficit convergence | proved | Each fixed natural deficit is totalized outside the finite support and eventually equals the exact reversed finite coordinate.  Its weight converges to the limiting `a=log 2` Gaussian atom; the exceptional `-1` atom and the fixed first/second-moment terms converge as well.  The required growing-support interchange is recorded in the next rows. |
| `tendsto_log_descFactorial_sub_mul_log`, `tendsto_log_nat_div_nat_add_one`, `tendsto_tsum_of_norm_le_summable`, `tsum_eq_sum_range_of_eq_zero`, `tendstoUniformlyOn_exp_affine_add_of_tendsto`, `tendstoUniformlyOn_tsum_of_uniform_coordinate_limits`, `tendstoUniformlyOn_div_of_denominator_ge`, `abs_div_sub_div_le_of_denominator_ge`, `hasDerivAt_mul_comp_div`, `hasDerivAt_mul_comp_div_add_const_and_lower` | generic passage from finite scores and sums to profile limits and part-count slope | proved | The fixed natural-deficit and exceptional corrections tend to zero; finite support converts exactly to `tsum`; coordinate convergence under one summable majorant passes uniformly through the infinite series on a supplied parameter set; normalized quotients preserve that uniform convergence under a common positive denominator bound; and `d/dk[k·(ψ(n/k)+c)]=ψ(n/k)+c-(n/k)ψ'(n/k)` exactly, together with a reusable lower bound.  The phase-specific objective identification and derivative estimates remain open. |
| `tendsto_profileDeficitPartition`, `tendsto_profileDeficitFirstNumerator`, `tendsto_profileDeficitSecondNumerator`, `tendsto_profileDeficitMean`, `tendstoUniformlyOn_profileDeficitPartition`, `tendstoUniformlyOn_profileDeficitFirstNumerator`, `tendstoUniformlyOn_profileDeficitSecondNumerator`, `tendstoUniformlyOn_profileDeficitMean` | full growing-support moment convergence | proved pointwise and uniformly on every bounded tilt interval | Exact finite-support-to-`tsum` identities, one summable Gaussian envelope, the exceptional atom, and a denominator lower bound justify the full partition/first/second-moment interchange and the normalized mean limit. |
| `profileDeficitTilt`, `profileDeficitMean_profileDeficitTilt`, `exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le`, `extendedGaussianTilt`, `extendedGaussianMean_extendedGaussianTilt`, `exists_abs_extendedGaussianTilt_le_on_compact`, `tendstoUniformlyOn_profileDeficitTilt` | finite and limiting selected tilts on compact target intervals | proved | The finite and limiting selectors realize the exact mean equation on their interior domains.  One eventual finite bound holds simultaneously for every target in any compact interval above `-1`; compact limiting trapping, uniform mean convergence, and a quantitative inverse modulus yield compact-uniform selected-tilt convergence. |
| `profileDeficitVariance`, `hasDerivAt_profileDeficitMean`, `tendstoUniformlyOn_profileDeficitVariance`, `continuousOn_extendedGaussianRawVariance_Icc`, `exists_pos_extendedGaussianRawVariance_lower_bound_on_Icc`, `extendedGaussianMean_lower_separation_on_Icc`, `uniform_inverse_close_of_lower_separation`, `normalized_raw_variance_stability` | compact variance and inverse stability | proved | The finite mean derivative is its centered variance; normalized raw variances converge uniformly to the limiting raw variance.  Positivity plus compact continuity supplies a fixed positive floor, derivative integration yields absolute lower separation, and explicit forward error controls inverse error uniformly. |
| `existsUnique_root_mem_Ioo_of_strictAntiOn`, `existsUnique_root_mem_corridor_of_center_bound_deriv_upper`, `derivative_lower_bound_mul_sub_le_sub`, `tilt_mem_Ioo_of_strictMono_mean_eq`, `rounded_left_value_le` | generic root-corridor and rounding glue | proved | Continuous local sign change plus strict decrease gives a unique root; an explicit center error and negative derivative ceiling put that root in a quantitative corridor; a derivative lower bound integrates to a finite decrement; endpoint mean brackets trap a matching tilt; and flooring the root then subtracting `⌈N⌉` gives the exact value drop.  The actual phase objective still must supply the center estimate, derivative bounds, corridor domain, and final negativity conclusion. |
| `exists_finpartition_refinement_card_eq`, `exists_bounded_proper_refinement_card_eq` | exact nonempty refinement in (4.5) | proved | Every finite partition with at most `k` parts can be refined to exactly `k` nonempty parts when `k` is at most the ground-set cardinality.  Properness and upper block-size bounds pass to the refinement, including the empty endpoint. |
| `boundedProfileColoringCount_pos_of_partition`, `exists_exact_proper_partition_of_chromaticNumberNat_le`, `boundedProfileColoringCount_pos_of_chromaticNumberNat_le` | deterministic profile witness in (4.5) | proved | A `Fin k` coloring gives a kernel partition with at most `k` nonempty fibers, exact refinement gives `k` parts, and the resulting bounded partition is extracted into a positive profile count.  No `n>0`, `k>0`, or `b>0` hypothesis is inserted. |
| `chromaticNumberNat_le_set_subset_boundedProfileColoringCount_pos_union` | deterministic event containment in (4.5) | proved | For `k≤n`, every graph with `χ≤k` either has a positive exactly-`k`, size-`b` bounded profile count or has independence number greater than `b`.  The continuous-root estimate and final probability limit remain open. |
| `randomGraphMeasure_boundedProfileColoringCountPositive_le_expectation`, `randomGraphMeasure_chromaticNumberAtMost_le_expectation_add_independence`, `randomGraphMeasure_chromaticNumberAtMost_le_box_mul_exp_add_mu` | finite probability reduction in (4.5) | proved | Threshold-one Markov on the actual finite graph space and the deterministic containment give `P(χ≤k)≤E[bounded count]+P(α>b)`.  Supplying any common finite logarithmic profile bound gives the sharp shifted estimate `(n+1)^b exp(L)+μ(n,b+1)`, matching the already formalized full-sequence independence tail.  Only the continuous-root/asymptotic input and limit remain. |
| `randomGraphMeasure_chromaticNumberAtMost_le_profileDual_add_mu` | concrete dual probability inequality joining (4.3)–(4.5) | proved for `b>0`, `parts>0`, and `parts≤n` | Every real dual parameter `t` gives the explicit finite bound `ofReal((n+1)^b)·ofReal(exp(dual(t)+error_n))+ofReal(μ(n,b+1))`.  The remaining task is a phase-uniform parameter choice/root estimate making the first term vanish. |
| `randomGraphMeasure_chromaticNumberAtMost_phaseCap_tendsto_zero_of_dual` | asymptotic assembly of (4.3)–(4.5) | proved conditionally on the explicit dual main-term limit | At cap `b=phaseNat n+1`, eventual positivity and `parts n≤n` plus convergence of the displayed dual main term to zero imply the unrestricted chromatic event probability tends to zero.  The shifted `μ(n,phaseNat n+2)` term is discharged by the already proved (2.3)/(2.9) limit; no root is assumed. |

| `sum_table_rows_eq_sum_table_columns`, `sum_demand_le_sum_table`, `no_contingencyTable_of_infeasible_demands` | feasibility branch before Lemma 6.2 and (6.8) | proved | Row and column summation of a finite nonnegative integer table gives the same total, entrywise prescribed demands sum monotonically, and any excessive row demand, excessive column demand, or unequal pair of total margins makes the table-witness type empty. This closes the impossible-event branch; the uniform-matching event and probability inequality remain open. |
| `highCells_form_matching` | high-cell assertion before (8.2) | proved | If every row and column of a nonnegative integer table has mass at most `U`, then two entries in one row or column cannot both exceed `U/2`. Thus the high cells form a partial matching. This does not yet construct the canonical skeleton or its conditional residual law. |
| `card_iUnion_stubAllocation`, `card_disjoint_extension`, `card_stubEmbedding_eq_descFactorial`, `card_stubEmbedding_eq_labeledAllocation`, `card_labeledStubAllocation`, `card_stubAllocation_mul_factorials` | finite allocation factors before (6.8) | proved | A pairwise-disjoint family uses exactly the total demanded number of labelled stubs; after fixing it the exact number of disjoint new `d`-subsets is the residual binomial coefficient; and internally ordered allocations are explicitly equivalent to embeddings of the demanded blocks, giving the total descending-factorial count without a feasibility premise. |
| `PrescribedDemandWitness`, `card_prescribedDemandWitness_mul_factorials` | numerator count in Lemma 6.2 / (6.8) | defined; exact cardinal identity proved | Row-stub selections, column-stub selections, and one bijection per demanded cell are combined into a finite witness type. Its cardinal multiplied by `∏_{a,b} x_{ab}!` is exactly the product of the row and column descending factorials, including infeasible cases. The global matching encoding, witness-to-exposure map, event coverage, and probability union bound remain open. |
| `MatchingExtensions`, `card_extensions_of_exposed_equiv`, `card_extensions_of_embedding_pairing` | fixed-exposure count before (6.8), and residual count after (8.3) | defined; exact cardinal identities proved | Full bijections extending an exposed finite pairing are explicitly equivalent to arbitrary bijections between the complements. The same count is repackaged for distinct prescribed pairs indexed by any finite type `X`, giving exactly `(card L-card X)!`. The global configuration-model stub encoding, witness pairing embeddings, event coverage, uniform-law transport, and (6.8) union bound remain open. |

## Remaining proof dependency graph

The following items are open.  Names here are work-package labels, not hidden
Lean axioms or claimed theorems.

1. Complete the remaining phase-root part of the continuous profile analysis
   (Lemma 3.1): compose the proved growing-support moments and compact-uniform
   selected-tilt convergence with the phase part-count objective, establish the
   scalar root corridor and its slope, and justify the real-to-integer rounding
   decrement.  Fixed-support inversion, uniqueness, attainment, exact
   derivative formulas, phase-uniform tilt bounds, compact variance convergence,
   and selected-inverse convergence are proved.
2. Complete the analytic/asymptotic part of the unrestricted chromatic
   lower-location argument (§4): insert that phase-uniform root choice into the
   attained finite maximum and prove that the already assembled finite
   probability bound tends to zero.  The exact enumeration, finite Stirling/multiplicity
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
are complete.  Growing-support moments, compact selected-tilt convergence,
variance stability, and the generic root/rounding interfaces are also
complete.  The next high-level checkpoints are the concrete phase-objective
center/slope substitution and the atomic overlap, skeleton, cycle, and
residual obligations in Sections 6--9.  Deterministic leftover and rare-seed
amplification interfaces may be formalized independently.  At the user's
direction, a private arXiv-style
layout is being prepared in parallel; it is not evidence that
`Erdos625Statement` has been kernel-checked.
