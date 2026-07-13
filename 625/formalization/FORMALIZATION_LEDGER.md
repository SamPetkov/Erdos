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
| `ProfileEntropyS4.partition`, `ProfileEntropyS4.weight`, `ProfileEntropyS4.mean`, `ProfileEntropyS4.variance` | finite-support analytic infrastructure for Lemma 3.1 | defined; normalization and positivity proved | Exact exponential-family objects on support `{2,3,4,5}` with positive normalized weights. |
| `ProfileEntropyS4.hasDerivAt_mean`, `ProfileEntropyS4.variance_pos`, `ProfileEntropyS4.existsUnique_mean_eq_of_mem_Ioo` | finite-support analytic infrastructure for Lemma 3.1 | proved | The mean derivative is the strictly positive variance, its endpoint limits are `2` and `5`, and every target in `(2,5)` has a unique real tilt parameter. This file explicitly does not claim manuscript Lemma 3.1. |
| `ProfileEntropyS4.optimizer_isFeasible`, `ProfileEntropyS4.entropy_score_le_log_partition_sub_tilt_mul_target`, `ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target` | finite-support entropy optimizer | proved | `ProfileOptimizerS4.lean` extends the common `ProfileEntropyS4` namespace: the unique target-mean tilt gives the exact positive optimizer; a zero-safe relative-entropy argument proves the variational inequality for every feasible competitor and exact equality at the optimizer. |
| `ProfileEntropyS4.optimizedValue`, `ProfileEntropyS4.abs_optimizedValue_sub_optimizedValue_le`, `ProfileEntropyS4.tendsto_optimizedValue_of_uniform_scores` | finite-support value part of (3.9) | defined; stability and fixed-target convergence proved | At every fixed `T∈(2,5)`, the optimized value is 1-Lipschitz in the coordinatewise score norm; uniform convergence over the four coordinates implies sequential value convergence.  This does not yet prove compact-uniform tilt or optimizer convergence in `T`. |

## Remaining proof dependency graph

The following items are open.  Names here are work-package labels, not hidden
Lean axioms or claimed theorems.

1. Prove existence, uniqueness, derivative bounds, and support comparison for the
   continuous profile roots (Lemma 3.1).  Roots will not be introduced by
   choice until existence and uniqueness are proved.
2. The unrestricted chromatic lower-location argument (§4).
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
   core, exact leftover size, graph-specific expectation bound (10.7), and
   deterministic concatenation inequality (10.9) are now proved.  The
   lower-tail step (10.8) and the
   simultaneous leftover-colouring event remain.
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
