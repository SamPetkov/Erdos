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
| `cubeMean_exp_center_le`, `boundedDifferences_hasSubgaussianMGF` | fair-bit case of (1.4) | proved | Coordinate oscillation on the uniform finite Boolean cube implies the centered MGF bound with exact proxy `Σcᵢ²/4`; no MGF premise is assumed. |
| `integral_boolCubePMF_eq_cubeMean`, `boundedDifferences_twoSidedTail` | fair-bit measure bridge and tail | proved | Recursive cube averaging is the actual uniform-PMF expectation, giving the exact two-sided fair-bit tail. |

## Remaining proof dependency graph

The following items are open.  Names here are work-package labels, not hidden
Lean axioms or claimed theorems.

1. Generalize the proved fair-bit bounded-differences bridge to the manuscript's
   arbitrary finite block coordinates, transport the vertex-block exposure of
   `G(n,1/2)` to that product law, and prove the induced-set statistic's
   one-block oscillation. Flattening a vertex block into individual bits is
   not sufficient because it loses the required variance scale.
2. Assemble the now-proved quantitative falling-factorial,
   Robbins/Stirling, and logarithmic Taylor estimates into endpoint-uniform
   (2.5), (2.6), and (2.2), and derive (2.3), (2.4), and the probability
   limit (2.9).
3. Prove existence, uniqueness, derivative bounds, and support comparison for the
   continuous profile roots (Lemma 3.1).  Roots will not be introduced by
   choice until existence and uniqueness are proved.
4. The unrestricted chromatic lower-location argument (§4).
5. The four-size signed first-moment calculation and uniform entropy
   certificate (Lemma 5.1).
6. Exact sign-summed second-moment and prescribed-cell bounds (Lemmas 6.1–6.2).
7. All partial-diagonal ranges, with empty, central, and full corners kept
   explicit (Lemma 7.1).
8. Canonical high cells, endpoint transportation, and all nonendpoint high
   multiplicities (Lemmas 8.1–8.3).
9. Residual local/cycle attachment bound and normalized signed second moment
   (Lemma 9.1 and Proposition 9.2).  The residual estimate must remain
   one-sided; no equality is to be inferred from an upper bound.
10. Simultaneous leftover colouring and seed amplification (Lemmas 10.1–10.2).
11. Assembly of the preceding results into `Erdos625Statement` (§11).

The central high-risk corridor is items 6–9.  A reduction that merely restates
their global overlap bound will not count as progress; each profile family,
quantifier, endpoint, and uniform error term must be explicit.

## Trust and validation policy

- Toolchain: Lean `v4.31.0`; mathlib tag `v4.31.0`, pinned transitively by
  `lake-manifest.json`.
- Aristotle and other external proof-generation services are not used.
- CI rejects placeholders/project axioms with a source gate and runs
  `lake build --wfail`, making Lean's own placeholder warning fatal.  The
  optional external `nanoda` helper path is disabled.
- Before each published milestone: run `lake build`, scan all project `.lean`
  files for `sorry`, `admit`, and project axioms, inspect `#print axioms` for
  public theorems, and obtain an independent statement/dependency audit.
- Python experiments and manuscript audits remain evidence and diagnostics;
  they are not imported as proof certificates.

## Next checkpoint

The user has confirmed the full-proof-first campaign. The next technical
checkpoint is completion of the genuine bounded-differences bridge and the
quantified endpoint-uniform phase expansion. The private arXiv package remains
paused until `Erdos625Statement` itself is proved and the final kernel/source
audit passes.
