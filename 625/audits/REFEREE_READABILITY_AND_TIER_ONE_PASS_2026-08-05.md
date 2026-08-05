# Referee-readability and publication-rank audit

**Date:** 2026-08-05  
**Scope:** Erdős Problem 625 self-contained AMS verification manuscript  
**Base:** `agent/625-self-contained-bulletproof-manuscript`  
**Pass:** `agent/625-referee-readable-tier-one-pass`

## Executive assessment

This pass improves the manuscript in the dimensions that a demanding random-graph referee can evaluate directly: theorem visibility, proof navigation, exact finite interfaces, separation of asymptotic and combinatorial arguments, and reproducibility of the quantitative constant.

It does **not** change the verification status of the top-level theorem. A higher publication rank cannot be obtained by prose alone. The decisive remaining requirement is closure and independent replay of the phase, first-moment, partial-diagonal, and global assembly obligations listed in Appendix A.

If those obligations close without weakening the full-sequence statement, the mathematical contribution is substantially stronger than the earlier 95%-of-integers result: it resolves the exceptional phase and supplies a quantitative lower bound of order `n/(log n)^3` along every integer sequence. That theorem, rather than additional ornamentation, is the basis for a top specialist or broader high-level submission.

## Readability changes

### Front matter

- Replaced the repository-style boxed warning with a short typographic verification note.
- Rewrote the abstract around the mathematical theorem, obstruction, method, and consequence.
- Replaced the numbered “Theorem 0.1” presentation with an unnumbered main theorem.
- Reorganized the introduction into:
  1. problem and theorem;
  2. relation to previous work;
  3. four main ideas;
  4. why four consecutive sizes are used;
  5. a compact guide to the argument.
- Removed duplicated definitions from the introduction.

### Proof-object preliminaries

- Condensed the former sequence of Definition 0.x environments into a short notation section.
- Kept only objects used across multiple later sections.
- Distinguished configuration matchings, physical partial matchings, and block supports in one place.
- Stated the no-double-counting convention for high-skeleton and residual factors explicitly.

### Generated Sections 1–7 and 10

- Converted legacy paragraph proofs and terminal square symbols to genuine AMS `proof` environments.
- Retained the three-part proof structure in Section 7 through descriptive internal headings.
- Normalized `log 2` notation and several high-density transition paragraphs.
- Preserved every finite identity, hypothesis, quantifier, and summation domain from the frozen source.

## Mathematical hardening

### Section 8

The revised section now exposes the finite argument in the order in which it is valid:

1. sum the complete matching fiber;
2. extract exact one-cell deficit ratios;
3. pay the ambient falling-factorial loss once;
4. sum optional deficits;
5. partition the full references by endpoint table;
6. transport endpoint tables to the partial-diagonal weights;
7. insert the phase estimates.

The square-free endpoint comparison is no longer attributed to unnamed “local identities.” Its proof now derives:

- the exact cancellation of profile and multinomial factors;
- the local ratio between a two-sided full-containment atom and the two one-sided atoms;
- the identity `g(t)/g(s)=2^(ds+binom(d,2))`;
- the one ambient falling-factorial inequality;
- the cancellation producing the `Q_ij` factors.

The section also identifies the genuinely reusable finite core: the fiber sum, single ambient loss, optional-choice product, and endpoint-table regrouping work for any finite endpoint alphabet whose selected cells form a matching.

### Section 9

The former phrase “capped local reward with the thresholds of F” has been replaced by an exact function `Phi_F(r')`. The cycle-space expansion is now an equality before expectation.

The joint prescribed-cell estimate is derived explicitly from factorial moments:

```text
P(r'_ab >= x_ab for all a,b)
 <= product_ab theta_ab^(x_ab) / x_ab!.
```

The proof now explains why thresholds in cells sharing rows or columns may be expanded simultaneously.

The activity estimate `q_ab <= C theta_ab^2` has been promoted from a ratio heuristic to a lemma. Its proof uses:

- the intrinsic-regime bound `theta_ab <= e U^2 2^(-U/3)`;
- log-convexity of `g(x) theta^x / x!`;
- endpoint control at `x=3` and `x=floor(U/2)`;
- the exponent `-U^2/24 + O(U log U)` at the upper endpoint;
- a finite compactness argument for the remaining values of `U`.

The complementary regime now derives both factors explicitly:

- local rewards contribute at most `2^((U-1)m_0/2)`;
- restriction outside the exposed matching gives the cycle-space bound `2^(m_0/2)`.

### Quantitative constant

The coefficient ledger is now supported by an exact rational checker. It uses:

```text
r = 2^(1/20),
r_- = 1035264923841377 / 10^15,
r_+ = 1035264923841378 / 10^15,
r_-^20 < 2 < r_+^20.
```

All finite weights at the three rational tilts are integral powers of `r`. The high tails are bounded by an explicit first term plus a geometric remainder. Rational bounds for `log 2` come from

```text
sum_{k=1}^N 1/(k 2^k)
```

with an exact tail bound. The checker verifies the mean bracket, all four omitted-mass inequalities, and the final `139/500` ledger without floating-point decisions.

## What would actually raise the paper to a Tier-1 level

The manuscript is now closer to a form in which experts can audit the proof efficiently. The remaining rank-limiting issues are mathematical and verification-related:

1. **Close the concrete phase/chromatic-tail package.** Its constants and full-sequence quantifiers must match the paper exactly.
2. **Close the signed four-size first-moment assembly.** The entropy certificate, root displacement, tangent rounding, and positive signed first moment must be one theorem-facing chain.
3. **Close the complete partial-diagonal theorem.** Empty corner, central range, full corner, and assembly should be separate declarations with uniform phase hypotheses.
4. **Close the global high-skeleton and residual assembly.** The outputs of Sections 8 and 9 must feed one exact normalized-second-moment theorem without duplicate factors.
5. **Replay the final adapter on one integrated commit.** No theorem should be counted as closed from an isolated or stale branch.
6. **Obtain independent expert review.** At least one random-graph specialist should check the first-moment location and one combinatorics/formalization reviewer should check the overlap decomposition.
7. **Only then switch the front matter to publication mode.** The verification note and conditional language are mandatory until the preceding gates are green.

## Validation contract

The dedicated workflow now checks:

- deterministic generation from the frozen canonical TeX blob;
- conversion to AMS proof environments;
- absence of legacy boxes, paragraph proofs, terminal manual squares, placeholders, and implementation prose in Section 8;
- presence of the exact `Phi_F` interface and quadratic-activity lemma;
- exact rational constant verification;
- unique labels and balanced environments;
- successful AMS/BibTeX compilation;
- no unresolved references or citations;
- no overfull box wider than 5 pt;
- a full extractable manuscript of at least 30 pages and 15,000 words;
- representative renders of the first page, Sections 8 and 9, and the final page.

A green workflow certifies assembly, typesetting, structural invariants, and the constant ledger. It does not by itself certify the remaining top-level mathematical obligations.
