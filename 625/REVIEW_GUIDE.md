# Reviewer guide for Erdős Problem 625

## 1. Scope and status

This guide is an entry point for an independent mathematical review of the
candidate proof in
[`proofs/COMPLETE_PROOF_SELF_CONTAINED.md`](proofs/COMPLETE_PROOF_SELF_CONTAINED.md).
The current review appendix has been re-audited against repository `main` at
`cda78922ea6c87bfc81f9bf693374dd045dac624`.  The PR branch was originally
cut earlier, so all added files state their base explicitly and remain
additive.

The current status is deliberately narrower than “verified solution”:

- the manuscript is a self-contained candidate proof;
- internal audits report no presently known blocking defect after the repairs
  recorded on 13 July 2026;
- the diagnostics test finite identities and selected numerical inequalities
  but do not prove the asymptotic theorem;
- the Lean project is substantial but partial, and `Erdos625Statement` remains
  unproved.

A reviewer should therefore treat every manuscript claim as unproved and use
this guide only as a navigation and traceability aid.

The current PR appendix incorporates the blocking corrections raised in the
first PR review: bounded row/column degrees are now hypotheses of the high-cell
matching statement; the middle strip has exact floor bounds; the Section 8
summation exposes its dependent witness fibres and admits infeasible formal data
only as a nonnegative overcount; and the Section 9 square-sum identity is stated
only off the exposed matching.  The separate verification report records the
finite regression coverage and the remaining asymptotic review boundary.

## 2. Exact theorem under review

For `G_n ~ G(n,1/2)`, the manuscript claims

\[
 \Pr\!\left\{\chi(G_n)-\zeta(G_n)\ge
 \frac{(\ln2)^2}{32}\ln\!\left(\frac{200}{153}\right)
 \frac{n}{(\ln n)^3}\right\}\longrightarrow1.
\]

The quantifier is along the full sequence of integers `n`, not merely an
infinite subsequence or a density-one set.

## 3. Canonical files

| Purpose | Canonical location |
|---|---|
| Mathematical manuscript | `proofs/COMPLETE_PROOF_SELF_CONTAINED.md` |
| Generated TeX | `output/tex/COMPLETE_PROOF_SELF_CONTAINED.tex` |
| Internal-layout PDF | `COMPLETE_PROOF_SELF_CONTAINED.pdf` |
| Publication source | `arxiv/main.tex` |
| Formal target | `formalization/Erdos625/Target.lean` |
| Formalization status | `formalization/FORMALIZATION_LEDGER.md` |
| Adversarial repair audit | `audits/ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` |
| Verification and artifact record | `FINAL_VERIFICATION.md` |
| Independent finite checker | `verification/erdos625_independent_checks.py` |
| PR #27 verification report | `PR27_VERIFICATION_REPORT.md` |
| Corrected Section 7 appendix | `proofs/PR27_SECTION7_CENTRAL_RATE.md` |
| Corrected Section 8 exposure | `proofs/PR27_SECTION8_EXPOSURE.md` |
| Corrected Section 8 sum | `proofs/PR27_SECTION8_HIGH_SKELETON_SUM.md` |
| Corrected Section 9 route | `proofs/PR27_SECTION9_RESIDUAL_RESTRICTION.md` |
| PR #27 finite regression checker | `experiments/review27_verification.py` |
| Entropy certificate checker | `experiments/entropy_certificate_upgrade.py` |

Historical drafts and earlier `PASS` audits are not substitutes for the
canonical manuscript.  Their scope is limited to the hashes and dates stated
inside them.

## 4. Logical dependency chain

The proof route is:

1. endpoint-uniform independence-number phase expansion;
2. unrestricted chromatic lower location;
3. four-size signed first-moment root and integer profile;
4. exact sign-summed overlap identity;
5. all partial diagonals;
6. canonical high-cell decomposition and high-skeleton summation;
7. uniform capped residual attachment estimate;
8. normalized second moment;
9. Paley--Zygmund seed and induced-capacity amplification;
10. final gap comparison.

The profile is constructed before the second-moment estimate is invoked.
Lemma 7.1 uses first-moment/profile information; Sections 8--9 then estimate
the exact overlap sum from Section 6.

## 5. Recommended review order

### Pass A: model, first moment, and root geometry

Read Sections 1--5.  Check:

- the definition of the phase `alpha_0`, floor phase `alpha`, and `delta`;
- uniformity as `delta` approaches either endpoint;
- exact adjacent-size ratios for `mu_s`;
- existence and localization of both ordinary and signed roots before applying
  the mean-value theorem;
- the entropy-loss constant and the direction of every comparison;
- tangent integer rounding and the effect on the exact signed first moment.

### Pass B: exact overlap representation

Read Section 6.  Check:

- ordered versus unordered normalization;
- compatibility of row and column signs on cells of multiplicity at least two;
- the component count `2^{c(H)}`;
- the factorization into local rewards and the binary cycle-space factor;
- the prescribed-cell bound before any product relaxation.

### Pass C: partial diagonals

Read Section 7 and
[`proofs/PR27_SECTION7_CENTRAL_RATE.md`](proofs/PR27_SECTION7_CENTRAL_RATE.md).
Check all three ranges separately:

- empty corner: iteration of the exact recurrence and the Poisson majorant;
- central range: the Stirling expression, the rate function, and its uniform
  negative gap;
- full corner: the reverse recurrence and use of the complete signed
  first-moment margin.

### Pass D: canonical high skeleton

Read Section 8 together with
[`proofs/PR27_SECTION8_EXPOSURE.md`](proofs/PR27_SECTION8_EXPOSURE.md) and
[`proofs/PR27_SECTION8_HIGH_SKELETON_SUM.md`](proofs/PR27_SECTION8_HIGH_SKELETON_SUM.md).
The critical finite statement is the exact exposure identity:
for every overlap table, the canonical high support, its multiplicities, the
selected labelled stub pairs, and the capped residual table reconstruct the
original table uniquely, and the incidence times the residual contingency law
cancels exactly to the original law.

Then check separately:

- endpoint transportation;
- near-containment decoration products;
- the large-residual middle strip;
- the small-residual completion bound;
- the final sum over all feasible canonical skeletons.

### Pass E: residual attachments

Read Section 9 and
[`proofs/PR27_SECTION9_RESIDUAL_RESTRICTION.md`](proofs/PR27_SECTION9_RESIDUAL_RESTRICTION.md).
Check:

- local reward telescoping and the fact that threshold alternatives do not
  double-charge triple cells;
- injectivity of the restriction `F -> F \ M` on even edge sets;
- the weighted subset-product expansion and nonnegativity of every `q_e`;
- the distinction between the off-matching square sum and its unrestricted
  factorized upper bound;
- both residual-mass regimes and the uniformity in the skeleton.

The direct restriction argument removes the simple-cycle decomposition,
residual-walk enumeration, and mixed matching-cycle encoding from the proposed
large-residual proof.

### Pass F: amplification and final quantifiers

Read Sections 10--11.  Check:

- the one-block oscillation of the induced cocolourable capacity;
- inversion of the rare seed into an expectation deficit;
- the simultaneous leftover-colouring event;
- deterministic selection of the growing tail parameter;
- the final union bound and full-sequence quantifier.

## 6. Four concentrated proof obligations

### 6.1 Uniform root and optimizer corridor

The derivative estimate must hold on a corridor already known to contain every
root of `L_S(n,k)+ck` for `0 <= c <= ln 2`.  The signed-root localization may
not depend on the derivative estimate it is later used with.

### 6.2 Complete partial-diagonal rate

The central rate is

\[
 \Phi_T(z)=R\ln R+\frac{\ln2}{2}(I_r-TR).
\]

The review rewrite isolates a finite analytic lemma proving a uniform negative
multiple of `1-R` over the exact stated domain.  Check the domain restrictions,
numerical endpoint inequalities, and the domination of entropy/Stirling
errors.

### 6.3 Conditioned global high-skeleton expansion

A per-cell ratio is not enough.  The proof needs a finite global identity or
nonnegative expansion that records:

- distinguishable selected cells;
- typed multiplicities when labels are forgotten;
- the one global falling-factorial denominator;
- cap and no-return constraints;
- the split between large and small residual mass.

### 6.4 Weighted residual restriction

The revised large-residual route uses the simpler finite fact that an even edge
set supported on a matching plus residual edges is uniquely determined by its
residual restriction.  Check the injection, then verify

\[
 \sum_{F\text{ even}}\prod_{e\in F\setminus M}q_e
 \le\prod_{e\notin M}(1+q_e).
\]

The off-matching square sum is only bounded by the unrestricted factorized sum;
it is not equal to it.  The exact finite cycle and traversal modules remain
valid but are not needed by this replacement route.

## 7. Uniformity checklist

For every load-bearing `O`, `o`, or `Omega`, record:

| Item | Required uniform variables |
|---|---|
| Section 3 root corridor | phase `delta`, support, `0 <= c <= ln 2` |
| finite optimizer convergence | target mean in the fixed compact interval |
| Section 7 rate gap | phase, exact rounded profile, all central subprofiles |
| Section 8 middle strip | cell type, floor errors, residual skeleton |
| Section 9 local increments | every feasible canonical skeleton |
| Section 9 residual restriction | residual edge relation, degree lists, and matching support |
| amplification | deterministic `k_n`, seed exponent, and tail parameter |

A useful audit question is: “Could the implicit constant change with the
skeleton, phase, profile coordinate, or residual mass?”  If yes, the estimate
is not yet sufficient for the downstream supremum or full-sequence limit.

## 8. Notation cleanup

The current manuscript uses `B_n` for two unrelated quantities:

- the affine coefficient in the profile decomposition near equation (3.12);
- the scale `n/N^4` near equation (10.10).

The review rewrite recommends `b_n^{aff}` for the first and `mathcal B_n` for
the second.  It also recommends reserving:

- `M` for the high matching only;
- `m_0` for residual stub mass;
- `R` for the partial-diagonal residual proportion;
- `r` for an overlap table or tail parameter only when the context is explicit.

## 9. Mechanical checks

The following are useful regression checks, not proof certificates:

```text
python 625/verification/erdos625_independent_checks.py
python 625/experiments/exact_chi_zeta.py --self-test --exhaustive-n 5
python 625/experiments/review27_verification.py
python 625/experiments/entropy_certificate_upgrade.py
```

For Lean reproduction, follow
[`formalization/SELF_CONTAINED_BUILD.md`](formalization/SELF_CONTAINED_BUILD.md)
and the pinned toolchain.  The formalization ledger, not successful compilation
alone, determines which manuscript claims are actually closed.

## 10. Reporting a finding

A useful review report should identify:

1. the exact equation, lemma, or paragraph;
2. the quantified domain in which the issue occurs;
3. whether the problem is logical, asymptotic, combinatorial, probabilistic,
   notational, or expository;
4. a minimal counterexample or failed inequality when available;
5. whether downstream statements use only a weaker claim;
6. the smallest repair that restores the dependency chain.

Avoid reporting finite numerical agreement as proof, or a successful Lean
component build as proof of an unformalized manuscript endpoint.
