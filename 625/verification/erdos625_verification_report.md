# Verification report: proposed solution of Erdős Problem 625

**Review date:** 2026-07-12  
**Input archive:** `d76e97b2-6bde-4e19-905d-16733d1ea5c2.zip`  
**Archive SHA-256:** `037f9a32a1c0d32c996bfd64222f65d121ac14871efab92826dd16def810c783`  
**Primary manuscript:** `proofs/COMPLETE_PROOF_SELF_CONTAINED.md`

## 1. Verdict

**Provisional internal verification: PASS.**

I found no blocking mathematical error in the submitted proof. The theorem statement, first-moment root separation, exact signed overlap identity, partial-diagonal analysis, dense-cell transportation, residual cycle expansion, and rare-event amplification form a coherent proof chain. The central exact identities survived independent finite reconstruction, and all supplied diagnostic programs executed successfully.

This is sufficient to proceed to autoformalization. It is **not** equivalent to peer review, journal refereeing, community acceptance, or machine verification. Because the manuscript claims an all-`n` positive resolution of a problem that is still publicly listed as open, the appropriate public description remains **“candidate proof with a completed internal audit”** until the proof is formally checked or independently refereed.

## 2. Claimed result

The manuscript proves that, for `G_n ~ G(n,1/2)`, with `chi` denoting chromatic number and `zeta` denoting cochromatic number,

\[
\Pr\!\left(
 \chi(G_n)-\zeta(G_n)
 \ge
 \frac{(\ln 2)^2}{32}\ln\!\frac{200}{153}
 \frac{n}{(\ln n)^3}
\right)\longrightarrow 1.
\]

The explicit constant is approximately

\[
\frac{(\ln 2)^2}{32}\ln\!\frac{200}{153}
\approx 0.004021983962242005.
\]

This implies `chi(G_n)-zeta(G_n) -> infinity` with high probability and therefore answers Erdős Problem 625 positively.

## 3. External status checked

As of the review date, the Erdős Problems page still marks Problem 625 **OPEN** and summarizes the published state as follows: earlier work rules out a bounded gap with high probability; Heckel proves a positive answer for roughly 95% of integers `n`; and the conjectured scale is `n/(log n)^3`. The page records no complete solution in its comments and no existing formalization.

Relevant current sources:

- [Erdős Problems, Problem 625](https://www.erdosproblems.com/625)
- [Annika Heckel, *The difference between the chromatic and the cochromatic number of a random graph*, arXiv:2409.17614v2](https://arxiv.org/abs/2409.17614)
- [Annika Heckel, *On a question of Erdős and Gimbel on the cochromatic number*, arXiv:2408.13839](https://arxiv.org/abs/2408.13839)
- [Raphael Steiner, *On the Difference Between the Chromatic and Cochromatic Number*, SIAM Journal on Discrete Mathematics 39(4), 2025](https://doi.org/10.1137/24M1715180)
- [Google DeepMind formal-conjectures issue 2122](https://github.com/google-deepmind/formal-conjectures/issues/2122)

The submitted theorem is therefore materially stronger than the currently recorded literature if correct: it covers all sufficiently large integers rather than a density subset and obtains the conjectured polynomial scale.

## 4. Archive and reproducibility audit

The archive contained 44 files, with 665,369 uncompressed bytes and 259,736 compressed bytes. I found no path-traversal entry or malformed archive structure.

The core SHA-256 identifiers agree with `FINAL_VERIFICATION.md`:

| File | SHA-256 |
|---|---|
| `proofs/COMPLETE_PROOF_SELF_CONTAINED.md` | `53b2adccd64133991f3dcdcaa9f8e8820f38a12c982cc5735f96568dd014a190` |
| `proofs/COMPLETE_PROOF_DRAFT.md` | `42a39bc3a7d922b74ec3501ef233f93711f9c2769fe602eda70e145220b923d3` |
| `audits/FULL_PROOF_AUDIT_1.md` | `cc17be8a3196258ff6bfac6fad154ef7fa3d7ec7ce32cb29c4384c0397028213` |
| `audits/FULL_PROOF_AUDIT_2.md` | `2b9d96cbb560fd0674978b3111e1df22a511412cec42fdddf2be099f4e31125e` |
| `audits/FULL_PROOF_AUDIT_3.md` | `f7724290612866bd6d6a2105c95202c6c943c4ca93574708f980afb0d087ae6e` |
| `audits/FULL_PROOF_AUDIT_4.md` | `110549cedc8056bb7de57d43789ca81d3fd48bcf9d45add697141117166e632e` |
| `SOURCE_LEDGER.md` | `6b7d2acd66c4e51ff9c4608a081e4662cac28445bea98435dab990fcf1fd0f55` |

All seven Python files in `experiments/` compiled under Python 3.13.5. The following supplied programs ran without assertion or arithmetic failure:

- `alpha_minus_two_route.py`
- `constrained_profile.py`
- `constrained_profile_certify.py`
- `dense_transport_scan.py`
- `exceptional_cycle.py`
- `finite_slack_profile.py`
- `exact_chi_zeta.py --self-test --exhaustive-n 5`

The exact solver reported:

```text
SELF-TEST PASS: 1099 labelled graphs (all n=1..5) plus n=0
```

These computations are diagnostic only; the asymptotic theorem does not follow from them.

## 5. Mathematical audit, section by section

### 5.1 Independence-number phase — Section 2

**Assessment: pass.**

The expansion of

\[
\mu_s(n)=\binom ns2^{-\binom s2}
\]

at the phase value `alpha=floor(alpha_0)` is consistent with Stirling’s formula and the exact adjacent-size ratios. The deductions

\[
\mu_{\alpha+2}=o(1)
\quad\text{and}\quad
\mu_{\alpha-2}\ge c n^2(\ln n)^{2/\ln 2-5/2}
\]

have the correct powers and are uniform in the phase parameter `delta`. Markov’s inequality then correctly gives `alpha(G_n) <= alpha+1` with high probability.

### 5.2 Continuous profile roots — Section 3

**Assessment: pass, with a formalization-expansion requirement.**

The constrained entropy maximization, affine-plus-Gaussian decomposition of `-log d_{alpha-i}`, and envelope derivative yield the stated local root location and derivative

\[
\partial_k L_S(n,k)=\frac{2}{\ln 2}(\ln n)^2+O((\ln n)\ln\ln n).
\]

The support-comparison identity is exact after the common affine terms are removed. The limiting optimizer has a bounded exponential tilt and a Gaussian tail, which makes the claimed uniform dominated-convergence step plausible and consistent.

For formalization, Lemma 3.1 should be split into separate statements for:

1. existence and uniqueness of the entropy optimizer;
2. a phase-uniform bound on its Lagrange multiplier;
3. uniform summability of the infinite-support tail;
4. convergence of the value function;
5. local existence and uniqueness of the relevant root;
6. the derivative estimate in the entire `O(n/(log n)^3)` window.

### 5.3 Unrestricted chromatic lower bound — Section 4

**Assessment: pass.**

The first-moment count is correct for unordered profiles. The number of bounded profiles contributes only `exp(O((log n)^2))`, whereas moving `ceil(log n)` colours below the continuous root produces a negative exponent of order `(log n)^3`. On the high-probability independence-number event, any colouring with fewer parts can be refined to exactly `k_chi^-` nonempty independent parts, so the bounded-profile first moment gives an unrestricted chromatic lower bound.

### 5.4 Four-size signed first-moment advantage — Section 5

**Assessment: pass.**

The four sizes `alpha-2,...,alpha-5` cover the complete phase interval for the mean deficit. The entropy-loss certificate has the correct variational direction: evaluating the unrestricted dual function at the restricted optimizer gives an upper bound on the support loss. The explicit tail estimates imply

\[
\ln 2-D_4(\delta)>\ln(200/153)
\]

uniformly through the phase.

The root displacement calculation has the correct scale and coefficient:

\[
r_+-r_4^{co}
 =\left(\frac{(\ln2)^2}{4}\{\ln2-D_4(\delta)\}+o(1)\right)
 \frac{n}{(\ln n)^3}.
\]

The integer rounding uses two tangent corrections and changes all counts by only `O(1)`. Positivity of every type count is protected by a phase-uniform lower bound on the optimizer proportions. The signed first moment remains exponentially large on the `n/log n` scale.

### 5.5 Exact signed overlap representation — Section 6

**Assessment: pass; high confidence.**

For two labelled profile partitions, the overlap law

\[
p(r)=\frac{\prod_a s_a!\prod_b t_b!}{n!\prod_{a,b}r_{ab}!}
\]

is the standard bipartite configuration-model contingency law.

The exact sign sum is correct. A cell of size at least two forces equality of its row and column declarations. Sign assignments are therefore constant on each connected component of the support graph. After normalization, this gives

\[
A_\zeta(r)
 =2^{W+c(H)-|V(H)|}
 =2^{\beta(H)}\prod_{a,b}g(r_{ab}).
\]

I independently checked this identity exhaustively on all 625 two-by-two overlap matrices with entries from 0 through 4.

The prescribed-cell estimate retains one global falling factorial before taking the product majorant. Its stub-selection count and union-bound direction are correct. I independently checked it in 4,170 small configuration-model cases.

### 5.6 Exact partial diagonals — Section 7

**Assessment: pass, but this is one of the main formalization targets.**

The exact recurrence

\[
\frac{D(\ell+e_i)}{D(\ell)}
 =\frac{(k_i-\ell_i)^2}
 {2(\ell_i+1)\mu_{u_i}(n-m)}
\]

and the full-corner recurrence are obtained by valid factorial cancellation.

The three-region decomposition is coherent:

- the empty corner is controlled by a Poisson-type recurrence with total intensity `o(1)`;
- the central range is killed by a phase-uniform negative rate;
- the full corner is exponentially suppressed by the positive signed first-moment margin and the very small independence-set expectations in a residual set of size at most `n/32`.

The signs in the central rate are consistent. In particular,

\[
I_r-TR=TY-I,
\]

and the two endpoint inequalities used to bound the rate follow from support in deficits `2,...,5`.

Before machine formalization, the derivation of equation (7.14) and the numerical negative-rate certificate should be isolated into explicit lemmas with all zero-coordinate conventions and uniform Stirling errors stated formally.

### 5.7 Dense endpoint transportation and middle cells — Section 8

**Assessment: pass, with concentrated residual risk in Lemma 8.3.**

Cells larger than half the maximum class size form a matching. This makes the canonical high-cell decomposition unique.

The geometric-mean transportation inequality has the correct denominator direction. Concavity of `x -> log (n)_x` gives

\[
\frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_{J(L)}}
 \le (n+1)^{\frac12\sum |i-j|\ell_{ij}},
\]

and the unequal-type local factor is exactly the displayed `Q_ij`. I independently exhausted 2,901 finite typed endpoint tables; every case satisfied the inequality, with equality only on expected diagonal cases.

The exact near-containment ratio (8.21) was independently checked in 684 cases. The sequence of consecutive ratios is log-convex on the stated range, so its maximum occurs at an endpoint; both endpoint values are small enough to make the near-containment series geometric.

The middle-strip estimate has the correct leading exponent. With `j=x log_2 n`, `1+o(1)<=x<=3/2+o(1)`, the quadratic coefficient is

\[
\frac{x^2}{2}-x\le-\frac38+o(1),
\]

which dominates all `O(j log log n)` terms. In the small-residual branch, the crude pointwise local-plus-cycle bound is still only `exp(O(n/(log n)^5))`.

For formalization, the transition from the joint prescribed-cell bound to the exponential middle-cell sum should be written as a standalone finite combinatorial expansion rather than one paragraph.

### 5.8 Residual local and cycle attachments — Section 9

**Assessment: pass, with concentrated residual risk in the cycle-kernel estimate.**

The expansion of each local factor into threshold indicators is nonnegative and exact. For an edge selected by an even subgraph, the alternatives

\[
1_{\{r\ge2\}}
 +\sum_{x\ge3}\Delta_x1_{\{r\ge x\}}
\]

avoid charging a triple cell twice. Applying the joint prescribed-cell bound only after fixing all demands preserves the required global dependence.

The estimates

\[
\Lambda_0=O(U^4/m_0),
\qquad
\tau=O(U^3/m_0)
\]

follow from the residual degree sums. The cycle-space factor is then bounded by a sum over simple cycles. Cycles disjoint from the high matching cost at most `n tau^4/(1-tau^2)`. For cycles meeting the matching, marking one matching edge and using the residual-walk kernel avoids an erroneous extra factor of the matching size at every traversal; the resulting cost is `O(h tau)`.

The small-residual branch correctly uses only the facts that the high skeleton is a matching, every residual support edge consumes at least two stubs, and every residual cell has size at most `U`.

For formalization, Lemma 9.1 should be decomposed into:

1. the finite cycle-space identity;
2. the nonnegative local-threshold expansion;
3. a joint-demand summation lemma;
4. row/column norm bounds for the residual kernel;
5. disjoint-from-matching cycle enumeration;
6. matching-intersecting cycle enumeration;
7. the small-residual deterministic bound.

### 5.9 Rare-event amplification — Section 10

**Assessment: pass; high confidence.**

The simultaneous leftover-colouring lemma follows from a union bound over all `n^(1/4)`-sets in the complement graph and a deterministic greedy clique construction. It gives a bound valid simultaneously for every induced vertex set.

The maximum size `S_k` of a `k_n`-cocolourable induced subgraph is 1-Lipschitz under the independent vertex-block exposure: after deleting the affected vertex, the two graph configurations agree. McDiarmid’s upper tail converts the seed probability into a bound on `n-E S_k`, and the lower tail then gives a large cocolourable induced set with high probability. Colouring the leftover vertices ordinarily produces the required full cocolouring.

All error terms are `o(n/(log n)^3)` under the proved second-moment exponent.

### 5.10 Final comparison — Section 11

**Assessment: pass.**

The chromatic lower event and cochromatic upper event need not be independent; a union bound is sufficient. Integer rounding losses of order `log n` are negligible compared with `n/(log n)^3`. The final constant is a conservative factor-two reduction of the preceding asymptotic separation.

## 6. Independent finite checks

I wrote a separate checker rather than modifying or importing the dossier’s programs. It verifies:

1. Lemma 6.1 on every `2 x 2` matrix with entries `0,...,4`;
2. the entire normalized signed second moment for `n=6`, profile `(3,3)`, both by direct enumeration of all graphs and by the overlap formula;
3. Lemma 6.2 in 4,170 small labelled-stub cases;
4. Lemma 8.1 on 2,901 finite four-type endpoint tables;
5. the exact local ratio (8.21) in 684 cases.

Output:

```text
PASS Lemma 6.1 sign-sum identity (625 overlap matrices)
PASS exact signed second moment for n=6, profile (3,3): ratio=5/2
PASS Lemma 6.2 prescribed-cell bound (4170 finite cases)
PASS Lemma 8.1 transport inequality (2901 typed tables; maximum ratio=1)
PASS exact near-containment ratio (8.21) (684 cases)
ALL INDEPENDENT FINITE CHECKS PASSED
```

The checker is supplied separately as `erdos625_independent_checks.py`.

## 7. Issues found

### Mathematical blockers

**None found.**

### Non-blocking editorial/package issue

`README.md` and `FINAL_VERIFICATION.md` refer to files such as
`sources/SOURCE_LEDGER.md`, `sources/RECENT_WORK_AUDIT.md`, and
`sources/HISTORICAL_SOURCE_AUDIT.md`. In the supplied ZIP, those files are at the archive root rather than inside a `sources/` directory. The recorded SHA-256 for `SOURCE_LEDGER.md` itself is correct; only the path is inconsistent.

This should be fixed before public distribution because it breaks documented cross-references and reproducibility commands.

### Remaining epistemic risk

The proof’s main remaining risk is not an identified contradiction; it is the density of several asymptotic arguments. The four locations most likely to expose a hidden quantifier or bookkeeping issue during formalization are:

1. Lemma 3.1: uniform infinite-support entropy convergence and local-root uniqueness;
2. Lemma 7.1: uniform Stirling expansion and central negative-rate certificate;
3. Lemma 8.3: the full middle-cell expansion after a near-containment skeleton;
4. Lemma 9.1: the operator/kernel bound for cycles intersecting the high matching.

These are the first places a formal proof should attack.

## 8. Recommended autoformalization order

A monolithic translation would be inefficient. The proof should be formalized in dependency layers.

### Layer A — finite graph definitions

- finite simple graphs and complements;
- independent sets and cliques;
- proper colourings and chromatic number;
- cocolourings and cochromatic number;
- monotonicity under induced subgraphs;
- concatenation of a cocolouring with an ordinary colouring.

### Layer B — exact finite combinatorics

- unordered and labelled profile partitions;
- exact first-moment formula;
- overlap matrices and their configuration-model law;
- exact sign-sum identity;
- binary cycle-space cardinality;
- joint prescribed-cell bound;
- exact diagonal and endpoint weights;
- exact near-containment ratio.

This layer is the best first milestone because it is independent of asymptotic probability and contains the novel algebraic core.

### Layer C — finite analytic inequalities

- Stirling bounds with explicit remainders;
- falling-factorial concavity;
- entropy maximizers on finite support;
- the explicit four-size entropy certificate;
- geometric-mean transportation;
- finite negative-rate inequalities.

### Layer D — asymptotic profile geometry

- phase expansion for `mu_alpha`;
- continuous roots and derivatives;
- root separation;
- integer profile rounding;
- partial-diagonal three-region estimate.

### Layer E — second moment

- unique high-cell matching decomposition;
- endpoint table sum;
- near and middle high cells;
- residual threshold expansion;
- cycle-kernel bounds;
- normalized second-moment exponent.

### Layer F — probability amplification and conclusion

- Paley–Zygmund;
- bounded differences for `S_k`;
- simultaneous leftover colouring;
- rare-event-to-high-probability transfer;
- final chromatic–cochromatic comparison.

## 9. Recommended formalization status label

Use the following status in the repository until a proof assistant accepts the central theorem:

> **Candidate all-`n` solution; internally audited; exact finite core independently checked; formal verification in progress.**

## 10. Final conclusion

The dossier is coherent, reproducible, and mathematically strong enough to justify proceeding. I found no fatal gap, missing regime, reversed inequality, lost factorial, double-counted sign factor, or invalid amplification step. The exact combinatorial core is especially well supported by independent checks.

The correct next action is to formalize the finite overlap/sign/configuration machinery first, then formalize the four concentrated asymptotic lemmas listed above. A proof-assistant failure in one of those lemmas would give a precise diagnostic; success would provide substantially stronger verification than another prose audit.
