# Erdős Problem 625: full theorem-by-theorem and lemma-by-lemma audit

**Audit date:** 25 July 2026  
**Canonical text audited:** `625/arxiv/main.tex` on `main`, together with public PRs #27 and #30--#39  
**Status of this document:** adversarial mathematical review and integration plan; not external peer review and not a declaration that the theorem is proved

## 1. Executive verdict

The candidate manuscript has a coherent global strategy and a large sound core. I found no contradiction in the location calculation (Sections 2--5), the exact signed overlap identities (Section 6), the partial-diagonal estimate (Section 7), or the rare-seed amplification (Section 10). The final event intersection in Section 11 is also correct once its inputs are available.

The proof should nevertheless **not yet be described as closed**. The load-bearing unresolved boundary is concentrated in the following two bridges:

1. **Section 8 physical assembly.** The endpoint transportation inequality and the one-cell high-deficit estimates must be transported through the exact labelled/unlabelled quotient, the dependent family of physical endpoint cells, and the global stub-matching normalization. The present public branches contain most finite ingredients, but not one theorem that identifies their product with the complete canonical high-skeleton sum.
2. **Section 9 asymptotic assembly.** The simplified matching-restriction/q-only attachment theorem must be combined with the attained midpoint profile in both intrinsic residual regimes, including the complementary phase-asymptotic estimate, and then inserted into the exact decomposition defining Proposition 9.2.

These are narrower obligations than the original near/middle/cycle-walk analysis, but they are substantive. Until they are discharged, Proposition 9.2 and hence Theorem 1 remain conditional.

### Audit labels

- **GREEN:** the displayed result and its local proof are logically sound at manuscript level; suggested edits improve exposition or modularity only.
- **GREEN-FINITE:** an exact finite theorem is kernel-checked or exhaustively regression-tested, but its asymptotic/profile specialization is separate.
- **AMBER:** the argument is plausible and no counterexample was found, but a quantified bridge, normalization, or uniformity statement is not fully supplied.
- **BLOCKED:** the stated downstream conclusion depends on an AMBER bridge and must not yet be treated as established.
- **IMPROVEMENT:** a stronger statement follows from the accepted chain once a short explicit bridge is added.

## 2. Dependency graph

The proof has the following logical spine.

```text
Lemma 2.1
   |
   +--> Lemma 3.1 --> Section 4 chromatic lower location
   |          |
   |          +--> Lemma 5.1 --> midpoint profile and root separation
   |                                      |
   |                                      +--> Lemmas 6.1--6.2
   |                                                   |
   |                                                   +--> Lemma 7.1
   |                                                           |
   |                                                           +--> Lemmas 8.1--8.3
   |                                                                     |
   |                                                                     +--> Lemma 9.1
   |                                                                              |
   |                                                                              +--> Proposition 9.2
   |                                                                                         |
   +-----------------------------------------------------------------------------------------+
                                                                                             |
                                                               Lemmas 10.1--10.2 <-----------+
                                                                         |
                                                                         +--> Section 11 --> Theorem 1
```

The exact finite overlap algebra in Section 6 is independent of the asymptotic root calculation. Lemma 10.2 is also an abstract amplification mechanism: it needs only a rare seed for a hereditary induced-subgraph feasibility event and a simultaneous leftover-coloring estimate.

## 3. Preliminary inequalities and conventions

### 3.1 Stirling, bounded differences, Paley--Zygmund, binomial tail, Markov

**Verdict: GREEN.**

The manuscript uses standard forms with the correct directions. The binomial estimate

\[
 \Pr\{\operatorname{Bin}(m,1/2)\le m/4\}\le e^{-m/16}
\]

is weaker than the sharp Chernoff exponent but sufficient. The one-sided bounded-differences inequalities used later follow from the stated two-sided form.

**Recommended edit.** State once that all asymptotic constants in Sections 2--11 are deterministic and, whenever claimed, uniform over the closed phase interval used for compactness. This prevents later uses of `o(1)` from silently changing quantifier order.

## 4. Section 2: complete independence-number phase

### 4.1 Lemma 2.1 (phase expansion)

**Verdict: GREEN.**

The expansion of `ln mu_alpha` follows from the exact identity

\[
 \ln\mu_\alpha=\ln(n)_\alpha-\ln(\alpha!)-(\ln2)\binom\alpha2
\]

and a uniform expansion of `ln alpha`. The adjacent-size ratios in (2.8) are exact. They correctly imply

\[
 \mu_{\alpha+2}=n^{\delta-2+o(1)}=o(1)
\]

uniformly in the phase and the lower bound on `mu_(alpha-2)` used in the empty-corner estimate.

The endpoint `delta=1` is used only as a compact limiting endpoint; the actual fractional part lies in `[0,1)`. The formulas extend continuously and uniformly to the closed interval, so this is legitimate.

**Recommended edits.**

1. Add a one-sentence statement that the error in (2.2) is uniform on the closed interval `[0,1]`, with `delta=1` interpreted by continuous extension.
2. Isolate the adjacent-ratio corollary as a named statement. It is used repeatedly in Sections 4 and 7 and is easier to audit as a reusable lemma.

## 5. Section 3: continuous profile roots

### 5.1 Lemma 3.1 (root phase, derivative, and support comparison)

**Verdict: GREEN, with one modularity improvement.**

The affine-plus-curved decomposition (3.11) is exact. Under the fixed mean constraint, its affine terms cancel, leaving the finite entropy variational problem. The Gaussian upper bound on `h_n(i)` gives uniform summability for the unrestricted support. The tilted mean has derivative equal to a positive variance, so the inverse mean map is well-defined and uniformly Lipschitz on the compact target interval.

The root corridor follows from the sign change of the scalar objective and the uniform derivative

\[
 \frac{\partial}{\partial k}\{L_S(n,k)+ck\}
   =\frac{2}{\ln2}(\ln n)^2+O((\ln n)(\ln\ln n)).
\]

The statement says “unique zero in the root corridor,” not global uniqueness outside that corridor; the proof establishes exactly that claim.

**Required explicit bridge for later constant improvements.** Add a named compactness lemma:

> The limiting value functions `F_(S_+)` and `F_(S_4)`, their optimizing tilts, and `D_4(delta)` are continuous on `delta in [0,1]`.

The proof is already implicit in the uniform convergence/inverse-map argument, but PR #31 needs the conclusion in this explicit form to convert a pointwise strict entropy inequality into a uniform positive margin.

**Recommended decomposition.** Split Lemma 3.1 into:

1. finite/limiting tilt existence and compact convergence;
2. the exact support-comparison identity;
3. root corridor and derivative asymptotics.

This does not change the mathematics, but substantially lowers the cognitive load of later citations.

## 6. Section 4: unrestricted chromatic lower location

### 6.1 Profile enumeration and first-moment lower bound

**Verdict: GREEN.**

The exact expectation (4.2) is correct for unordered colorings with a prescribed profile. The number of bounded profiles is at most `(n+1)^(alpha+1)=exp(O((ln n)^2))`, which is negligible compared with the negative displacement `-Theta((ln n)^3)` obtained by moving `ceil(ln n)` parts to the left of the root.

On the event `alpha(G_n)<=alpha+1`, any coloring with at most `k_chi^-` parts can be refined to exactly `k_chi^-` nonempty independent parts of size at most `alpha+1`; for large `n`, `k_chi^-<n`, so splitting is possible. This justifies (4.5).

**Recommended edit.** State `k_chi^-<n` explicitly before invoking refinement. It is immediate from `k_chi^-=Theta(n/ln n)` but removes a hidden finite condition.

## 7. Section 5: signed four-size first moment

### 7.1 Lemma 5.1 (uniform entropy certificate)

**Verdict: GREEN; a strictly stronger certificate is available.**

The tilt bracketing, monotonicity of the omitted low/high ratios, and the dual evaluation are logically correct. The manuscript proves

\[
 D_4(\delta)<\ln(153/100),\qquad
 \ln2-D_4(\delta)>\ln(200/153).
\]

PR #32 supplies a sharper exact rational certificate for the same support:

\[
 D_4(\delta)<\ln(639/500),\qquad
 \ln2-D_4(\delta)>\ln(1000/639).
\]

The latter uses exact rational enclosures for `ln 2`, `2^(1/20)`, both endpoint mean comparisons, and four omitted-weight ratios. It changes neither the profile nor any second-moment argument.

**Integration condition.** The finite-to-limiting convergence from Lemma 3.1 must remain stated uniformly on the entire target interval. No additional probabilistic argument is needed.

### 7.2 Exact integer midpoint profile

**Verdict: GREEN.**

The correction

\[
 \Delta k_2=e_1-3e_0,\qquad \Delta k_3=2e_0-e_1
\]

solves both integer conservation equations exactly. Since the four limiting type proportions are uniformly bounded below, the `O(1)` correction preserves positivity. The displacement is tangent to the feasible affine plane, and the entropy Hessian gives only an `O(1/k_co)` loss.

The signed first moment at the midpoint has a uniform positive exponential margin of order `k_co`; this is much larger than all polynomial profile-count losses.

### 7.3 Root separation and theorem constant

**Verdict: IMPROVEMENT.**

Equation (5.11) gives the phase-resolved separation

\[
 r_+-r_4^{\mathrm{co}}
 =\left(\frac{(\ln2)^2}{4}\{\ln2-D_4(\delta_n)\}+o(1)\right)
   \frac{n}{(\ln n)^3}.
\]

The midpoint retains one half of this separation. The floor/ceiling losses are additive `O(ln n)`, and the amplification loss is `o(n/(ln n)^3)`. Neither causes another fixed halving. Therefore the natural phase-resolved final coefficient is

\[
 \frac{(\ln2)^2}{8}\{\ln2-D_4(\delta_n)\}.
\]

To obtain a fixed explicit constant from a strict limiting inequality, define

\[
 \eta_0:=\min_{0\le\delta\le1}
  \left[\ln2-D_4(\delta)-\gamma\right].
\]

Continuity and strict positivity imply `eta_0>0`. The uniform `o(1)` can then be absorbed without halving the target coefficient. With the canonical entropy certificate this gives

\[
 c=\frac{(\ln2)^2}{8}\ln(200/153),
\]

four times the displayed constant. Combining PRs #31 and #32 gives

\[
 \boxed{c=\frac{(\ln2)^2}{8}\ln(1000/639)
        =0.026896409808379\ldots .}
\]

This improvement remains conditional on the complete second-moment chain, but it does not require changing that chain.

## 8. Section 6: exact signed second moment

### 8.1 Lemma 6.1 (exact sign sum)

**Verdict: GREEN and independently reusable.**

For two partitions, signs must agree across every overlap cell of size at least two. Hence signs are constant on each connected component of the support graph `H`. The compatible sign-pair count is exactly

\[
 2^{2k-|V(H)|+c(H)}.
\]

After dividing by the square of the one-partition signed probability, the normalized factor is

\[
 A_\zeta(r)=2^{W+c(H)-|V(H)|}
 =\left(\prod_{a,b}g(r_{ab})\right)2^{\beta(H)}.
\]

The second equality follows by separating one binary factor per support edge. The cycle-space identity

\[
 2^{\beta(H)}=\#\{F\subseteq E(H):\deg_F(v)\text{ is even for all }v\}
\]

is exact.

**Paper-strengthening opportunity.** Isolate this as a general proposition for two signed set partitions. It is a clean finite theorem with potential use in other random partition and spin-compatibility problems.

### 8.2 Lemma 6.2 (joint prescribed-cell bound)

**Verdict: GREEN.**

The witness count assigns disjoint row and column stubs to every demanded cell and then pairs them inside each cell. A fixed witness has probability `1/(m_0)_x`; the union bound yields (6.8). The simplification

\[
 (m_0)_x\ge(m_0/e)^x
\]

has the correct direction and gives (6.9).

**Recommended edit.** State the `m_0=0` boundary separately wherever the lemma is invoked, although the residual decomposition normally treats it deterministically.

## 9. Section 7: exact partial diagonals

### 9.1 Exact marked identities and recurrences

**Verdict: GREEN.**

The common-subprofile weight `D(ell)`, the forward ratio (7.4), the reverse representation (7.5), and the reverse ratio (7.6) follow by exact factorial cancellation. Marking intentionally overcounts overlaps containing several common blocks; because every term is nonnegative, this is valid for an upper bound.

### 9.2 Lemma 7.1 (all common subprofiles)

**Verdict: GREEN.**

The three ranges are exhaustive:

1. `m<=eta n` (empty corner);
2. `m>eta n` and `n-m>n/32` (central range);
3. `n-m<=n/32` (full corner).

In the empty corner, the forward recurrence gives a Poissonized majorant with total intensity `o(1)`. In the central range, the exact Stirling identity reduces the exponent to the rate function

\[
 \Phi_T(z)=R\ln R+\frac{\ln2}{2}(I_r-TR),
\]

plus lower-order entropy terms. The manuscript's numerical certificate `Phi_T<=-Y/5000` is sufficient. PR #30 proves the stronger exact rational endpoint certificate

\[
 \Phi_T\le -Y/100
\]

on the same domain. In the full corner, the reverse recurrence is decreasing and the exponentially large complete first moment suppresses all residual vectors.

**Recommended integration.** Replace the decimal endpoint checks by the exact rational/logarithmic certificate from PR #30. This is stronger, shorter, and easier to reproduce.

## 10. Section 8: canonical high skeletons

This is the principal unresolved part of the proof.

### 10.1 Lemma 8.1 (geometric-mean transportation comparison)

**Verdict: GREEN-FINITE / AMBER-INTEGRATION.**

The local falling-factorial/log-concavity comparison is algebraically correct. PR #36 proves a denominator-free squared version in Lean, including the exact product identity over the four endpoint types. This is the preferable formal form because it avoids cancellation before positivity is established.

**Remaining manuscript bridge.** State all factorial factors as positive on the feasible domain, then derive the unsquared geometric-mean inequality. Alternatively, keep the complete Section 8 argument square-free and use the AM--GM route of PR #38.

### 10.2 Lemma 8.2 (sum of endpoint tables)

**Verdict: AMBER in the canonical presentation; simplification available.**

The current Cauchy--Schwarz summation is plausible, but it introduces an unnecessary square of a margin sum and a polynomial count of margin vectors. PR #38 observes the termwise implication

\[
 W(L)\le\sqrt{D(r)A_LD(c)C_L}\,Q^L
 \quad\Longrightarrow\quad
 W(L)\le\frac{D(r)A_L+D(c)C_L}{2}Q^L.
\]

Each half can then be summed by dropping only one family of margin constraints and using a one-sided multinomial expansion. This removes the global Cauchy step and its polynomial loss.

**Required bridge.** The linear endpoint inequality must be stated for the exact physical table weight, not merely for an abstract type table. The quotient by permutations of indistinguishable slots and the dependence of the allowed cells on the endpoint pairing must be included in the theorem statement.

### 10.3 Lemma 8.3 (all nonendpoint high multiplicities)

**Verdict: BLOCKED in the canonical manuscript; promising replacement in PR #38.**

The canonical near/middle split contains several proof-audit hazards:

- asymptotic notation such as `3a/4+O(1)` appears inside finite summation limits and should be replaced by exact floor/ceiling cutoffs;
- the relation between labelled physical cells, type tables, and the unlabelled canonical skeleton weight is not stated as one disjoint-union/quotient identity;
- the global allocation of falling-factorial denominators across decorated cells is compressed into prose;
- the no-return/cap event and the residual attachment are not kept completely separate in every intermediate bound.

PR #38 replaces the near/middle split by one deficit coordinate. If a high cell has endpoint size `m` and multiplicity `j=m-e`, then `2e<m`, and the exact local ratio satisfies

\[
 n^e R_{m,d}(e)
 \le\left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^e.
\]

For the four endpoint sizes this produces a common base

\[
 \rho_n=O\!\left(\frac{(\ln n)^{7/3}}{n^{1/3}}\right)=o(1),
\]

and a total all-high decoration cost

\[
 \exp\{O(n^{2/3}(\ln n)^{4/3})\}
 =\exp\{o(n/(\ln n)^4)\}.
\]

The exact arithmetic checker passes. PR #39 repairs two local Lean elaboration failures in the product and one-cell modules. However, the following global obligations remain:

1. identify the physical endpoint-decoration family as an exact dependent finite fibre over endpoint pairings;
2. transport the one-cell ENNReal bound through the exact stub-matching cardinality ratio;
3. prove that the product over distinguishable physical cells corresponds to the intended canonical skeleton sum, with no omitted symmetry factor;
4. combine the endpoint-table and all-high-decoration sums in one quantified theorem uniform over the attained midpoint profile.

Until these are supplied, Lemma 8.3 is not established by the simplified branch.

## 11. Section 9: residual local and cycle attachments

### 11.1 Exact conditional decomposition

**Verdict: GREEN as an identity, subject to the precise definition of the Section 8 skeleton index.**

Once a canonical high skeleton has been exposed and the conditional residual matching law is fixed, the normalized moment decomposes as

\[
 \frac{\mathbb E Z^2}{(\mathbb EZ)^2}
 =\sum_{(\mathcal M,j)}w_{\mathrm{hi}}(\mathcal M,j)
   \mathcal A(\mathcal M,j).
\]

The high-skeleton index and residual event must match exactly the quotient used in Section 8; this is why the two sections cannot be verified independently at the final assembly step.

### 11.2 Lemma 9.1 (uniform attachment bound)

**Verdict: AMBER canonically; substantially simpler finite route available.**

The manuscript's local-increment expansion and deterministic small-residual bound have correct directions. No explicit counterexample was found to the cycle-kernel argument. Nevertheless, the matching-restriction route is both shorter and less fragile.

Let `M` be the exposed matching. Restriction

\[
 F\longmapsto F\setminus M
\]

is injective on even edge sets: if two even sets have the same residual part, their symmetric difference is an even subset of a matching, hence empty. Therefore, for nonnegative residual weights,

\[
 \sum_{F\text{ even}}\prod_{e\in F\setminus M}q_e
 \le\prod_{e\notin M}(1+q_e)
 \le\exp\!\left(\sum_{e\notin M}q_e\right).
\]

PR #34 kernel-checks this finite theorem. PR #35 carries it to a green `exp(O((ln n)^2))` large-residual profile envelope. PR #37 further observes `lambda_e<=q_e` and proposes the intrinsic split

\[
 2^U\le m_0^3
 \quad\text{versus}\quad
 m_0<2^{\lceil U/3\rceil}.
\]

In the first regime, the attachment is `exp(O(U^2))`; in the second, the deterministic bound has exponent `O(U 2^(U/3))=n^(2/3+o(1))` at the midpoint phase.

**Current CI boundary.** PR #37's full repository Lean job is green, but its focused two-regime target is not green at the audited head. The failed exported assembly theorem therefore must not be cited as kernel-checked until the local arithmetic proof is repaired and the focused workflow passes.

**Remaining mathematical bridge.** Prove the complementary phase-asymptotic estimate with the exact midpoint cap `U=(2+o(1))log_2 n`, and package both regimes into one uniform deterministic sequence `epsilon_n->0` at scale `n/(ln n)^4`.

### 11.3 Proposition 9.2 (normalized signed second moment)

**Verdict: BLOCKED.**

The final multiplication is correct:

\[
 \sup\mathcal A\cdot\sum w_{\mathrm{hi}}
 \le\exp\{o(n/(\ln n)^4)\}.
\]

The logarithm is nonnegative because the normalized second moment is at least one. But the proposition depends exactly on the unresolved global Section 8 sum and the Section 9 two-regime adapter. It is the single decisive bottleneck for Theorem 1.

## 12. Section 10: rare-event amplification

### 12.1 Lemma 10.1 (simultaneous leftover coloring)

**Verdict: GREEN.**

A union bound shows that every `n^(1/4)`-set has complement density at least `1/4` with high probability; averaging extends this to every larger set. Iterating maximum-degree neighborhoods in the complement produces an independent set of size `c ln n` inside every set of size at least `n^(1/3)`. Greedy removal yields simultaneously for all `S`

\[
 \chi(G_n[S])\le C|S|/\ln n+n^{1/3}.
\]

The constants are deliberately coarse but adequate.

### 12.2 Lemma 10.2 (amplification from a seed)

**Verdict: GREEN and independently reusable.**

The maximum size `S_k` of a `k_n`-cocolorable induced subgraph is one-Lipschitz under vertex-block exposure: deleting the altered vertex transfers a feasible set between the two configurations. The seed event is exactly `S_k=n`. The upper bounded-differences tail converts its probability into a bound on `n-E S_k`; the lower tail then bounds the leftover size. Lemma 10.1 colors the leftover and completes the graph.

The quantifier order is correct: the same simultaneous leftover event works for every deterministic `k_n`, `Lambda_n`, and `r`.

**Paper-strengthening opportunity.** Extract an abstract “rare seed to typical completion” lemma for vertex-hereditary partition properties. This method is useful independently of cochromatic number.

## 13. Section 11 and Theorem 1

### 13.1 Final event intersection

**Verdict: GREEN conditional on Proposition 9.2.**

The chromatic lower event and cocoloring upper event each have probability tending to one. A union bound is sufficient; no independence is required. The amplification loss is `o(n/(ln n)^3)`.

### 13.2 Theorem 1

**Verdict: BLOCKED by Proposition 9.2, not by the final arithmetic.**

Once Proposition 9.2 is proved with phase-uniform errors, the all-integer conclusion follows. The theorem should then be stated first in its stronger phase-resolved form and second as a fixed-constant corollary.

Recommended phase-resolved statement:

\[
 \chi(G_n)-\zeta(G_n)
 \ge\left(\frac{(\ln2)^2}{8}
     \{\ln2-D_4(\delta_n)\}-o(1)\right)
   \frac{n}{(\ln n)^3}
\]

with high probability.

Recommended certified fixed constant after integrating PRs #31 and #32:

\[
 \chi(G_n)-\zeta(G_n)
 \ge\frac{(\ln2)^2}{8}\ln(1000/639)
   \frac{n}{(\ln n)^3}
\]

with high probability.

## 14. Public PR audit and integration order

The open PRs are **not one linear stack**. There is an independent review layer, a Section 9 stack, and a Section 8 stack.

| PR | Role | Audit status | Recommended action |
|---|---|---|---|
| #27 | broad research notebook and early rewrites | draft; useful provenance, too broad to merge canonically | keep as notebook; do not merge wholesale |
| #30 | exact Section 7 rate and direct Section 9 restriction idea | green regression layer | merge/cherry-pick the Section 7 certificate; retain Section 9 note as motivation for #34--#35 |
| #31 | factor-four constant propagation | mathematically sound conditional on compact uniform slack | integrate after adding the explicit continuity/minimum lemma |
| #32 | stronger four-support entropy certificate | exact elementary certificate; conditional only on existing variational bridge | integrate into Lemma 5.1 after independent arithmetic review |
| #33 | review roadmap and support scan | diagnostic/coordination only | retain; do not cite scans as proof |
| #34 | finite matching-restriction product in Lean | green focused and full workflows | merge first in Section 9 stack |
| #35 | attained-profile direct attachment envelope | green focused and full workflows | merge after #34 |
| #37 | q-only intrinsic residual split | conceptually strong, focused workflow currently failing | keep draft; repair before merge or citation as kernel-checked |
| #36 | finite endpoint transport core in Lean | green focused and full workflows | merge first in Section 8 stack |
| #38 | endpoint AM--GM and all-high-deficit simplification | exact checker green; focused workflow failed at audited head | keep draft; PR #39 contains local Lean repairs and the audit layer |
| #39 | this full audit, local Section 8 repairs, and reusable-results dossier | stacked on #38 | keep draft until focused Lean and audit workflow are green |

### Recommended merge/integration sequence

1. Merge the independent, green finite modules: #34 and #36.
2. Merge/cherry-pick the clean independent improvements from #30, then #31 and #32 after their explicit bridges are inserted.
3. Merge #35 on top of #34.
4. Repair and green #37; retain only the q-only statements that pass the focused target without placeholders or hidden axioms.
5. Green #38/#39 on top of #36.
6. Create one new integration branch containing both the Section 8 and Section 9 stacks. Do not attempt to merge #37 directly into #38 without resolving their common-base topology.
7. Prove the exact Section 8 physical assembly theorem.
8. Prove the Section 9 midpoint phase adapter and instantiate the two intrinsic regimes.
9. Derive Proposition 9.2 in one theorem with no manuscript-only assumptions.
10. Only then replace canonical Sections 8--9 and update Theorem 1's constant.

## 15. Formalization status

The repository contains a substantial partial Lean development, but it does not prove `Erdos625Statement`. Green finite modules should be described exactly as finite or conditional endpoints. A successful full repository build can coexist with a failing focused target when the new module is not imported into the root aggregate; therefore focused workflow status is load-bearing for every new PR.

The final formalization frontier is not “event plumbing.” It is the same mathematical boundary identified by the manuscript audit: the exact global Section 8 quotient/product and the attained-profile Section 9 asymptotic assembly.

## 16. Minimal acceptance checklist for a submission-grade proof

Before presenting the paper as a resolution, the following must all be true.

- [ ] The exact physical high-skeleton index is defined once and used identically in Sections 8 and 9.
- [ ] The endpoint table quotient and all symmetry factors are proved by a finite disjoint-union or bijection statement.
- [ ] Every high-cell decoration factor is derived from the literal stub-matching ratio.
- [ ] The product/sum interchange is justified over the dependent physical cell family.
- [ ] Both intrinsic residual regimes are specialized uniformly to the exact midpoint profile.
- [ ] Proposition 9.2 is proved from those two integrated statements, not asserted by prose.
- [ ] Every `o(1)` used in the final chain is uniform in the full phase parameter.
- [ ] The stronger entropy constant and factor-four propagation are inserted only after the compact uniform-slack lemma is explicit.
- [ ] All focused workflows and the full Lean workflow are green at the exact submitted commit.
- [ ] The manuscript, generated PDF, audit notes, and formalization status use consistent claims.

## 17. Bottom line

The project is materially stronger than the canonical manuscript suggests: the first-moment constant can be improved, the Section 7 rate can be sharpened, the Section 9 cycle walk can be eliminated, and most of the Section 8 near/middle split can be replaced by one deficit calculation. These are real advances.

The remaining work is not a vague request for “more rigor.” It consists of two explicit integration theorems. Proving them would convert the present candidate solution into a substantially shorter and stronger all-phase proof. Failing to prove them would leave the second-moment proposition unsupported. The audit therefore recommends concentrating all new proof effort on these two bridges rather than adding further numerical experiments or unrelated formal lemmas.
