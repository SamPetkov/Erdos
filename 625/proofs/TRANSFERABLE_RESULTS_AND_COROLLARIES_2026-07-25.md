# Erdős 625: transferable results, stronger corollaries, and follow-up paper directions

**Date:** 25 July 2026  
**Purpose:** separate results that can strengthen the Erdős 625 manuscript from methods that may support independent papers  
**Status convention:** every item is labelled as an immediate conditional corollary, a finite theorem already checked in the repository, or a research direction requiring new work

## 1. Literature position after the public search

The public literature located in this audit contains the following closest results.

- Annika Heckel, *The difference between the chromatic and the cochromatic number of a random graph*, arXiv:2409.17614, proves a positive answer for roughly 95% of integers `n`.
- Annika Heckel, *On a question of Erdős and Gimbel on the cochromatic number*, Electronic Journal of Combinatorics 31(4), P4.72 (2024), proves that a high-probability upper bound on the gap cannot stay below `n^(1/2-o(1))` along all large `n`.
- Raphael Steiner, *On the Difference Between the Chromatic and Cochromatic Number*, SIAM Journal on Discrete Mathematics 39(4), 2268--2274 (2025), gives independent positive evidence and resolves related cochromatic questions.
- Heckel--Panagiotou, *Colouring random graphs: Tame colourings*, arXiv:2306.07253, develops the delicate second-moment technology used in the admissible-phase coloring literature.
- Gimbel--Kündgen--Molloy, *Fractional cocoloring of graphs*, arXiv:1906.05504, studies the fractional analogue but does not supply the all-phase random-graph result sought here.
- The Erdős Problems page for #625 still lists the problem as open and records Heckel's roughly-95% result. Its discussion thread also records a different two-independent-random-graphs coupling direction; that direction should be credited to the people named there if pursued.

The search found no public paper dated through 25 July 2026 that claims the same full-sequence `Omega(n/(log n)^3)` high-probability lower bound. This is a search result, not a guarantee that no unpublished or unindexed work exists.

## 2. Results that should strengthen the main Erdős 625 paper

### 2.1 Phase-resolved gap theorem

**Status: immediate conditional corollary of the canonical root formula, Proposition 9.2, and Lemma 10.2.**

Let

\[
 A_4(\delta)=\ln2-D_4(\delta).
\]

Equation (5.11), midpoint placement, integer rounding, and the `o(n/(ln n)^3)` amplification loss give

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge\left(\frac{(\ln2)^2}{8}A_4(\delta_n)-o(1)\right)
       \frac{n}{(\ln n)^3}}
\]

with high probability, once the normalized second moment is established.

This statement is stronger and more informative than a single uniform constant. It displays the residual phase oscillation instead of discarding it. A fixed-constant theorem should be presented as its corollary.

**Required manuscript bridge:** state continuity of `D_4` and uniformity of the error in (5.11) explicitly.

### 2.2 Stronger certified uniform constant

**Status: immediate conditional corollary after integrating PRs #31 and #32.**

PR #32 certifies

\[
 A_4(\delta)>\ln(1000/639)
\]

uniformly. PR #31 shows that the final fixed coefficient is divided by `8`, not `32`. Hence

\[
 \boxed{
 \chi(G_n)-\zeta(G_n)
 \ge \frac{(\ln2)^2}{8}\ln(1000/639)
      \frac{n}{(\ln n)^3}}
\]

with high probability, conditional on the completed second-moment chain.

The numerical coefficient is

\[
 0.026896409808379\ldots,
\]

about `6.687` times the coefficient currently printed in the canonical manuscript.

### 2.3 Simultaneous complement-symmetric corollary

**Status: immediate conditional corollary; no new second moment.**

Cochromatic number is complement-invariant:

\[
 \zeta(\overline G)=\zeta(G).
\]

Moreover, if `G_n~G(n,1/2)`, then `\overline G_n` has the same distribution. Apply the completed theorem once to `G_n` and once to `\overline G_n`, and take a union bound. For every certified coefficient `c` from the main theorem,

\[
 \boxed{
 \min\{\chi(G_n),\chi(\overline G_n)\}-\zeta(G_n)
 \ge c\frac{n}{(\ln n)^3}}
\]

with high probability.

This says that a mixed clique/independent partition beats both pure orientations simultaneously by polynomial scale. It is a clean structural corollary worth stating in the introduction.

### 2.4 Balanced-sign midpoint seed

**Status: rigorous conditional seed corollary; the high-probability structural upgrade needs a modified amplifier.**

Let `k=k_co`, and restrict the signed witness count to assignments having exactly

\[
 b=\lfloor k/2\rfloor
\]

clique declarations. Denote the restricted count by `Z_bal`. For each underlying partition,

\[
 \mathbb E Z_{\mathrm{bal}}
 =\frac{\binom{k}{b}}{2^k}\mathbb E Z_{\mathrm{sgn}}.
\]

Since the largest binomial coefficient is at least the average coefficient,

\[
 \binom{k}{\lfloor k/2\rfloor}\ge\frac{2^k}{k+1}.
\]

Thus the first-moment logarithm loses at most `ln(k+1)`, negligible compared with the `Theta(k)` midpoint margin.

Pointwise `Z_bal<=Z_sgn`, so

\[
 \frac{\mathbb E Z_{\mathrm{bal}}^2}
      {(\mathbb E Z_{\mathrm{bal}})^2}
 \le (k+1)^2
 \frac{\mathbb E Z_{\mathrm{sgn}}^2}
      {(\mathbb E Z_{\mathrm{sgn}})^2}.
\]

Consequently Proposition 9.2 would give the balanced seed

\[
 \Pr\{Z_{\mathrm{bal}}>0\}
 \ge\exp\{-\Lambda_n-O(\ln k)\}.
\]

This is already a nontrivial structural result: the rare witness can be required to use asymptotically equal numbers of clique and independent classes.

**High-probability upgrade.** A direct application of Lemma 10.2 forgets the balance information. To preserve it, introduce `k` labelled signed slots and the two-Lipschitz score

\[
 T=\max\{|W|+\#\text{nonempty slots}\},
\]

with exactly `b` clique-labelled slots. Deleting the altered vertex changes this score by at most two. The seed event has score `n+k`; bounded differences then shows that both the uncovered vertex count and the empty-slot count are `o(k)`. Coloring the leftover with independent classes produces, with high probability, a near-optimal cocoloring with

\[
 \#\text{clique parts}=(1/2+o(1))k,
 \qquad
 \#\text{independent parts}=(1/2+o(1))k.
\]

This modified amplifier should be written and audited before the structural statement is promoted to a theorem.

### 2.5 Explicit upper-tail family for the cocoloring location

**Status: already contained in Lemma 10.2; should be highlighted.**

For any deterministic `r>0`, the seed exponent `Lambda_n` gives

\[
 \Pr\!\left(
 \zeta(G_n)>k_n+C\left(
 \frac{\sqrt{n\Lambda_n}+\sqrt{nr}}{\ln n}
 +n^{1/3}+1\right)\right)
 \le e^{-r}+o(1).
\]

This is stronger than the one chosen specialization in the final proof. It gives a tunable tail family and can be quoted independently in later work on random partition parameters.

## 3. Finite results suitable for reuse outside Erdős 625

### 3.1 Matching-restriction inequality for weighted even subgraphs

**Status: finite theorem; kernel-checked in PR #34.**

Let `H=(V,E)` be a finite graph, let `M` be a matching, and let `E_even` be the family of even edge sets. Restriction

\[
 \rho_M:F\mapsto F\setminus M
\]

is injective on `E_even`. Indeed, if two even sets have the same restriction, their symmetric difference is an even subset of a matching. A nonempty subset of a matching has degree one at each of its incident vertices, so it cannot be even.

For arbitrary nonnegative edge weights `q_e`, injection into the full subset family gives

\[
 \boxed{
 \sum_{F\in E_{\mathrm{even}}}
   \prod_{e\in F\setminus M}q_e
 \le\prod_{e\in E\setminus M}(1+q_e)
 \le\exp\!\left(\sum_{e\in E\setminus M}q_e\right).}
\]

This removes cycle decompositions whenever a matching has already been exposed. Potential applications include configuration-model second moments, polymer expansions, parity-constrained subgraph sums, and high-temperature expansions with frozen matching edges.

**Possible standalone note.** The theorem alone is short; a separate paper would require a broader family of applications or extensions, for example matroidal restrictions, `Z/qZ` flows, or sharpness/stability results.

### 3.2 Exact cycle-space factor for two signed partitions

**Status: finite theorem proved in manuscript Lemma 6.1; much of the algebra is formalized.**

For two set partitions, build the bipartite support graph whose edges are overlap cells of size at least two. Compatible binary declarations are constant on connected components. The exact normalized factor is

\[
 2^{W+c(H)-|V(H)|}
 =\left(\prod_e g(r_e)\right)2^{\beta(H)}.
\]

The topological term is the size of the binary cycle space. This identity is a finite partition analogue of a high-temperature Ising expansion: local cell multiplicities contribute edge activities, while global sign compatibility contributes the cycle-space dimension.

**Generalization direction.** Replace the two declarations by `q` templates. Compatibility would be governed by a `q`-state constraint system on the overlap support, leading to Potts/Tutte-type factors rather than a binary cycle space. This is not required for Erdős 625 but could form a separate combinatorial-statistical-mechanics project.

### 3.3 All-high deficit calculus

**Status: finite arithmetic largely checked in PR #38; physical global assembly still missing.**

For an endpoint cell of size `m` and deficit `e` with `2e<m`, the exact local ratio has a uniform binary exponent budget

\[
 e\lfloor2m/3\rfloor
 \le em-\frac{e(e+1)}2.
\]

This yields a geometric base independent of the individual deficit. The resulting one-product treatment replaces separate near and middle ranges.

The reusable principle is:

> If a high-overlap local ratio has a convex quadratic exponent and every admissible deficit lies below half the endpoint size, charge every deficit to one fixed linear fraction of the endpoint exponent and sum one geometric series.

This pattern should be useful in second moments for bounded colorings and random set partitions. A standalone theorem would need an abstract hypothesis/result formulation rather than the current Erdős-625-specific type table.

## 4. General method theorems that could support independent papers

### 4.1 Rare-seed to typical-completion amplifier

**Status: exact theorem in the manuscript for cochromatic number; abstract generalization requires writing.**

The mechanism of Lemma 10.2 depends on four properties only:

1. a random object is exposed in independent vertex blocks;
2. `S_k`, the maximum size of an induced feasible subobject, is one-Lipschitz;
3. the rare seed event is exactly `S_k=n`;
4. an arbitrary leftover of size `s` can be completed at cost `g_n(s)` on one simultaneous high-probability event.

Then

\[
 \Pr\{S_k=n\}\ge e^{-\Lambda}
\]

implies, except with probability `e^{-r}+o(1)`, a leftover of size at most

\[
 O(\sqrt{n\Lambda}+\sqrt{nr}),
\]

and hence total cost at most `k+g_n(O(sqrt(n Lambda)+sqrt(n r)))`.

This abstract statement applies to many hereditary covering and partition parameters. A methods paper could develop variants with block Lipschitz constants, weighted scores, multiple resource types, and product-space measures beyond `G(n,1/2)`.

### 4.2 Finite-support root-displacement theorem

**Status: the required analysis is already implicit in Lemma 3.1 and Section 5; abstract formulation requires writing.**

Let `S` be a fixed finite deficit support whose convex hull contains the complete phase target interval. Define the limiting support loss

\[
 D_S(\delta)=\mathcal F_{S_+}(T_0)-\mathcal F_S(T_0).
\]

If

\[
 \inf_{\delta\in[0,1]}\{\ln2-D_S(\delta)\}>0,
\]

then the signed root for support `S` satisfies

\[
 r_+-r_S^{\mathrm{co}}
 =\left(\frac{(\ln2)^2}{4}
   \{\ln2-D_S(\delta_n)\}+o(1)\right)
   \frac{n}{(\ln n)^3}.
\]

Midpoint placement retains one half of this coefficient before the support-specific second moment is considered.

This theorem cleanly separates two tasks:

- **support design:** optimize the phase-uniform entropy advantage;
- **admissibility:** prove a second moment for the chosen support.

It provides a reusable optimization framework and explains why a numerically better support may still be a worse proof choice if it raises the transportation dimension.

### 4.3 Support frontier and complexity/advantage trade-off

**Status: diagnostic only.**

PR #33 scans finite supports and reports that `{2,3,4,5,6}` improves the limiting minimum advantage by only about `1.017%` over `{2,3,4,5}`, while raising the dense endpoint table from `4x4` to `5x5`. This supports the four-size support as the current practical frontier.

A publishable optimization result would require interval-certified global support comparisons, not grid scans. A useful theorem would characterize which fixed supports maximize the minimum advantage subject to cardinality or diameter constraints.

## 5. Additional research directions

### 5.1 Prove the exact phase minimum of the four-support advantage

The numerical scans place the minimum of `A_4(delta)` near the phase endpoint `delta=1`. Proving monotonicity or a unique minimum would replace the conservative omitted-mass certificate by a substantially sharper exact constant and clarify the phase geometry.

A possible route is to use

\[
 \frac{d}{dT}\mathcal F_S(T)=-\lambda_S(T)
\]

and compare the full- and four-support tilts with certified interval arithmetic. This remains a new analytic problem.

### 5.2 Asymmetric edge density `p != 1/2`

At `p=1/2`, clique and independent declarations have equal one-class weights, producing the exact `2^k` sign gain. For `p!=1/2`, declarations acquire an external field depending on class size. The overlap compatibility factor should become an inhomogeneous Ising partition function on the support graph.

A systematic extension could study when a mixed partition still improves on ordinary coloring and how the optimal clique/independent proportion depends on `p`. This is a plausible separate paper, not a corollary of the present proof.

### 5.3 Two-independent-graph coupling

The current Erdős Problems discussion records a reduction using two independent `G(n,1/2)` graphs and a McDiarmid coupling. This approach is conceptually different from the signed-overlap proof and may yield cleaner concentration or comparison statements. It should be pursued only with explicit attribution to the collaborators named in that discussion and after obtaining the precise coupling statement from a primary source or direct communication.

### 5.4 Fractional and LP relaxations

The fractional cochromatic literature suggests comparing the integral random gap with the fractional cochromatic number. Possible questions include whether the signed four-size profile has an LP interpretation, whether the integral/fractional gap is smaller than `n/(ln n)^3`, and whether dual variables recover the limiting tilt calculation. No such result follows automatically from the present manuscript.

## 6. Recommended paper strategy

### Main Erdős 625 paper

The strongest coherent version should contain:

1. the full-sequence theorem;
2. the phase-resolved coefficient;
3. the stronger certified constant from PRs #31--#32;
4. the simultaneous complement corollary;
5. the matching-restriction simplification and all-high-deficit Section 8 route;
6. the abstract rare-seed amplifier as a named method lemma.

The balanced-core statement may be included if the weighted-slot amplifier is completed cleanly. Otherwise it belongs in a final “further consequences” section as a proved seed statement plus an explicit conjectural upgrade.

### Best independent follow-up paper

The most promising standalone direction is not another numerical support scan. It is a methods paper combining:

- weighted even-subgraph restriction through an exposed matching;
- exact signed-partition cycle-space factors;
- a general rare-seed to typical-completion theorem;
- applications to at least two random partition models.

Without multiple applications, these ingredients are better presented as reusable propositions inside the main paper rather than split into several very short notes.

## 7. Priority order

1. Complete the Section 8 physical quotient/product theorem.
2. Complete the Section 9 intrinsic two-regime phase adapter.
3. Derive Proposition 9.2 on one integrated branch.
4. Insert the phase-resolved theorem and improved constant.
5. Add the simultaneous complement corollary.
6. Write the balanced-sign seed formally; decide whether the weighted-slot amplifier is concise enough for the main paper.
7. Only after the main theorem is closed, develop the abstract methods/general-`p` follow-up.
