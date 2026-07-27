# Erdős 625: literal line-by-line and theorem-by-theorem audit

**Audit date:** 27 July 2026  
**Canonical source audited:** `625/arxiv/main.tex`  
**Source blob:** `c4d090b73cd5efcdb98cc30f79bb5f53c6c9bc97`  
**Audit branch:** `agent/625-line-by-line-theorem-audit-v2`  
**Parent mathematics branch:** PR #49  

## 1. Scope and standard of review

This audit treats the canonical TeX as a mathematical dependency graph, not as
one continuous essay. Every boxed theorem, lemma, and proposition is assigned
an exact source range, a proof range, a status, its first downstream use, and
an explicit repair when one is needed. Important unboxed claims are audited in
the same way.

The statuses are:

- **GREEN:** correct as written and sufficient for its first downstream use;
- **GREEN-REWRITE:** mathematically sound, or supported by a shorter checked
  replacement, but the theorem contract or exposition should be rewritten;
- **AMBER:** conditionally correct, with one named missing hypothesis,
  uniformity statement, or finite bridge;
- **RED:** not established by the canonical text as written, or downstream of
  an unresolved load-bearing result;
- **TYPO/EDITORIAL:** a source defect that does not itself invalidate the
  mathematics;
- **SUPERSEDED:** a longer route that should be removed from Version 2 in favor
  of a shorter checked argument.

A line range marked GREEN is not a claim that every displayed asymptotic has a
complete Lean formalization. It means that no mathematical gap was found in
that source argument and that the hypotheses stated or proved there suffice
for the first place where the result is used.

## 2. Executive verdict

There is one submission-blocking chain:

```text
Lemma 8.3
  -> Proposition 9.2
  -> Theorem 1.
```

No second unrelated fatal gap was found. Sections 2--7 and Lemmas 10.1--10.2
are structurally coherent. Lemmas 8.1--8.2 are also coherent and have cleaner
checked replacements. Section 9 is no longer an independent bottleneck because
the direct matching-restriction/q-only route controls the literal attained
attachment sum once the Section VIII bare-skeleton estimate is supplied.

The blocker is finite and precise:

> The canonical text does not prove that the entire attained physical
> high-skeleton family is reindexed without multiplicity by a block-level
> matching support, one admissible deficit per selected cell, and the associated
> local partial physical-matching fibres, with the exact aggregate weight.

The local ratio and global falling-factorial estimate used after that
reindexing are correct. The missing item is the exact global fibre theorem.

### Boxed-statement count

| Status | Boxed statements |
|---|---:|
| GREEN | 5 |
| GREEN-REWRITE | 5 |
| SUPERSEDED | 1 |
| RED | 3 |

The three RED boxed statements are Theorem 1, Lemma 8.3, and Proposition 9.2.
Theorem 1 and Proposition 9.2 are RED only through their dependence on Lemma
8.3; their final logical deductions are valid.

## 3. Complete source-range map

| Source lines | Content | Status | Audit conclusion |
|---:|---|---|---|
| 1--72 | Preamble and metadata | TYPO/EDITORIAL | The date and publication metadata are stale relative to the current audit. Mathematical content unaffected. |
| 73--98 | Abstract | RED | It says “We prove” before the load-bearing Section VIII theorem is closed. Use the audit-safe abstract until closure. |
| 99--225 | Introduction, Theorem 1, background, roadmap | MIXED | Theorem 1 is RED; the background and three-layer roadmap are useful but describe the old Sections VIII--IX rather than the shorter replacement route. |
| 227--292 | Notation and inequalities (1.1)--(1.5) | GREEN | Stirling, McDiarmid, Paley--Zygmund, the binomial tail, and Markov are used in valid ranges. |
| 293--447 | Section 2 and Lemma 2.1 | GREEN | Phase expansion, adjacent-size ratios, and the independence-number cap are uniform in the full phase. |
| 448--741 | Section 3 and Lemma 3.1 | GREEN-REWRITE | Correct continuous-root architecture, but one lemma currently contains several logically independent analytic theorems. |
| 742--797 | Section 4 | GREEN | The chromatic lower location is genuinely unrestricted after the probabilistic size cap. |
| 798--1307 | Section 5 and Lemma 5.1 | GREEN-REWRITE | Root displacement and integer rounding are coherent. The entropy certificate and final constant can be strengthened substantially. |
| 1308--1524 | Section 6 and Lemmas 6.1--6.2 | GREEN | Exact sign sum and prescribed-cell configuration bound are correct and reusable. |
| 1525--1936 | Section 7 and Lemma 7.1 | GREEN-REWRITE | Exact recurrences and three-range proof are coherent. Fix the TeX exponent typo and replace decimal rate checks by the exact certificate. |
| 1937--2149 | Section 8 definitions and Lemma 8.1 | GREEN-REWRITE | Canonical high support and endpoint transport are sound; use the square-free checked presentation. |
| 2150--2230 | Lemma 8.2 | GREEN-REWRITE | The Cauchy proof works, but termwise square-free AM--GM is shorter and avoids a polynomial loss. |
| 2231--2491 | Lemma 8.3 | RED | The exact attained-demand/physical-fibre reindexing and aggregate weight identity are not established. Replace the entire near/middle route. |
| 2492--2548 | Exact conditional decomposition (9.1)--(9.2) | GREEN-REWRITE | Correct target; synchronize it with the literal attained-attachment formalization. |
| 2549--2828 | Lemma 9.1 | SUPERSEDED | The old cycle/walk proof is unnecessary. Use matching restriction and the q-only two-regime theorem. |
| 2829--2866 | Proposition 9.2 | RED | Its final multiplication is correct, but it depends on RED Lemma 8.3. |
| 2867--2964 | Lemma 10.1 | GREEN | The simultaneous leftover coloring argument is valid. |
| 2965--3047 | Lemma 10.2 | GREEN | The seed-to-typical bounded-differences amplifier is valid and uniform in deterministic parameters. |
| 3048--3077 | Application of amplification | AMBER | Analytic scales are correct conditional on Proposition 9.2. |
| 3078--3111 | Completion of proof | RED | Union-bound intersection and subtraction are correct, but depend on Proposition 9.2. |
| 3112--3161 | Reproducibility, AI, funding, references | EDITORIAL | The statement that the Lean formalization is partial is accurate. Synchronize all theorem-status language before publication. |

## 4. Front matter and notation: lines 1--292

### Lines 1--72: metadata

- Lines 64--71 define the title, affiliation, date, MSC, and keywords.
- No mathematical issue arises here.
- The canonical date predates the present audit and should not be treated as a
  publication-status timestamp.
- The current audit-safe policy is to keep theorem claims conditional until the
  blocking chain closes.

### Lines 73--98: abstract — **RED**

- Lines 77--85 define the two invariants and state the full theorem.
- Line 80 says “We prove”. That sentence is not currently justified because
  Proposition 9.2 is not established on the integrated source branch.
- Lines 88--98 give a faithful high-level description of the method, but the
  configuration-model/cycle wording reflects the old Section IX route.

**Required repair.** Use an audit-safe abstract saying that the manuscript
contains a candidate proof whose only unresolved verification seam is the exact
Section VIII physical-fibre reindexing. After closure, replace the method
sentence by the shorter all-deficit and matching-restriction architecture.

### Lines 99--225: introduction and Theorem 1

- Lines 106--112 define the model and invariants correctly.
- Lines 114--119 state the historical question and introduce the result.
- Lines 121--130 state Theorem 1. The numerical constant is positive and would
  follow from the current first-moment calculation if Proposition 9.2 were
  established. The theorem is nevertheless **RED at present**.
- Lines 132--137 correctly emphasize the full-sequence phase issue.
- Lines 139--186 give relevant historical context. The bibliography should be
  synchronized with the later literature audit, including the foundational
  cochromatic and generalized-coloring references.
- Lines 188--225 give a useful dependency roadmap, but Sections VIII--IX should
  be described using the Version 2 route rather than the old near/middle and
  cycle-walk machinery.

### Lines 227--292: elementary inputs — **GREEN**

- Equation (1.1) is the expected number of \(s\)-vertex independent sets.
- Stirling (1.2) is invoked only with the stated zero-safe \(O(\log(m+1))\)
  variant when coordinates may vanish.
- McDiarmid (1.3) is later used with \(n-1\) independent vertex-exposure blocks
  and a one-Lipschitz variable.
- Paley--Zygmund (1.4) is used with a finite nonnegative witness count.
- The binomial bound (1.5) follows from exponential Markov; the displayed
  numerical exponential is conservative.
- Markov is used in the standard first-moment form.

No repair is needed.

## 5. Lemma 2.1: lines 295--322, proof lines 324--437 — **GREEN**

### Contract

The lemma must supply:

1. a phase-uniform expansion for \(\log\mu_\alpha\);
2. \(\mu_{\alpha+2}=o(1)\), to cap all independent sets at size
   \(\alpha+1\) with high probability;
3. a uniform polynomial lower bound for \(\mu_{\alpha-2}\), used in the empty
   corner of the partial-diagonal sum.

### Statement audit

- Lines 297--307 state the expansion with a bounded continuous \(K\).
- Lines 309--314 derive the upper adjacent-size estimate.
- Lines 315--322 state the lower estimate at \(a=\alpha-2\).
- The extension to \(\delta=1\) is harmless: the displayed formula for \(K\)
  extends continuously to the closed interval even though the actual phase has
  \(\delta<1\).

### Proof audit

- **Lines 324--343:** the representation
  \(\alpha=2S/\log2+b\), the falling-factorial expansion, and the use of
  Stirling are valid because \(\alpha=O(\log n)\) and
  \(\alpha^2/n=o(1)\).
- **Lines 344--384:** the Taylor expansion of \(\log\alpha\), multiplication by
  \(\alpha\), and the half-log Stirling correction give (2.2). All error terms
  are uniform for \(b\in(0,1]\).
- **Lines 385--405:** the adjacent-size ratios are exact. Their uniform
  \(\Theta(\log n/n)\) and \(\Theta(n/\log n)\) forms follow from the phase
  formula for \(\alpha\).
- **Lines 406--437:** (2.3) and (2.4) follow with the stated exponents; Markov
  then gives (2.9).

### Downstream sufficiency

- Equation (2.9) is strong enough for the unrestricted refinement argument in
  Section 4.
- The lower bound (2.4), together with the finite number of adjacent shifts,
  is strong enough for the empty-corner estimate in Section 7.

**Verdict:** no mathematical repair required.

## 6. Lemma 3.1: lines 495--561, proof lines 563--740 — **GREEN-REWRITE**

### Contract

This lemma simultaneously claims:

- existence and uniqueness of the two continuous roots;
- their common phase corridor;
- a uniform derivative of order \((\log n)^2\);
- exact support comparison at fixed mean;
- compact-uniform convergence of finite entropy values;
- bounded tilts, positive variance, and uniform optimizer convergence.

The content is coherent, but this is too much for one lemma.

### Statement audit

- The target \(T_0=1+2/\log2-\delta\) remains strictly inside the convex hull
  of \(S_4=\{2,3,4,5\}\) and of the truncated \(S_+\) support.
- The root corridor and derivative have the correct scales.
- Equation (3.8) is an exact fixed-mean cancellation of the affine score.
- \(K_*\) is a valid compact target interval contained in \((2,5)\).
- The finite-\(n\) optimizer on \(S_4\) has all four coordinates bounded below
  because the limiting Gibbs weights are continuous and strictly positive on a
  compact tilt interval.

### Proof audit

- **Lines 563--598:** dividing by \(k\) and decomposing
  \(-\log d_{\alpha-i}=A_n+B_ni+h_n(i)\) are exact. The separate \(i=-1\)
  formula is required and is supplied.
- **Lines 599--645:** Gaussian domination controls the finite \(S_+\) cutoff,
  the partition sums, first moments, and variances uniformly. The strict target
  inequalities at \(\pm\Lambda\) and the variance floor imply uniformly
  Lipschitz inverse mean maps. This justifies compact-uniform convergence and
  (3.8)--(3.9b).
- **Lines 646--700:** the scalar exponent at \(s_0\) is \(O(\log\log n)\).
  The cancellations in (3.15a)--(3.16) have the correct order.
- **Lines 701--740:** differentiating through the finite optimum is justified
  by the unique interior Gibbs optimizer. The derivative is
  \(-\log n+O(\log\log n)\) in the \(s\)-coordinate, yielding strict
  monotonicity, a unique corridor zero, and the stated \(k\)-derivative.

### Hidden conditions made explicit

1. For \(S_+\), every finite-\(n\) sum is truncated at \(i=\alpha-1\).
2. The target interval stays in the relative interior of both finite supports.
3. The variance floor is applied only on the selected compact tilt interval.
4. The envelope derivative is for the unique interior optimizer.

### Rewrite

Split the current lemma into:

1. finite Gibbs dual attainment and exact support comparison;
2. compact-uniform partition/moment/tilt convergence;
3. root corridor and uniqueness;
4. derivative at the root corridor.

**Verdict:** mathematically sound; rewrite for auditability.

## 7. Section 4: lines 743--797 — **GREEN**

- Lines 747--761 define the unrestricted continuous root, the integer lower
  location, and the exact unordered-profile expectation.
- Lines 764--780 sum all bounded profiles. There are
  \(\exp(O((\log n)^2))\) such profiles, and zero profile coordinates are
  handled by the zero-safe Stirling bound.
- Lines 782--795 use the derivative from Lemma 3.1 to move
  \(\lceil\log n\rceil\) to the left of the root, producing a negative exponent
  of order \((\log n)^3\).
- On the event \(\alpha(G_n)\le\alpha+1\), any coloring with at most
  \(k_\chi^-\) parts can be split into exactly \(k_\chi^-\) nonempty independent
  parts. Since \(k_\chi^-<n\) for large \(n\), no empty-part obstruction occurs.
- Markov proves (4.5).

This is a genuinely unrestricted lower bound. Promote (4.5) to a named
proposition in Version 2.

## 8. Lemma 5.1: lines 860--869, proof lines 871--1121 — **GREEN-REWRITE**

The loss \(D_4(\delta)\) is nonnegative because the four-point support is a
subset of the unrestricted support. The strict upper certificate implies a
uniform sign advantage.

- **Lines 871--968:** the lower tilt bracket at \(2\log2\) is correct. The
  reindexing \(j=i-2\) is bijective, and the infinite Gaussian mean is larger
  than the truncated mean. The rational tail estimates imply the stated
  \(4/5\) bound.
- **Lines 969--1000:** the upper tilt bracket at \(9\log2/2\) is exact; the
  numerator calculation \(t(1-t^8-2t^{24})=t/4\) is correct.
- **Lines 1001--1109:** monotonicity of the omitted low and high masses follows
  by differentiating their logarithms. The endpoint tail estimates are
  conservative and yield the two-region omitted-mass bounds.
- **Lines 1110--1121:** evaluating the unrestricted dual at the four-support
  optimizer gives the correct inequality direction, and the entropy loss is
  bounded by the log of the omitted-mass ratio.

The later exact certificate improves

\[
 D_4(\delta)<\log(153/100)
\]

to

\[
 D_4(\delta)<\log(639/500),
 \qquad
 \log2-D_4(\delta)>\log(1000/639).
\]

The stronger certificate should replace the current long tail ledger.

## 9. Root displacement and midpoint profile: lines 1123--1307 — **GREEN-REWRITE**

- **Lines 1123--1173:** the \(2^k\) signed gain is exact because all class sizes
  are at least two for large \(n\), so the independent and complete declarations
  are disjoint.
- **Lines 1174--1212:** the mean-value theorem, root corridor, and derivative
  give
  \[
    r_+-r_4^{\mathrm{co}}
    =\left(\frac{(\log2)^2}{4}
      (\log2-D_4(\delta))+o(1)\right)
      \frac n{(\log n)^3}.
  \]
- **Lines 1213--1248:** the midpoint integer and the two-coordinate correction
  enforce both conservation laws. The correction has bounded size and
  positivity follows from \(k_i=\Theta(n/\log n)\).
- **Lines 1249--1260:** the displacement is tangent to both constraints. The
  Hessian calculation gives an \(O(1/k)\) loss, stronger than needed.
- **Lines 1261--1307:** the exact signed first moment is exponentially large in
  \(k\), and a positive signed witness gives a genuine cocoloring.

The text loses more constant than required. Midpoint placement retains the
coefficient \((\log2)^2/8\), and integer rounding and amplification are lower
order. After Section VIII closure, the natural theorem is

\[
 \chi(G_n)-\zeta(G_n)
 \ge
 \left[
   \frac{(\log2)^2}{8}(\log2-D_4(\delta_n))-o(1)
 \right]
 \frac n{(\log n)^3}.
\]

The stronger certified fixed coefficient is

\[
 \frac{(\log2)^2}{8}\log(1000/639)
 =0.026896409808379\ldots.
\]

## 10. Lemma 6.1: lines 1354--1383, proof lines 1385--1428 — **GREEN**

- **Lines 1385--1394:** label slots. This deterministic labeling factor cancels
  in the normalized second moment.
- **Lines 1395--1405:** signs must agree across every overlap cell of size at
  least two, so they are constant on components of \(H\). Isolated row and
  column slots retain independent signs.
- **Lines 1406--1418:** \(W\) internal edge bits are prescribed twice. Dividing
  by the two marginal signed probabilities gives the first exact formula.
- **Lines 1419--1428:** split one unit from each support-edge exponent and use
  \(|E|-|V|+c=\beta\) to obtain the local/topological factorization.

No gap was found. Equation (6.7), lines 1429--1443, is the standard binary
cycle-space cardinality identity and is also GREEN.

## 11. Lemma 6.2: lines 1445--1482, proof lines 1484--1523 — **GREEN**

- **Lines 1445--1482:** feasibility conditions and both probability bounds are
  stated with the correct zero cases.
- **Lines 1484--1501:** selecting disjoint row and column stubs and then local
  bijections produces exactly
  \(\prod_a(d_a)_{D_a}\prod_b(d'_b)_{D'_b}/\prod x_{ab}!\)
  witnesses.
- **Lines 1502--1505:** a fixed witness has probability \(1/(m_0)_x\).
- **Lines 1506--1523:** the binomial and factorial inequalities yield
  \((m_0)_x\ge(m_0/e)^x\), after which falling factorials are bounded by powers.

The crucial feature is preserved: the exact result keeps one global
\((m_0)_x\) denominator before taking the cellwise product majorant.

## 12. Lemma 7.1: lines 1651--1659, proof lines 1667--1935 — **GREEN-REWRITE**

### Exact identities before the lemma

- The marked partial-diagonal definition is deliberately an overcount by
  nonnegative marked terms; no disjointness is claimed.
- **Source defect:** equation (7.2) writes `2^\ell_\bullet`. It must be
  `2^{\ell_\bullet}`.
- Equations (7.3)--(7.6) follow by exact factorial cancellation and one-coordinate
  ratios.

### Empty corner: lines 1667--1704

The lower bound on \(\mu_{u_i}(n)\) gives
\(\Xi_{\mathrm{empty}}=o(1)\). Iterating the exact recurrence while selected
mass is at most \(\eta n\) produces a product of exponential-series terms whose
total is \(1+o(1)\).

### Central range: lines 1705--1906

- Lines 1705--1723 introduce normalized selected and residual profiles and the
  exact residual vertex fraction.
- Lines 1724--1785 apply zero-safe Stirling and isolate the four coordinate
  costs \(E_i\).
- Lines 1786--1847 use the signed first-moment margin to control the affine
  average and derive the rate function.
- Lines 1848--1878 prove uniform negativity by two convex endpoint checks. The
  decimal inequalities should be replaced by the exact rational certificate
  from the later audit stack.
- Lines 1879--1906 show that the negative leading term dominates entropy and
  logarithmic errors uniformly away from both corners.

### Full corner: lines 1907--1935

The adjacent-size estimates and the factor \(32^{-u_i}=n^{-10+o(1)}\) make the
reverse recurrence decreasing. Division by the exponentially large complete
signed first moment makes the full corner negligible.

## 13. Lemma 8.1: lines 2053--2079, proof lines 2081--2146 — **GREEN-REWRITE**

The global falling-factorial comparison follows from concavity of
\(f(x)=\log(n)_x\) and the exact mass identity (8.11). The local unequal-size
factor follows from (8.13), and the phase relation gives the stated \(\eta_n\).

The square-root-free cross-multiplied theorem from the later formal stack is
safer: it handles positivity before cancellation and makes endpoint cases
total. Use that theorem as the primary statement.

## 14. Lemma 8.2: lines 2151--2169, proof lines 2171--2228 — **GREEN-REWRITE**

Cauchy's inequality and the two nonnegative domain enlargements are valid. The
multinomial theorem gives the one-sided row and column sums, and Lemma 7.1
closes the diagonal sum.

The termwise square-free AM--GM route is shorter and yields

\[
 \sum_L W(L)
 \le (1+C\eta_n)^{k_{\mathrm{co}}}\sum_rD(r)
\]

directly, without \((\sum\sqrt D)^2\).

## 15. Lemma 8.3: lines 2233--2243, proof lines 2245--2490 — **RED**

This is the only independent submission blocker.

### Proof introduction: lines 2245--2263

The near/middle charging narrative announces an objectwise completion picture.
That picture is not literal: a partial physical matching generally has many
full completions and may leave stubs that participate in residual cells.

### Step I: lines 2264--2284

Writing \(j=m-e\) is unique, and the high/middle inequalities are correct.
Replacing selected multiplicities by full endpoint multiplicities gives a
valid block-level reference table. What is missing is a weight-preserving
finite theorem connecting the actual physical family to that reference table
and deficit data.

### Step II: lines 2285--2369

- Equation (8.21) is the correct aggregate local ratio after summing the local
  partial-stub-matching fibre.
- Equation (8.22) is the correct single global denominator ratio.
- The one-cell near series (8.25) is valid.
- **Blocking transition:** equations (8.25a)--(8.26) and the sentence
  “distinguishing and then forgetting identical typed cells is exactly the
  multinomial expansion” do not prove the required global physical-fibre
  decomposition.

### Steps III--IV: lines 2370--2469

The joint threshold estimate is applied before constraints are relaxed, so the
upper-bound direction is preserved. However, finite sums use the nonliteral
range \(3a/4+O(1)\), and Step IV pays residual local and cycle factors despite
the section contract saying those factors are deferred.

### Assembly: lines 2470--2490

The assembly would be valid if the preceding exact fibre inequality were
proved. It does not repair that missing theorem.

### Required replacement

Prove an exact decomposition by block support, admissible deficits, and local
partial physical matching fibres. Then use

\[
 \frac{w(P,m-h)}{w_{\mathrm{full}}(P)}
 \le \prod_e n^{h_e}R_{m_e,d_e}(h_e)
\]

with the global denominator charged once. The checked sharper arithmetic gives

\[
 h\left\lfloor\frac{3m-1}{4}\right\rfloor
 \le hm-\frac{h(h+1)}2
\]

for \(2h<m\). Cellwise geometric summation yields a direct all-deficit exponent
\(O(\sqrt n(\log n)^{3/2})\); the optional head--tail split yields
\(O((\log n)^4)\).

## 16. Exact decomposition (9.2): lines 2492--2548 — **GREEN-REWRITE**

The normalized second moment should be an exact sum of bare high-skeleton
weights times literal residual attachment factors. The newer formal stack
states this as an attained canonical attachment sum and factors a pointwise
attachment estimate from that exact mixture. Synchronize the notation with the
aggregate Section VIII repair.

## 17. Lemma 9.1: lines 2550--2565, proof lines 2567--2827 — **SUPERSEDED**

The old proof has coherent local-expansion, activity, cycle-family, walk-kernel,
and small-residual stages. No explicit counterexample to the stated upper bound
was found. It should nevertheless be replaced.

Deleting the exposed matching is injective on the even residual edge family,
so

\[
 \sum_{F\text{ even}}\prod_{e\in F\setminus M}q_e
 \le\prod_{e\notin M}(1+q_e).
\]

The local increment is pointwise dominated by the same \(q\). The checked
q-only two-regime theorem therefore gives the literal attained attachment
bound without cycle decompositions, walk kernels, \(	au\), or \(h\tau\).

## 18. Proposition 9.2: lines 2832--2842, proof lines 2844--2865 — **RED**

Equation (9.2) plus a uniform attachment bound and a bare-skeleton sum gives the
displayed upper bound immediately. The normalized second moment is at least
one by variance, so its logarithm is nonnegative. The proof is logically
correct conditional on Lemma 8.3.

## 19. Lemma 10.1: lines 2903--2912, proof lines 2914--2963 — **GREEN**

A union bound makes every \(n^{1/4}\)-set dense in the complement; averaging
propagates the density bound to all larger sets. The maximum-degree
neighborhood recurrence constructs an independent set of logarithmic size,
and repeated removal gives (10.3) simultaneously for every subset.

## 20. Lemma 10.2: lines 2968--2989, proof lines 2991--3046 — **GREEN**

The induced cocolorable-capacity variable is one-Lipschitz under vertex-block
exposure. The seed event is exactly \(S_k=n\). One-sided McDiarmid bounds give
the expectation deficit and random leftover size, while Lemma 10.1 colors the
leftover. The failure sequence is independent of all deterministic parameters.

## 21. Final application: lines 3047--3111

- **Lines 3047--3077:** the amplification scales are correct conditional on
  Proposition 9.2.
- **Lines 3078--3111:** the union-bound intersection and subtraction are
  correct, but the conclusion remains conditional on Proposition 9.2. The
  final fixed halving is conservative.

After closure, use the phase-resolved /8 theorem and the stronger fixed
coefficient.

## 22. Exact defects and mandatory edits

| Source | Defect | Severity | Required edit |
|---|---|---|---|
| Abstract line 80 | Unconditional “We prove” | RED status language | Use audit-safe abstract until Proposition 9.2 is green. |
| Theorem 1 lines 119--130 | Unconditional theorem | RED dependency | Keep conditional in working draft. |
| Equation (7.2) | `2^\ell_\bullet` | TYPO | Replace by `2^{\ell_\bullet}`. |
| Central-rate proof | Decimal endpoint checks | GREEN-REWRITE | Replace by exact rational certificate. |
| Lemma 8.3 Step I | Objectwise completion language | RED | Replace by aggregate physical-fibre reindexing. |
| Lemma 8.3 Step III | `3a/4+O(1)` inside finite sums | RED/EDITORIAL | Use exact integer bounds. |
| Lemma 8.3 contract vs Step IV | Residual factors said to be deferred but paid in Section VIII | GREEN-REWRITE | Remove middle split under the all-deficit route. |
| Lemma 9.1 | Cycle/walk machinery | SUPERSEDED | Replace by matching restriction and q-only sum. |
| Equations (5.12), (5.20), (11.2) | Unnecessary fixed halvings | IMPROVABLE | State phase-resolved /8 theorem after closure. |
| Multiple `o(1)` events | No named deterministic sequence | GREEN-REWRITE | Bind to explicit phase-uniform sequences in final statements. |

## 23. Version 2 dependency graph

```text
Lemma 2.1
  -> Lemma 3.1
     -> Section 4 chromatic lower location
     -> Lemma 5.1 and four-size root displacement
        -> exact midpoint profile and signed first moment

Lemma 6.1 + Lemma 6.2
  -> Lemma 7.1 partial diagonals
  -> endpoint reference normalization and transport
  -> exact attained-demand support/deficit/partial-fibre reindexing   [OPEN]
  -> cellwise all-deficit product
  -> bare-skeleton estimate                                           [OPEN]

matching restriction + q-only two-regime attachment
  -> normalized second moment                                         [OPEN only through bare skeleton]
  -> Paley--Zygmund seed

Lemma 10.1 + Lemma 10.2
  -> high-probability cochromatic upper location

chromatic lower location + cochromatic upper location
  -> phase-resolved gap theorem.
```

## 24. Acceptance gates before changing theorem status

The canonical abstract and Theorem 1 may be promoted from RED only after all of
the following are green on one integrated commit:

1. the actual midpoint profile is proved to satisfy the four-endpoint cover;
2. attained canonical high demands inject into support/deficit data;
3. the partial physical matching fibre has the exact aggregate cardinality;
4. `profileHighSkeletonWeight` is identified pointwise with that aggregate
   weight;
5. the one global falling-factorial comparison is applied after the aggregate
   fibre sum;
6. the complete positive-deficit fibre is summed cellwise;
7. full-reference supports are identified with the exact endpoint table weights
   \(W(L)\);
8. endpoint transport and Lemma 7.1 produce the bare-skeleton estimate;
9. the q-only literal attachment theorem is composed with that estimate;
10. Proposition 9.2 is built warning-fatally with no placeholders or
    project-defined axioms;
11. Lemmas 10.1--10.2 and the final event intersection are replayed against the
    resulting deterministic error sequence;
12. the TeX, bibliography, source typo, theorem coefficient, Lean status, and
    reproducibility language are synchronized.

## 25. Final audit verdict

The candidate proof is not a diffuse collection of unchecked claims. The
mathematics before Section VIII and after Proposition 9.2 is substantially
coherent. The exact signed overlap identity and amplification argument are
particularly clean.

The current canonical TeX is nevertheless not ready to assert Theorem 1. The
one load-bearing finite reindexing in Lemma 8.3 is not proved by its present
“complete, distinguish, and forget” prose. The repair is sharply specified and
supported by several green finite components, but the final pointwise aggregate
weight identification and global bare-skeleton assembly must still be checked.

Accordingly:

- **Theorem 1:** RED, conditional on one explicit chain;
- **Lemmas 2.1, 6.1, 6.2, 10.1, 10.2:** GREEN;
- **Lemmas 3.1, 5.1, 7.1, 8.1, 8.2:** GREEN-REWRITE;
- **Lemma 8.3:** RED and the unique independent blocker;
- **Lemma 9.1:** SUPERSEDED by a shorter checked route;
- **Proposition 9.2:** RED only through Lemma 8.3.
