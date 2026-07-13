# Independent audit of `RESIDUAL_ATTACHMENT.md`

> **Historical-scope notice (2026-07-13).** This document preserves the
> internal 2026-07-12 verdict on the component bytes then under review. It is
> not a review of the later repaired or synchronized bytes. The authoritative
> proof is `../proofs/COMPLETE_PROOF_SELF_CONTAINED.md`; see
> `ADVERSARIAL_LEAP_AUDIT_2026-07-13.md` for the correction to a one-sided
> residual bound and its regression check, and
> `PROOF_COMPONENT_SYNCHRONIZATION_AUDIT_2026-07-13.md` for the synchronized
> component mapping. The original audit body and verdict below are retained
> unchanged.

**Audit status:** pass, with three minor repairs/clarifications stated below.

**Scope.**  This audit rederived the canonical exposure law, the threshold
expansion, the cycle-space summation, both residual-mass regimes, and the
equitable high-cell assembly.  It did not use the narrative claims in the
note as premises.  The conclusion audited here is conditional on the
equitable hypotheses `n=ks`, `s=(2+o(1)) log_2 n`, and `Z_k>=1`.

The repairs are not changes to the asymptotic result:

1. The sentence after (1.10) should say that the exposed stub pairs are
   unique for a **stub matching**, not for an overlap matrix.  An overlap
   matrix has many stub-matching realizations.  Formula (1.10) is nevertheless
   exact because `pi` already sums all stub choices and every such realization
   is counted once.
2. In Section 2, set both `lambda_{a_i b_i}=0` and `q_{a_i b_i}=0`, or define
   `Lambda` as a sum over cells outside `M`.  As written, `lambda` is introduced
   only off `M` but (2.9) writes an unrestricted sum.
3. The prose before (2.16) must not be read as discarding the endpoint of a
   residual walk and then freely choosing another one of the `h` matching
   edges.  The correct argument retains the endpoint-to-matching-edge partial
   permutation.  Its row-sum norm is one, which proves (2.16) with no `h^r`
   factor.  A complete operator proof is given below.

There is one harmless endpoint case omitted from the citation used for
(2.8): Corollary 3.1 of `SIGNED_PROFILE_OVERLAP.md` is stated for `U->infinity`
and `R>=3`, whereas Theorem 2.1 here only states an upper bound on `U`.  If
`R<3`, the `lambda` sum is empty; for bounded `R>=3`, its finitely many terms
give the same estimate directly.  Thus this does not restrict Theorem 2.1.

## Verdict by proof obligation

| Item | Verdict | Audit conclusion |
|---|---:|---|
| High cells form a matching | PASS | `2(floor(U/2)+1)>U`, so two high cells cannot share a row or column. |
| Incidence factor (1.6) | PASS | Every cell contributes `(s_a)_j(t_b)_j/j!`; the common denominator is `(n)_J`. |
| Canonical decomposition (1.10) | PASS with wording repair | Exact on stub matchings; algebraically recovers the overlap-matrix probability exactly. |
| Local signed factor (1.8) | PASS | All high-cell `g(j_i)` factors are outside, while their topological contribution remains inside `beta(M union H_res)`. |
| Threshold expansion (2.12) | PASS with notation repair | Triple-or-larger cells selected by an even subgraph are alternatives, not products; the joint `(N)_m` denominator is retained before the global `e` bound. |
| Endpoint estimates (2.8)--(2.10) | PASS | The degree sums give `Lambda=O(U^4/N)` and maximum weighted degree `tau=O(U^3/N)`. |
| Cycle-decomposition overcount (2.13) | PASS | A fixed edge-disjoint decomposition is injective; the product over all cycles is a nonnegative overcount. |
| Cycles disjoint from `M`, (2.14) | PASS | Weighted walk row sums are at most `tau`; bipartiteness starts the sum at length four. |
| Mixed cycles, (2.16) | PASS with proof clarification | The matching is a partial permutation of norm one.  Hence later high edges cost no independent `h` factor. |
| No illicit `2^h` | PASS | A matching alone has no nonempty even subgraph.  A high edge is charged only through a residual path in a cycle. |
| Large-residual scale (2.3) | PASS | `h tau=O(nU^2/N)=O((ln n)^8)` is the largest displayed term at the cutoff. |
| Small-residual bound (2.4) | PASS | `beta<=|E(H_res)|<=N/2` and the local exponent is at most `(U-1)N/2`. |
| Near-exact equitable sum (3.3)--(3.8) | PASS | The exact diagonal identity and every deficiency factorial were checked. |
| Middle strip (3.11)--(3.13) | PASS | Its one-cell exponent is at most `-(3/8-o(1))(log_2 n)^2`, uniformly at the stated mass cutoff. |
| Equitable Corollary 3.1 | PASS | Conditional factorials factor at the near/middle exposure, and the uniform attachment supremum may be multiplied only after summing the exact canonical skeletons. |

## 1. Canonical decomposition and factorial audit

Fix an overlap matrix `r`.  Let

\[
 M=\{ab:r_{ab}>R\},\qquad j_{ab}=r_{ab},\qquad
 J=\sum_{ab\in M}j_{ab}.
\]

Because `M` is a matching, subtracting `j_{ab}` from the degree at each of
its two endpoints gives the residual degrees `d_a,d'_b` without ambiguity.
For one high cell, the number of ways to choose its row stubs, choose its
column stubs, and biject them is

\[
 \binom{s_a}{j}\binom{t_b}{j}j!
 =\frac{(s_a)_j(t_b)_j}{j!}.
\]

A prescribed collection of `J` paired stubs occurs with probability
`1/(n)_J`.  This proves (1.6), including its single factor `j!` in the
denominator.  There is neither a missing `j!` nor an extra one.

For a fixed exposed stub realization, the residual overlap matrix `r'` has
configuration-model probability

\[
 p_{\rm res}(r')=
 \frac{\prod_a d_a!\prod_b d'_b!}
      {N!\prod_{ab}r'_{ab}!}.
\]

Multiplying by (1.6), using `(n)_J N!=n!`, and cancelling the endpoint
factorials gives

\[
 \pi(M,\mathbf j)p_{\rm res}(r')
 =\frac{\prod_a s_a!\prod_b t_b!}
        {n!\prod_{ab}r_{ab}!}
 =p_{\mathbf s,\mathbf t}(r).
\]

Here `r'_{a_i b_i}=0` and `r'_{ab}=r_{ab}` elsewhere.  The no-backtracking
and cap event is exactly what forces this canonical residual matrix.  Thus
every stub matching, and after summation every overlap matrix, contributes
once to (1.10).

As a finite check, exact rational enumeration gave total probability one
and zero error in the displayed factorization for the profiles

\[
 (3,3)\leftrightarrow(3,3),\quad
 (3,2,1)\leftrightarrow(2,2,2),\quad
 (4,3,2)\leftrightarrow(3,3,3),
\]

covering respectively 4, 15, and 45 contingency matrices.  This check is
diagnostic only; the cancellation above is the proof.

Finally,

\[
 A_\zeta(r)=
 \left(\prod_{ab\in M}g(j_{ab})\right)
 \left(\prod_{ab\notin M}g(r'_{ab})\right)
 2^{\beta(M\cup H_{\rm res})}
\]

is exact.  Factoring out `g(j)` does not factor out the topology of a high
edge; that topology correctly remains in the cycle-rank term.

## 2. Independent derivation of (2.12)

For a capped residual cell `e` outside `M`,

\[
 g(r_e)=1+\sum_{x=3}^{R}\Delta_x\mathbf1_{\{r_e\ge x\}},
\]

whereas, when `e` belongs to a fixed even subgraph,

\[
 \mathbf1_{\{r_e\ge2\}}g(r_e)
 =\mathbf1_{\{r_e\ge2\}}
  +\sum_{x=3}^{R}\Delta_x\mathbf1_{\{r_e\ge x\}}.
\]

The second display is a sum of alternatives.  In particular, a triple cell
in the even subgraph is assigned either demand two or demand three; it is not
assigned both.  This is exactly the source of

\[
 q_e=\frac{\theta_e^2}{2}+\lambda_e,
 \qquad
 \lambda_e=\sum_{x=3}^{R}\Delta_x\frac{\theta_e^x}{x!}.
\]

For a monomial demanding multiplicities `x_e` in distinct residual cells,
put `m=sum_e x_e`.  Direct stub selection gives

\[
 \Pr(r_e\ge x_e\ \forall e)
 \le
 \frac{\prod_a(d_a)_{D_a}\prod_b(d'_b)_{D'_b}}
      {(N)_m\prod_e x_e!}.
\]

For feasible `m`, `(N)_m>=(N/e)^m`; infeasible demands have probability
zero and may be discarded.  Therefore the last display is at most

\[
 \prod_e\frac{(e d_a d'_b/N)^{x_e}}{x_e!}.
\]

This is one joint bound with the global residual denominator, not a product
of marginal cell probabilities.

Now use

\[
 2^{\beta(M\cup H_{\rm res})}
 =\sum_{F\subseteq M\cup H_{\rm res}}
   \mathbf1_{\{F\ \mathrm{even}\}}.
\]

For fixed `F`, cells of `F\setminus M` contribute `q_e`; cells outside `F`
contribute at most `1+lambda_e`; and cells of `M` have already been exposed
and carry weight one in this cycle-space sum.  Consequently

\[
 \mathcal A(M,\mathbf j)
 \le
 \prod_{e\notin M}(1+\lambda_e)
 \sum_{F\ \mathrm{even}}\prod_{e\in F\setminus M}q_e
 \le
 e^\Lambda
 \sum_{F\ \mathrm{even}}\prod_{e\in F\setminus M}q_e.
\]

This is (2.12).  The cap and exactness indicators may be dropped only after
the capped identities have been expanded; doing so then enlarges every
nonnegative monomial.  To remove the small notational ambiguity, use
`lambda_e=q_e=0` on `M` and `Lambda=sum_{e notin M}lambda_e`.

The endpoint argument gives `lambda_e<=C theta_e^3` and
`q_e<=C theta_e^2`.  Hence

\[
 \Lambda\le \frac{C}{N^3}
   \left(\sum_a d_a^3\right)
   \left(\sum_b(d'_b)^3\right)
 \le C\frac{U^4}{N},
\]

because each cubic degree sum is at most `U^2N`.  Similarly,

\[
 \sum_bq_{ab}
 \le C\frac{d_a^2}{N^2}\sum_b(d'_b)^2
 \le C\frac{U^3}{N},
\]

and the same holds on the column side.  Thus (2.9)--(2.10) contain the
correct powers of `U` and `N`.

## 3. Cycle overcount and the mixed-cycle bound

Every finite even simple graph has an edge-disjoint simple-cycle
decomposition.  Choose one deterministic decomposition `D(F)` for each
even `F`.  The map `F -> D(F)` is injective because the union of the cycles
is `F`, and for an edge-disjoint decomposition

\[
 \prod_{C\in D(F)}\prod_{e\in C\setminus M}q_e
 =\prod_{e\in F\setminus M}q_e.
\]

The product over all simple cycles includes every `D(F)` and many additional
intersecting collections, all with nonnegative weight.  Therefore (2.13) is
a valid overcount for arbitrary nonnegative `q_e`; it does not require
`q_e<=1`.

For a fully explicit proof of (2.16), put the row and column vertices in one
bipartite state space and define the nonnegative residual-edge kernel

\[
 T_{uv}=q_{uv}.
\]

Both its row and column weighted degrees are at most `tau`, so
`||T||_infinity<=tau`.  The kernel of a nonempty residual walk is bounded by

\[
 S=\sum_{\ell\ge1}T^\ell,
 \qquad ||S||_\infty\le
 a:=\frac{\tau}{1-\tau}.
\]

Let `P` be the partial permutation that traverses the deterministic matching
`M`; set it to zero at vertices not incident with `M`.  Because `M` is a
matching,

\[
 ||P||_\infty\le1.
\]

Mark and orient one matching edge of a mixed simple cycle.  There are at
most `2h` choices.  If the cycle contains `r` matching edges, cutting all of
them leaves `r` nonempty residual paths.  Starting just after the marked
edge, their relaxed total weight is bounded by the row sum of `(SP)^r`,
hence by `a^r`; discarding simplicity and the final return constraint only
increases this sum.  Therefore

\[
 \sum_{C:C\cap M\ne\varnothing}
    \prod_{e\in C\setminus M}q_e
 \le2h\sum_{r\ge1}a^r
 \le C h\tau
\]

when `tau<1/3`.

This calculation explains exactly why no `h^r` occurs.  The endpoint of one
residual path determines the next matching edge uniquely through `P`; its
choice is already included in the weighted walk sum.  Replacing that
determined edge by a fresh arbitrary choice among `h` edges would be an
illicit overcount and is not used.  Nor is there a `2^h`: a matching is a
forest and has only the empty even subgraph until residual paths create
cycles.

For cycles disjoint from `M`, the same kernel estimate, with a marked row
start and even length at least four, yields

\[
 \sum_{C:C\cap M=\varnothing}\prod_{e\in C}q_e
 \le n\sum_{j\ge2}\tau^{2j}
 =\frac{n\tau^4}{1-\tau^2},
\]

which verifies (2.14).

## 4. Residual-mass regimes

In the large-residual regime,

\[
 \tau=O(U^3/N),\qquad h<2n/U.
\]

At `N>=n/(ln n)^6` and `U=O(ln n)`,

\[
 \frac{U^4}{N}=o(1),\qquad
 n\tau^4=o(1),\qquad
 h\tau=O\!\left(\frac{nU^2}{N}\right)=O((\ln n)^8).
\]

Thus (2.3) has the asserted scale.

In the small-residual regime, add the residual support edges to the matching
forest `M`.  Each added edge raises cycle rank by at most one, so

\[
 \beta(M\cup H_{\rm res})\le |E(H_{\rm res})|.
\]

Every support edge uses at least two of the `N` residual matched pairs;
hence `|E(H_res)|<=N/2`.  Also

\[
 \sum_e\log_2g(r'_e)
 \le\sum_e\binom{r'_e}{2}
 \le\frac{U-1}{2}\sum_er'_e
 =\frac{U-1}{2}N.
\]

The total base-two exponent is therefore at most `UN/2`.  This proves (2.4)
without charging any of the `h` high edges separately.  At
`N<n/(ln n)^6`, it is `O(n/(ln n)^5)` in natural logarithms.

## 5. Equitable assembly

### 5.1 Exact and near-exact cells

For `h` exact common blocks, direct configuration counting gives

\[
 A_h=\binom{k}{h}^2h!
 \frac{(s!)^h(n-hs)!}{n!}
 2^{h(\binom{s}{2}-1)}.
\]

Putting `ell=k-h` and substituting the definition of `Z_ell` gives, with no
asymptotic approximation,

\[
 A_h=\binom{k}{\ell}\frac{Z_\ell}{Z_k}.
\]

The factorials on the two sides both reduce to
`(k!)^2/(h!(ell!)^2)`, which checks the ordered-slot/unordered-partition
normalization.  The partial-diagonal estimate used in (3.5) follows from

\[
 \ln Z_\ell-\frac{\ell}{k}\ln Z_k
 =\ell(s-1)\ln(\ell/k)
   +\frac{1-\ell/k}{2}\ln s+O(1),
\]

uniformly for `1<=ell<=k`, together with `s>(2+epsilon)ln k` and `Z_k>=1`.
Thus the imported diagonal suppression does not conceal an additional
profile assumption.

For a deficiency `d`, the local factorial ratio relative to a full block is

\[
 \frac{(s)_{s-d}^2}{(s-d)!s!}
 =\frac{\binom{s}{d}}{d!},
\]

the reward ratio is

\[
 \frac{g(s-d)}{g(s)}
 =2^{-ds+d(d+1)/2},
\]

and the global denominator ratio is

\[
 \frac{(n)_{hs}}{(n)_{hs-\sum d_i}}
 \le n^{\sum d_i}.
\]

These are exactly the three factors in (3.6).  Moreover,

\[
 \frac{\eta_{d+1}}{\eta_d}
 =n\frac{s-d}{(d+1)^2}2^{-s+d+1}.
\]

For `d<s/4` and `s=(2+o(1))log_2 n`, this is uniformly `o(1)`, so the sum is
dominated by

\[
 \eta_1=2ns\,2^{-s}=n^{-1+o(1)}.
\]

In the refined window it is `O(s^3/n)`.  Consequently (3.7)--(3.8) have the
correct exponent `k epsilon_n=n^{o(1)}`, or `O(s^2)` in the refined window.

### 5.2 Middle strip and conditional denominators

After the near-exact exposure, let `J_0` be its exposed mass and
`M_0=n-J_0`.  A subsequent middle exposure of mass `J_1` has the exact
conditional denominator

\[
 (M_0)_{J_1},\qquad
 (n)_{J_0+J_1}=(n)_{J_0}(M_0)_{J_1}.
\]

Thus the near-exact comparison and the middle-strip factorial bound really
do concatenate; there is no replacement of a joint denominator by
independent denominators.

When `M_0>=n/(ln n)^6`, the prescribed-cell bound with maximum residual
degree `s` gives the one-cell middle activity used in (3.11).  If
`L=log_2 n` and `j=xL`, then uniformly for
`s/2<j<=3s/4`, `x in [1+o(1),3/2+o(1)]`,

\[
 \log_2\!\left[
 k^2g(j)\frac{(es^2/M_0)^j}{j!}
 \right]
 \le\left(\frac{x^2}{2}-x\right)L^2+O(L\log L)
 \le-\left(\frac38-o(1)\right)L^2.
\]

Summing the `O(log n)` possible multiplicities proves (3.13).  Dropping the
matching constraint and exponentiating is safe because all activities are
nonnegative; it is an overcount, not an independence assertion.

If `M_0<n/(ln n)^6`, the pointwise small-residual argument may be applied
immediately to everything remaining after the near-exact skeleton.  It does
not require the middle cells first to be exposed and costs only
`O(sM_0)=O(n/(ln n)^5)`.

Finally, before applying a product of estimates, write the canonical sum as

\[
 \sum_{\text{complete high skeletons}}
   (\text{bare incidence})\,\mathcal A(M,\mathbf j).
\]

Theorem 2.1 bounds the second factor uniformly.  The first factor is summed
by the near/middle estimates just checked.  Taking the attachment supremum
only after this exact separation is legitimate and gives

\[
 \ln R_\zeta
 \le O\!\left(\frac{n}{(\ln n)^5}
              +(\ln n)^8+n^{o(1)}\right)
 =o\!\left(\frac{n}{(\ln n)^4}\right).
\]

This verifies Corollary 3.1.  The audit found no missing factorial, hidden
`2^h`, marginal-independence substitution, or unaccounted residual-cycle
family in the equitable argument.
