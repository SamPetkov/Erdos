# Concise replacement draft for Sections 8 and 9

This draft is intended to replace the present high-skeleton and residual
attachment arguments after the supporting PRs have been reviewed.  It retains
the exact canonical exposure, but removes the table-family Cauchy step, the
near/middle split, the Section 8 residual model, the cycle decomposition, and
the separate cubic lambda estimate.

Throughout, \(N=\ln n\),

\[
U=\alpha-2,
\qquad
R_0=\lfloor U/2\rfloor,
\]

and the four block sizes are \(u_i=U-i\), \(0\le i\le3\).

## 8. Canonical high cells

For an overlap table \(r=(r_{ab})\), let

\[
\mathcal M(r)=\{(a,b):r_{ab}>R_0\}.
\]

Because every row and column sum is at most \(U\), the support
\(\mathcal M(r)\) is a bipartite matching.  Write its cell multiplicities as
\(j_{ab}=r_{ab}\), and let \(J=\sum_{(a,b)\in\mathcal M}j_{ab}\).
Exposing the corresponding stub pairs has incidence

\[
\pi(\mathcal M,j)
=
\frac{\prod_{(a,b)\in\mathcal M}(s_a)_{j_{ab}}(t_b)_{j_{ab}}}
     {(n)_J\prod_{(a,b)\in\mathcal M}j_{ab}!}.
\tag{8.1}
\]

Conditional on those pairs, the remaining matching is uniform with the
induced residual degrees, is zero on \(\mathcal M\), and is capped by \(R_0\).
Multiplying (8.1) by the exact residual configuration-table law recovers the
original overlap probability.  Thus the decomposition is exact and every
overlap table occurs once.

### 8.1 Endpoint transportation

First suppose every high cell is a full-containment cell.  Aggregate the
physical block pairs by their endpoint types into a table
\(L=(\ell_{ij})_{0\le i,j\le3}\).  Let \(r_i=\sum_j\ell_{ij}\),
\(c_j=\sum_i\ell_{ij}\), and let \(W(L)\) be the exact endpoint incidence and
local signed reward.  Let \(D(r)\) be the common-subprofile weight from
Section 7.  Define

\[
A_L=\frac{\prod_i r_i!}{\prod_{ij}\ell_{ij}!},
\qquad
C_L=\frac{\prod_j c_j!}{\prod_{ij}\ell_{ij}!}.
\]

The endpoint transport calculation gives

\[
W(L)
\le
\sqrt{D(r)A_L\,D(c)C_L}\,Q^L,
\qquad
Q^L:=\prod_{ij}Q_{ij}^{\ell_{ij}},
\tag{8.2}
\]

where \(Q_{ii}=1\) and, for \(d=|i-j|\in\{1,2,3\}\),

\[
Q_{ij}\le\frac{\eta_n^d}{d!},
\qquad
\eta_n=O\!\left(\frac{N^{3/2}}{\sqrt n}\right).
\tag{8.3}
\]

The square-free finite algebra behind (8.2) is the statement formalized in
PR #36.  For summation, apply \(2\sqrt{xy}\le x+y\) termwise:

\[
W(L)
\le
\frac12\bigl(D(r)A_L+D(c)C_L\bigr)Q^L.
\tag{8.4}
\]

Fixing \(r\) and dropping only the column-margin constraint gives the exact
multinomial bound

\[
\sum_{L:\operatorname{row}(L)=r}A_LQ^L
\le
\prod_i\left(\sum_jQ_{ij}\right)^{r_i}.
\tag{8.5}
\]

The symmetric estimate holds after fixing \(c\).  Every row and column sum of
\(Q\) is at most \(1+C\eta_n\), while the total number of selected blocks is at
most \(k_{\mathrm{co}}\).  Hence

\[
\sum_LW(L)
\le
(1+C\eta_n)^{k_{\mathrm{co}}}\sum_rD(r).
\tag{8.6}
\]

Lemma 7.1 gives \(\sum_rD(r)=1+o(1)\), and therefore

\[
\sum_LW(L)
\le
\exp\{O(\eta_nk_{\mathrm{co}})\}
=
\exp\{O(\sqrt{nN})\}.
\tag{8.7}
\]

This proves the endpoint sum without Cauchy's inequality, without
\((\sum_r\sqrt{D(r)})^2\), and without a polynomial count of margin vectors.

### 8.2 All high multiplicities in one geometric expansion

Let a high cell join endpoint sizes \(m\) and \(m+d\), \(0\le d\le3\), and
write its multiplicity as \(j=m-e\).  Since \(j>R_0\ge\lfloor m/2\rfloor\),

\[
2e<m.
\tag{8.8}
\]

Filling the cell from \(m-e\) to its endpoint multiplicity \(m\) changes the
local factor by the exact ratio

\[
R_{m,d}(e)
=
\frac{\binom me}{(d+1)\cdots(d+e)}
2^{-em+e(e+1)/2}.
\tag{8.9}
\]

For several cells, if \(E=\sum e\), the single global denominator ratio is at
most \(n^E\).  Thus each cell may be charged the factor
\(A_{m,d}(e)=n^eR_{m,d}(e)\).

The formalization-first integer estimate is

\[
e\left\lfloor\frac{2m}{3}\right\rfloor
\le
em-\frac{e(e+1)}2
\qquad(2e<m).
\tag{8.10}
\]

It is kernel-checked in PR #38.  Since
\(inom me\le m^e\) and the denominator in (8.9) is at least one,

\[
A_{m,d}(e)
\le
\left(
\frac{nm}{2^{\lfloor2m/3\rfloor}}
\right)^e.
\tag{8.11}
\]

All endpoint sizes satisfy \(U-3\le m\le U\).  Put

\[
b_*:=\left\lfloor\frac{2(U-3)}3\right\rfloor,
\qquad
\rho_n:=\frac{nU}{2^{b_*}}.
\]

The phase relation \(2^U=\Theta(n^2/N^2)\) gives

\[
\rho_n
=O\!\left(\frac{N^{7/3}}{n^{1/3}}\right)
=o(1).
\tag{8.12}
\]

Consequently the sum of all nonzero high deficits of one endpoint cell is at
most \(2\rho_n\) eventually.  A high skeleton is a matching, so filling all its
cells to their endpoints produces a feasible endpoint skeleton.  Conversely,
an endpoint skeleton together with one allowed deficit per cell reconstructs
the original high skeleton uniquely.  Distinguishing identical typed cells and
then forgetting the labels is exactly the multinomial expansion; no further
multiplicity is introduced.

There are at most \(k_{\mathrm{co}}\) endpoint cells.  Therefore all high
multiplicities cost at most

\[
(1+2\rho_n)^{k_{\mathrm{co}}}
\le
\exp\{O(k_{\mathrm{co}}\rho_n)\}
=
\exp\{O(n^{2/3}N^{4/3})\}.
\tag{8.13}
\]

Combining (8.7) and (8.13),

\[
\boxed{
\sum_{(\mathcal M,j)}w_{\mathrm{hi}}(\mathcal M,j)
\le
\exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.}
\tag{8.14}
\]

No near/middle partition or residual configuration-model argument is needed in
Section 8.

## 9. Residual attachment

Fix an attained high skeleton \((\mathcal M,j)\), and let \(m_0=n-J\) be its
residual stub mass.  Its exact residual attachment is

\[
\mathcal A(\mathcal M,j)
=
\mathbb E_{\mathrm{res}}\!\left[
\prod_e g(r'_e)
2^{\beta(\mathcal M\cup H_{\mathrm{res}})}
\mathbf1_{\mathcal E(\mathcal M,j)}
\right].
\tag{9.1}
\]

For cells outside \(\mathcal M\), set

\[
\theta_{ab}=\frac{e\,d_ad'_b}{m_0},
\qquad
q_{ab}
=
\frac{\theta_{ab}^2}{2}
+
\sum_{x=3}^{R_0}\bigl(g(x)-g(x-1)\bigr)
\frac{\theta_{ab}^x}{x!},
\tag{9.2}
\]

and put \(q_{ab}=0\) on \(\mathcal M\).

The threshold expansion for a fixed even edge set \(F\) is bounded by a product
of selected \(q\)-weights and unselected local increments.  Every local
increment is at most \(q_{ab}\).  Hence

\[
\mathcal A(\mathcal M,j)
\le
\left(\prod_{e\notin\mathcal M}(1+q_e)\right)
\sum_{F\text{ even}}
\prod_{e\in F\setminus\mathcal M}q_e.
\tag{9.3}
\]

The restriction map \(F\mapsto F\setminus\mathcal M\) is injective on even edge
sets: two completions with the same residual restriction differ by an even
subset of a matching, and the only such subset is empty.  Therefore

\[
\sum_{F\text{ even}}
\prod_{e\in F\setminus\mathcal M}q_e
\le
\prod_{e\notin\mathcal M}(1+q_e).
\tag{9.4}
\]

Combining (9.3)--(9.4),

\[
\boxed{
\mathcal A(\mathcal M,j)
\le
\exp\left(2\sum_eq_e\right).}
\tag{9.5}
\]

### 9.1 Intrinsic quadratic regime

If

\[
2^U\le m_0^3,
\tag{9.6}
\]

then the finite endpoint estimate gives \(q_{ab}\le C\theta_{ab}^2\).  The
square mass factorizes exactly:

\[
\sum_{a,b}\theta_{ab}^2
=
\frac{e^2}{m_0^2}
\left(\sum_ad_a^2\right)
\left(\sum_b(d'_b)^2\right)
\le e^2U^2.
\tag{9.7}
\]

Thus

\[
\boxed{
\mathcal A(\mathcal M,j)
\le\exp(CU^2)
=\exp(O(N^2)).}
\tag{9.8}
\]

PR #37 kernel-checks the finite q-only bound and its attained-profile
specialization.

### 9.2 Complementary small-power regime

If (9.6) fails, the exact arithmetic dichotomy in PR #37 gives

\[
m_0<2^{\lceil U/3\rceil}.
\tag{9.9}
\]

The deterministic residual estimate gives

\[
\mathcal A(\mathcal M,j)
\le2^{Um_0/2}
\le
\exp\{O(U2^{U/3})\}.
\tag{9.10}
\]

Since \(U=(2+o(1))\log_2n\), the exponent in (9.10) is
\(n^{2/3+o(1)}\), and hence is \(o(n/N^4)\).  Together with (9.8), there is a
deterministic sequence \(\varepsilon_n\to0\) such that uniformly over all
attained high skeletons,

\[
\boxed{
\mathcal A(\mathcal M,j)
\le
\exp\!\left\{\varepsilon_n\frac n{N^4}\right\}.}
\tag{9.11}
\]

This regime split is intrinsic to the finite q estimate and avoids introducing
the auxiliary threshold \(n/N^6\).

## 9.3 Completion of the normalized second moment

The exact canonical decomposition gives

\[
\frac{\mathbb E(Z_k^{\mathrm{sgn}})^2}
     {(\mathbb EZ_k^{\mathrm{sgn}})^2}
=
\sum_{(\mathcal M,j)}
 w_{\mathrm{hi}}(\mathcal M,j)
 \mathcal A(\mathcal M,j).
\tag{9.12}
\]

Equations (8.14) and (9.11) imply

\[
\frac{\mathbb E(Z_k^{\mathrm{sgn}})^2}
     {(\mathbb EZ_k^{\mathrm{sgn}})^2}
\le
\exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.
\tag{9.13}
\]

This is the normalized second-moment estimate required by the seed and
amplification argument.

## Formalization map

The concise route is supported by the following focused developments:

- PR #34: matching-restriction injectivity and subset-product bound;
- PR #35: literal attachment, attained-profile transport, and
  `exp(O((log n)^2))` specialization;
- PR #36: square-free endpoint transportation core;
- PR #37: q-only absorption and intrinsic finite residual dichotomy;
- PR #38: one all-high-deficit parametrization, its injectivity, and the
  two-thirds exponent budget.

The remaining formal work is concentrated in two bridges:

1. derive the linear endpoint inequality (8.4) from the square-free theorem and
   sum it through the exact physical/type-table quotient;
2. transport the local geometric bound (8.11) through the physical endpoint
   decoration map and prove its phase-uniform asymptotic form.

Those two obligations are considerably narrower than the current separate
endpoint, near, middle, residual-cycle, and cubic-moment proof branches.
