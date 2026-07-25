# A simpler route through Sections 8 and 9

This note records three compatible simplifications of the current candidate
proof.  They are designed to reduce both the manuscript's conceptual load and
the number of distinct objects that must be carried through Lean.

The first two concern the bare high-skeleton sum in Section 8.  The third
concerns the residual attachment in Section 9.

## 1. Replace the Cauchy step by termwise AM--GM

Retain the notation of manuscript (8.8).  For a feasible endpoint table
\(\mathbf L\), let

\[
 A_{\mathbf L}=\frac{\prod_i r_i!}{\prod_{ij}\ell_{ij}!},
 \qquad
 C_{\mathbf L}=\frac{\prod_j c_j!}{\prod_{ij}\ell_{ij}!},
 \qquad
 Q^{\mathbf L}=\prod_{ij}Q_{ij}^{\ell_{ij}}.
\]

Equation (8.8) is

\[
 W(\mathbf L)
 \le
 \sqrt{D(r)A_{\mathbf L}\,D(c)C_{\mathbf L}}\,Q^{\mathbf L}.
\]

Apply \(2\sqrt{xy}\le x+y\) term by term:

\[
 W(\mathbf L)
 \le
 \frac12\bigl(D(r)A_{\mathbf L}+D(c)C_{\mathbf L}\bigr)
 Q^{\mathbf L}.                                      \tag{S8.1}
\]

For the first term, group by the row margin and drop only the column-margin
constraint.  The multinomial theorem gives

\[
 \sum_{\mathbf L:\,\operatorname{row}(\mathbf L)=r}
 A_{\mathbf L}Q^{\mathbf L}
 \le
 \prod_i\left(\sum_jQ_{ij}\right)^{r_i}.
\]

The symmetric statement holds for the second term.  Since every row and column
sum of \(Q\) is at most \(1+C\eta_n\), and every margin has total mass at most
\(k_{\mathrm{co}}\), summing (S8.1) yields directly

\[
 \boxed{
 \sum_{\mathbf L}W(\mathbf L)
 \le
 (1+C\eta_n)^{k_{\mathrm{co}}}
 \sum_rD(r).}                                         \tag{S8.2}
\]

Lemma 7.1 then gives

\[
 \sum_{\mathbf L}W(\mathbf L)
 \le \exp\{O(\eta_nk_{\mathrm{co}})\}
 =\exp\{O(\sqrt{n\ln n})\}.
\]

This removes:

- Cauchy's inequality on the table family;
- the quantity \((\sum_r\sqrt{D(r)})^2\);
- the polynomial margin-count factor \(O(k_{\mathrm{co}}^4)\);
- one layer of square-root bookkeeping in the formalization.

The endpoint comparison itself may remain in the square-free form proved in
PR #36.  The formal target corresponding to (S8.1) is the elementary
linearization

\[
 x^2\le yz\quad\Longrightarrow\quad 2x\le y+z
\]

for the finite nonnegative quantities appearing after the positive factorial
factors have been exposed.

## 2. Charge every high multiplicity directly to an endpoint cell

The current manuscript treats deficits \(e<m/4\) cellwise and sends the
remaining high multiplicities to a residual middle-strip argument.  The latter
is unnecessary if one accepts a slightly weaker, but still ample, error term.

Let a high cell join sizes \(m\) and \(m+d\), where \(0\le d\le3\), and write
its multiplicity as \(j=m-e\).  Since

\[
 j>R_0=\lfloor a/2\rfloor\ge\lfloor m/2\rfloor,
\]

we always have

\[
 2e<m.                                                   \tag{S8.3}
\]

The exact local ratio from (8.21), including the global denominator charge
from (8.22), is

\[
 A_{m,d}(e)
 :=n^eR_{m,d}(e)
 =n^e\frac{\binom me}{(d+1)\cdots(d+e)}
   2^{-em+e(e+1)/2}.                                    \tag{S8.4}
\]

Put

\[
 b_m=\left\lfloor\frac{3m-1}{4}\right\rfloor.
\]

From (S8.3),

\[
 em-\frac{e(e+1)}2\ge e b_m.                            \tag{S8.5}
\]

Moreover \(\binom me\le m^e\), while
\((d+1)\cdots(d+e)\ge1\).  Therefore

\[
 \boxed{
 A_{m,d}(e)
 \le
 \left(\frac{nm}{2^{b_m}}\right)^e.}                   \tag{S8.6}
\]

All four endpoint sizes lie in \([a-3,a]\).  Define

\[
 b_*:=\left\lfloor\frac{3a-10}{4}\right\rfloor,
 \qquad
 \rho_n:=\frac{na}{2^{b_*}}.
\]

Then (S8.6) is at most \(\rho_n^e\) uniformly in the cell type.  Using
\(2^a=\Theta(n^2/(\ln n)^2)\),

\[
 \rho_n=O\!\left(\frac{(\ln n)^{5/2}}{\sqrt n}\right)=o(1).
                                                               \tag{S8.7}
\]

Hence, for every endpoint cell,

\[
 \sum_{\substack{e\ge1\\m-e>R_0}}A_{m,d}(e)
 \le\sum_{e\ge1}\rho_n^e
 \le 2\rho_n                                           \tag{S8.8}
\]

for all sufficiently large \(n\).  Distinguish the cells of an endpoint table,
assign either \(e=0\) or any allowed high deficit, and then forget the labels.
As in the current near-cell argument, this is exactly the multinomial
expansion and introduces no extra multiplicity.  Since an endpoint skeleton
contains at most \(k_{\mathrm{co}}\) cells,

\[
 \prod_c\left(1+\sum_eA_{m_c,d_c}(e)\right)
 \le
 \exp\{O(k_{\mathrm{co}}\rho_n)\}
 =
 \exp\{O(\sqrt n(\ln n)^{3/2})\}.                       \tag{S8.9}
\]

The exponent in (S8.9) is still

\[
 o\!\left(\frac{n}{(\ln n)^4}\right).
\]

Combining (S8.2) and (S8.9) gives the complete bare high-skeleton estimate
without a residual middle strip:

\[
 \boxed{
 \sum_{(\mathcal M,j)}w_{\mathrm{hi}}(\mathcal M,j)
 \le
 \exp\{O(\sqrt n(\ln n)^{3/2})\}
 =
 \exp\!\left\{o\!\left(\frac{n}{(\ln n)^4}\right)\right\}.}
                                                               \tag{S8.10}
\]

This removes from Section 8:

- the near/middle classification at \(e=m/4\);
- the event \(\mathcal N(S)\);
- the truncated residual factor \(E_{\mathrm{mid}}(S)\);
- the joint middle-threshold quantity \(\Xi_4\);
- the large/small residual split inside Section 8;
- equations (8.26a)--(8.29b).

It also restores a clean conceptual boundary: Section 8 is purely a sum over
exposed high cells; Section 9 alone treats the residual configuration model.

## 3. Absorb the Section 9 local product into the q mass

After the threshold expansion, the current direct route gives

\[
 \mathcal A(\mathcal M,j)
 \le
 \exp(\Lambda_{\mathrm{loc}})
 \sum_{F\text{ even}}
   \prod_{e\in F\setminus\mathcal M}q_e,
 \qquad
 \Lambda_{\mathrm{loc}}=\sum_e\lambda_e.                \tag{S9.1}
\]

By definition,

\[
 q_e=\frac{\theta_e^2}{2}+\lambda_e,
 \qquad
 \lambda_e\le q_e.                                      \tag{S9.2}
\]

Restriction to the residual edges is injective on the even family because a
nonempty subset of a matching cannot be even.  Thus

\[
 \sum_{F\text{ even}}\prod_{e\in F\setminus\mathcal M}q_e
 \le
 \prod_{e\notin\mathcal M}(1+q_e)
 \le
 \exp\left(\sum_eq_e\right).                             \tag{S9.3}
\]

Equations (S9.1)--(S9.3) give

\[
 \mathcal A(\mathcal M,j)
 \le
 \exp\left(2\sum_eq_e\right).                            \tag{S9.4}
\]

The pointwise quadratic estimate and the degree caps imply

\[
 \sum_eq_e
 \le C\sum_{a,b}\theta_{ab}^2
 =\frac{C}{m_0^2}
   \left(\sum_ad_a^2\right)
   \left(\sum_b(d'_b)^2\right)
 \le C u_{\max}^2.                                       \tag{S9.5}
\]

Consequently the large-residual branch is simply

\[
 \boxed{
 \mathcal A(\mathcal M,j)
 \le \exp(Cu_{\max}^2)
 =\exp(O((\ln n)^2)).}                                   \tag{S9.6}
\]

This removes the separate cubic lambda estimate
\(C u_{\max}^4/m_0\).  Together with the matching-restriction injection, it
also removes all cycle and walk estimates from the proof of Lemma 9.1.
PR #37 kernel-checks the finite q-only version of this argument.

## Proposed manuscript organization

A clearer final organization is:

1. **Endpoint transportation:** state the square-free finite core and its
   geometric-mean corollary.
2. **Endpoint summation:** apply termwise AM--GM and one-sided multinomial
   expansions.
3. **All high deficits:** use the single geometric bound (S8.6)--(S8.9).
4. **Residual attachment:** perform the threshold expansion, matching
   restriction, and q-only total-mass estimate.
5. **Two residual regimes:** retain only the simple deterministic small-residual
   estimate and the q-only large-residual estimate.

Under this organization, Section 8 no longer contains a conditional residual
expectation, while Section 9 no longer contains a cycle decomposition or a
separate cubic-moment branch.

## Remaining checks before canonical integration

The main new point requiring independent mathematical review is the extension
of the endpoint charging from \(e<m/4\) to the full high range via (S8.3)--(S8.8).
The accompanying exact checker verifies the finite exponent inequality and the
local ratio domination over a large exhaustive integer range; its phase scans
are diagnostics, not a proof of the asymptotic use of (8.15).
