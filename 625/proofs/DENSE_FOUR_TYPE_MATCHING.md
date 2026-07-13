# Dense endpoint matchings for the four-size profile

**Purpose.**  This note closes the finite-dimensional bare-matching
obligation isolated in `RESIDUAL_ATTACHMENT.md`, (4.11)--(4.13), and the
four-type high-matching lemma in `ALPHA_MINUS_TWO_ROUTE.md`, (8.4).  It uses
the exact common-part theorem proved independently in
`FOUR_SIZE_PARTIAL_RATES.md`; in particular, it does **not** assume the
published tame-profile estimate that is unavailable for the midpoint
four-type witness.  The only complete-moment input is the already proved
signed margin `exp(Omega(n/ln n))`.

**Synchronization status (2026-07-13).**  The endpoint-decoration and
middle-strip assembly below has been synchronized with the global
high-skeleton argument in `COMPLETE_PROOF_SELF_CONTAINED.md`,
(8.25a)--(8.29b).  The added bookkeeping makes explicit how the fixed-table
and conditional estimates enter the one global sum; it changes neither the
theorem nor any asymptotic constant.

The key point is not that an off-diagonal transportation matrix is smaller
than a diagonal one pointwise.  That assertion is false at finite positive
mass.  Instead, an exact geometric-mean comparison reduces the whole
transportation sum to diagonal common-part weights.  A Cauchy--multinomial
summation then absorbs all directed type cycles and all imbalance paths at
cost only

\[
 \exp\{O(\sqrt{n\ln n})\}
 =\exp\{o(n/(\ln n)^4)\}.                                  \tag{0.1}
\]

Throughout, `ln` is the natural logarithm and `q=ln 2`.

## 1. Hypotheses and notation

Let

\[
 u_i=a-i,\qquad 0\le i\le3,\qquad
 \sum_{i=0}^3u_i k_i=n,\qquad k_i=\Theta(n/\ln n),          \tag{1.1}
\]

where `a=alpha-2`.  Uniformly through the independence-number cycle,

\[
 qa=2\ln n-2\ln\ln n+O(1),\qquad
 2^a=\Theta\!\left(\frac{n^2}{(\ln n)^2}\right).           \tag{1.2}
\]

Put `K=sum_i k_i`.  Then

\[
 K=(1+O(1/a))\frac n a=\Theta(n/\ln n).                    \tag{1.3}
\]

Write

\[
 \mu_u=\binom nu2^{-\binom u2},\qquad
 g(u)=2^{\binom u2-1},\qquad b_i=u_i!g(u_i).               \tag{1.4}
\]

We use the quantitative top-size hypothesis from (4.6) of
`RESIDUAL_ATTACHMENT.md`,

\[
 \mu_a\ge c n^2(\ln n)^{2/q-5/2}.                         \tag{1.5}
\]

The integer vector is the tangent-rounded four-type entropy optimizer from
Sections 3--4 of `ALPHA_MINUS_TWO_ROUTE.md`.  Thus, in the original deficit
coordinates `2,3,4,5`, its mean and masses satisfy

\[
 \frac2q-o(1)\le T\le1+\frac2q+o(1),\qquad
 \min_i\frac{k_i}{K}\ge\frac1{92}                       \tag{1.6}
\]

for all large `n`; see (1.4)--(1.6) of
`FOUR_SIZE_PARTIAL_RATES.md`.  For `r=(r_i)`, `0<=r_i<=k_i`, put

\[
 m_r=\sum_i u_i r_i,
\]

and let `Y_r^sgn` be the signed partial-partition first moment in (5.31) of
`SIGNED_PROFILE_OVERLAP.md`.  The complete signed first moment satisfies,
for some fixed `c_Z>0`,

\[
 Z_k^{\rm sgn}(n)\ge e^{c_ZK}.                            \tag{1.7}
\]

This is (6.7) of `ALPHA_MINUS_TWO_ROUTE.md`.  It is also the sole
first-moment hypothesis of the direct common-part proof in
`FOUR_SIZE_PARTIAL_RATES.md`; no lower bound on the ordinary first moment is
used.

For a nonnegative integer matrix `L=(ell_ij)`, set

\[
 r_i=\sum_j\ell_{ij},\quad c_j=\sum_i\ell_{ij},\quad
 x_{ij}=\min(u_i,u_j),\quad J=\sum_{i,j}x_{ij}\ell_{ij}.   \tag{1.8}
\]

We require `r_i,c_i<=k_i`.  Its exact endpoint weight is

\[
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{i,j}\ell_{ij}!}
 \frac1{(n)_J}
 \prod_{i,j}B_{ij}^{\ell_{ij}},                           \tag{1.9}
\]

where

\[
 B_{ij}=\frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}
          g(x_{ij}).                                      \tag{1.10}
\]

This is exactly (4.11) in `RESIDUAL_ATTACHMENT.md`.

## 2. Exact geometric-mean comparison

For a margin vector `r`, define the exact diagonal common-part weight

\[
 D(r)=
 \frac{\prod_i(k_i)_{r_i}^{2}}{\prod_i r_i!}
 \frac{\prod_i b_i^{r_i}}{(n)_{m_r}}
 =\frac{\prod_i\binom{k_i}{r_i}^{2}}{Y_r^{\rm sgn}}.       \tag{2.1}
\]

Thus `D(r)` is (4.12), with `D(0)=1`.

### Lemma 2.1 (transportation comparison)

For every feasible `L` with margins `r,c`, let

\[
 d_{ij}=|i-j|.
\]

Then

\[
 W(L)\le \sqrt{D(r)D(c)}
 \frac{\sqrt{\prod_i r_i!c_i!}}{\prod_{i,j}\ell_{ij}!}
 \prod_{i,j}Q_{ij}^{\ell_{ij}},                            \tag{2.2}
\]

where `Q_ii=1` and, if the two sizes are `t=s+d`, `1<=d<=3`,

\[
 \boxed{
 Q_{ij}=(n+1)^{d/2}\frac{\sqrt{(t)_d}}{d!}
       2^{-\{ds+\binom d2\}/2}.}                          \tag{2.3}
\]

Uniformly in the phase,

\[
 Q_{ij}\le\frac{\eta_n^{d_{ij}}}{d_{ij}!},\qquad
 \eta_n:=2^{3/2}\sqrt{\frac{(n+1)a}{2^a}}
 =O\!\left(\frac{(\ln n)^{3/2}}{\sqrt n}\right)=o(1).    \tag{2.4}
\]

#### Proof

Let `f(x)=ln (n)_x`, using the Gamma interpolation on `[0,n]`.  Since

\[
 f''(x)=-\psi'(n-x+1)<0,                                  \tag{2.5}
\]

`f` is concave.  Moreover,

\[
 \frac{m_r+m_c}{2}
 =J+\frac12\sum_{i,j}|u_i-u_j|\ell_{ij}
 =J+\frac12\sum_{i,j}d_{ij}\ell_{ij}.                    \tag{2.6}
\]

Both `m_r` and `m_c` are at most `n`.  Concavity, followed by the elementary
upper bound `f(x+h)-f(x)<=h ln(n+1)`, gives

\[
 \frac{\sqrt{(n)_{m_r}(n)_{m_c}}}{(n)_J}
 \le (n+1)^{\frac12\sum_{i,j}d_{ij}\ell_{ij}}.           \tag{2.7}
\]

This is the required direction of the finite-population comparison.  In
particular, the global `(n)_J` has not been replaced by a product of cell
denominators.

It remains to calculate the local ratio.  If `t=s+d`, then

\[
 B_{ij}=b_s\binom td,\qquad
 \frac{b_t}{b_s}=(t)_d2^{ds+\binom d2}.                   \tag{2.8}
\]

Consequently

\[
 \frac{B_{ij}}{\sqrt{b_i b_j}}
 =\frac{\sqrt{(t)_d}}{d!}
 2^{-\{ds+\binom d2\}/2}.                                \tag{2.9}
\]

Dividing (1.9) by the geometric mean of the two expressions (2.1), and
using (2.7)--(2.9), proves (2.2)--(2.3).  Finally `t<=a`, `s>=a-3`, and
(1.2) give (2.4). \(\square\)

The exponent in (2.6) is half the total variation of the type sizes along
the directed edges.  If `r=c`, the off-diagonal flow decomposes into
directed cycles and the upward and downward size changes cancel on each
cycle.  If `r!=c`, the same decomposition has imbalance paths.  Lemma 2.1
handles both at once: the two endpoint diagonals `D(r)` and `D(c)` close the
paths, while (2.7) charges the moved residual vertices.  Thus no equality
of the exposed margins is being assumed.

## 3. Summing every `4 by 4` transportation matrix

### Lemma 3.1 (Cauchy--multinomial summation)

For fixed feasible margins `r,c`,

\[
 \sum_{L:\,\operatorname{row}L=r,\ \operatorname{col}L=c}W(L)
 \le \sqrt{D(r)D(c)}\exp\{C\eta_nK\}.                    \tag{3.1}
\]

Consequently

\[
 \boxed{
 \sum_LW(L)
 \le \exp\{C\eta_nK+O(\ln n)\}\sum_rD(r).}              \tag{3.2}
\]

In particular, `C eta_n K=O(sqrt(n ln n))`.

#### Proof

Put

\[
 A_L=\frac{\prod_i r_i!}{\prod_{i,j}\ell_{ij}!},\qquad
 C_L=\frac{\prod_j c_j!}{\prod_{i,j}\ell_{ij}!}.          \tag{3.3}
\]

The factorial in (2.2) is `sqrt(A_L C_L)`.  Cauchy's inequality gives

\[
 \sum_L\sqrt{A_LC_L}\,Q^L
 \le\left(\sum_LA_LQ^L\right)^{1/2}
      \left(\sum_LC_LQ^L\right)^{1/2}.                   \tag{3.4}
\]

Dropping the column constraints in the first sum and the row constraints in
the second sum leaves exact multinomial expansions:

\[
 \sum_LA_LQ^L\le\prod_i\left(\sum_jQ_{ij}\right)^{r_i},
 \qquad
 \sum_LC_LQ^L\le\prod_j\left(\sum_iQ_{ij}\right)^{c_j}. \tag{3.5}
\]

By (2.4), every row and column sum of `Q` is at most `1+C eta_n`.
Also `sum r_i=sum c_i<=K`.  Equations (2.2), (3.4), and (3.5) prove
(3.1).

There are at most `prod_i(k_i+1)=exp(O(ln n))` margin vectors.  Hence

\[
 \left(\sum_r\sqrt{D(r)}\right)^2
 \le \left\{\prod_i(k_i+1)\right\}\sum_rD(r).             \tag{3.6}
\]

Summing (3.1) and using (3.6) proves (3.2).  Finally (1.3)--(1.4) give

\[
 \eta_nK
 =O\!\left(\frac{n}{\ln n}
               \frac{(\ln n)^{3/2}}{\sqrt n}\right)
 =O(\sqrt{n\ln n}).                                      \tag{3.7}
\]

\(\square\)

This proof is a joint transportation-table sum.  It neither multiplies
one-cell expectations nor asserts that a diagonal table is the pointwise
maximizer.  Sparse off-diagonal cycles can increase an individual
fixed-mass diagonal term by a polynomial factor; (3.4)--(3.5) is precisely
what absorbs all such choices.

## 4. The exact diagonal sum

### Lemma 4.1 (all diagonal endpoints)

Under (1.5)--(1.7),

\[
 \boxed{\sum_{0\le r_i\le k_i}D(r)=1+o(1).}               \tag{4.1}
\]

#### 4.1 Vanishing exposed mass

Set

\[
 \lambda_i=\frac{k_i^2}{2\mu_{u_i}},\qquad
 \Lambda=\sum_i\lambda_i.                                \tag{4.2}
\]

The exact ratio

\[
 \frac{\mu_{v-1}}{\mu_v}
 =\frac{v}{n-v+1}2^{v-1}                                 \tag{4.3}
\]

and (1.2), (1.5) imply

\[
 \Lambda=O\!\left((\ln n)^{-\gamma}\right)=o(1),
 \qquad \gamma=\frac2q-\frac12>0.                        \tag{4.4}
\]

Indeed, the `i=0` term is at most
`O((ln n)^(-2/q+1/2))`, and each decrease of the size multiplies `mu` by
`Theta(n/ln n)`.

For `E=sum_i r_i` and `m=m_r`, (2.1) and

\[
 \frac{b_i}{n^{u_i}}
 =\frac{(n)_{u_i}}{n^{u_i}}\frac1{2\mu_{u_i}}
 \le\frac1{2\mu_{u_i}}                                  \tag{4.5}
\]

give the exact-global-denominator bound

\[
 D(r)\le\frac{n^m}{(n)_m}\prod_i\frac{\lambda_i^{r_i}}{r_i!}. \tag{4.6}
\]

Since `m<=aE`, summing at fixed `E` yields, whenever `aE<n`,

\[
 \sum_{\sum r_i=E}D(r)
 \le\frac{n^{aE}}{(n)_{aE}}\frac{\Lambda^E}{E!}.          \tag{4.7}
\]

Choose a sufficiently small fixed `delta>0`.  If
`E<=n/a^3`, then

\[
 \ln\frac{n^{aE}}{(n)_{aE}}
 \le\frac{(aE)^2}{n-aE}\le\frac{2E}{a},                 \tag{4.8}
\]

so the sum of (4.7) over this range is `o(1)` by (4.4).  If
`n/a^3<E<=delta n/(a-3)`, put `t=aE/n`.  Uniformly in this range,

\[
 \ln\frac{n^{aE}}{(n)_{aE}}
 \le\frac{t^2n}{1-t},\qquad
 \ln E!\ge E(\ln E-1),\qquad
 \frac{\ln E-1}{a}\ge\frac q3.                          \tag{4.9}
\]

After reducing `delta` if necessary, (4.7)--(4.9) are at most
`exp(-c t n)`.  Summation over `E` is still `o(1)`.  Since
`m_r<=delta n` implies `E<=delta n/(a-3)`, we have proved

\[
 \sum_{0<m_r\le\delta n}D(r)=o(1).                        \tag{4.10}
\]

#### 4.2 Fixed positive mass

No published ordinary-profile estimate is used here.  The direct
finite-dimensional calculation in `FOUR_SIZE_PARTIAL_RATES.md`, Lemmas
3.1--3.2, associates to each residual subprofile the rate

\[
 \Phi_T(\mathbf z)
 =R\ln R+\frac q2(I_r-TR),                                \tag{4.11}
\]

and proves analytically, using only the endpoints `2` and `5` of the
support, that `Phi_T(z)<0` away from the empty and full corners.  More
precisely, its (3.5) and (3.16) give, uniformly for every fixed
`delta>0`,

\[
 \delta n\le m_r\le(1-\delta)n
 \quad\Longrightarrow\quad
 D(r)\le e^{-c_\delta n}.                                \tag{4.11a}
\]

That proof assumes only (1.6)--(1.7), retains the exact partial-diagonal
factorials, and explicitly covers nongreedy subprofiles; it is not a
floating-point prefix check.  There are only `O(n^4)` vectors, so their sum
is `e^{-Omega(n)}`.

#### 4.3 Near-full exposed mass

Let `h=k-r`,

\[
 H=\sum_i h_i,\qquad M=\sum_i u_i h_i=n-m_r.              \tag{4.12}
\]

The complement identity (5.33) of `SIGNED_PROFILE_OVERLAP.md` is

\[
 D(k-h)=\left\{\prod_i\binom{k_i}{h_i}\right\}
          \frac{Z_h^{\rm sgn}(M)}{Z_k^{\rm sgn}(n)}.       \tag{4.13}
\]

We next make the required residual-first-moment bound uniform in the phase.
Put `s=a-3`.  The number of unordered partitions of `M` vertices into the
`H` prescribed blocks is at most `H^M`.  Therefore

\[
 \ln Z_h^{\rm sgn}(M)
 \le qH+M\ln H-q\sum_i h_i\binom{u_i}{2}
 \le qH+M\left\{\ln H-\frac q2(s-1)\right\}.             \tag{4.14}
\]

If `0<M<=delta n`, then `H<=M/s` and (1.2) gives, with an absolute
phase-uniform constant `C`,

\[
 \ln H-\frac q2(s-1)
 \le \ln n+\ln\delta-\ln s-\frac q2(s-1)
 \le\ln\delta+C.                                         \tag{4.15}
\]

Choose `delta` so small that the right side of (4.15), plus `q/s`, is
negative.  Equations (4.14)--(4.15) then prove

\[
 Z_h^{\rm sgn}(M)\le1                                    \tag{4.16}
\]

for every nonzero residual profile of mass at most `delta n`, uniformly
through the cycle.  The zero profile also has signed first moment one.

By (1.3), `M<=delta n` implies `H<=2delta K` for large `n`.  Combining
(1.7), (4.13), (4.16), and Vandermonde's identity gives

\[
 \begin{aligned}
 \sum_{M\le\delta n}D(k-h)
 &\le e^{-c_ZK}\sum_{H\le2\delta K}\binom KH\\
 &\le\exp\{-c_ZK+K h_{\rm bin}(2\delta)\},               \tag{4.17}
 \end{aligned}
\]

where `h_bin(x)=-x ln x-(1-x)ln(1-x)`.  Reducing `delta` once more so that
`h_bin(2delta)<c_Z/2`, (4.17) is `exp(-Omega(K))`.  Together with
(4.10)--(4.11) and `D(0)=1`, this proves (4.1). \(\square\)

## 5. Near-containment decorations

The preceding sum uses the full-containment endpoint
`x=min(u_i,u_j)`.  It remains to verify that the near-containment decoration
does not undo the bound.

Let the smaller size be `m`, the larger be `m+d`, `0<=d<=3`, and lower the
cell multiplicity from `m` to `m-e`.  The exact local ratio is

\[
 R_{m,d}(e)=
 \frac{\binom me}{\prod_{h=1}^{e}(d+h)}
 2^{-em+e(e+1)/2}.                                        \tag{5.1}
\]

For a collection of decorated cells with total deficit `Q=sum e`, the
ratio of the global denominators is exactly

\[
 \frac{(n)_{J_0}}{(n)_{J_0-Q}}
 =(n-J_0+Q)_Q\le n^Q,                                    \tag{5.2}
\]

where `J_0` is the mass of the corresponding full-containment skeleton.
Thus the global denominator is retained before the safe bound in (5.2) is
taken.

Define the single uniform near-containment error

\[
 \epsilon_n^{\rm near}:=
 \max_{\substack{a-3\le m\le a\\0\le d\le3}}
 \sum_{1\le e<m/4} n^eR_{m,d}(e)
 =O\!\left(\frac{(\ln n)^3}{n}\right).                   \tag{5.3}
\]

For completeness, the ratio of consecutive summands in (5.3) is

\[
 \frac{n(m-e)2^{-m+e+1}}{(e+1)(d+e+1)}.                  \tag{5.4}
\]

Its possible maximum on the indicated interval is at an endpoint after
the elementary one-turn ratio check: the quotient of the expression in
(5.4) at `e+1` by its value at `e` is

\[
 2\frac{m-e-1}{m-e}\frac{e+1}{e+2}
   \frac{d+e+1}{d+e+2},                                  \tag{5.4a}
\]

which is increasing for `0<=e<=m/4` (direct cross-multiplication, using
`d<=3`).  Hence the consecutive-term ratios first decrease and then
increase, so their maximum is at an endpoint.  At `e=0` it is
`O((ln n)^3/n)`, while at `e=floor(m/4)` it is
`n^{-1/2+o(1)}`.  Hence the summands decrease geometrically from the first
one, which proves (5.3).  This is the four-size specialization of (3.6)--
(3.7) in `RESIDUAL_ATTACHMENT.md`.

Fix a full-containment endpoint matrix `L`, temporarily distinguish its
endpoint cells, and let `S(L)` be the set of near-containment skeletons
obtained by assigning to each cell either deficit zero or a deficit
`1<=e<m/4`.  If `w(S)` is the resulting bare incidence and local weight,
then (5.2)--(5.4a) give the nonnegative product bound

\[
 \begin{aligned}
 \sum_{S\in\mathcal S(L)}w(S)
 &\le W(L)\prod_{c\in L}
  \left(1+\sum_{1\le e<m_c/4}n^eR_{m_c,d_c}(e)\right)\\
 &\le W(L)(1+\epsilon_n^{\rm near})^{\sum_{i,j}\ell_{ij}}
 \le W(L)\exp\{O((\ln n)^2)\}.                           \tag{5.5}
 \end{aligned}
\]

Define the decoration factor by
`D_near(L):=(sum_{S in S(L)}w(S))/W(L)` when `W(L)>0`, and set it to zero
when `W(L)=0`.  Thus (5.5) is exactly
`D_near(L)<=exp{O((ln n)^2)}` uniformly in `L`.

Distinguishing and then forgetting identical cells of one type is exactly
the multinomial expansion
`ell_ij!/prod_e ell_{ij,e}!`.  Thus (5.5) has no extra ordering,
`K!`, or other hidden multiplicity.  This is the four-type form of
(8.25a)--(8.26) in the canonical proof.

It remains to insert the middle strip, outside the near-containment range,
without treating its cells independently.  Expose a particular near
skeleton `S`, let `M_0` be its residual stub mass, and denote the residual
row and column degrees by `d_u,d'_v`.  Put

\[
 \theta_{uv}=\frac{e d_ud'_v}{M_0}\le\frac{ea^2}{M_0},
\]

with `theta_uv=0` on an already exposed cell.  Let `E_mid(S)` be the
conditional middle-extension factor.  If `M_0>=n/(ln n)^6`, expand first
over distinct residual cells and all their threshold demands.  Applying
the joint configuration-model factorial bound before dropping either the
matching constraint or the common denominator gives

\[
 \begin{aligned}
 E_{\rm mid}(S)
 &\le\sum_{\substack{D\ \mathrm{distinct\ residual\ cells}\\
              a/2<j_{uv}\le3a/4+O(1)}}
       \prod_{uv\in D}g(j_{uv})
       \Pr\{r_{uv}\ge j_{uv}\ \forall uv\in D\}\\
 &\le\prod_{u,v}\left(1+
       \sum_{a/2<j\le3a/4+O(1)}
       g(j)\frac{\theta_{uv}^j}{j!}\right)
 \le\exp\{\Xi_4(M_0)\},                                  \tag{5.6}
 \end{aligned}
\]

where, uniformly in the already exposed skeleton,

\[
 \Xi_4(M_0)\le K^2\sum_{a/2<j\le3a/4+O(1)}
    g(j)\frac{(e a^2/M_0)^j}{j!}.                         \tag{5.6a}
\]

Thus the product in (5.6) is the result of one joint threshold expansion,
not a product of marginal probabilities.  Writing `L=log_2 n`, uniformly
for `j/L in [1+o(1),3/2+o(1)]`,

\[
 \log_2\!\left[K^2g(j)\frac{(e a^2/M_0)^j}{j!}\right]
 \le2L+\frac{j^2}{2}-j\log_2M_0+O(j\log_2a)
 \le-cL^2.                                                \tag{5.7}
\]

The `O(1)` variation among the four slot sizes is absorbed by the last
term.  Consequently
`Xi_4^*:=sup_{S:M_0>=n/(ln n)^6}Xi_4(M_0)=2^{-Omega(L^2)}`.  This is the
conditional large-residual branch of (8.26a)--(8.28) in the canonical
proof.

If instead `M_0<n/(ln n)^6`, leave the entire residual matching unexposed.
Every residual cell then has `r_e<=a`.  Since the exposed near skeleton is
a matching, pointwise

\[
 \beta(S\cup H_{\rm res})\le|E(H_{\rm res})|\le M_0/2,
 \qquad
 \sum_e\binom{r_e}{2}\le\frac{a-1}{2}M_0.                \tag{5.8}
\]

All remaining local and topological factors are therefore at most
`exp(CaM_0)`.  In this branch take `E_mid(S)` to be the resulting terminal
conditional factor, which only enlarges the middle-extension sum.  Because
all terms are nonnegative, summing the residual matching probability first
gives the explicit alternative

\[
 E_{\rm mid}(S)
 \le\mathbb E_{\rm res}\!\left[
       \prod_eg(r_e)2^{\beta(S\cup H_{\rm res})}\right]
 \le\exp(CaM_0)
 \le\exp\{Cn/(\ln n)^5\}.                                \tag{5.8a}
\]

Finally let `H_high` range over all complete canonical high skeletons and
let `w_bare(H)` denote the bare incidence and high-cell local weight at this
stage of the exposure.  Combining the endpoint-table sum, the
decoration product (5.5), the conditional expansion (5.6), and the two
residual-mass branches gives the single global inequality

\[
 \begin{aligned}
 \sum_{H\in\mathcal H_{\rm high}}w_{\rm bare}(H)
 &\le e^{O((\ln n)^2)}\left(\sum_LW(L)\right)
       \max\left\{e^{\Xi_4^*},e^{Cn/(\ln n)^5}\right\}\\
 &\le\exp\left\{O(\sqrt{n\ln n})+O((\ln n)^2)
                 +O\!\left(\frac n{(\ln n)^5}\right)\right\}\\
 &=\exp\{o(n/(\ln n)^4)\}.                               \tag{5.9}
 \end{aligned}
\]

Here the first line is a sum over endpoint tables and all their
decorations, followed by a uniform conditional estimate; no fixed-skeleton
bound is silently promoted term by term.  Equation (5.9) is the notation of
this note for the globalization in canonical (8.29a)--(8.29b).

## 6. Dense-endpoint theorem

### Theorem 6.1

Under (1.1)--(1.7), the complete endpoint transportation sum, including all
near-containment decorations, satisfies

\[
 \boxed{
 \sum_L W(L)D_{\rm near}(L)
 \le\exp\{O(\sqrt{n\ln n})+O((\ln n)^2)\}
 =\exp\{o(n/(\ln n)^4)\}.}                                \tag{6.1}
\]

The same bound holds after restricting to `J(L)=Theta(n)`, so (6.1) proves
(4.13) of `RESIDUAL_ATTACHMENT.md`.  Combined with the fixed-mass estimate,
the vanishing- and near-full endpoint bounds above prove the sufficient
condition (5.36) of `SIGNED_PROFILE_OVERLAP.md` for this four-size profile.

#### Proof

Equations (3.2) and (4.1) give

\[
 \sum_LW(L)
 \le\exp\{O(\sqrt{n\ln n})+O(\ln n)\}.                   \tag{6.2}
\]

Equation (5.5) adds only `O((ln n)^2)` to its logarithm.  Finally

\[
 \frac{\sqrt{n\ln n}}{n/(\ln n)^4}
 =\frac{(\ln n)^{9/2}}{\sqrt n}\longrightarrow0.          \tag{6.3}
\]

This proves (6.1).  Equations (5.6)--(5.9) then condition on each summed
endpoint/near skeleton and promote the middle-strip estimates to the full
global high-skeleton sum. \(\square\)

Together with the residual-attachment theorem, the entire signed overlap
sum contributed by these bare high skeletons and all their residual
double/triple/cycle attachments is still `exp(o(n/(ln n)^4))`.

### Corollary 6.2 (the missing high-matching lemma)

For the tangent-rounded midpoint profile constructed in
`ALPHA_MINUS_TWO_ROUTE.md`, the canonical bare high-matching sum in its
(8.4) satisfies

\[
 \boxed{\ln S_{\rm high}=o(n/(\ln n)^4).}                 \tag{6.4}
\]

Indeed, `RESIDUAL_ATTACHMENT.md`, Section 4.1, reduces that assertion
exactly to (4.13).  The endpoint-decoration product (5.5), the joint
conditional threshold expansion (5.6), and both residual-mass alternatives
(5.7)--(5.8a) are assembled globally in (5.9).  Theorem 6.1 supplies the
endpoint transportation estimate used there, so all endpoint
containments, near-containment decorations, and middle-strip cells are in
the same summed bound.

## 7. Adversarial checks and scope

1. **Concavity direction.**  The numerator in (2.7) is bounded *above* by
   the falling factorial at the average mass because `ln(n)_x` is concave.
   Reversing this inequality would invalidate the proof.
2. **No cellwise finite-population replacement.**  The exact `(n)_J` is
   present in (1.9), (2.2), and (5.2).  It is bounded only once, after all
   cells have been combined.
3. **Unequal margins.**  No condition `r=c` is imposed.  The geometric mean
   `sqrt(D(r)D(c))` is what closes imbalance paths; circulation cycles are
   the special case `r=c`.
4. **No pointwise diagonal maximality.**  Such a statement is false: a
   sparse off-diagonal two-cycle can increase a fixed-mass diagonal term by
   a polynomial factor.  The joint Cauchy--multinomial bound is subbudget
   even after summing all of them.
5. **Near-full uniformity.**  The constant in (4.15) is uniform in the
   fractional phase because the entire phase dependence in (1.2) is
   `O(1)`.  The small cutoff `delta` is chosen after that constant and after
   `c_Z` are fixed.
6. **First-moment dependence.**  The profile in (1.6)--(1.7) is the
   tangent-rounded midpoint profile already constructed in
   `ALPHA_MINUS_TWO_ROUTE.md`, Sections 4 and 6; its signed margin is (6.7)
   there.  No ordinary-first-moment or published-tameness assumption has
   been added.  The present note supplies exactly its previously missing
   dense `4 by 4` endpoint estimate.
7. **No fixed-skeleton globalization gap.**  Formula (5.5) sums every
   endpoint decoration with its exact multinomial multiplicity, (5.6)
   applies the threshold estimate jointly under the conditioned residual
   law, and (5.9) performs the endpoint-table sum before taking the uniform
   conditional bound.  Hence no unrecorded number of skeletons is absorbed
   into an `o(1)` term.
