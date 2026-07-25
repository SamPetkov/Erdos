# Concise replacement draft for Sections 8 and 9

This draft records the shortest proof route currently supported by the focused
review PRs. It keeps the exact canonical exposure but removes four layers of
machinery:

- the table-family Cauchy inequality;
- the near/middle high-cell split;
- the residual configuration-model argument inside Section 8;
- the cycle decomposition and separate cubic-lambda estimate in Section 9.

The notation is chosen to avoid collisions. We use $U=\alpha-2$ for the
largest block size, $\mathcal M$ for the exposed matching, $h$ for a local
endpoint deficit, $m_0$ for residual mass, and $\mathrm e$ for Euler's number.
Throughout,

$$
N=\ln n,\qquad U=\alpha-2,\qquad R_0=\lfloor U/2\rfloor,
$$

and the four block sizes are $u_i=U-i$, $0\le i\le3$.

## 8. Canonical high cells

For an overlap table $r=(r_{ab})$, define

$$
\mathcal M(r)=\{(a,b):r_{ab}>R_0\}.
$$

Every row and column sum is at most $U$, so $\mathcal M(r)$ is a bipartite
matching. Write its cell multiplicities as $j_{ab}=r_{ab}$, and put
$J=\sum_{(a,b)\in\mathcal M}j_{ab}$. Exposing the corresponding stub pairs has
incidence

$$
\pi(\mathcal M,j)
=
\frac{\prod_{(a,b)\in\mathcal M}
      (s_a)_{j_{ab}}(t_b)_{j_{ab}}}
     {(n)_J\prod_{(a,b)\in\mathcal M}j_{ab}!}.
\tag{8.1}
$$

Conditional on those pairs, the remaining matching is uniform with the induced
residual degrees, is zero on $\mathcal M$, and is capped by $R_0$. Multiplying
(8.1) by the exact residual configuration-table law recovers the original
overlap probability. Thus the decomposition is exact and every overlap table
occurs once.

### 8.1 Endpoint transportation without a global Cauchy step

First suppose every high cell is a full-containment cell. Aggregate the selected
block pairs by endpoint type into $L=(\ell_{ij})_{0\le i,j\le3}$. Let

$$
r_i=\sum_j\ell_{ij},\qquad c_j=\sum_i\ell_{ij},
$$

and let $W(L)$ be the exact endpoint incidence and local signed reward. Let
$D(r)$ be the common-subprofile weight from Section 7, and define

$$
A_L=\frac{\prod_i r_i!}{\prod_{ij}\ell_{ij}!},
\qquad
C_L=\frac{\prod_j c_j!}{\prod_{ij}\ell_{ij}!}.
$$

The endpoint transport calculation gives

$$
W(L)
\le
\sqrt{D(r)A_L\,D(c)C_L}\,Q^L,
\qquad
Q^L=\prod_{ij}Q_{ij}^{\ell_{ij}},
\tag{8.2}
$$

where $Q_{ii}=1$, and for $d=|i-j|\in\{1,2,3\}$,

$$
Q_{ij}\le\frac{\eta_n^d}{d!},
\qquad
\eta_n=O\!\left(\frac{N^{3/2}}{\sqrt n}\right).
\tag{8.3}
$$

PR #36 proves the square-free finite algebra underlying (8.2). For the table
sum, apply $2\sqrt{xy}\le x+y$ termwise:

$$
W(L)
\le
\frac12\bigl(D(r)A_L+D(c)C_L\bigr)Q^L.
\tag{8.4}
$$

Fix $r$. Dropping only the column-margin constraint and using the multinomial
theorem gives

$$
\sum_{L:\operatorname{row}(L)=r}A_LQ^L
\le
\prod_i\left(\sum_jQ_{ij}\right)^{r_i}.
\tag{8.5}
$$

The symmetric estimate holds after fixing $c$. Every row and column sum of $Q$
is at most $1+C\eta_n$, while every margin uses at most $k_{\mathrm{co}}$
blocks. Therefore

$$
\sum_LW(L)
\le
(1+C\eta_n)^{k_{\mathrm{co}}}\sum_rD(r).
\tag{8.6}
$$

Lemma 7.1 gives $\sum_rD(r)=1+o(1)$, so

$$
\sum_LW(L)
\le
\exp\{O(\eta_nk_{\mathrm{co}})\}
=
\exp\{O(\sqrt{nN})\}.
\tag{8.7}
$$

Thus the endpoint sum needs neither a Cauchy inequality over the table family,
nor $(\sum_r\sqrt{D(r)})^2$, nor a polynomial count of margin vectors.

### 8.2 One decorated-cell expansion for all high multiplicities

Fix one selected block pair whose endpoint sizes are $m$ and $m+d$, with
$0\le d\le3$. A high multiplicity has the form

$$
j=m-h.
$$

Since $j>R_0\ge\lfloor m/2\rfloor$, we have

$$
2h<m.
\tag{8.8}
$$

The relevant object is not merely the number $h$. A **cell decoration** consists
of a literal single-cell stub matching of size $m-h$. We sum all such
decorations by their exact cardinality and signed local reward. Comparing that
weighted cardinality with the full endpoint cell gives the exact ratio

$$
R_{m,d}(h)
=
\frac{\binom mh}{(d+1)\cdots(d+h)}
2^{-hm+h(h+1)/2}.
\tag{8.9}
$$

Thus no unique physical completion is claimed or needed: the missing-stub and
pairing multiplicities are already contained in the ratio (8.9). For several
selected block pairs, the block-pair support is a matching, so the local stub
decorations are independent. If $H=\sum h$, the single global denominator ratio
is at most $n^H$. Hence each decorated cell may be charged

$$
A_{m,d}(h)=n^hR_{m,d}(h).
$$

The formalization-first integer estimate is

$$
h\left\lfloor\frac{2m}{3}\right\rfloor
\le
hm-\frac{h(h+1)}2
\qquad(2h<m).
\tag{8.10}
$$

PR #38 isolates this arithmetic statement. The binomial coefficient in (8.9)
is at most $m^h$, while its denominator is at least one. Hence

$$
A_{m,d}(h)
\le
\left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^h.
\tag{8.11}
$$

All endpoint sizes satisfy $U-3\le m\le U$. Set

$$
b_*:=\left\lfloor\frac{2(U-3)}3\right\rfloor,
\qquad
\rho_n:=\frac{nU}{2^{b_*}}.
$$

The phase relation $2^U=\Theta(n^2/N^2)$ gives

$$
\rho_n
=O\!\left(\frac{N^{7/3}}{n^{1/3}}\right)
=o(1).
\tag{8.12}
$$

For every selected endpoint block pair, summing over all nonzero high deficits
and all corresponding stub decorations contributes at most $2\rho_n$ times the
full-cell weight, eventually. Distinguish the selected block pairs, apply the
exact product expansion over their allowed decorations, and only then group
identical endpoint types. The existing block-pairing factorials perform that
grouping; there is no additional unlabelled multiplicity.

There are at most $k_{\mathrm{co}}$ selected block pairs. Therefore all high
multiplicities cost at most

$$
(1+2\rho_n)^{k_{\mathrm{co}}}
\le
\exp\{O(k_{\mathrm{co}}\rho_n)\}
=
\exp\{O(n^{2/3}N^{4/3})\}.
\tag{8.13}
$$

Combining (8.7) and (8.13),

$$
\boxed{
\sum_{(\mathcal M,j)}w_{\mathrm{hi}}(\mathcal M,j)
\le
\exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.}
\tag{8.14}
$$

No near/middle partition or residual configuration-model argument is needed in
Section 8.

## 9. Residual attachment

Fix an attained high skeleton $(\mathcal M,j)$, and let $m_0=n-J$ be its
residual stub mass. Its exact residual attachment is

$$
\mathcal A(\mathcal M,j)
=
\mathbb E_{\mathrm{res}}\!\left[
\prod_{a,b} g(r'_{ab})
2^{\beta(\mathcal M\cup H_{\mathrm{res}})}
\mathbf1_{\mathcal E(\mathcal M,j)}
\right].
\tag{9.1}
$$

For cells outside $\mathcal M$, set

$$
\theta_{ab}=\frac{\mathrm e\,d_ad'_b}{m_0},
\qquad
q_{ab}
=
\frac{\theta_{ab}^2}{2}
+
\sum_{x=3}^{R_0}\bigl(g(x)-g(x-1)\bigr)
\frac{\theta_{ab}^x}{x!},
\tag{9.2}
$$

and put $q_{ab}=0$ on $\mathcal M$.

The threshold expansion for a fixed even edge set $F$ is bounded by selected
$q$-weights and unselected local increments. Every local increment is at most
$q_{ab}$. Hence

$$
\mathcal A(\mathcal M,j)
\le
\left(\prod_{(a,b)\notin\mathcal M}(1+q_{ab})\right)
\sum_{F\text{ even}}
\prod_{(a,b)\in F\setminus\mathcal M}q_{ab}.
\tag{9.3}
$$

The restriction map $F\mapsto F\setminus\mathcal M$ is injective on even edge
sets: two completions with the same residual restriction differ by an even
subset of a matching, and the only such subset is empty. Therefore

$$
\sum_{F\text{ even}}
\prod_{(a,b)\in F\setminus\mathcal M}q_{ab}
\le
\prod_{(a,b)\notin\mathcal M}(1+q_{ab}).
\tag{9.4}
$$

Combining (9.3) and (9.4),

$$
\boxed{
\mathcal A(\mathcal M,j)
\le
\exp\left(2\sum_{a,b}q_{ab}\right).}
\tag{9.5}
$$

### 9.1 Intrinsic quadratic regime

Assume

$$
2^U\le m_0^3.
\tag{9.6}
$$

The finite endpoint estimate gives $q_{ab}\le C\theta_{ab}^2$. Moreover,

$$
\sum_{a,b}\theta_{ab}^2
=
\frac{\mathrm e^2}{m_0^2}
\left(\sum_ad_a^2\right)
\left(\sum_b(d'_b)^2\right)
\le
\mathrm e^2U^2.
\tag{9.7}
$$

Thus

$$
\boxed{
\mathcal A(\mathcal M,j)
\le\exp(CU^2)
=\exp(O(N^2)).}
\tag{9.8}
$$

PR #37 formalizes the finite q-only bound and its attained-profile
specialization.

### 9.2 Complementary small-power regime

If (9.6) fails, the exact arithmetic dichotomy gives

$$
m_0<2^{\lceil U/3\rceil}.
\tag{9.9}
$$

The deterministic residual estimate then yields

$$
\mathcal A(\mathcal M,j)
\le2^{Um_0/2}
\le
\exp\{O(U2^{U/3})\}.
\tag{9.10}
$$

Since $U=(2+o(1))\log_2n$, this exponent is $n^{2/3+o(1)}$, and hence is
$o(n/N^4)$. Together with (9.8), there is a deterministic sequence
$\varepsilon_n\to0$ such that uniformly over all attained high skeletons,

$$
\boxed{
\mathcal A(\mathcal M,j)
\le
\exp\!\left\{\varepsilon_n\frac n{N^4}\right\}.}
\tag{9.11}
$$

This split is intrinsic to the finite $q$-estimate and avoids the auxiliary
threshold $n/N^6$.

### 9.3 Completion of the normalized second moment

The exact canonical decomposition gives

$$
\frac{\mathbb E(Z_k^{\mathrm{sgn}})^2}
     {(\mathbb EZ_k^{\mathrm{sgn}})^2}
=
\sum_{(\mathcal M,j)}
 w_{\mathrm{hi}}(\mathcal M,j)
 \mathcal A(\mathcal M,j).
\tag{9.12}
$$

Equations (8.14) and (9.11) imply

$$
\boxed{
\frac{\mathbb E(Z_k^{\mathrm{sgn}})^2}
     {(\mathbb EZ_k^{\mathrm{sgn}})^2}
\le
\exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.}
\tag{9.13}
$$

This is the normalized second-moment estimate required by the seed and
amplification argument.

## Formalization map and remaining boundary

The concise route is supported by:

- PR #34: matching-restriction injectivity and the finite subset-product bound;
- PR #35: literal attachment, attained-profile transport, and the
  $\exp(O(N^2))$ large-residual specialization;
- PR #36: square-free endpoint transportation;
- PR #37: q-only absorption and the intrinsic finite residual dichotomy;
- PR #38: square-free AM--GM linearization, one all-high-deficit
  parametrization, and the two-thirds exponent budget.

The remaining formal work is concentrated in two bridges:

1. transport (8.4) through the exact physical/type-table quotient and sum it
   by the one-sided multinomial expansions;
2. prove the decorated-cell ratio bound (8.11) in the repository's `ENNReal`
   language and transport the resulting product through the exact block-pair
   and single-cell stub-matching cardinalities.

These are narrower obligations than the present separate endpoint, near,
middle, residual-cycle, and cubic-moment branches.
