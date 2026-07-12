# Signed-cocolouring overlaps for nonconstant profiles

**Status.**  This note proves a uniform second-moment bound for the entire
bounded-cell (scrambled) range of the raw signed-cocolouring count, for
arbitrary nonconstant profiles whose largest part is `O(log n)`.  In that
range the normalized contribution is `1+O(log^4 n/n)`: triple cells give the
leading error and cycles in the multiplicity-at-least-two support contribute
only `O(log^12 n/n^4)` in the exponent.  It also proves that exact common
parts can force a normalized second moment of order

\[
  \exp\!\left((1-o(1))\frac{k_u^2}{2\mu_u}\right),
  \qquad \mu_u=\binom nu2^{-\binom u2},
\]

so the signed factor does not yield a bounded raw second moment.  The cells
above the bounded-cell range, especially simultaneous common/containment
clusters for a mixed profile, are not fully summed in this note.  For the
`(alpha-2)` optimal profile the bare one-polymer activity is proved to be
`n^o(1)`, and every fixed-positive-mass exact partial diagonal is proved
exponentially negligible; the vanishing-mass and near-full dense bare
matching endpoints were left open at this stage.  Consequently this note
alone is not an existence theorem.  Those endpoints are subsequently closed
for the four-size midpoint profile in `FOUR_SIZE_PARTIAL_RATES.md` and
`DENSE_FOUR_TYPE_MATCHING.md`, and the resulting proposed resolution is
assembled in `COMPLETE_PROOF_DRAFT.md`.

All logarithms are base 2 unless `ln` is displayed.  The letter `e` denotes
the base of the natural logarithm.

## 1. Setup and the configuration model

Let

\[
 \mathbf s=(s_1,\ldots,s_k),\qquad
 \mathbf t=(t_1,\ldots,t_h),\qquad
 \sum_a s_a=\sum_b t_b=n                                      \tag{1.1}
\]

be two ordered slot profiles.  Choose independently and uniformly an ordered
partition with each profile, and let

\[
 r_{ab}=|V_a\cap W_b|.                                        \tag{1.2}
\]

Its law is

\[
 p_{\mathbf s,\mathbf t}(r)
 =\frac{\prod_a s_a!\prod_b t_b!}
        {n!\prod_{a,b}r_{ab}!}.                               \tag{1.3}
\]

Equivalently, put `s_a` stubs at row vertex `a`, `t_b` stubs at
column vertex `b`, and take a uniform perfect matching of the two sets of
`n` stubs.  The cell multiplicities of the resulting bipartite multigraph
have exactly the law (1.3).  This remains true for nonconstant degrees.

Let `H(r)` be the simple bipartite graph on the row and column slots whose
edges are the cells with `r_ab>=2`.  Put

\[
 w_{ab}=\binom{r_{ab}}2,
 \quad W=\sum_{ab:r_{ab}\ge2}w_{ab},
 \quad \beta(H)=|E(H)|-|V(H)|+c(H),                            \tag{1.4}
\]

where isolated vertices are omitted and `c(H)` is the number of nonempty
components.  The exact one-graph sign-summed factor from
`X_SECOND_MOMENT.md` is

\[
 A_\zeta(r)=2^{W+c(H)-|V(H)|}
 =2^{\sum_{e\in E(H)}(w_e-1)+\beta(H)}.                       \tag{1.5}
\]

For later use define

\[
 g(0)=g(1)=g(2)=1,\qquad
 g(x)=2^{\binom x2-1}\quad(x\ge3).                            \tag{1.6}
\]

Since the cycle space of `H` has `2^{beta(H)}` elements,

\[
 A_\zeta(r)
 =\left(\prod_{a,b}g(r_{ab})\right)
   \#\{F\subseteq E(H):\deg_F(v)\text{ is even for every }v\}.
                                                                    \tag{1.7}
\]

Thus a double cell has no direct energetic cost.  A forest made entirely of
double cells has factor exactly one.  The first local excess is a triple cell,
for which `g(3)=4`, and the first topological excess is a four-cycle of double
cells.

## 2. A joint factorial bound

The following elementary estimate is the input that makes the result uniform
over nonconstant profiles.

### Lemma 2.1 (prescribed cell multiplicities)

Let `D` be a set of distinct cells and prescribe integers `x_ab>=1` for
`(a,b) in D`.  Set

\[
 m=\sum_{(a,b)\in D}x_{ab},\quad
 d_a=\sum_{b:(a,b)\in D}x_{ab},\quad
 d'_b=\sum_{a:(a,b)\in D}x_{ab}.                             \tag{2.1}
\]

Then

\[
 \Pr(r_{ab}\ge x_{ab}\text{ for all }(a,b)\in D)
 \le
 \frac{\prod_a(s_a)_{d_a}\prod_b(t_b)_{d'_b}}
      {(n)_m\prod_{(a,b)\in D}x_{ab}!}.                      \tag{2.2}
\]

In particular, with

\[
 \theta_{ab}=\frac{e s_at_b}{n},                             \tag{2.3}
\]

the right side of (2.2) is at most

\[
 \prod_{(a,b)\in D}\frac{\theta_{ab}^{x_{ab}}}{x_{ab}!}.    \tag{2.4}
\]

#### Proof

Select the required row stubs and column stubs and then a bijection inside
each prescribed cell.  The number of such choices is

\[
 \frac{\prod_a(s_a)_{d_a}\prod_b(t_b)_{d'_b}}
      {\prod_{(a,b)\in D}x_{ab}!}.
\]

A fixed collection of `m` matched stub pairs occurs with probability
`1/(n)_m`.  A union bound proves (2.2).  Next use
`(s_a)_{d_a}<=s_a^{d_a}`, and similarly on the column side.  Finally,

\[
 (n)_m=m!\binom nm\ge (m/e)^m(n/m)^m=(n/e)^m,                \tag{2.5}
\]

which proves (2.4).  \(\square\)

The loss of the constant `e` makes (2.4) global in `m`; there is no hidden
assumption that the total number of prescribed stubs is `o(sqrt(n))`.

## 3. The bounded-cell theorem

Write

\[
 U=\max\{s_a,t_b:a\le k,b\le h\},\qquad
 \theta_*=eU^2/n.                                           \tag{3.1}
\]

### Theorem 3.1 (uniform signed bound below the large-cell scale)

Assume `U=O(log n)`.  Let `R=R(n)>=3` be an integer such that

\[
 2^R\theta_*\le R.                                          \tag{3.2}
\]

Then, uniformly over all profiles satisfying (1.1),

\[
\begin{split}
 1-O(U^6/n^2)
 &\le \mathbb E_p\!\left[A_\zeta(r)
                  \mathbf1_{\{\max_{a,b}r_{ab}\le R\}}\right]\\
 &\le \exp\!\left\{
       \frac{4e^3}{3n^3}
         \Big(\sum_a s_a^3\Big)\Big(\sum_b t_b^3\Big)
       +2\rho^2\right\},                                  \tag{3.3}
\end{split}
\]

where

\[
 \rho=\frac{e^4}{n^4}
       \Big(\sum_a s_a^4\Big)\Big(\sum_b t_b^4\Big)
 \le \frac{e^4U^6}{n^2}.                                   \tag{3.4}
\]

In particular,

\[
 \boxed{
 \mathbb E_p\!\left[A_\zeta(r)
             \mathbf1_{\{\max r_{ab}\le R\}}\right]
 =1+O(U^4/n).}                                               \tag{3.5}
\]

For chromatic-scale profiles, `U=Theta(log n)`, the error in (3.5) is
`O(log^4 n/n)`.  Condition (3.2) permits, for example,

\[
 R=\log n-3\log\log n-O(1),                                 \tag{3.6}
\]

so the theorem is not restricted to constant-size overlap cells.
Indeed, if `U<=C log_2 n` and

\[
 R=\left\lfloor\log_2n-3\log_2\log_2n-C_0\right\rfloor,
                                                                    \tag{3.6a}
\]

then `2^R eU^2/n<=eC^2 2^{-C_0}/log_2 n`, while
`R~log_2 n`.  Hence (3.2) holds for every fixed `C_0` (and all sufficiently
large `n`).  This calculation uses base-two logarithms consistently.

#### Proof

Put

\[
 \Delta_x=g(x)-g(x-1)\quad(x\ge3),                           \tag{3.7}
\]

and for every cell define

\[
 \lambda_{ab}=\sum_{x=3}^R
       \Delta_x\frac{\theta_{ab}^x}{x!},\qquad
 q_{ab}=\frac{\theta_{ab}^2}{2}+\lambda_{ab}.                \tag{3.8}
\]

On the event `max r_ab<=R`,

\[
 g(r_{ab})=1+\sum_{x=3}^R\Delta_x\mathbf1_{\{r_{ab}\ge x\}}.
                                                                    \tag{3.9}
\]

If the cell is an edge of a fixed even subgraph, the identity used instead
is, explicitly,

\[
 \mathbf1_{\{r_{ab}\ge2\}}g(r_{ab})
 =\mathbf1_{\{r_{ab}\ge2\}}
  +\sum_{x=3}^R\Delta_x\mathbf1_{\{r_{ab}\ge x\}}.          \tag{3.9a}
\]

Thus, in each monomial of the threshold expansion, a triple-or-larger edge
is represented either by the base-threshold summand or by one increment
summand; it is never assigned their product.  Summing those alternative
monomials gives exactly `theta_ab^2/2+lambda_ab` in (3.8).  At the level of
the original indicator identity, of course, a realized triple contributes
the numerical sum `1+Delta_3=4`.

Use (1.7) and first fix an even subgraph `F`.  Expanding (3.9), an edge of
`F` either receives its base threshold two or a threshold `x>=3`; a cell
outside `F` either receives no threshold or a threshold `x>=3`.  Lemma 2.1
therefore gives

\[
 \mathbb E_p[A_\zeta(r)\mathbf1_{\{\max r\le R\}}]
 \le e^\Lambda
      \sum_{F\text{ even}}\prod_{ab\in F}q_{ab},
 \qquad \Lambda=\sum_{a,b}\lambda_{ab}.                    \tag{3.10}
\]

This step controls arbitrary simultaneous triple cells, including cells
sharing rows or columns; it is not a first-moment union bound on the number
of triples.

The ratio of consecutive majorants in the sum defining `lambda_ab` is

\[
 \frac{g(x+1)\theta_{ab}^{x+1}/(x+1)!}
      {g(x)\theta_{ab}^{x}/x!}
 =\frac{2^x\theta_{ab}}{x+1}.                               \tag{3.11}
\]

It is increasing in `x`, and (3.2) makes it at most `1/2` for
`3<=x<R`.  Hence

\[
 \lambda_{ab}\le
 2g(3)\frac{\theta_{ab}^3}{3!}
 =\frac43\theta_{ab}^3,                                    \tag{3.12}
\]

and, for all large `n`, `q_ab<=theta_ab^2`.  Consequently

\[
 \Lambda\le\frac{4e^3}{3n^3}
       \Big(\sum_as_a^3\Big)\Big(\sum_bt_b^3\Big)
 \le\frac{4e^3U^4}{3n}.                                    \tag{3.13}
\]

It remains to control the cycle-space term.  Every nonempty even simple
graph is a union of edge-disjoint simple cycles.  After choosing one such
decomposition for every even graph and then dropping the edge-disjointness
condition,

\[
 \sum_{F\text{ even}}\prod_{e\in F}q_e
 \le \prod_{C\text{ simple cycle}}
       \left(1+\prod_{e\in C}q_e\right)
 \le \exp\left\{\sum_C\prod_{e\in C}q_e\right\}.            \tag{3.14}
\]

The first inequality is a genuine overcount.  Fix one deterministic
edge-disjoint cycle decomposition `D(F)` for each even `F`.  The map
`F -> D(F)` is injective because the union of the cycles in `D(F)` is exactly
`F`.  The product in (3.14) sums all finite sets of cycles, including
intersecting ones, and therefore contains every selected `D(F)` with the
same edge weight.

A bipartite cycle has length `2j` with `j>=2`.  Since

\[
 q_{ab}\le \frac{e^2s_a^2t_b^2}{n^2},                       \tag{3.15}
\]

summing first over unrestricted sequences of its `j` row and `j` column
vertices gives

\[
 \sum_{C:|C|=2j}\prod_{e\in C}q_e\le \rho^j.                \tag{3.16}
\]

Now `rho=o(1)`, so the cycle exponent in (3.14) is at most
`sum_{j>=2}rho^j<=2rho^2`.  Equations (3.10), (3.13), and (3.14) prove the
upper bound in (3.3).

Finally, `A_zeta(r)>=1` for every `r`.  Lemma 2.1 and a union bound give

\[
 \Pr(\max r_{ab}>R)
 \le \Pr(\max r_{ab}\ge4)
 \le \frac1{24}\sum_{a,b}\theta_{ab}^4
 \le \frac{e^4U^6}{24n^2}.                                 \tag{3.17}
\]

This proves the lower bound and completes the theorem. \(\square\)

### Corollary 3.1 (half-part cap and matching remainder)

Fix `epsilon>0`.  Suppose `U->infinity` and

\[
 U\le(4-\epsilon)\log_2n,\qquad R=\lfloor U/2\rfloor\ge3.   \tag{3.17a}
\]

Then the conclusion (3.5) remains valid, even if the sufficient condition
(3.2) fails:

\[
 \mathbb E_p\!\left[A_\zeta(r)
             \mathbf1_{\{\max r_{ab}\le\lfloor U/2\rfloor\}}\right]
 =1+O(U^4/n).                                                \tag{3.17b}
\]

Moreover, the cells omitted by (3.17b), those with multiplicity greater than
`floor(U/2)`, form a matching: no two can share a row or a column.

#### Proof

Only the estimate (3.12) needs replacement.  Put

\[
 b_x=\frac{g(x)\theta_*^{x-3}}{x!},\qquad3\le x\le R.       \tag{3.17c}
\]

Its consecutive ratio is `2^x theta_*/(x+1)`, hence is increasing; the
sequence is log-convex.  Moreover, consecutive ratios of these ratios equal
`2(x+1)/(x+2)>=8/5` for `x>=3`.  Hence there are only `O(1)` indices at
which the term ratio lies between `1/2` and `1`: before them the decreasing
head is a geometric sum dominated by its `x=3` term, and after them the
increasing tail is at most `R` times its right endpoint.  The endpoint
satisfies

\[
\begin{split}
 \log_2\!\left(g(R)\frac{\theta_*^R}{R!}\right)
 &\le \frac{R^2}{2}-R\log_2n+O(R\log U)\\
 &=-\Omega_\epsilon(R\log n),                              \tag{3.17d}
\end{split}
\]

where (3.17a) is used in the last line.  This is smaller than the `x=3`
term by a superpolynomial factor in the present range.  Consequently,

\[
 \sum_{x=3}^R\Delta_x\frac{\theta_{ab}^x}{x!}
 \le \theta_{ab}^3\sum_{x=3}^R
       g(x)\frac{\theta_*^{x-3}}{x!}
 =O(\theta_{ab}^3),                                        \tag{3.17e}
\]

uniformly in the cell.  Equations (3.10)--(3.17) now apply with changed
absolute constants and prove (3.17b).  Finally,
`2(floor(U/2)+1)>U`, while every row and column has total multiplicity at
most `U`; hence two omitted cells cannot meet the same row or column.
\(\square\)

### 3.2 What the two error terms count

The two terms in (3.3) have different origins.

For triples, the exact factorial identity is

\[
 \mathbb E\sum_{a,b}\binom{r_{ab}}3
 =\frac{
       \big(\sum_a(s_a)_3\big)\big(\sum_b(t_b)_3\big)}
       {6(n)_3}
 \le O(U^4/n).                                              \tag{3.18}
\]

An isolated triple cell changes the signed factor from `1` to `4`, so its
increment is `3`.  Formula (3.10), rather than (3.18) alone, controls products
of many triple-cell increments.

If all cells have multiplicity at most two, then

\[
 A_\zeta(r)=2^{\beta(H)}.                                   \tag{3.19}
\]

The first possible nonempty even subgraph is a bipartite four-cycle.  The
total weighted contribution of all such cycles and longer ones is at most
`2rho^2=O(U^12/n^4)`.  Thus double cells occur in number `Theta(log^2 n)`
for an equitable chromatic-scale profile, but their support is so sparse that
its cycle rank is negligible.

### 3.3 Comparison with the transferred tame-profile bound

For Heckel's range `mu_alpha>=n^(0.05+epsilon)`, the transferred ordinary-
colouring estimate for truncated scrambled pairs is

\[
 \exp\{O(n/\mu_\alpha+\log^2n)\}
 \le \exp\{O(n^{0.95-\epsilon})\}.                           \tag{3.20}
\]

Theorem 3.1 is much sharper on the cells it covers:

\[
 1+O(\log^4n/n).                                             \tag{3.21}
\]

These statements are not interchangeable.  The truncated notion of a
relevant scrambled pair permits `O(log^3 n)` exceptional parts with cells
near the full class size.  Such cells violate (3.2), and their contribution
is deliberately excluded from (3.21).  Theorem 3.1 therefore replaces the
small-block part of the transferred calculation, not its exceptional/common-
part analysis.

## 4. Exact common parts force an exponential cluster term

Now take the same profile on both sides.  Let `k_u` be its number of slots of
size `u`, and put

\[
 m_u=\binom u2,\qquad
 \mu_u=\binom nu2^{-m_u},\qquad
 G_u=2^{m_u-1}.                                              \tag{4.1}
\]

### Proposition 4.1 (common-part matching lower bound)

For every choice of nonnegative integers `ell_u<=k_u`, let
`q=sum_u ell_u u`.  The full normalized signed second moment satisfies

\[
\boxed{
 R_\zeta=\mathbb E_p A_\zeta(r)
 \ge
 \sum_{(\ell_u)}
 \frac1{(n)_q}
 \prod_u
   \frac{(k_u)_{\ell_u}^2}{\ell_u!}
   \big[(G_u-1)u!\big]^{\ell_u}.}                            \tag{4.2}
\]

In particular, define

\[
 x_u=\frac{k_u^2(G_u-1)u!}{n^u}
 =(1-o(1))\frac{k_u^2}{2\mu_u}                              \tag{4.3}
\]

uniformly for `u=O(log n)` with `u->infinity`.  If for some `u=u(n)`

\[
 x_u\to\infty\qquad\text{and}\qquad x_u=o(k_u),             \tag{4.4}
\]

then

\[
 \boxed{R_\zeta\ge\exp\{(1-o(1))x_u\}.}                    \tag{4.5}
\]

#### Proof

For two slots of the same size `u`, an exact common part is the event
`V_a=W_b`.  Exact common parts form a matching between the row and column
slots.  Since an exact common cell is an isolated edge of `H`, its local
factor is `G_u`.  Hence

\[
 A_\zeta(r)\ge
 \prod_{u}\prod_{a,b:\,s_a=t_b=u}
 \left[1+(G_u-1)\mathbf1_{\{V_a=W_b\}}\right].              \tag{4.6}
\]

There are `(k_u)_ell_u^2/ell_u!` matchings of size `ell_u` between the
size-`u` slots.  For a fixed collection of these matchings, the probability
that all required equalities hold is

\[
 \frac{\prod_u(u!)^{\ell_u}}{(n)_q}.                         \tag{4.7}
\]

Expanding (4.6) and using (4.7) proves (4.2).

For one fixed `u`, use `(n)_{ell u}<=n^{ell u}` in (4.2).  For
`ell=O(x_u)=o(k_u)`,

\[
 \frac{(k_u)_\ell^2}{k_u^{2\ell}}
 =\exp\{-O(\ell^2/k_u)\}.                                   \tag{4.8}
\]

Summing the terms in a central Poisson window `ell=x_u+O(sqrt(x_u))`
therefore gives

\[
 R_\zeta\ge
 \exp\{x_u-O(x_u^2/k_u)-o(x_u)\},                           \tag{4.9}
\]

which is (4.5).  Finally, `(n)_u/n^u=1-o(1)` and
`1-1/G_u=1-o(1)` give (4.3). \(\square\)

This is a concrete obstruction to a bounded-ratio Paley--Zygmund argument
with the raw signed count.  The sign sum halves the ordinary common-part
activity, but only by the constant factor two.

For a chromatic-window top size `u=alpha-1`, one has

\[
 \mu_{\alpha-1}=\Theta(\mu_\alpha n/\log n).                 \tag{4.10}
\]

If `k_u=Theta(n/log n)`, (4.3) becomes

\[
 x_u=\Theta\!\left(\frac{n}{\mu_\alpha\log n}\right).       \tag{4.11}
\]

At `mu_alpha=n^(0.05+epsilon)`, the forced lower exponent is therefore
`Theta(n^(0.95-epsilon)/log n)`.  Up to this logarithmic factor, it has the
same polynomial scale as the transferred upper exponent (3.20).  Thus the
`n^0.95` scale is not created solely by a lossy ordinary-colouring
comparison; common top-size parts already produce it in the exact signed
factor.

### Corollary 4.2 (common clusters at the minimal exceptional phase)

Let `q=ln 2`, `N=ln n`, and `w=ln N`.  Let `n` run along the integers
nearest the starts of the independence-number cycles; equivalently, the
phase in `EXCEPTIONAL_REGIME.md` has `delta=o(w/N)`.  (At the real cycle
boundary it is exactly zero.)  Let `a=alpha-1`, and consider any integer
profile whose number of size-`a` slots realizes, up to `1+o(1)`, the active
cap from `CONSTRAINED_EXCEPTIONAL_PROFILE.md` before adding slack.  Its
largest-class vertex mass and class count satisfy

\[
 c(x(n))=\left(2-\frac q2+o(1)\right)\frac wN,
 \qquad
 k_a=\left(\frac{q(4-q)}4+o(1)\right)
             \frac{nw}{N^2}.                               \tag{4.12}
\]

If `K(0)` is the constant in the uniform expansion of `ln mu_alpha`, then

\[
 \mu_a=\left(\frac{e^2q}{2}e^{K(0)}+o(1)\right)
             nN^{2/q-3/2}.                                \tag{4.13}
\]

Consequently the parameter in Proposition 4.1 is

\[
 x_a=(C_*+o(1))
       \frac{nw^2}{N^{2/q+5/2}},
 \qquad
 C_*=
 \frac{[q(4-q)/4]^2}{e^2q e^{K(0)}}>0.                    \tag{4.14}
\]

The denominator in `C_*` is
`2[(e^2q/2)e^{K(0)}]=e^2q e^{K(0)}`: the outer factor two is
the signed common-part penalty in `x_a~k_a^2/(2mu_a)`.  Thus no factor two
is absorbed into the class-count constant `q(4-q)/4`.

It tends to infinity and is `o(k_a)`, so

\[
\boxed{
 \ln R_\zeta\ge(C_*+o(1))
       \frac{n(\ln\ln n)^2}
            {(\ln n)^{2/\ln2+5/2}}.}                     \tag{4.15}
\]

Here

\[
 \frac2{\ln2}+\frac52=5.385390\ldots .                    \tag{4.16}
\]

This lower exponent is too large for *direct Azuma* amplification of a
target gap `H=Theta(n/N^3)`: that method has budget
`H^2/n=Theta(n/N^6)`, and (4.15) is larger by
`Theta(N^(0.61460...)w^2)`.  It is, however, comfortably inside the sharper
Alon--Scott rare-event budget proved in `ALON_CONCENTRATION_EXTENSION.md`:

\[
 \frac{H^2\log^2n}{n}=\Theta(n/N^4),                        \tag{4.17}
\]

because

\[
 \frac{nw^2/N^{5.385390\ldots}}{n/N^4}
 =\frac{w^2}{N^{1.385390\ldots}}\longrightarrow0.          \tag{4.18}
\]

Thus exact common parts do **not** obstruct an `n/log^3 n` gap when the
logarithmically sharpened rare-event amplification is used.  They instead set
a compulsory contribution that any full large-cell upper bound must retain.
The remaining quantitative target is

\[
 \ln R_\zeta=o(n/\log^4n),                                  \tag{4.19}
\]

after all common, containment, and near-common clusters are summed.  The
corollary concerns the unslackened active cap.  A slack rule that deletes all
size-`a` classes at the very start of the cycle removes this particular
lower bound, but changes the profile and must be analysed separately.

## 5. Near-identical and containment cells

The exact one-cell calculations below locate the endpoints not covered by
Theorem 3.1.

### Proposition 5.1 (fixed-distance near copies)

Suppose two slots both have size `u`.  For `0<=j<=u`,

\[
 \Pr(r_{ab}=u-j)
 =\frac{\binom uj\binom{n-u}j}{\binom nu}.                   \tag{5.1}
\]

Consequently, for `u-j>=2`, the ratio of the weighted one-cell incidence at
distance `j` to the exact-common incidence is

\[
\boxed{
 \frac{G_{u-j}\Pr(r_{ab}=u-j)}
      {G_u\Pr(r_{ab}=u)}
 =\binom uj\binom{n-u}j
   2^{-ju+j(j+1)/2}.}                                       \tag{5.2}
\]

If

\[
 u=2\log n-2\log\log n+O(1),                               \tag{5.3}
\]

then, for every fixed `j>=1`, (5.2) is

\[
 O_j\!\left((\log^3 n/n)^j\right).                          \tag{5.4}
\]

In particular, a one-vertex perturbation has relative activity

\[
 u(n-u)2^{-(u-1)}=\Theta(\log^3 n/n).                        \tag{5.5}
\]

#### Proof

Equation (5.1) is the hypergeometric law.  Also

\[
 \binom u2-\binom{u-j}2=ju-\frac{j(j+1)}2,                  \tag{5.6}
\]

which proves (5.2).  Under (5.3), `2^u=Theta(n^2/log^2 n)`, and (5.4)
follows. \(\square\)

Thus a fixed-distance near-copy is locally negligible compared with an exact
common part.  This does not itself sum clusters of many interacting near-
copies: the residual `j` vertices must enter other cells, and those cells can
join several large edges into one component of `H`.

### Proposition 5.2 (mixed-size containment activity)

For slots of sizes `2<=s<=t`,

\[
 \Pr(r_{ab}=s)=\frac{\binom ts}{\binom ns},qquad
 G_s\Pr(r_{ab}=s)=\frac{\binom ts}{2\mu_s}.                  \tag{5.7}
\]

Hence the aggregate first-order activity of all oriented size-`s`-inside-
size-`t` cells is

\[
 \frac{k_sk_t\binom ts}{2\mu_s}.                            \tag{5.8}
\]

For `s=t` and `s->infinity`, this is asymptotically the common-part parameter
in (4.3).  For `s<t`, the edge
is not an isolated common component: it exhausts the size-`s` row but leaves
`t-s` column stubs, so a product bound based only on (5.8) loses the component
and cycle constraints.  Uniformly summing simultaneous containments is one
of the regimes left open below.

### Lemma 5.3 (no hidden interior maximum for one cell)

For fixed slot sizes `s,t`, set

\[
 h_x=2^{\binom x2-1}\frac{(st/n)^x}{x!},\qquad x\ge2.        \tag{5.9}
\]

Then

\[
 \frac{h_{x+1}}{h_x}=\frac{2^xst}{n(x+1)}                  \tag{5.10}
\]

is increasing in `x`.  Thus `(h_x)` is log-convex, and on every integer
interval its maximum is at an endpoint.  For a chromatic-scale pair of
slots, the interior multiplicities near `log n` are the *minimum*-activity
cells.  The possible large contributions are therefore the triple endpoint
and the common/containment endpoint, exactly the two ranges isolated in
Sections 3--5.

This is a one-cell statement.  It does not by itself factor the contingency-
table sum when several endpoint cells share slots.

### Proposition 5.4 (residual attachments to a moderate high-cell skeleton)

Assume the hypotheses of Corollary 3.1 and put `R=floor(U/2)`.  In the
threshold-increment expansion of `A_zeta`, call a selected demand `(a,b,x)`
*high* when `x>R`.  Every feasible set `S` of high demands is a matching.
Write

\[
 J(S)=\sum_{(a,b,x)\in S}x                                  \tag{5.11}
\]

and define its exact bare upper weight

\[
 \omega(S)=
 \frac{1}{(n)_{J(S)}}
 \prod_{(a,b,x)\in S}
   \frac{2\Delta_x(s_a)_x(t_b)_x}{x!}.                     \tag{5.12}
\]

The factor two allows the high support edge either to belong or not to the
even subgraph in (1.7).  There is an absolute constant `C` such that, for
every feasible `S` with `J(S)<=n/2`, the sum of **all** low-increment and
cycle-space attachments to `S` is at most

\[
 \boxed{\omega(S)\exp\{CU^2+CU^4/(n-J(S))\}.}               \tag{5.13}
\]

Consequently, put

\[
 B_{>R}=\sum_{a,b}\sum_{x=R+1}^{\min(s_a,t_b)}
   \frac{2\Delta_x(s_a)_x(t_b)_x}{x!n^x}.                  \tag{5.14}
\]

For every deterministic `J_0<=n/2`, the total contribution from all high
skeletons with `J(S)<=J_0` is at most

\[
\boxed{
 \exp\left\{
  B_{>R}+\frac{J_0^2}{n-J_0}+CU^2+\frac{CU^4}{n-J_0}
 \right\}.}                                                 \tag{5.15}
\]

In particular, for a target `H=n/log^3 n`, the moderate-skeleton range is
within the rare-event budget whenever

\[
 B_{>R}=o(n/\log^4n),\qquad J_0=o(n/\log^2n).               \tag{5.16}
\]

#### Proof

Expand `prod g(r_ab)` by its threshold increments and expand `2^beta` as
the number of even subgraphs.  Fix the selected high increments `S`.  Drop
the parity restriction on the remaining support subgraph.  For each high
edge this creates at most two choices, which accounts for the factor two in
(5.12).

Select the `J=J(S)` prescribed matched stub pairs.  Because `S` is a
matching, the number of selections gives exactly the numerator in (5.12),
and the unexposed stubs form a uniform bipartite configuration model with
`n'=n-J` stubs.  Its row and column degrees are at most `U`.  Dropping parity
means that an unselected residual cell may either carry no support-edge
demand or a base demand of two; a cell selected for a low increment may in
addition receive either parity choice.  Thus the residual factorial
expansion has local activities bounded by

\[
 \frac{\vartheta_{ab}^2}{2}
 +2\sum_{x=3}^{R}\Delta_x\frac{\vartheta_{ab}^x}{x!},
 \qquad \vartheta_{ab}=\frac{e d_ad'_b}{n'},                \tag{5.17}
\]

where `d_a,d'_b` are the residual degrees.  Allowing low increments back
into an exposed high cell only enlarges the expression.  The half-cap proof
of Corollary 3.1, now with `n'>=n/2`, bounds the second term after summation
by `O(U^4/n')`.  The base terms satisfy

\[
 \sum_{a,b}\frac{\vartheta_{ab}^2}{2}
 =\frac{e^2}{2n'^2}
   \Big(\sum_ad_a^2\Big)\Big(\sum_b(d'_b)^2\Big)
 \le\frac{e^2U^2}{2}.                                      \tag{5.18}
\]

Exponentiating the sum of all local activities proves (5.13).  This
argument deliberately drops all residual parity constraints, so it includes
components that attach several high edges and cannot miss a cycle-space
factor.

For (5.15), use

\[
 \frac{n^J}{(n)_J}
 \le\exp\{J^2/(n-J)\}                                      \tag{5.19}
\]

and then drop the matching and distinct-cell constraints in the skeleton
sum.  The resulting product of `1+` local high activities is at most
`exp(B_{>R})`.  Substitution of `J<=J_0` into (5.13) proves (5.15).
\(\square\)

Proposition 5.4 proves that arbitrary residual double/triple attachments are
not an additional obstruction for moderate skeletons.  The exact remaining
large-cell problem is now twofold: bound the profile-dependent activity
`B_{>R}`, and sum the dense skeletons with `J` beyond every useful
`o(n/log^2 n)` cutoff without paying the finite-population error in (5.19).

### 5.5 Specialization to an `(alpha-2)`-bounded optimal profile

The high-polymer activity can be evaluated for the promising second bounded
phase.  The following hypotheses are exactly the properties supplied by the
optimal-profile construction in the tame-colourings paper:

\[
 a=\alpha-2=(2+o(1))\log_2n,\qquad
 k_u=0\ \text{unless}\ a-D\le u\le a,\qquad
 D=O(\sqrt{\ln n}),                                        \tag{5.20}
\]

and `sum_u u k_u=n`.  Put `mu_u=binom(n,u)2^(-binom(u,2))`.
Lemma 3.1 of that paper gives, more precisely,

\[
 \mu_a=n^{2+\delta+O(\ln\ln n/\ln n)},
 \qquad \delta=\{\alpha_0(n)\}\in[0,1).                   \tag{5.21}
\]

Thus `mu_a=n^(2+o(1))` at the minimal phase `delta=o(1)`, while uniformly
over the full cycle the correct statement is the lower bound
`mu_a>=n^(2-o(1))`; it is not uniformly equal to `n^(2+o(1))` when `delta`
stays positive.

### Proposition 5.5 (the bare high activity is below budget)

Under (5.20)--(5.21), for the same profile on the row and column sides,

\[
 \boxed{B_{>\lfloor a/2\rfloor}=n^{o(1)}
        =o(n/\log^4n).}                                    \tag{5.22}
\]

More explicitly,

\[
 B_{>\lfloor a/2\rfloor}
 \le(1+o(1))\left[
  \sum_u\frac{k_u^2}{\mu_u}
  +2\sum_{u<v}\frac{k_uk_v\binom vu}{\mu_u}
 \right]+2^{-\Omega((\log n)^2)},                         \tag{5.23}
\]

and the bracket is at most

\[
 n^{o(1)}\frac{n^2}{a^2\mu_a}+n^{-1+o(1)}
 =n^{o(1)}.                                                 \tag{5.24}
\]

#### Proof

Fix slot sizes `u<=v` in the support and majorize the high activity at
multiplicity `x` by

\[
 H_{u,v}(x)=2^{\binom x2}\frac{(u)_x(v)_x}{x!n^x};         \tag{5.25}
\]

this is valid because `2 Delta_x<=2g(x)=2^(binom(x,2))`.
At the containment endpoint,

\[
 H_{u,v}(u)=\frac{(n)_u}{n^u}\frac{\binom vu}{\mu_u}
 \le\frac{\binom vu}{\mu_u}.                              \tag{5.26}
\]

For `d>=1`, exact cancellation gives

\[
 \frac{H_{u,v}(u-d)}{H_{u,v}(u)}
 =\frac{\binom ud n^d}{(v-u+1)(v-u+2)\cdots(v-u+d)}
   2^{-du+d(d+1)/2}.                                       \tag{5.27}
\]

The right side is largest when `v=u`.  Uniformly under (5.20), summing
(5.27) for `1<=d<u/4` gives `n^(-1+o(1))`.  For the remaining middle strip
`a/2<x<=3u/4`, the crude bounds `(u)_x<=a^x`,
`(v)_x<=a^x`, and `k_u,k_v<=n/a` give

\[
 \log_2\{k_uk_vH_{u,v}(x)\}
 \le2\log_2n+\frac{x^2}{2}-x\log_2n+O(x\log\log n)
 =-\Omega((\log n)^2).                                     \tag{5.28}
\]

Equations (5.26)--(5.28), summed over the `O(D^2)` size pairs, prove
(5.23).

For `u=a-d`, `v=a-e`, `0<=e<=d<=D`, Lemma 3.2 of the tame-colourings
paper yields

\[
 \frac{\mu_u}{\mu_a}\ge n^{(1-o(1))d}                     \tag{5.29}
\]

uniformly in the displayed range.  Also `binom(v,u)<=a^(d-e)` and
`k_u,k_v<=n/(a-D)`.  The `d=0` term is at most
`n^2/[(a-D)^2 mu_a]`; every `d>=1` term is smaller by
`n^(-1+o(1))`.  Summation over `D^2=n^o(1)` choices proves (5.24), and
(5.21) proves (5.22). \(\square\)

The dense exact-common endpoint has an exact multitype identity.  For a
subprofile `ell=(ell_u)` of common parts, let

\[
 m_\ell=\sum_u u\ell_u,
 \quad L_\ell=\sum_u\ell_u,
 \quad M_\ell=\sum_u\binom u2\ell_u,                       \tag{5.30}
\]

and let

\[
 Y^{\rm sgn}_\ell
 =2^{L_\ell}
  \frac{n!}{(n-m_\ell)!\prod_u(u!)^{\ell_u}\ell_u!}
  2^{-M_\ell}                                              \tag{5.31}
\]

be the signed first moment of partial partitions with profile `ell`.  The
total weighted incidence of selecting exactly this vector of common slots
(using the full common-cell rewards, hence upper-bounding the increment
expansion) is

\[
\boxed{
 A_\ell^{\rm common}
 =\frac{\prod_u\binom{k_u}{\ell_u}^{2}}
        {Y^{\rm sgn}_\ell}.}                               \tag{5.32}
\]

Indeed, choose the common slots on both sides, pair equal-size choices, use
the exact probability that the selected blocks coincide, and award
`2^(binom(u,2)-1)` per block; all factorials cancel to (5.32).  Equivalently,
if `r=k-ell` is the residual profile, then

\[
 A_\ell^{\rm common}
 =\left(\prod_u\binom{k_u}{\ell_u}\right)
   \frac{Z^{\rm sgn}_{r}(n-m_\ell)}
        {Z^{\rm sgn}_{k}(n)}.                              \tag{5.33}
\]

For the `(alpha-2)` optimal profile, `mu_a>=n^(1.05)` with enormous room.
Lemma 7.20(d) of the tame-colourings paper therefore says that, for every
fixed `delta_0>0` and every subprofile with vertex mass in
`[delta_0,1-delta_0]`,

\[
 Y^{\rm ord}_\ell
 \ge e^{C_{\delta_0}n}
       \prod_u\binom{k_u}{\ell_u}^{2}.                     \tag{5.34}
\]

Since `Y_sgn=2^(L_ell)Y_ord`, (5.32) and (5.34) give

\[
 \sum_{\substack{\ell:\ 
       \delta_0\le m_\ell/n\le1-\delta_0}}
 A_\ell^{\rm common}=e^{-\Omega_{\delta_0}(n)}.            \tag{5.35}
\]

The number of subprofile vectors is only
`exp(O(D ln n))=exp(o(n))`, so it is absorbed in (5.35).  Thus every
macroscopic exact partial diagonal is rigorously killed by the published
partial-profile theorem; this is the mixed-profile analogue of the equitable
partial-diagonal identity.

What is **not** yet implied by the source theorem is uniformity in a cutoff
`delta_0=delta_0(n)->0`, nor a complete comparison of dense off-size
containment matchings with the exact common vectors in (5.32).  A full
specialization of the raw signed moment follows if the chosen integer
profile additionally satisfies the following endpoint condition:

\[
 \sum_{\ell:\ m_\ell/n\notin[\delta_0,1-\delta_0]}
 \frac{\prod_u\binom{k_u}{\ell_u}^{2}}
      {Y^{\rm sgn}_\ell}
 \exp\{D_{\rm off}(\ell)\}
 \le\exp\{o(n/\log^4n)\},                                 \tag{5.36}
\]

for some fixed small `delta_0`, where `D_off(ell)` is the logarithm of the
exact factorial decoration sum obtained by replacing selected common cells
by unequal-size containments and near-containments.  Proposition 5.5 proves
`D_off=o(n/log^4n)` for every moderate skeleton, and
`RESIDUAL_ATTACHMENT.md` proves that residual cycles add only
`o(n/log^4n)` for **all** skeletons.  Condition (5.36) is therefore the exact
remaining dense-endpoint hypothesis; it is a bare multitype matching
statement, not a residual-cycle problem.

In particular, the hypotheses already verified are:

- the high one-polymer activity is `n^o(1)` by (5.22);
- every fixed-mass partial diagonal is exponentially negligible by (5.35);
- the full diagonal is `1/Z_k^sgn`, so it is at most one when the chosen
  signed first moment is at least one, and is `o(1)` if that first moment
  tends to infinity.

Only the vanishing-mass and near-full dense endpoint in (5.36), together
with its off-size decorations, is not closed by the currently stated
profile theorems.

#### Separation of the proved activity bound from the open dense sum

Equation (5.22) is a bound on the exact **one-polymer activity** `B_{>R}`.
It implies the required skeleton bound through Proposition 5.4 only while
the exposed mass is `J=o(n/log^2 n)`.  It must not be exponentiated through
the whole matching range: for dense skeletons the correction
`n^J/(n)_J` is macroscopic, and the full/partial diagonal identities, rather
than independent polymer activities, control the cancellation.  Equations
(5.32)--(5.35) close the fixed-positive-mass exact-common range.  Equation
(5.36), covering vanishing mass, near-full mass, and their off-size
decorations, remains open.  The profile-independent theorem in
`RESIDUAL_ATTACHMENT.md` removes residual cycles from this list but does not
bound the bare matching sum itself.

#### Does four-size support close the endpoint?

Suppose, conditionally, that a complete profile can be chosen with support

\[
 \{\alpha-2,\alpha-3,\alpha-4,\alpha-5\}.                  \tag{5.37}
\]

Then the proof of Proposition 5.5 sharpens to

\[
 B_{>\lfloor a/2\rfloor}
 =O\!\left(\frac{n^2}{a^2\mu_a}+n^{-1+o(1)}\right)
 =n^{o(1)},                                                 \tag{5.38}
\]

with no growing-support factor.  The vector `ell` in (5.32) has only four
coordinates, so there are at most `O(n^4)` exact-common subprofiles, and all
off-size containments live in a fixed `4 by 4` type matrix.  This materially
improves the sufficient sum (5.36): it turns it into a finite-dimensional
endpoint saddle problem and removes the `exp(O(sqrt(ln n) ln n))` count of
possible subprofile vectors.

It does **not**, by itself, prove (5.36).  Polynomially many vectors can
still contain an exponentially large vanishing-mass or near-full term, and
the falling-factorial correction couples dense containments.  In addition,
truncating the discrete-Gaussian optimum to the four sizes in (5.37) changes
the complete-profile entropy and mean constraints; a re-optimized integer
profile must still be shown to retain a signed first moment large enough for
the desired `n/log^3 n` displacement.  Thus four-size support is a genuine
finite-dimensional simplification, not a completed dense-skeleton proof.

## 6. What is proved, and the exact remaining regimes

**Subsequent closure.**  This section records the boundary at the time this
component was derived.  For the exact four-size midpoint profile, the
vanishing/near-full diagonal terms are later proved in
`FOUR_SIZE_PARTIAL_RATES.md`, and all unequal-type dense transports and
decorations are later proved in `DENSE_FOUR_TYPE_MATCHING.md`.  Thus the
"unclosed" labels below are historical within this note, not the final
dossier status.

The preceding results give the following rigorous decomposition.

1. **Small and intermediate scrambled cells.**  For every nonconstant
   profile with maximum part `O(log n)`, the range under (3.2) has entire
   normalized signed contribution `1+O(log^4 n/n)`.  For near-optimal
   profiles Corollary 3.1 extends this through multiplicity `floor(U/2)`;
   the omitted cells form a matching.  Triple cells are controlled
   multiplicatively, and the full capped cycle-space factor is included.
2. **Exact common parts.**  They force the monomer--dimer-type lower bound
   (4.2).  Whenever `k_u^2/mu_u` diverges but is `o(k_u)`, the raw normalized
   moment is exponentially large as in (4.5).
3. **Fixed-distance near copies.**  Their individual weighted incidence is
   smaller than the exact common incidence by (5.2), in particular by
   `Theta(log^3 n/n)` per one-vertex perturbation in the chromatic window.
4. **Residual attachments.**  Proposition 5.4 bounds every moderate high-cell
   skeleton after arbitrary residual double/triple and cycle attachments.
   The stronger profile-independent result in `RESIDUAL_ATTACHMENT.md`
   controls those attachments for all skeleton sizes at logarithmic budget.
   Residual topology is therefore no longer the mixed-profile bottleneck.
5. **The `(alpha-2)` optimal profile.**  Its exact high one-polymer activity
   is `n^o(1)` by Proposition 5.5, and every fixed-positive-mass exact partial
   diagonal is exponentially negligible by (5.35).
6. **Unclosed dense bare matching endpoints.**  The remaining terms are the
   vanishing-mass and near-full vectors in (5.36), especially their
   unequal-size containment decorations.  No uniform upper bound is proved
   for these dense bare matchings.  The target supplied by rare-event
   amplification is `ln R_zeta=o(n/log^4 n)`.

Therefore the exact signed factor makes the structural truncation unnecessary
for the bounded-cell portion of the scrambled calculation.  It does **not**
currently make a truncated witness unnecessary for the full theorem.  The
raw signed count has the rigorous exponential common-part lower bound (4.5),
and the above argument does not upper-bound the dense bare endpoint in item
6.  A proof using the raw witness needs the finite-dimensional
partial-diagonal/containment estimate (5.36), or an equivalent
profile-dependent treatment.  The existing `B,C,D` truncation supplies
structural control by allowing only polylogarithmically many exceptional
large blocks, but the direct signed calculation has now reduced the required
replacement to a bare matching problem rather than a residual-cycle problem.

This conclusion is deliberately limited: (4.5) rules out a bounded raw
second-moment ratio, but Corollary 4.2 shows that its unavoidable exponent is
still `o(n/log^4 n)` at the minimal phase and is therefore compatible with
the sharp rare-event amplification budget for an `n/log^3 n` gap.  It does
not prove that truncation is mathematically necessary, nor that a raw-count
proof is impossible.  It proves only that the signed local factor by itself
has not removed the large-cell upper-bound obligation.

## 7. Adversarial checks

- **Double cells.**  A double cell has `w=1`; its `w-1` contribution is zero.
  A forest of double cells has `beta=0`, hence factor one.  Counting every
  double as a factor two would reproduce the ordinary-colouring moment and
  is incorrect.
- **Cycles.**  `2^beta` is exactly the number of even subgraphs, not merely an
  upper bound.  Bipartiteness rules out triangles, so the first cycle term is
  a four-cycle and has the `O(U^12/n^4)` scale in (3.14)--(3.16).
- **Triples.**  A triple has factor four, but its increment over the double-
  forest baseline is three.  The proof uses the threshold increments
  `Delta_x`, avoiding a spurious extra factor on cells already selected by an
  even subgraph.
- **Nonconstant degrees.**  All degree dependence is kept in
  `theta_ab=e s_at_b/n`.  Bounds (3.13) and (3.16) use
  `sum s_a^j<=U^(j-1)n`; no equitable-profile substitution is hidden.
- **Large expansion sets.**  Lemma 2.1 uses `(n)_m>=(n/e)^m`, so the expansion
  does not silently assume `m=o(sqrt n)`.
- **Common-part normalization.**  The exact local activity is
  `G_u/C(n,u)=1/(2mu_u)`.  The factor `1/2` is the signed compatibility
  penalty for an isolated common part.
- **Activity versus dense sum.**  `B_{>R}=n^o(1)` is a one-polymer statement.
  It does not control dense skeletons after `n^J/(n)_J` becomes macroscopic;
  those require (5.32) and the still-open endpoint estimate (5.36).
- **Four sizes.**  Restricting to four adjacent sizes makes (5.36)
  finite-dimensional and removes a growing vector count, but it neither
  proves the endpoint saddle bound nor preserves the optimal signed first
  moment automatically.
- **Scope.**  Theorem 3.1 is an overlap-sum theorem, not a first-moment
  existence result.  Proposition 4.1 is a lower bound on the normalized
  moment, not evidence against the existence of cocolourings.
