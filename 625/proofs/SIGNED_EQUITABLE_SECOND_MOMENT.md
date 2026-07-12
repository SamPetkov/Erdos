# Direct signed second moment for an equitable profile

**Status.**  This note proves the exact configuration-model formulas, a
quantitative `Q=0` typicality theorem, a uniform endpoint bound for every
single large cell, an exact formula and an upper bound for all exact-common
block clusters, and a fixed-distance near-copy comparison.  These results
show that none of the one-cell, exact-diagonal, or partial-diagonal regimes is
an obstruction for an equitable chromatic-scale profile whose signed first
moment is at least one (and a fortiori at least `exp(n^0.99)`).  They also
show that every contribution proved here is far below the
`n/log^4 n` logarithmic second-moment budget supplied by the
Alon--Scott rare-event amplification step.

The note does **not** prove a full uncapped overlap sum.  The remaining term is
now quite specific: simultaneous cells above roughly half a class, joined to
the bounded-cell support through their residual stubs.  A valid proof must
sum those joint clusters rather than infer uniform integrability from the
one-cell estimates below.  No overlap family contradicting the desired bound
was found.

Natural logarithms are denoted by `ln`.  Powers of two and `log_2` are used
where displayed.  Put

\[
 n=ks,\qquad m=\binom{s}{2},\qquad k=n/s,
 \tag{0.1}
\]

and assume throughout the chromatic scale

\[
 s=(2+o(1))\log _2 n=\left(\frac{2}{\ln2}+o(1)\right)\ln n.
 \tag{0.2}
\]

There are no singleton parts.

## 1. Exact overlap law and the signed exponent

Let `P=(V_1,...,V_k)` and `P'=(W_1,...,W_k)` be independent uniform
ordered equitable partitions and set

\[
 r_{ab}=|V_a\cap W_b|.
 \tag{1.1}
\]

Then

\[
 p(r)=\frac{(s!)^{2k}}{n!\prod_{a,b}r_{ab}!},
 \tag{1.2}
\]

over the nonnegative integer matrices with all row and column sums `s`.
Equivalently, `r` is the multiplicity matrix of the uniform bipartite
configuration model with `k` row vertices and `k` column vertices, all of
degree `s`.

Let `H=H(r)` be the simple bipartite graph whose edges are the cells with
`r_ab>=2`.  For an edge `e=ab`, write

\[
 w_e=\binom{r_{ab}}2,
 \qquad W=\sum_{e\in E(H)}w_e,
 \qquad \beta(H)=|E(H)|-|V(H)|+c(H).
 \tag{1.3}
\]

The exact sign-summed one-graph factor is

\[
 A_\zeta(r)=2^{W+c(H)-|V(H)|}=2^{Q(r)},
 \tag{1.4}
\]

where

\[
 \boxed{
 Q(r)=\sum_{e\in E(H)}\left(\binom{r_e}{2}-1\right)+\beta(H).}
 \tag{1.5}
\]

Thus the normalized signed second moment is

\[
 R_\zeta=\mathbb E_p2^{Q(r)}.
 \tag{1.6}
\]

In particular, an isolated double cell has exponent zero, as does every
forest consisting only of double cells.  This cancellation is the main
difference from the ordinary-colouring factor `2^W`.

### Lemma 1.1 (joint factorial moments)

For distinct cells `e`, prescribe nonnegative integers `d_e`, and put

\[
 D=\sum_e d_e,\qquad
 D_a=\sum_{e\ni a,\ a\text{ a row}}d_e,\qquad
 D'_b=\sum_{e\ni b,\ b\text{ a column}}d_e.
\]

Then

\[
 \boxed{
 \mathbb E_p\prod_e\binom{r_e}{d_e}
 =\frac{\prod_a(s)_{D_a}\prod_b(s)_{D'_b}}
        {(n)_D\prod_e d_e!}.}
 \tag{1.7}
\]

Here `(x)_d=x(x-1)...(x-d+1)`.  To prove (1.7), select the required row
and column stubs, biject the selected stubs inside each cell, and divide by
the `(n)_D` possible ordered images of the selected row stubs.  Notice that
(1.7), unlike independent-cell heuristics, retains both degree constraints.

## 2. Typical overlaps have exactly `Q=0`

### Proposition 2.1 (triple and cycle witnesses)

Uniformly under (0.2),

\[
 \Pr(Q>0)=O\!\left(\frac{s^4}{n}\right),
 \tag{2.1}
\]

and more precisely the probability of a triple cell is

\[
 \Pr(\max_{a,b}r_{ab}\ge3)
 \le \frac{k^2(s)_3^2}{6(n)_3}
 =O\!\left(\frac{s^4}{n}\right),
 \tag{2.2}
\]

whereas the probability that `H` contains a cycle while all cells have
multiplicity at most two is

\[
 O\!\left(\frac{s^{12}}{n^4}\right).
 \tag{2.3}
\]

#### Proof

If some cell has multiplicity at least three, the first sum in (1.5) is
positive.  Markov's inequality and (1.7) with one demand `d=3` give (2.2).

If every cell has multiplicity at most two, the first sum in (1.5) is zero,
so `Q>0` exactly when `H` contains a cycle.  A simple bipartite cycle of
length `2 ell` uses `ell` row vertices, `ell` column vertices and `2 ell`
double cells.  There are at most

\[
 \frac{(k)_\ell^2}{2\ell}
\]

such cycles.  Applying (1.7) with demand two on every cycle cell gives the
union-bound term

\[
 \frac{(k)_\ell^2}{2\ell}
 \frac{(s)_4^{2\ell}}{2^{2\ell}(n)_{4\ell}}.
 \tag{2.4}
\]

Since `ell<=k=n/s` and `s -> infinity`, uniformly
`(n)_{4 ell} >= [n(1-4/s)]^{4 ell}`.  Hence (2.4) is at most a constant
times

\[
 \frac1\ell\left[(1+o(1))\frac{s^6}{4n^2}\right]^\ell.
\]

Summing from `ell=2` proves (2.3), and (2.1) follows.  \(\square\)

Proposition 2.1 is a probability statement, not yet a moment statement:
rare matrices can have enormous `2^Q`.  Sections 3--5 address the dangerous
endpoints explicitly.

## 3. The full one-cell energy has only endpoint maxima

For `3<=j<=s`, define the signed weighted factorial activity

\[
 b_j=k^2 2^{\binom j2-1}
       \frac{(s)_j^2}{j!(n)_j}.
 \tag{3.1}
\]

This majorizes the sum over all cells of the contribution obtained by
selecting a `j`-subset in that cell and awarding it the signed local factor.
Its consecutive ratio is exact:

\[
 \boxed{
 \frac{b_{j+1}}{b_j}
 =\frac{2^j(s-j)^2}{(j+1)(n-j)}.}
 \tag{3.2}
\]

For `j<=s-8`, the ratios in (3.2) are increasing, because

\[
 \frac{(b_{j+2}/b_{j+1})}{(b_{j+1}/b_j)}
 =2\left(\frac{s-j-1}{s-j}\right)^2
   \frac{j+1}{j+2}\frac{n-j}{n-j-1}>1.
 \tag{3.3}
\]

For the remaining seven indices, (0.2) gives `b_{j+1}/b_j>1` for all
large `n`.  Consequently `(b_j)` decreases and then increases; it has no
interior maximum.  In particular,

\[
 \sum_{j=3}^s b_j\le s(b_3+b_s),
 \tag{3.4}
\]

where

\[
 b_3=O(s^4/n),\qquad
 b_s=\frac{k^2}{2\mu_s},\qquad
 \mu_s=\binom ns2^{-m}.
 \tag{3.5}
\]

The factor `1/2` in `b_s` is the exact signed compatibility penalty.

### Proposition 3.1 (the first moment kills the large endpoint)

Let

\[
 Z_j=2^j\frac{(js)!}{(s!)^j j!}2^{-jm}
 \tag{3.6}
\]

be the signed first moment for an equitable partition of `js` vertices into
`j` unordered signed blocks of size `s`.  If `Z_k>=1`, then

\[
 \boxed{
 b_s\le
 k\left(\frac{(k!)^{1/k}}{k}\right)^{s-1}Z_k^{-1/k}
 \le k\exp\{-s+1+o(1)\}.}
 \tag{3.7}
\]

Under (0.2), this is

\[
 b_s\le n^{-(2/\ln2-1)+o(1)}=n^{-1.885\ldots+o(1)}.
 \tag{3.8}
\]

Therefore

\[
 \sum_{j=3}^s b_j
 =O(s^5/n)+n^{-1.885\ldots+o(1)}=o(1).
 \tag{3.9}
\]

#### Proof

Put `mu_i=binom(is,s)2^{-m}`.  Telescoping the successive choices of
blocks gives

\[
 Z_k=\frac{2^k}{k!}\prod_{i=1}^k\mu_i.
 \tag{3.10}
\]

For `i<=k`, factor by factor,

\[
 \frac{\mu_i}{\mu_k}
 =\prod_{a=0}^{s-1}\frac{is-a}{ks-a}
 \le(i/k)^s.
 \tag{3.11}
\]

Thus

\[
 Z_k\le
 \frac{(2\mu_k)^k}{k!}
 \left(\frac{k!}{k^k}\right)^s.
 \tag{3.12}
\]

Solving (3.12) for `mu_k` and substituting in
`b_s=k^2/(2 mu_k)` proves the first inequality in (3.7).  Stirling's
upper bound for `(k!)^(1/k)` proves the second.  Equations (3.8)--(3.9)
then follow from (0.2), (3.4), and (3.5).  \(\square\)

This proves genuine weighted integrability for one selected high cell.  It
does not license replacing an expectation of a product by a product of
expectations; that is exactly the joint issue isolated in Section 6.

## 4. Exact common blocks and every partial diagonal

For `0<=t<=k`, let `A_t` be the total weighted incidence obtained by choosing
a matching of `t` row--column slot pairs, requiring every chosen pair to be
an exact common block, and assigning the full local reward `2^(m-1)` to each.
The configuration model gives

\[
 A_t=\binom kt^2t!\,
      \frac{(s!)^t(n-ts)!}{n!}\,2^{t(m-1)}.
 \tag{4.1}
\]

Writing `j=k-t`, direct cancellation with (3.6) yields the useful exact
identity

\[
 \boxed{
 A_t=\binom{k}{j}\frac{Z_j}{Z_k},\qquad j=k-t.}
 \tag{4.2}
\]

In particular, `A_0=1` and `A_k=1/Z_k`.  Formula (4.2) also audits the
ordering convention: summing the `k!` ordered diagonal matrices gives the
inverse of the **unordered** signed first moment.

### Proposition 4.1 (all nontrivial partial diagonals are negligible)

Assume, more generally, that for some fixed `epsilon>0`,

\[
 s\ge(2+\epsilon)\ln k
 \tag{4.3}
\]

and `Z_k>=1`.  Then

\[
 \sum_{t=1}^{k-1}A_t=o(1),
 \qquad A_k=Z_k^{-1}.
 \tag{4.4}
\]

This applies to (0.2), since `2/ln2=2.885...`.

#### Proof

Let `x=j/k`.  Stirling's formula, with its remainder kept in the four large
factorials, gives uniformly for `1<=j<=k`

\[
 \ln Z_j-x\ln Z_k
 =xk(s-1)\ln x+\frac{1-x}{2}\ln s+O(1).
 \tag{4.5}
\]

Using `ln binom(k,j)<=k H(x)`, where
`H(x)=-x ln x-(1-x)ln(1-x)`, equations (4.2), (4.5), and
`ln Z_k>=0` imply

\[
 \ln A_t
 \le k\{x(s-2)\ln x-(1-x)\ln(1-x)\}+O(\ln s).
 \tag{4.6}
\]

If `x<=1/2`, use `-(1-x)ln(1-x)<=x` and `ln x<=-ln2`; the right side is
at most `-c_epsilon js+O(ln s)`.  If `x>=1/2`, use
`-x ln x>=(1-x)/2` and
`-ln(1-x)<=ln k`; (4.3) makes the right side at most
`-c_epsilon t ln k+O(ln s)`.  Both resulting geometric sums tend to zero.
The endpoint `j=0` is (4.2) with `Z_0=1`.  \(\square\)

For the exact expansion of common-block factors one uses
`2^(m-1)-1` instead of `2^(m-1)`.  Hence (4.1)--(4.4) are upper bounds for
that entire monomer--dimer expansion, not merely lower bounds on selected
terms.

If `Z_k>=exp(n^0.99)`, the full diagonal is at most `exp(-n^0.99)`, and all
the estimates above only improve.

## 5. Near copies are suppressed relative to common blocks

For one row slot and one column slot, the hypergeometric identity

\[
 \Pr(r=s-d)=\frac{\binom sd\binom{n-s}d}{\binom ns}
 \tag{5.1}
\]

gives the exact weighted ratio

\[
 \boxed{
 \frac{2^{\binom{s-d}{2}-1}\Pr(r=s-d)}
      {2^{\binom s2-1}\Pr(r=s)}
 =\binom sd\binom{n-s}d
 2^{-ds+d(d+1)/2}.}
 \tag{5.2}
\]

For fixed `d>=1`, (0.2) makes (5.2)

\[
 n^{-d+o(1)}.
\tag{5.3}
\]

In the refined chromatic window
`s=2 log_2 n-2 log_2 log_2 n+O(1)`, this sharpens to
`O_d((s^3/n)^d)`.

There is also a joint factorial version.  Select `h` cells with demands
`j_i=s-d_i>3s/4`.  They necessarily form a matching.  Relative to the
factorial incidence of `h` exact common blocks, Lemma 1.1 bounds their total
incidence by the product of

\[
 \eta_{d_i}
 =n^{d_i}\frac{\binom{s}{d_i}}{d_i!}
   2^{-d_i(2s-d_i-1)/2}.
 \tag{5.4}
\]

Indeed, `(n)_{sh}/(n)_{sum j_i}<=n^{sum d_i}` and

\[
 \frac{(s)_{s-d}^2}{(s-d)!s!}
 =\frac{\binom sd}{d!}.
\]

For `1<=d<=s/4`, consecutive ratios in (5.4) and (0.2) show

\[
 \sum_{d=1}^{s/4}\eta_d=n^{-1+o(1)}.
\tag{5.5}
\]

In the refined window just stated, the right side is `O(s^3/n)`.

Thus, if only the large local increments are retained, their complete
matching expansion is majorized by

\[
 \sum_{h=0}^k A_h\left(1+O(s^3/n)\right)^h.
 \tag{5.6}
\]

Proposition 4.1 and the same proof with the additional term
`h O(s^3/n)` show that (5.6) is

\[
 1+o(1)+Z_k^{-1}\exp\{n^{o(1)}\}.
\tag{5.7}
\]

In the refined window, the last exponent can be replaced by `O(s^2)`.

In particular, for `Z_k>=exp(n^0.99)`, even the fully decorated diagonal
term in (5.7) is negligible.  This rules out fixed-distance near copies as
the source of a large equitable second moment.

The estimate (5.7) controls the local high-cell rewards.  It does not yet
include every cycle-space factor created when residual stubs from several
near copies attach to the same bounded-cell component; this distinction is
essential.

## 6. What remains above the bounded-cell theorem

The general bounded-cell expansion in
`research/proofs/SIGNED_PROFILE_OVERLAP.md` proves, for maximum part `s`,

\[
 \mathbb E[2^Q\,\mathbf1_{\{\max r_{ab}\le R\}}]
 =1+O(s^4/n)
 \tag{6.1}
\]

whenever

\[
 2^R e s^2/n\le R.
 \tag{6.2}
\]

At (0.2), the largest such `R` is `s/2-O(1)`.  The one-cell sequence in
Section 3 shows that the few multiplicities between that cap and `s/2` have
exponentially small total activity, while Sections 4--5 control exact and
near-exact matching cells.

The remaining proof obligation can be stated without ambiguity.  Put
`T=floor(s/2)+1`; the cells of multiplicity at least `T` necessarily form a
row--column matching.  For a matching skeleton

\[
 {cal S}=\{(a_i,b_i,j_i):1\le i\le h,\ j_i\ge T\},
 \qquad J=\sum_i j_i,
 \tag{6.3}
\]

expose `j_i` matched stub pairs in every listed cell.  The residual
configuration has total degree `N=n-J`, degrees `s-j_i` at the exposed row
and column endpoints, and degree `s` elsewhere.  Let

\[
 \Delta_j=g(j)-g(j-1),\qquad
 \omega({\cal S})=
 \frac{\prod_i (s)_{j_i}^2}{(n)_J\prod_i j_i!}
 \prod_i 2\Delta_{j_i}.
 \tag{6.4}
\]

The factor two is a valid allowance for the fact that adding one exposed
matching edge can raise cycle rank by at most one.  Delete the exposed edges,
let `H_res` be the multiplicity-at-least-two support generated by the
residual matching, and define

\[
 B_{\cal S}=
 2^{\sum_{e\in H_{res}}(\binom{r_e}{2}-1)+\beta(H_{res})}.
 \tag{6.5}
\]

Allowing residual matches back into an exposed cell only enlarges this
majorant.  A precise sufficient statement is therefore

> **Residual attachment lemma needed.**  After also including the already
> controlled `R<r<T` strip, prove uniformly that the matching-skeleton
> expansion
> \[
>  \sum_{{\cal S}\ {m a\ matching}}
>       \omega({\cal S})\,
>       \mathbb E_{\rm residual}B_{\cal S}
>  \le \exp\{o(n/\log^4 n)\}.
>  \tag{6.6}
> \]
> An equivalent canonical (non-overcounting) threshold expansion is also
> acceptable.  It must remain valid when residual double/triple cells attach
> several exposed high edges to the same component; treating their
> expectations as independent is not sufficient.

For at most `k/2` exposed high cells, the remaining number of stubs is a
constant fraction of `n`, and the factorial expansion behind (6.1) appears
to give the lemma after a constant adjustment.  For more than `k/2` exposed
high cells, (5.2)--(5.7) give strong near-diagonal suppression, but a written
uniform summation of the residual cycle attachments is still missing.  A
first-moment estimate for one cell cannot replace that summation.

No explicit dominant overlap was found.  The three potentially dangerous
families give the following proved outcomes:

* isolated triples and all capped products: `1+O(s^4/n)`;
* exact partial diagonals: `o(1)+Z_k^{-1}`;
* fixed-distance near diagonals: at most the common-block expansion times
  `exp(n^{o(1)})` (and `exp(O(s^2))` in the refined chromatic window), hence
  negligible when `ln Z_k>=n^0.99`.

Even (6.6) would be strictly weaker than a resolution of Problem #625.  It
would control the raw second moment for one equitable signed profile.  One
would still have to construct a suitable integer or mixed profile uniformly
through every profile transition, turn its positive probability into a whp
upper bound for `zeta`, and prove that the resulting number of parts lies a
diverging distance below `chi` for **all** sufficiently large `n`.  Moreover,
the logarithmic bound in (6.6) is deliberately weaker than a bounded second
moment or an `exp(o(n^0.998))` estimate; it is only the scale needed by the
available amplification theorem.

## 7. Comparison with the amplification budget

The Alon--Scott rare-event amplification available in the main investigation
has the following consequence: if a signed profile exists with probability
at least `exp(-Lambda)`, then the resulting additive cost is

\[
 O\left(\frac{\sqrt{n\Lambda}}{\log n}+n^{1/3}\right).
 \tag{7.1}
\]

To preserve a target gap `n/log^3 n`, it is enough that

\[
 \Lambda=o(n/log^4 n).
 \tag{7.2}
\]

Everything proved in this note is much smaller than (7.2): the capped term
has logarithm `o(1)`, and the only diagonal decoration loss is `n^{o(1)}`
(`O(s^2)` in the refined chromatic window).
For comparison, the mixed-profile common-part scale identified elsewhere,

\[
 \Lambda_{\rm common}
 =O\left(\frac{n(\log\log n)^2}{\log^{5.385\ldots}n}\right),
 \tag{7.3}
\]

also satisfies (7.2).  Likewise `n^0.99=o(n/log^4 n)`, since
`log^4 n/n^0.01 -> 0`.

Therefore a full upper bound of the older form `exp(o(n^0.998))` would be
more than sufficient, but it is not necessary.  The exact target for the
residual attachment lemma is the weaker and more natural logarithmic budget
in (7.2).

## 8. Adversarial audit

1. `Q=0` with high probability does not imply `E 2^Q=1+o(1)`; Sections
   3--5 are weighted endpoint checks, and Section 6 keeps the remaining
   uniform-integrability issue explicit.
2. A double cell has factor one unless it participates in cycle rank.  Giving
   every double a factor two incorrectly recovers the ordinary-colouring
   density fluctuation.
3. The signed full-cell activity is `k^2/(2 mu_s)`, not `k^2/mu_s`.
4. The `k!` ordered diagonal matrices together contribute `1/Z_k`, where
   `Z_k` is the unordered signed first moment.  Keeping just one diagonal
   matrix misses this normalization.
5. Formula (4.4) uses the equitable first-moment hypothesis.  It must not be
   transferred to a mixed profile, where a top-size class can have
   `k_u^2/(2 mu_u)` diverging and can force a genuine exponential cluster
   term.
6. Numerical or continuous first-moment displacement is not an existence
   theorem.  Even after the residual attachment lemma is proved, a profile
   with a sufficiently large signed first moment must still be constructed
   uniformly through integer profile transitions.
