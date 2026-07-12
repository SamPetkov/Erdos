# Residual attachments to a matching of large overlap cells

**Status.**  The residual-attachment lemma requested in
`SIGNED_EQUITABLE_SECOND_MOMENT.md`, Section 6, is proved below.  The proof
keeps the exact configuration-model law and sums the full even-subgraph
factor.  In particular, residual double and triple cells are allowed to join
arbitrarily many exposed large cells; they are not treated as independent.

For an equitable chromatic-scale profile with signed first moment at least
one, the lemma combines with the exact partial-diagonal calculation and the
near-copy calculation already in `SIGNED_EQUITABLE_SECOND_MOMENT.md` to give

\[
 \boxed{\log R_\zeta=o(n/\log ^4 n).}                       \tag{0.1}
\]

Thus the *equitable* residual-cycle obligation in (6.6) of that note is
closed at the logarithmic accuracy needed by the Alon--Scott amplification.
For a nonconstant profile the attachment estimate itself remains valid, but
the bare matching sum of common and containment cells is profile-dependent
and is not bounded in this note.  That was the precise remaining
mixed-profile obligation; for the four-size profile used in the proposed
resolution it is subsequently closed in `DENSE_FOUR_TYPE_MATCHING.md`.

Throughout this note, `log` means `log_2`, while `ln` is the natural
logarithm.

## 1. Canonical exposure and the exact residual law

Let the row and column slot degrees be

\[
 (s_a)_{a\in A},\qquad (t_b)_{b\in B},\qquad
 \sum_a s_a=\sum_b t_b=n,\qquad
 U=\max\{s_a,t_b\}.                                       \tag{1.1}
\]

Put

\[
 R=\lfloor U/2\rfloor.                                     \tag{1.2}
\]

In an overlap matrix, the cells of multiplicity greater than `R` form a
matching: two such cells cannot meet one row or one column, because
`2(R+1)>U`.  Denote this canonical matching by

\[
 M=\{a_i b_i:1\le i\le h\},\qquad r_{a_i b_i}=j_i>R,
 \qquad J=\sum_i j_i.                                      \tag{1.3}
\]

After exposing all pairs in these cells, the residual configuration model
has total degree

\[
 N=n-J                                                       \tag{1.4}
\]

and degrees

\[
 d_{a_i}=s_{a_i}-j_i,\quad d'_{b_i}=t_{b_i}-j_i,
 \qquad d_a=s_a,\quad d'_b=t_b                              \tag{1.5}
\]

at unexposed endpoints.  Conditional on the exposed stub pairs, the
remaining matching is uniform.  The exact incidence factor for the exposed
cells is

\[
 \pi(M,\mathbf j)=
 \frac{\prod_{i=1}^h(s_{a_i})_{j_i}(t_{b_i})_{j_i}}
      {(n)_J\prod_{i=1}^h j_i!}.                            \tag{1.6}
\]

To recover the event that (1.3) is the *canonical exact* large-cell
skeleton, the residual matching is restricted to have no pair in the cells
`a_i b_i` and to have every other multiplicity at most `R`.  This
restriction is important for uniqueness, but it can be retained throughout
the upper bound.

Recall

\[
 g(0)=g(1)=g(2)=1,\qquad g(x)=2^{\binom x2-1}\quad(x\ge3).
                                                                    \tag{1.7}
\]

Let `H_res` be the multiplicity-at-least-two support of the residual
matching.  Since the high cells are exact, the exact factor on this event is

\[
 A_\zeta(r)=
 \left(\prod_{i=1}^h g(j_i)\right)
 \left(\prod_{e}g(r'_e)\right)
 2^{\beta(M\cup H_{\rm res})}.                              \tag{1.8}
\]

Define the residual attachment factor

\[
 \mathcal A(M,\mathbf j)=
 \mathbb E_{\mathbf d,\mathbf d'}\!\left[
  \left(\prod_e g(r'_e)\right)2^{\beta(M\cup H_{\rm res})}
  \mathbf1_{\mathcal E(M,\mathbf j)}\right],              \tag{1.9}
\]

where `E(M,j)` is the preceding no-backtracking and cap event.  Summing
canonically over skeletons gives the exact decomposition

\[
 R_\zeta=
 \sum_{(M,\mathbf j)}
   \pi(M,\mathbf j)\left(\prod_i g(j_i)\right)
   \mathcal A(M,\mathbf j).                                \tag{1.10}
\]

There is no overcount in (1.10): every overlap matrix has one set of cells
whose multiplicity is greater than `R`; within each realization of that
matrix by a stub matching, the exposed stub pairs are unique.  The factor
`pi` already sums all stub realizations, each exactly once.

## 2. The attachment lemma

### Theorem 2.1 (uniform residual attachment bound)

Assume that for some fixed `epsilon_0>0`,

\[
 U\le(4-\epsilon_0)\log n.                                 \tag{2.1}
\]

Uniformly over the two profiles in (1.1), every canonical high-cell
skeleton in (1.3), and all its multiplicities,

\[
 \boxed{
  \sup_{M,\mathbf j}\ln\mathcal A(M,\mathbf j)
  =o(n/\log ^4 n).}                                        \tag{2.2}
\]

More explicitly, if `N>=n/(ln n)^6`, then for an absolute constant `C`,

\[
 \ln\mathcal A(M,\mathbf j)
 \le C\left\{
       \frac{U^4}{N}+n\tau^4+h\tau
      \right\},
 \qquad \tau=C\frac{U^3}{N}.                              \tag{2.3}
\]

Consequently the right side of (2.3) is `O((ln n)^8)`.  If instead
`N<n/(ln n)^6`, then the deterministic estimate

\[
 \ln\mathcal A(M,\mathbf j)
 \le\frac{\ln2}{2}UN
 =O(n/(\ln n)^5)                                           \tag{2.4}
\]

holds.  Both bounds are `o(n/(ln n)^4)`.

#### Proof: the large-residual regime

Suppose first that

\[
 N\ge n/(\ln n)^6.                                         \tag{2.5}
\]

Then `log N=log n-O(log log n)`, so (2.1) implies

\[
 U\le(4-\epsilon_0/2)\log N                                \tag{2.6}
\]

for all sufficiently large `n`.  We now repeat the capped threshold
expansion of `SIGNED_PROFILE_OVERLAP.md`, but retain the deterministic
matching `M` inside the cycle space.

For every residual cell not in `M`, set

\[
 \theta_{ab}=\frac{e d_a d'_b}{N},qquad
 \lambda_{ab}=\sum_{x=3}^{R}
    \Delta_x\frac{\theta_{ab}^x}{x!},qquad
 q_{ab}=\frac{\theta_{ab}^2}{2}+\lambda_{ab},              \tag{2.7}
\]

where `Delta_x=g(x)-g(x-1)`.  Set
`lambda_{a_i b_i}=q_{a_i b_i}=0`, as required by the
no-backtracking part of `E(M,j)`.  The endpoint argument in Corollary 3.1 of
`SIGNED_PROFILE_OVERLAP.md` applies because of (2.6) and gives, uniformly,

\[
 \lambda_{ab}\le C\theta_{ab}^3,qquad
 q_{ab}\le C\theta_{ab}^2.                                \tag{2.8}
\]

If `R<3`, the `lambda` sum is empty; if `R>=3` remains bounded, the same
estimate follows directly from its finitely many terms.  Thus no implicit
lower-growth assumption on `U` is being used here.

The exact configuration-model factorial estimate therefore gives

\[
 \Lambda:=\sum_{a,b}\lambda_{ab}
 \le \frac{C}{N^3}
       \left(\sum_a d_a^3\right)
       \left(\sum_b(d'_b)^3\right)
 \le C\frac{U^4}{N}.                                      \tag{2.9}
\]

Furthermore,

\[
 \max_a\sum_bq_{ab}\ \vee\
 \max_b\sum_aq_{ab}
 \le C\frac{U^3}{N}=:\tau.                               \tag{2.10}
\]

Indeed, `sum_b(d'_b)^2<=UN`, and the row estimate in (2.10) is at most
`C d_a^2 U/N`; the column estimate is identical.  In the range (2.5),
`tau=o(1)`.

Use the cycle-space identity

\[
 2^{\beta(M\cup H_{\rm res})}
 =\#\{F\subseteq M\cup H_{\rm res}:F\text{ is even}\}.   \tag{2.11}
\]

Fixing `F`, expanding the local thresholds, and applying the joint
factorial bound to all chosen residual cells gives

\[
 \mathcal A(M,\mathbf j)
 \le e^\Lambda
    \sum_{F\ {\rm even}}
       \prod_{e\in F\setminus M}q_e.                       \tag{2.12}
\]

This is the step that retains all attachments.  A residual triple selected
both by its local increment and by an even subgraph is represented by the
alternative threshold terms in (2.7), exactly as in the proof of the
bounded-cell theorem; no product of marginal expectations is taken.

Choose one edge-disjoint simple-cycle decomposition for each even graph.
Dropping edge-disjointness gives

\[
 \sum_{F\ {\rm even}}\prod_{e\in F\setminus M}q_e
 \le \exp\left\{
       \sum_{C\ {\rm simple\ cycle}}
       \prod_{e\in C\setminus M}q_e
      \right\}.                                            \tag{2.13}
\]

We bound the cycle exponent without deleting cycles that touch `M`.

For cycles containing no edge of `M`, orient a cycle and mark a starting
row vertex.  Dropping simplicity and the closing constraint turns it into a
residual closed walk.  By (2.10), the total weight of all walks of length
`ell` from a fixed start, with the endpoint unrestricted, is at most
`tau^ell`.  Bipartite cycles have length at least four, and there are fewer
than `n` possible row starts.  Hence

\[
 \sum_{C:C\cap M=\varnothing}\prod_{e\in C}q_e
 \le \frac{n\tau^4}{1-\tau^2}.                             \tag{2.14}
\]

For a cycle meeting `M`, mark and orient one of its matching edges.  After
cutting at all matching edges, the cycle is a sequence of nonempty residual
walks separated by deterministic matching edges.  Formally, the matching is
a partial-permutation operator of row-sum norm one: the endpoint of each
residual walk determines the next matching edge, if one exists.  Thus no
fresh factor `h` is introduced between successive segments.  A residual
segment has
total weight at most

\[
 a:=\sum_{\ell\ge1}\tau^\ell=\frac{\tau}{1-\tau}.          \tag{2.15}
\]

There are at most `2h` oriented choices for the marked first matching edge.
Dropping endpoint, parity, simplicity, distinctness, and closure constraints
only enlarges the sum.  Therefore, once `tau<1/3`,

\[
 \sum_{C:C\cap M\ne\varnothing}
       \prod_{e\in C\setminus M}q_e
 \le 2h\sum_{r\ge1}a^r
 \le C h\tau.                                               \tag{2.16}
\]

Equations (2.9), (2.12)--(2.16) prove (2.3).  Finally, every high cell uses
more than `U/2` stubs, so

\[
 h<2n/U.                                                     \tag{2.17}
\]

Under (2.5), `h tau=O(nU^2/N)=O((ln n)^8)`, while the other
terms in (2.3) are smaller.  This proves the asserted large-residual bound.

#### Proof: the small-residual regime

Suppose now that `N<n/(ln n)^6`.  The matching `M` is a forest.  Adding
the edges of `H_res` one at a time can increase cycle rank by at most one,
so

\[
 \beta(M\cup H_{\rm res})\le |E(H_{\rm res})|\le N/2.      \tag{2.18}
\]

Also

\[
 \sum_e\binom{r'_e}{2}
 \le\frac{U-1}{2}\sum_e r'_e
 =\frac{U-1}{2}N.                                          \tag{2.19}
\]

Using (1.7), (2.18), and (2.19), pointwise on every residual matching,

\[
 \left(\prod_eg(r'_e)\right)2^{\beta(M\cup H_{\rm res})}
 \le2^{UN/2}.                                               \tag{2.20}
\]

Taking expectations proves (2.4), and completes the proof. \(\square\)

### What (2.16) counts

The first nontrivial mixed term can be a four-cycle containing two high
matching edges and two residual cross-edges.  It is present in (2.16) with
its exact product `q_{a_i b_j}q_{a_j b_i}`.  A cycle containing one high
edge and a three-edge residual path is also present.  Longer residual paths,
multiple high edges in one cycle, intersecting cycles, triple cells on a
path, and several cycles incident with the same high edge are all included
by (2.12)--(2.16).  The loss is deliberate overcounting by residual walks,
not an independence assumption.

## 3. Summing the equitable high-cell skeletons

The attachment lemma is profile-independent at the stated scale.  For an
equitable profile the remaining bare matching sum can also be completed.
Assume

\[
 n=ks,\qquad s=(2+o(1))\log n,                              \tag{3.1}
\]

and let

\[
 Z_k=2^k\frac{n!}{(s!)^k k!}
          2^{-k\binom s2}                                  \tag{3.2}
\]

be the unordered signed first moment.  Assume `Z_k>=1`.
For \(0\le\ell\le k\), the notation \(Z_\ell\) below means the analogous
first moment on \(\ell s\) vertices partitioned into \(\ell\) size-\(s\)
blocks, with \(Z_0=1\).

### 3.1 Near-exact cells

Call a high cell near-exact if `j=s-d>3s/4`.  For `h` exact common blocks,
the complete bare incidence is

\[
 A_h=\binom kh^2h!
      \frac{(s!)^h(n-hs)!}{n!}
      2^{h(\binom s2-1)}.                                  \tag{3.3}
\]

With `ell=k-h`, exact cancellation gives

\[
 A_h=\binom{k}{\ell}\frac{Z_\ell}{Z_k}.                   \tag{3.4}
\]

The partial-diagonal estimate in Proposition 4.1 of
`SIGNED_EQUITABLE_SECOND_MOMENT.md` says

\[
 \sum_{h=1}^{k-1}A_h=o(1),\qquad A_k=Z_k^{-1}\le1.         \tag{3.5}
\]

For a demand `s-d`, the exact joint factorial incidence relative to a full
block is at most

\[
 \eta_d=
 n^d\frac{\binom sd}{d!}
 2^{-ds+d(d+1)/2}.                                         \tag{3.6}
\]

The factor `n^d` is the exact safe comparison
`(n)_{hs}/(n)_{hs-\sum d_i}<=n^{\sum d_i}`; thus (3.6) does
not replace the joint denominator by independent denominators.  The endpoint
ratio calculation gives

\[
 \epsilon_n:=\sum_{1\le d<s/4}\eta_d=n^{-1+o(1)}.          \tag{3.7}
\]

Consequently the entire near-exact matching expansion is bounded by

\[
 S_{\rm near}
 \le\sum_{h=0}^kA_h(1+\epsilon_n)^h
 \le e^{k\epsilon_n}(2+o(1))
 =\exp\{n^{o(1)}\}.                                        \tag{3.8}
\]

In the refined window

\[
 s=2\log n-2\log\log n+O(1),                              \tag{3.9}
\]

one has `epsilon_n=O(s^3/n)`, and the last bound in (3.8) is
`exp(O(s^2))`.  Equations (3.4)--(3.5) are the first-moment diagonal
suppression: replacing them by a product of one-cell activities would lose
the full and partial diagonal endpoints.

### 3.2 The middle high strip

It remains to insert cells with

\[
 s/2<j\le3s/4.                                              \tag{3.10}
\]

First expose a near-exact skeleton and let `M_0` be its remaining stub mass.
If `M_0>=n/(ln n)^6`, the global factorial bound in that residual
configuration majorizes the full middle matching expansion by

\[
 \exp\{\Xi(M_0)\},
 \qquad
 \Xi(M_0)=k^2\sum_{s/2<j\le3s/4}
   g(j)\frac{(e s^2/M_0)^j}{j!}.                            \tag{3.11}
\]

Uniformly in this range,

\[
 \log_2\left[
 k^2g(j)\frac{(e s^2/M_0)^j}{j!}
 \right]
 \le 2\log n+\frac{j^2}{2}-j\log M_0+O(j\log s)
 \le-c(\log n)^2                                          \tag{3.12}
\]

for some fixed `c>0` and all sufficiently large `n`.  The last inequality
uses `j/(log n) \in [1+o(1),3/2+o(1)]`; the quadratic coefficient
`x^2/2-x` is at most `-3/8+o(1)` on that interval.  Hence

\[
 \Xi(M_0)=2^{-\Omega((\log n)^2)}.                          \tag{3.13}
\]

This argument sums arbitrary simultaneous middle cells with the exact
global falling-factorial majorant.  Their matching constraint is only
dropped after it has made the canonical exposure well defined.

If `M_0<n/(ln n)^6`, all remaining local factors and all topology can
instead be bounded pointwise exactly as in (2.18)--(2.20), at logarithmic
cost `O(sM_0)=O(n/(ln n)^5)`.

### Corollary 3.1 (equitable raw signed moment at the amplification scale)

Under (3.1) and `Z_k>=1`,

\[
 \boxed{
  \ln R_\zeta
  \le O\!\left(\frac{n}{(\ln n)^5}+(\ln n)^8+n^{o(1)}\right)
  =o\!\left(\frac{n}{(\ln n)^4}\right).}                  \tag{3.14}
\]

In the refined window (3.9), the `n^{o(1)}` term in (3.14) can be replaced
by `O((ln n)^2)`.

#### Proof

Use the canonical decomposition (1.10).  Split its high-cell matching into
the near-exact cells and the middle strip.  Equations (3.8) and (3.11)--
(3.13) bound the bare local matching sum when the mass after the first split
is at least `n/(ln n)^6`; the small-mass alternative has cost
`O(n/(ln n)^5)`.  For every resulting complete high skeleton, Theorem 2.1
sums the capped residual local factors and the entire even-subgraph
attachment factor, uniformly.  Multiplying these nonnegative upper bounds
and taking logarithms gives (3.14). \(\square\)

## 4. Mixed profiles: proved part and remaining part

Theorem 2.1 does **not** use equitability.  It applies to any two profiles
with maximum slot size at most `(4-epsilon_0)log n`; this includes residual configurations
after common cells, unequal-size containments, and near-containments have
been exposed above the global half-part threshold.  Therefore residual
cycles cannot by themselves consume the `n/log^4 n` budget.

What does not generalize automatically is Section 3.1.  For a mixed profile,
the bare activity of exact size-`u` common cells is

\[
 (1+o(1))\frac{k_u^2}{2\mu_u},                              \tag{4.1}
\]

and an oriented size-`u`-inside-size-`v` containment has aggregate activity

\[
 \frac{k_uk_v\binom vu}{2\mu_u}.                           \tag{4.2}
\]

The common-cell term can genuinely have logarithm
`Theta(n(ln ln n)^2/(ln n)^{5.385...})`, as proved in
`SIGNED_PROFILE_OVERLAP.md`.  This is still below `n/(ln n)^4`, but a
uniform *upper* summation of all vectors of common and unequal-size
containment cells requires profile-specific first-moment identities.  The
present lemma shows that once such a bare matching sum is controlled, all
residual attachments multiply it by only

\[
 \exp\{o(n/(\ln n)^4)\}.                                   \tag{4.3}
\]

Thus the remaining mixed-profile problem is no longer a cycle-attachment
problem.  It is the explicit monomer--dimer/containment matching sum in
(4.1)--(4.2), together with integer-profile transition control.

### 4.1 Assessment of the four-size `(alpha-2)` profile

Consider the more specific support

\[
 u_i=a-i,\qquad 0\le i\le3,\qquad a=\alpha-2,
 \qquad k_i\asymp k\asymp n/\ln n.                         \tag{4.4}
\]

Here the one-polymer calculation really does improve.  Put `N_0=ln n` and
`q=ln 2`.  The uniform independence-set expansion and the exact ratio

\[
 \frac{\mu_{r-1}}{\mu_r}
 =\frac{r}{n-r+1}2^{r-1}                                  \tag{4.5}
\]

give, uniformly through the independence-number cycle,

\[
 \mu_a\ge c n^2N_0^{2/q-5/2},\qquad
 \frac2q-\frac52=0.385390\ldots .                         \tag{4.6}
\]

Consequently

\[
 \frac{k_0^2}{\mu_a}
 =O\!\left(N_0^{-(2/q-1/2)}\right)=o(1).                  \tag{4.7}
\]

Every decrease of the smaller slot size multiplies `mu_u` by
`Theta(n/N_0)`, while an unequal-size containment in this four-size support
costs at most the factor `binom(v,u)=O(N_0^3)`.  The endpoint and middle-strip
calculations of (3.6) and (3.11) therefore give

\[
 B_{>a/2}:=
 \sum_{i,j}k_ik_j\sum_{x>a/2}
 2\Delta_x\frac{(u_i)_x(u_j)_x}{x!n^x}=o(1).              \tag{4.8}
\]

Thus all bounded-mass and moderate-mass skeletons are harmless.  For
example, for total exposed mass `J<=J_0=o(n/(ln n)^2)`, retaining the exact
falling factorial gives

\[
 \log\sum_{J\le J_0}\text{(bare skeleton weights)}
 \le B_{>a/2}+\frac{J_0^2}{n-J_0}
 =o(n/(\ln n)^4).                                         \tag{4.9}
\]

The four-size hypothesis does **not**, by itself, close the dense endpoint.
The exact obstruction can be displayed as a finite transportation sum.  Let
`L=(ell_ij)_{0<=i,j<=3}` record a matching of endpoint containments, put

\[
 r_i=\sum_j\ell_{ij},\qquad c_j=\sum_i\ell_{ij},\qquad
 x_{ij}=\min(u_i,u_j),\qquad
 J(L)=\sum_{i,j}\ell_{ij}x_{ij}.                          \tag{4.10}
\]

The exact factorial incidence of this endpoint matrix, with its signed local
rewards, is

\[
 \boxed{
 W(L)=
 \frac{\prod_i(k_i)_{r_i}\prod_j(k_j)_{c_j}}
      {\prod_{i,j}\ell_{ij}!}
 \frac{1}{(n)_{J(L)}}
 \prod_{i,j}
 \left[
  \frac{(u_i)_{x_{ij}}(u_j)_{x_{ij}}}{x_{ij}!}
  g(x_{ij})
 \right]^{\ell_{ij}}.}                                    \tag{4.11}
\]

Near-containments replace each `x_ij` in (4.11) by `x_ij-d` and multiply by
the exact ratios analogous to (3.6).  When `L` is diagonal, (4.11) reduces
to the common-subprofile identity

\[
 A_{\boldsymbol\ell}^{\rm common}
 =\frac{\prod_i\binom{k_i}{\ell_i}^{2}}
        {Y_{\boldsymbol\ell}^{\rm sgn}}.                  \tag{4.12}
\]

Hence a published partial-profile lower bound kills diagonal subprofiles of
every fixed positive vertex mass, and the full diagonal is the reciprocal
of the complete signed first moment.  But an off-diagonal `L` in (4.11)
leaves `|u_i-u_j|` residual stubs at each unequal containment.  There is no
identity reducing the resulting dense `4 by 4` transportation matrix to one
partial first moment.  The small value in (4.8) controls the Taylor
coefficient at `L=0`; it does not control the finite-population factor
`n^{J(L)}/(n)_{J(L)}`, which is exponential when `J(L)=Theta(n)`.

Accordingly, the exact still-unproved four-size statement is

\[
 \sum_{L:\,J(L)=\Theta(n)}
   W(L)\,D_{\rm near}(L)
 \le\exp\{o(n/(\ln n)^4)\},                               \tag{4.13}
\]

where `D_near(L)` is the exact near-containment decoration sum.  There are
only polynomially many matrices `L`, but this does not bound an individual
dense term.  Theorem 2.1 proves that residual cycles multiply the left side
of (4.13) by only `exp(o(n/(ln n)^4))`.  Thus (4.13), not residual
attachment and not one-polymer activity, is the precise remaining
four-size obstruction.  A direct entropy analysis of (4.11) may prove it,
but such an analysis is not supplied here.

## 5. Adversarial audit

1. **No factor `2^h` was charged.**  Adding each high edge separately and
   bounding its cycle-rank increment by one would cost `2^h`, far above the
   target.  Equations (2.12)--(2.16) charge a high edge only when residual
   paths actually place it in an even subgraph.
2. **The small-residual estimate charges residual edges, not high edges.**
   Since `M` is a forest, `beta(M union H_res)<=|E(H_res)|<=N/2`; this is why
   (2.4) is `O(UN)` rather than `O(h)`.
3. **The residual matching is not independent across cells.**  The sole
   probability input in (2.12) is the joint falling-factorial bound with
   total degree `N`.  All products arise only after that joint denominator
   has been retained or safely bounded.
4. **The cap is canonical.**  Skeleton cells are exact cells above `U/2`.
   The residual cap and the no-backtracking condition prevent a matrix from
   appearing under several skeletons in (1.10).
5. **Equitable and mixed conclusions differ.**  Corollary 3.1 uses the
   equitable identity (3.4).  Theorem 2.1 is uniform over mixed profiles,
   but it does not assert a mixed-profile upper bound for the bare high-cell
   matching sum.
