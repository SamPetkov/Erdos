# Assigned-profile second moments for the two-graph variable

**Status.**  The finite-\(n\) overlap formulas, the comparisons with ordinary
colourings and signed cocolourings, the binomial-model second-moment obstruction,
and the continuous equitable first-moment displacement are proved below.  The
overlap sum needed to turn the displacement into an existence theorem remains
open.  In particular, this note does **not** prove that \(X\) lies below the
ordinary chromatic threshold, and it does not resolve Erdős Problem #625.

All logarithms are base \(2\) unless \(\ln\) is displayed.  The two graphs
\(G_1,G_2\) are independent copies of \(G(n,1/2)\).

## 1. Ordered slots and assigned profiles

Fix positive integers \(s_1,\ldots,s_k\) with sum \(n\), and fix graph
labels \(\sigma=(\sigma_1,\ldots,\sigma_k)\in\{1,2\}^k\).  Let
\(Z_{\mathbf s,\sigma}\) count ordered partitions

\[
  P=(V_1,\ldots,V_k),\qquad |V_a|=s_a,
\]

such that \(V_a\) is independent in \(G_{\sigma_a}\) for every
\(a\).  Put

\[
  m_a=\binom{s_a}{2},\qquad
  M=M(\mathbf s)=\sum_{a=1}^k m_a,\qquad
  N=N(\mathbf s)=\frac{n!}{\prod_a s_a!}.
\]

The first moment, independent of the label vector, is

\[
  \mathbb E Z_{\mathbf s,\sigma}=N2^{-M}.                    \tag{1.1}
\]

This ordered-slot convention loses no information about a prescribed assigned
profile \((k_{t,1},k_{t,2})_{t\geq1}\).  List \(k_{t,i}\) slots of size
\(t\) and label \(i\).  If \(Z^{\mathrm{unord}}\) counts partitions
unordered within every size-label group, then

\[
 Z_{\mathbf s,\sigma}
 =\Big(\prod_{t,i}k_{t,i}!\Big) Z^{\mathrm{unord}}.
\]

Consequently the normalized second moment is exactly the same in the two
conventions.  Raw unordered moments are obtained by dividing the formulas below
by the corresponding deterministic ordering factors.

## 2. Exact cross moment and the full overlap matrix

For a second slot profile \(\mathbf t,\tau\), let
\(\mathcal R(\mathbf s,\mathbf t)\) be the set of nonnegative integer
matrices \(r=(r_{ab})\) with row sums \(s_a\) and column sums \(t_b\).
For a pair of partitions \(P=(V_a)\), \(Q=(W_b)\), the full overlap
matrix is

\[
  r_{ab}=|V_a\cap W_b|.
\]

Define

\[
 w_{ab}=\binom{r_{ab}}2,\qquad
 W(r)=\sum_{a,b}w_{ab},\qquad
 S_{\sigma,\tau}(r)
 =\sum_{a,b:\,\sigma_a=\tau_b}w_{ab}.                 \tag{2.1}
\]

### Lemma 2.1 (exact assigned cross moment)

\[
\boxed{
 \mathbb E[Z_{\mathbf s,\sigma}Z_{\mathbf t,\tau}]
 =\sum_{r\in\mathcal R(\mathbf s,\mathbf t)}
   \frac{n!}{\prod_{a,b}r_{ab}!}
   2^{-M(\mathbf s)-M(\mathbf t)+S_{\sigma,\tau}(r)}.}
                                                                    \tag{2.2}
\]

Equivalently,

\[
 \frac{\mathbb E[Z_{\mathbf s,\sigma}
                         Z_{\mathbf t,\tau}]}
        {\mathbb EZ_{\mathbf s,\sigma}\,
         \mathbb EZ_{\mathbf t,\tau}}
 =\sum_{r\in\mathcal R(\mathbf s,\mathbf t)}
     p_{\mathbf s,\mathbf t}(r)2^{S_{\sigma,\tau}(r)}, \tag{2.3}
\]

where

\[
 p_{\mathbf s,\mathbf t}(r)
 =\frac{\prod_a s_a!\prod_b t_b!}
        {n!\prod_{a,b}r_{ab}!}.                                \tag{2.4}
\]

The weights in (2.4) sum to one: they are the overlap-matrix law of two
independent uniformly random ordered partitions with the two profiles.

#### Proof

After fixing \(P\), the number of \(Q\) with overlap matrix \(r\) is
\(\prod_a s_a!/\prod_{a,b}r_{ab}!\).  Hence the number of ordered
pairs with matrix \(r\) is \(n!/\prod_{a,b}r_{ab}!\).

The first certificate asks for \(M(\mathbf s)\) absent-edge coordinates,
and the second asks for \(M(\mathbf t)\).  A coordinate is requested by
both certificates precisely when its two vertices lie in one cell
\(V_a\cap W_b\) and \(\sigma_a=\tau_b\).  There are
\(w_{ab}\) such coordinates in that cell.  Thus duplicate requirements
save exactly \(S_{\sigma,\tau}(r)\) fair bits.  If
\(\sigma_a\neq\tau_b\), the two requirements concern independent
coordinates, one in each graph, and save no bit.  This proves (2.2); division
by (1.1) gives (2.3). \(\square\)

The last sentence is the precise sense in which opposite-label overlaps do not
correlate in the two-graph model.  They are not forbidden; their normalized
correlation factor is exactly \(1\).

For a prescribed unordered assigned profile, with
\(C=\prod_{t,i}k_{t,i}!\), (2.2) reads explicitly

\[
 \mathbb E[(Z^{\mathrm{unord}})^2]
 =C^{-2}\sum_{r\in\mathcal R(\mathbf s,\mathbf s)}
  \frac{n!}{\prod_{a,b}r_{ab}!}
  2^{-2M+S_{\sigma,\sigma}(r)}.                       \tag{2.5}
\]

## 3. Summing graph labels: an exact bipartite Ising factor

For a fixed unlabelled slot profile, let

\[
 Z_X^{\mathrm{cert}}=\sum_{\sigma\in\{1,2\}^k}
                         Z_{\mathbf s,\sigma}.
\]

This counts certificates, so a part independent in both graphs is counted with
both labels.  Nevertheless \(Z_X^{\mathrm{cert}}>0\) is exactly the event
that the profile occurs in an \(X\)-partition.  Its first moment is

\[
 \mathbb E Z_X^{\mathrm{cert}}=2^kN2^{-M}.              \tag{3.1}
\]

From (2.3),

\[
 R_X:=\frac{\mathbb E[(Z_X^{\mathrm{cert}})^2]}
                {(\mathbb EZ_X^{\mathrm{cert}})^2}
 =\sum_{r\in\mathcal R(\mathbf s,\mathbf s)}p(r)A_X(r),
                                                                    \tag{3.2}
\]

where

\[
 A_X(r)=2^{-2k}\sum_{\sigma,\tau\in\{1,2\}^k}
             2^{\sum_{a,b}w_{ab}\mathbf1_{\{\sigma_a=\tau_b\}}}.
                                                                    \tag{3.3}
\]

Thus \(A_X\) is the partition function of a ferromagnetic Ising model on
the bipartite overlap support.

Let \(H(r)\) be the bipartite graph whose row vertices are the first
partition's slots, whose column vertices are the second partition's slots, and
whose edges are the cells with \(w_{ab}>0\), weighted by \(w_{ab}\).
Delete isolated vertices, and write

\[
 v=v(H),\qquad e=e(H),\qquad c=c(H),\qquad
 W=\sum_{ab}w_{ab}.
\]

Identify labels with spins \(x_u\in\{\pm1\}\).  If
\(d(x)=\sum_{uv\in E(H)}w_{uv}\mathbf1_{\{x_u\neq x_v\}}\),
then

\[
 A_X(r)=2^W\mathbb E_x 2^{-d(x)}
       =2^{W+c-v}\Psi(H,w),                                \tag{3.4}
\]

where

\[
 \Psi(H,w)=\sum_{[x]\in\{\pm1\}^{V(H)}/\sim}
                   2^{-d(x)}.                                 \tag{3.5}
\]

Here \(\sim\) identifies spin configurations that differ by flipping all
spins in any connected component.  Formula (3.4) is exact; the all-equal orbit
in each component contributes \(1\) to \(\Psi\).

There is also a useful even-subgraph expansion.  Put

\[
 a_e=\frac{2^{w_e}+1}{2},\qquad
 t_e=\frac{2^{w_e}-1}{2^{w_e}+1}.
\]

Expanding \(2^{w_e\mathbf1_{\{x_u=x_v\}}}=a_e(1+t_ex_ux_v)\)
and averaging spins gives

\[
\boxed{
 A_X(r)=\prod_{e\in E(H)}a_e
   \sum_{\substack{F\subseteq E(H)\\
                      \deg_F(u)\ \mathrm{even}\ \forall u}}
       \prod_{e\in F}t_e.}                            \tag{3.6}
\]

In particular, if \(H\) is a forest, the empty even subgraph is the only
one, and

\[
 A_X(r)=\prod_{e\in E(H)}\frac{2^{w_e}+1}{2}.       \tag{3.7}
\]

## 4. Exact term-by-term comparison with the other models

For an ordinary colouring, every overlap cell reuses constraints in the same
graph.  Its normalized factor is

\[
 A_\chi(r)=2^{W(r)},\qquad
 R_\chi=\sum_r p(r)2^{W(r)}.                           \tag{4.1}
\]

For a signed cocolouring of a *single* graph, use sign \(-\) for an
independent part and \(+\) for a clique.  In a cell with \(w>0\), equal
signs duplicate \(w\) requirements, whereas opposite signs demand that the
same edges be simultaneously absent and present and hence have probability
zero.  Compatibility therefore forces equal signs along every edge of
\(H(r)\).  There are \(2^c\) compatible assignments on its \(v\)
nonisolated vertices.  After summing signs, the exact normalized factor is

\[
 A_\zeta(r)=2^{W(r)+c(r)-v(r)},\qquad
 R_\zeta=\sum_r p(r)2^{W+c-v}.                         \tag{4.2}
\]

The local comparison, after removing the common baseline probability
\(2^{-2M}\), is therefore

| overlap-cell labels | ordinary colouring | two independent graphs | signed one-graph cocolouring |
|---|---:|---:|---:|
| same label/sign, weight \(w\) | \(2^w\) | \(2^w\) | \(2^w\) |
| opposite label/sign, \(w>0\) | not applicable | \(1\) | \(0\) |

### Proposition 4.1 (termwise sandwich)

For every overlap matrix,

\[
\boxed{A_\zeta(r)\leq A_X(r)\leq A_\chi(r),}\qquad
\boxed{R_\zeta\leq R_X\leq R_\chi.}             \tag{4.3}
\]

Moreover,

\[
 1\leq\frac{A_X(r)}{A_\zeta(r)}
 \leq\prod_{e\in E(H)}(1+2^{-w_e}),               \tag{4.4}
\]

and hence

\[
 0\leq\ln\frac{A_X(r)}{A_\zeta(r)}
 \leq\sum_{e\in E(H)}2^{-w_e}.                    \tag{4.5}
\]

#### Proof

The lower bound in (4.3) retains in (3.3) only label assignments constant on
each component of \(H\); their contribution is exactly (4.2).  The upper
bound follows because every term in (3.3) is at most \(2^W\).

For (4.4), the cycle-space dimension of \(H\) is
\(\beta=e-v+c\).  The even-subgraph sum in (3.6) is at most
\(2^\beta\), while
\(\prod_ea_e=2^{W-e}\prod_e(1+2^{-w_e})\).  Division by
\(A_\zeta=2^{W-v+c}\) proves (4.4), and
\(\ln(1+x)\leq x\) proves (4.5). \(\square\)

Thus the two-graph moment is genuinely intermediate.  It is smaller than the
ordinary-colouring moment because opposite graph labels do not share bits, but
it is larger than the signed-cocolouring moment because those opposite labels
remain possible rather than contradictory.

### Example 4.2 (a four-cycle audit)

Take a \(2\times2\) overlap matrix with every entry \(r_{ab}=2\).  Then
\(H=C_4\) and every edge has \(w=1\).  The three factors are

\[
 A_\chi=16,\qquad A_\zeta=2,\qquad
 A_X=\Big(\frac32\Big)^4\Big(1+\frac1{3^4}\Big)
     =\frac{41}{8}.                                       \tag{4.6}
\]

This finite example detects both common mistakes: treating opposite labels as
incompatible would give \(A_\zeta\), while treating them as correlated
would give \(A_\chi\).

### Example 4.3 (an exponential termwise obstruction)

Let \(n=ks\), with \(k>s\), and consider equitable profiles.  The
matrix

\[
 r_{aa}=2,\qquad r_{a,a+d}=1\quad(1\leq d\leq s-2),
\]

with column indices read modulo \(k\), has every row and column sum \(s\).
Its positive-weight support is a matching of \(k\) edges of weight one.
Consequently

\[
 A_\chi=2^k,\qquad A_\zeta=1,\qquad A_X=(3/2)^k. \tag{4.7}
\]

The overlap probability of this particular matrix is
\(p(r)=(s!)^{2k}/(n!2^k)\), so (4.7) alone does not show that its total
contribution dominates.  It does prove that no uniform replacement
\(A_X=(1+o(1))A_\zeta\) is possible: low-weight overlap cells can create
an exponential discrepancy.  Their entropy must be controlled in the full
sum.

## 5. Diagonal terms and witness multiplicity

For the diagonal matrix \(r_{aa}=s_a\), let \(q\) be the number of
non-singleton slots.  Then \(H\) is a matching of \(q\) edges with weights
\(m_a\), and

\[
 p(r)A_X(r)
 =\frac1N\prod_{a:s_a\geq2}\frac{2^{m_a}+1}{2}.       \tag{5.1}
\]

Since \(\mathbb EZ_X^{\mathrm{cert}}=2^kN2^{-M}\), this is

\[
 \frac{2^{k-q}}{\mathbb EZ_X^{\mathrm{cert}}}
 \prod_{a:s_a\geq2}(1+2^{-m_a}).                       \tag{5.2}
\]

If there are no singletons and all parts are large, (5.2) is
\((1+o(1))/\mathbb EZ_X^{\mathrm{cert}}\), as a genuine first-moment
threshold heuristic would suggest.  If there are \(k-q\) singletons, the
extra factor \(2^{k-q}\) exactly records their duplicate labels.  In the
all-singleton profile the certified first moment has a factor \(2^n\), but
the underlying partition event is deterministic; the label factor supplies no
existence advantage.  Canonical singleton labels remove this artefact.

For signed cocolourings the diagonal contribution is simply
\(2^{k-q}/\mathbb EZ_\zeta^{\mathrm{cert}}\).  The additional
\(\prod(1+2^{-m_a})\) in (5.2) is the possibility that a part is
independent in both input graphs.

## 6. A rigorous obstruction to the raw binomial second moment

The exact formula does not give a bounded normalized second moment in the
unconditioned \(G(n,1/2)^2\) model, even for balanced graph labels.

### Proposition 6.1 (density-fluctuation lower bound)

For the label-summed certificate count of any slot profile,

\[
\boxed{
 R_X\geq
 2^{M^2/(2\binom n2)}.}                                   \tag{6.1}
\]

For an equitable profile \(n=ks\), this becomes

\[
 R_X\geq
 2^{n(s-1)^2/[4(n-1)]}.                                     \tag{6.2}
\]

In the chromatic regime \(s=(2+o(1))\log_2 n\), the exponent in (6.2)
is \((1+o(1))(\log_2 n)^2\).

#### Proof

Under the probability weights \(p(r)\), choose two independent uniform
partitions; in (3.3), also choose their labels independently and uniformly.
Then \(R_X=\mathbb E2^S\).  A fixed vertex pair lies together in a
uniform partition with probability \(M/\binom n2\), and, conditional on
being together, its class label is fair.  Therefore the probability that the
pair is required in the same graph by both independently labelled partitions
is

\[
 2\Big(\frac{M}{2\binom n2}\Big)^2.
\]

Summing over vertex pairs gives
\(\mathbb ES=M^2/(2\binom n2)\).  Jensen's inequality for the convex
function \(2^x\) proves (6.1).  In the equitable case
\(M=k\binom s2=n(s-1)/2\), which gives (6.2). \(\square\)

For one fixed assigned label vector, put

\[
 M_i=\sum_{a:\sigma_a=i}\binom{s_a}{2}.
\]

The same proof gives the sharper assignment-dependent statement

\[
 \frac{\mathbb EZ_{\mathbf s,\sigma}^2}
      {(\mathbb EZ_{\mathbf s,\sigma})^2}
 \geq 2^{(M_1^2+M_2^2)/\binom n2}
 \geq 2^{M^2/(2\binom n2)}.                             \tag{6.3}
\]

Thus even the energy-balanced assignment \(M_1\approx M_2\) retains the
lower bound (6.1); putting every class in one graph doubles its Jensen exponent
and recovers the ordinary-colouring scale.

This is an obstruction to a **raw bounded-ratio Paley--Zygmund proof**, not an
obstruction to existence.  It is the familiar global edge-density correlation
in a precise two-graph form.  Conditioning both input graphs on their edge
counts is a natural way to try to remove it, but then (2.2) is replaced by
hypergeometric union-size factors and the resulting conditioned overlap sum
still has to be bounded.

### 6.1 Exact fixed-density replacement

The preceding conditioned statement can be made completely explicit.  Put

\[
 B=\binom n2,\qquad m=\lfloor B/2\rfloor,
 \qquad
 h_B(t)=\frac{\binom{B-t}{m}}{\binom Bm}
       =\frac{(B-m)_t}{(B)_t},                                 \tag{6.4}
\]

where `(a)_t` is a falling factorial.  Thus `h_B(t)` is the probability
that `t` prescribed pairs are all absent from `G(n,m)`.

For labels `sigma,tau`, define

\[
 M_i(\mathbf s,\sigma)
 =\sum_{a:\sigma_a=i}\binom{s_a}{2},
 \qquad
 S_i(r;\sigma,\tau)
 =\sum_{a,b:\sigma_a=\tau_b=i}\binom{r_{ab}}2.                 \tag{6.5}
\]

For two independent copies of `G(n,m)`, the exact analogue of Lemma 2.1 is

\[
\boxed{
 \mathbb E_m[Z_{\mathbf s,\sigma}Z_{\mathbf t,\tau}]
 =\sum_r\frac{n!}{\prod_{a,b}r_{ab}!}
   \prod_{i=1}^2
   h_B\!\left(M_i(\mathbf s,\sigma)
              +M_i(\mathbf t,\tau)-S_i(r;\sigma,\tau)\right).}
                                                                    \tag{6.6}
\]

Indeed, in graph `i` the two certificates forbid the union of their two
within-part pair sets, whose size is exactly the argument of `h_B`.  Dividing
by the two first moments gives the exact normalized local factor

\[
 \prod_{i=1}^2
 \frac{h_B(M_i+M_i'-S_i)}{h_B(M_i)h_B(M_i')}.                  \tag{6.7}
\]

This formula also shows why it is convenient to work with fixed, approximately
energy-balanced label assignments: after summing labels, the individual first
moments in `G(n,m)^2` depend on the split `(M_1,M_2)`, so the simple uniform
spin average (3.3) acquires assignment weights.

There is a uniform asymptotic form.  Let

\[
 \rho_B=\frac{B-m}{B},\qquad
 d_B=\frac{m}{2B(B-m)}=\frac1{2B}+O(B^{-2}).                   \tag{6.8}
\]

For `t=O(n log n)`, expansion of the product in (6.4) gives

\[
 \ln h_B(t)
 =t\ln\rho_B-d_Bt(t-1)+O(t^3/B^2),                            \tag{6.9}
\]

where the error is uniform and is `o(1)` in the present range.  Consequently,
if `M_i=M_i'=u_i` and `S_i=s_i`, the logarithm of the `i`th factor in (6.7)
is

\[
 -s_i\ln\rho_B
 -d_B\{2u_i^2-4u_is_i+s_i^2+s_i\}+o(1).                      \tag{6.10}
\]

The first term is the binomial reuse reward `s_i ln 2+o(1)`.  Crucially,
(6.10) also contains the negative baseline

\[
 -2d_Bu_i^2=-u_i^2/B+o(1),                                   \tag{6.11}
\]

which is absent from the raw binomial formula and is exactly on the
`Theta(log^2 n)` global-density scale detected by Proposition 6.1.  Thus
conditioning does remove the specific Jensen obstruction proved there.  It
does **not** bound the remaining overlap sum: the terms involving `s_i`, the
low-weight support entropy, and nearly common parts still require a full
analysis.

At the putative shifted first-moment point, ordinary comparison alone is also
too lossy.  There \(\mathbb EZ_\chi\) is smaller than
\(\mathbb EZ_X^{\mathrm{cert}}\) by \(2^k\), so the ordinary
diagonal term can be larger by that same factor.  The inequality
\(R_X\leq R_\chi\) therefore cannot establish the shifted threshold;
one must use the label-dependent factor inside the sum.

## 7. Rigorous continuous equitable first-moment displacement

This section proves the leading constant for one precisely defined continuous
relaxation.  It is not a theorem about the integer chromatic number.

Let \(k\) and \(s=n/k\) be real.  Extend factorials by the gamma
function and define the base-two logarithm of the ordinary equitable-profile
first moment by

\[
 \Phi_n(k)=\log_2\Gamma(n+1)
   -k\log_2\Gamma(s+1)-\log_2\Gamma(k+1)
   -\frac n2(s-1).                                         \tag{7.1}
\]

The assigned/certified two-graph relaxation is

\[
 \Phi_n^X(k)=\Phi_n(k)+k.                              \tag{7.2}
\]

Write \(L=\log_2 n\) and \(\ell=\log_2L\).  For all sufficiently
large \(n\), each of (7.1) and (7.2) has a unique zero in the local window

\[
 2L-3\ell \leq s=n/k\leq2L-\ell.
\]

Denote the ordinary zero by \(k_\chi=n/s_\chi\) and the certified zero
by \(k_X=n/s_X\).

### Proposition 7.1 (leading constant)

\[
 s_\chi=2L-2\log_2L-2
             +O\Big(\frac{\log L}{L}\Big),                    \tag{7.3}
\]

\[
 s_X-s_\chi=\frac{2}{s_\chi}\Big(1+O(1/L)\Big),          \tag{7.4}
\]

and therefore

\[
\boxed{
 k_\chi-k_X
 =\frac{2n}{s_\chi^3}\Big(1+O(1/L)\Big)
 =\frac{n}{4(\log_2n)^3}
    \Big(1+O\Big(\frac{\log\log n}{\log n}\Big)\Big).}  \tag{7.5}
\]

In particular, \(1/4\) is the rigorous leading constant for this
continuous equitable first-moment relaxation.

#### Proof

Set \(H_n(s)=n^{-1}\Phi_n(n/s)\).  Uniform Stirling expansion in the
displayed window gives

\[
\begin{aligned}
 H_n(s)
  ={}&L-\log_2s-\frac{L-\log_2s}{s}
      +\frac{\log_2e}{s}
      -\frac{\log_2(2\pi s)}{2s}
      -\frac{s}{2}+\frac12
      +O(s^{-2}).                                             \tag{7.6}
\end{aligned}
\]

The omitted \(O((\log n)/n)\) term is absorbed by \(O(s^{-2})\).
Putting \(s=2L-2\ell+c\) in (7.6) yields

\[
 H_n(s)=-1-\frac c2+O(\ell/L).                         \tag{7.7}
\]

Also, uniformly in the window,

\[
 H_n'(s)=-\frac12+O(1/L).                                 \tag{7.8}
\]

For example, (7.8) follows directly by differentiating the gamma expression:

\[
 H_n'(s)=-\frac12
 +\frac{\ln\Gamma(s+1)+\psi(n/s+1)}{s^2\ln2}
 -\frac{\psi(s+1)}{s\ln2},                       \tag{7.9}
\]

where \(\psi\) is the digamma function.  Equations (7.7)--(7.8)
give local existence, uniqueness, and (7.3).

The certified zero satisfies
\(H_n(s_X)+1/s_X=0\), while \(H_n(s_\chi)=0\).  Since
\(H_n\) is decreasing, \(s_X>s_\chi\).  The mean-value theorem and
(7.8) give

\[
 s_X-s_\chi
 =\frac{1/s_X}{1/2+O(1/L)}
 =\frac2{s_\chi}\Big(1+O(1/L)\Big),
\]

which is (7.4).  Finally,

\[
 k_\chi-k_X
 =n\frac{s_X-s_\chi}{s_\chi s_X}
 =\frac{2n}{s_\chi^3}\Big(1+O(1/L)\Big).
\]

Substitution of (7.3) proves (7.5). \(\square\)

For an integer equitable class size \(s\geq2\), the *unassigned*
two-graph first moment has the additional exact term

\[
 k\log_2(1-2^{-\binom s2-1})                          \tag{7.10}
\]

relative to (7.2).  Uniformly for \(s=2L+O(\log L)\), its magnitude is
\(O(k2^{-\binom s2})\), so it is negligible compared with \(k\) and
does not change the leading constant in the same continuous relaxation.

### Uniformity and interpretation caveats

1. Equations (7.3)--(7.5) concern local zeros of gamma-extended **equitable
   profile first moments**.  They are not actual thresholds for \(\chi\),
   \(X\), or \(\zeta\).
2. Integer class-size granularity corresponds to a \(k\)-scale
   \(|d(n/s)/ds|\asymp n/(\log n)^2\), larger by a factor of order
   \(\log n\) than (7.5).  Mixtures of adjacent sizes can interpolate,
   but their optimal proportions change at profile transitions.  The
   continuous constant therefore cannot be asserted uniformly through
   independence-number jumps without a separate integer-profile analysis.
3. The error in (7.5) is uniform only in the displayed local window.  It says
   nothing about exceptional profiles with materially different size support
   or many small parts.
4. A first moment larger than one is not an existence theorem.  Proposition
   6.1 shows why the unconditioned raw second moment cannot supply the missing
   theorem with a bounded ratio.

## 8. The exact unclosed overlap sum

For the equitable no-singleton profile, the desired second-moment task in the
binomial model is exactly to control

\[
\boxed{
 R_X(n,k,s)=\sum_{\substack{r_{ab}\geq0\\
                              \sum_b r_{ab}=s\\
                              \sum_a r_{ab}=s}}
 \frac{(s!)^{2k}}{n!\prod_{a,b}r_{ab}!}
 \left[
 2^{-2k}\sum_{\sigma,\tau\in\{1,2\}^k}
 2^{\sum_{a,b}\binom{r_{ab}}2
              \mathbf1_{\{\sigma_a=\tau_b\}}}
 \right].}                                                \tag{8.1}
\]

The bracket may equivalently be replaced by (3.4) or (3.6).  Equation (8.1)
is fully explicit, but its entropy--energy sum is **not bounded here**.
Proposition 6.1 proves that it is at least
\(2^{(1+o(1))L^2}\) at chromatic-scale \(s\), so a successful route
should first condition away the two global edge densities or normalize them,
and then control at least the following regimes separately:

- low cells \(r_{ab}\in\{0,1,2\}\), where opposite-label terms and
  cycle-space factors can accumulate;
- intermediate overlap supports, where both the contingency-table entropy and
  the Ising cut enumerator matter;
- common or nearly common parts, where diagonal/cluster contributions govern
  condensation;
- integer-profile transitions, where the equitable continuous surrogate is
  not uniform.

No nontrivial existence theorem below the ordinary chromatic threshold follows
from the present bounds.  The concrete obstruction is twofold: the raw
binomial ratio has the rigorous lower bound (6.1), and termwise comparison with
signed cocolourings loses as much as \((3/2)^k\) on valid overlap matrices.
These facts isolate, rather than close, the remaining second-moment problem.

## 9. Adversarial audit

- **Graph independence:** an opposite-label cell contributes \(1\), not
  \(0\) and not \(2^w\).  Example 4.2 checks both directions.
- **Normalization:** \(p(r)\) is a probability distribution.  The factors
  \(2^k\) in the first moment become an average over \(2^{2k}\) label
  pairs in (3.3), not an extra multiplier in (3.2).
- **Finite enumeration:** for \(n=4\), ordered profile \((2,2)\), and fixed
  labels \((1,2)\), exhaustive enumeration of the \(2^{12}\) two-graph
  outcomes gives \(\mathbb EZ=3/2\) and \(\mathbb EZ^2=27/8\), exactly as
  (2.2).  Summing all four label vectors gives
  \(\mathbb EZ_X^{\mathrm{cert}}=6\) and
  \(\mathbb E[(Z_X^{\mathrm{cert}})^2]=51\), exactly as (3.2)--(3.3).
- **Singletons:** duplicate singleton labels are explicitly visible in (5.2);
  they must not be interpreted as extra partitions.
- **Ordinary versus signed:** the exact ordering is
  \(A_\zeta\leq A_X\leq A_\chi\).  The first inequality goes in
  the direction expected from opposite signs being impossible only in the
  one-graph model.
- **Second moment:** (6.1) blocks only a bounded-ratio raw Paley--Zygmund
  argument.  It is not a probabilistic lower bound on \(X\) and not evidence
  against the conjectured gap.
- **First-moment constant:** \(1/4\) is proved only for the specified gamma
  relaxation.  Integer rounding/profile transitions occur on a coarser scale,
  so the result is not advertised as a uniform threshold theorem.
