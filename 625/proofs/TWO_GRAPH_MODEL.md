# The two-independent-graph model: coupling, concentration, and first moments

**Status:** self-contained proof note. The coupling, concentration, amplification
lemma, and fixed-profile first moments below are proved. The estimate of
\(\mathbb E X\) at the precision needed for Erdős Problem #625 remains open.

| Item | Status |
|---|---|
| Adaptive product-space coupling \(X\geq\zeta\) | **Proved here** |
| \(X\) concentration with explicit subgaussian constants | **Proved here** |
| Uniform positive-probability condition implies the original whp gap | **Proved here; forum heuristic made precise** |
| Exact assigned and unassigned fixed-profile first moments | **Proved here** |
| Balanced \(n/(4\log_2^3 n)\) first-moment displacement | **Heuristic only** |
| \(\mathbb E\chi-\mathbb EX\gg\sqrt n\), uniformly in all \(n\) | **Open; decisive obstruction** |

The forum proposal is mathematically sound after its asymptotic shorthand is
made uniform. In particular, there is a coupling on which

\[
X(G_1,G_2)\geq \zeta(G)
\]

for \(G_1,G_2,G\sim G(n,1/2)\), with \(G_1,G_2\) independent. This is a
coupling of **values** produced by an adaptive coordinate argument; it is not a
pointwise assertion for \(G=G_1\), and it does not couple the homogeneous-set
families by inclusion.

The main quantitative consequence is the following. If

\[
\Pr\bigl(\chi(G_1)-X(G_1,G_2)\geq a_n\bigr)\geq p_n,
\]

then, for a fresh \(G\sim G(n,1/2)\),

\[
\Pr\left(\chi(G)-\zeta(G)\geq \frac{p_na_n}{2}\right)
\geq
1-\exp\left(-\frac{(p_na_n)^2}{8(n-1)}\right).                  \tag{0.1}
\]

Thus the forum condition is sufficient provided it means that there are fixed
\(\varepsilon,\delta>0\) for which

\[
\Pr\bigl(\chi(G_1)-X>n^{1/2+\varepsilon}\bigr)\geq\delta
\]

for **every sufficiently large** \(n\). If it holds only on a subsequence, the
conclusion also holds only on that subsequence.

---

## 1. Definitions and the product-space encoding

Let \(E=\binom{[n]}2\). For a pair of graphs \((G_1,G_2)\), define the
"good-bit" array

\[
A_{e,i}:=\mathbf 1_{\{e\notin E(G_i)\}},\qquad e\in E,\ i\in\{1,2\}.
\]

Under two independent \(G(n,1/2)\) graphs, the \(2|E|\) entries are mutually
independent fair bits.

A **certified partition** is a set partition
\(P=\{I_1,\ldots,I_k\}\), together with labels
\(\sigma_j\in\{1,2\}\), whose required set of bits is

\[
W(P,\sigma)
 =\bigcup_{j=1}^k
 \{(e,\sigma_j):e\in\tbinom{I_j}{2}\}.                         \tag{1.1}
\]

It is a certificate precisely when every bit in \(W(P,\sigma)\) equals one.
Consequently,

\[
X(G_1,G_2)=\min\{|P|:\text{some }\sigma\text{ makes }(P,\sigma)
\text{ a certificate}\}.                                      \tag{1.2}
\]

The crucial structural fact is

\[
|W(P,\sigma)\cap(\{e\}\times\{1,2\})|\leq 1                 \tag{1.3}
\]

for every edge \(e\). Indeed, the endpoints of \(e\) lie together in at most
one part, and that part has only one certifying label.

There is a second product model. For every \(e\), independently choose exactly
one of \((e,1),(e,2)\) to be good, each with probability \(1/2\). Write this as

\[
A_{e,1}=1-C_e,\qquad A_{e,2}=C_e,
\]

where the \(C_e\)'s are independent fair bits. Let \(G\) have edge indicator
\(C_e\). A label-1 part is then independent in \(G\), while a label-2 part is
a clique in \(G\). Therefore the minimum in (1.2) in this exactly-one model is
exactly \(\zeta(G)\). A singleton requires no good bits, so its two possible
labels cause no issue for this minimum-value identification; they matter only
if signed certificates are counted with multiplicity in a first moment.

### Lemma 1.1 (vertex-split representation)

For every deterministic pair \((G_1,G_2)\),

\[
\boxed{\quad
X(G_1,G_2)=\min_{S\subseteq[n]}
\bigl\{\chi(G_1[S])+\chi(G_2[[n]\setminus S])\bigr\}.
\quad}                                                        \tag{1.4}
\]

Indeed, from any certified partition let \(S\) be the union of its label-1
parts.  Those parts form a proper colouring of \(G_1[S]\), and the remaining
parts form a proper colouring of \(G_2[[n]\setminus S]\), proving the lower
bound in (1.4).  Conversely, concatenate optimal colourings of the two induced
graphs for any fixed \(S\).

Equivalently, the surrogate gap has the exact deterministic form

\[
\chi(G_1)-X(G_1,G_2)
=\max_{T\subseteq[n]}
\{\chi(G_1)-\chi(G_1[[n]\setminus T])-\chi(G_2[T])\}.          \tag{1.5}
\]

Thus the second graph helps precisely when one can find a vertex set whose
removal saves more colours in \(G_1\) than are needed to colour its induced
copy in \(G_2\).  Formula (1.5) is exact, but by itself supplies no such set:
for a typical unstructured set, the two terms are strongly mismatched at the
additive precision required here.  It offers a separate route through
chromatic vertex-deletion large deviations and is also useful for exact
computation.

---

## 2. The McDiarmid-style coupling

### Lemma 2.1 (one-fibre identity)

Fix all good bits except the two over one edge \(e\). Let \(x_{ab}\) denote
the minimum certified-partition size when
\((A_{e,1},A_{e,2})=(a,b)\). Then

\[
x_{11}=\min\{x_{10},x_{01}\},\qquad
x_{00}\geq\max\{x_{10},x_{01}\}.                              \tag{2.1}
\]

#### Proof

Adding good bits cannot increase the minimum, so
\(x_{11}\leq\min(x_{10},x_{01})\) and
\(x_{00}\geq\max(x_{10},x_{01})\).

Take an optimal certificate in state \(11\). By (1.3), it uses at most one of
the two bits over \(e\). It therefore remains a certificate in state \(10\) or
state \(01\) (in both if it uses neither). Hence
\(\min(x_{10},x_{01})\leq x_{11}\), proving (2.1). \(\square\)

### Lemma 2.2 (explicit local value coupling)

Conditional on all other fibres, a fibre of two independent fair bits can be
coupled with an exactly-one fair fibre so that the resulting minimum in the
independent-bit configuration is at least the minimum in the exactly-one
configuration.

#### Proof

Write \(b=x_{10}\), \(c=x_{01}\). If \(b\leq c\), take one of the following
four rows with probability \(1/4\):

| independent state | exactly-one state | comparison |
|---:|---:|---:|
| \(11\) | \(10\) | \(x_{11}=b=x_{10}\) |
| \(10\) | \(10\) | equality |
| \(01\) | \(01\) | equality |
| \(00\) | \(01\) | \(x_{00}\geq c=x_{01}\) |

The first column is uniform on \(\{00,10,01,11\}\), and the second is uniform
on \(\{10,01\}\). Every row has the desired value inequality. If \(c\leq b\),
interchange labels 1 and 2; explicitly use

\[
(11,01),\ (01,01),\ (10,10),\ (00,10).
\]

This proves the claim. \(\square\)

The table is adaptive: the choice between its two versions depends on the
minimum-partition values determined by the outside configuration. This
adaptivity is why a naive fixed edgewise map is not the right coupling.

### Theorem 2.3 (exact value domination)

For every \(n\),

\[
\boxed{\ \zeta(G(n,1/2))\ \preceq_{\rm st}\ X(G_1,G_2)\ },    \tag{2.2}
\]

meaning, for every integer \(k\),

\[
\Pr(X\leq k)\leq\Pr(\zeta\leq k).                              \tag{2.3}
\]

Equivalently, there exists a joint realization of
\(G_1,G_2,G\), with the required marginals and with \(G_1,G_2\) independent,
such that

\[
X(G_1,G_2)\geq\zeta(G)\quad\text{almost surely}.               \tag{2.4}
\]

#### Proof

Enumerate the \(N=\binom n2\) edge fibres. Let \(\mu_j\) be the product law in
which the first \(j\) fibres consist of two independent fair bits and the
remaining fibres are exactly-one fair fibres. Thus \(\mu_0\) is the single-graph
cocolouring model and \(\mu_N\) is the two-independent-graph model.

Here is an explicit induction on one product space. Start with
\(\Omega_0\sim\mu_0\) and independent auxiliary uniforms
\(U_1,\ldots,U_N\), each uniform on \(\{0,1\}\). Given \(\Omega_{j-1}\), keep
every fibre other than \(j\) fixed. Conditional on that outside configuration,
compute \(b=x_{10}\) and \(c=x_{01}\). The old \(j\)-th state is exactly-one.
If \(b\leq c\), use the transition kernel

\[
10\longmapsto
 \begin{cases}11,&U_j=0,\\10,&U_j=1,\end{cases}
\qquad
01\longmapsto
 \begin{cases}01,&U_j=0,\\00,&U_j=1.\end{cases}                \tag{2.5}
\]

If \(c\leq b\), use the label-reversed kernel

\[
01\longmapsto
 \begin{cases}11,&U_j=0,\\01,&U_j=1,\end{cases}
\qquad
10\longmapsto
 \begin{cases}10,&U_j=0,\\00,&U_j=1.\end{cases}                \tag{2.6}
\]

(Either kernel may be used on a tie.) For each fixed outside configuration,
the new state is uniform on all four states: the old state is uniform on
\(\{10,01\}\), and each of its two images is chosen fairly. Thus the new fibre
is two independent fair bits and remains independent of the outside, proving
inductively that \(\Omega_j\sim\mu_j\). The four rows in Lemma 2.2 show at the
same time that

\[
X(\Omega_j)\geq X(\Omega_{j-1})\quad\text{for every outcome}.   \tag{2.7}
\]

Consequently \(X(\Omega_N)\geq X(\Omega_0)\) on this explicit space
\(\mu_0\times\{0,1\}^N\). The endpoint identifications in Section 1 give
(2.4), and hence (2.3). This also fixes the interpolation direction: replacing
exactly-one (anti-correlated) fibres by independent fibres makes the minimum
nondecreasing and makes every lower-tail event \(\{X\leq k\}\) no more likely.
\(\square\)

### A probability-only verification

For auditing the direction, fix an integer \(k\), fix the outside fibres, and
let \(f_{ab}\) be the indicator that a certificate with at most \(k\) parts
exists. The witness property gives

\[
f_{11}=f_{10}\vee f_{01},\qquad f_{00}\leq f_{10}\wedge f_{01}.
\]

Therefore

\[
\frac{f_{10}+f_{01}}2-\frac{f_{00}+f_{10}+f_{01}+f_{11}}4
=\frac{\min(f_{10},f_{01})-f_{00}}4\geq0.                     \tag{2.8}
\]

The left side is exactly the conditional probability in the exactly-one model
minus that in the independent model. Iterating proves (2.3) independently of
the value-coupling table.

### Consequences and non-consequences

Since an ordinary colouring of either graph is allowed,

\[
X(G_1,G_2)\leq\min\{\chi(G_1),\chi(G_2)\}                     \tag{2.9}
\]

pointwise. Combining (2.2) and (2.9),

\[
\zeta\preceq_{\rm st}X\preceq_{\rm st}\chi,
\qquad
\mathbb E\zeta\leq\mathbb EX\leq\mathbb E\chi.                 \tag{2.10}
\]

But (2.4) does **not** hold with \(G=G_1\) in general. For example, if
\(G_2\) is empty then \(X=1\), while \(\zeta(G_1)\) need not be one. In the
opposite direction, if \(G_1=G_2=K_n\), then \(X=n\) while \(\zeta(G_1)=1\).
Thus the valid assertion is a stochastic/value coupling, not a deterministic
comparison with either input graph.

There also cannot be a coupling based on inclusion of all good-bit sets with
the independent fibre contained in the exactly-one fibre: both fibres have
expected size one, so such inclusion would force equality almost surely, which
is incompatible with the independent fibre taking states \(00\) and \(11\).

---

## 3. Concentration of \(X\)

### Lemma 3.1 (one-vertex Lipschitz property)

If two pairs of graphs differ only on edges incident with one vertex \(v\),
then their \(X\)-values differ by at most one.

#### Proof

Let \(x_0\) be the value after deleting \(v\); it is the same for both graph
pairs. Restricting a partition to \([n]\setminus\{v\}\) gives \(X\geq x_0\),
and adding \(\{v\}\) as a singleton gives \(X\leq x_0+1\). Both values lie in
\(\{x_0,x_0+1\}\). \(\square\)

### Theorem 3.2 (subgaussian concentration, explicit constants)

For \(n\geq2\) and every \(t\geq0\),

\[
\Pr(|X-\mathbb EX|\geq t)
\leq 2\exp\left(-\frac{2t^2}{n-1}\right).                      \tag{3.1}
\]

#### Proof

For \(v=2,\ldots,n\), expose as one block all edge indicators in both graphs
from \(v\) to \(\{1,\ldots,v-1\}\). These \(n-1\) vector-valued blocks are
independent. Changing one block changes only edges incident with \(v\), so its
bounded-difference constant is one by Lemma 3.1. McDiarmid's bounded-difference
inequality gives each one-sided tail as
\(\exp(-2t^2/(n-1))\). \(\square\)

For example, for every fixed \(c>0\),

\[
\Pr\left(|X-\mathbb EX|>
\sqrt{\frac c2(n-1)\ln n}\right)\leq2n^{-c}.                  \tag{3.2}
\]

This proves concentration in a deterministic interval of length
\(O(\sqrt{n\ln n})=n^{1/2+o(1)}\) with high probability. A fixed multiple of
\(\sqrt n\) is the subgaussian fluctuation scale, but its failure probability
from (3.1) is only a fixed constant; a diverging multiplier is needed for a
whp statement.

The same vertex-block proof gives, for \(Y=\chi(G)\) or \(Y=\zeta(G)\),

\[
\Pr(|Y-\mathbb EY|\geq t)
\leq2\exp\left(-\frac{2t^2}{n-1}\right).                       \tag{3.3}
\]

For the original single-graph gap

\[
Y_\Delta(G):=\chi(G)-\zeta(G),
\]

changing one vertex block changes each summand by at most one and hence changes
\(Y_\Delta\) by at most two. Direct bounded differences therefore gives

\[
\Pr\bigl(Y_\Delta-\mathbb EY_\Delta\leq-t\bigr)
\leq\exp\left(-\frac{t^2}{2(n-1)}\right),                       \tag{3.4}
\]

and the analogous upper tail. The constant two is an oscillation bound, not a
monotonicity claim: \(\chi-\zeta\) need not be monotone in the edge set.

No Alon-type logarithmic improvement for \(X\) is proved here; none is needed
for the forum's stated \(n^{1/2+o(1)}\) window.

---

## 4. The positive-probability amplification

### Proposition 4.1 (exact sufficient condition)

Let \(n\geq2\), let \(a_n,p_n>0\), and suppose

\[
\Pr(\chi(G_1)-X(G_1,G_2)\geq a_n)\geq p_n.                    \tag{4.1}
\]

Then (0.1) holds. In particular, if

\[
\frac{p_na_n}{\sqrt n}\longrightarrow\infty,                 \tag{4.2}
\]

then

\[
\chi(G)-\zeta(G)\geq\frac{p_na_n}{2}
\quad\text{with high probability}.                            \tag{4.3}
\]

#### Proof

By (2.9),

\[
D:=\chi(G_1)-X(G_1,G_2)\geq0
\]

pointwise. Hence (4.1) implies

\[
\mathbb E\chi-\mathbb EX=\mathbb ED\geq p_na_n.              \tag{4.4}
\]

By (2.10),

\[
\Delta_n:=\mathbb E\chi-\mathbb E\zeta
\geq\mathbb E\chi-\mathbb EX
\geq p_na_n.                                                   \tag{4.5}
\]

Equivalently, the complete expectation chain is

\[
\boxed{\ 
\mathbb E[\chi(G)-\zeta(G)]
\geq \mathbb E[\chi(G_1)-X(G_1,G_2)]
\geq p_na_n. \ }                                               \tag{4.6}
\]

For a fresh single graph,
\(\mathbb EY_\Delta=\mathbb E\chi-\mathbb E\zeta\geq p_na_n\).
Apply (3.4) with \(t=p_na_n/2\). If
\(Y_\Delta<p_na_n/2\), then
\(Y_\Delta-\mathbb EY_\Delta\leq-p_na_n/2\). Hence

\[
\Pr\left(Y_\Delta<\frac{p_na_n}{2}\right)
\leq\exp\left(-\frac{(p_na_n)^2}{8(n-1)}\right),
\]

which is (0.1). \(\square\)

### Corollary 4.2 (formal version of the forum claim)

If there exist fixed \(\varepsilon,\delta>0\) and \(n_0\) such that, for all
\(n\geq n_0\),

\[
\Pr(\chi(G_1)-X\geq n^{1/2+\varepsilon})\geq\delta,           \tag{4.7}
\]

then

\[
\Pr\left(\chi(G)-\zeta(G)
\geq \frac\delta2 n^{1/2+\varepsilon}\right)
\geq
1-\exp\left(-\frac{\delta^2 n^{1+2\varepsilon}}{8(n-1)}\right)
\longrightarrow1.                                             \tag{4.8}
\]

This would resolve Problem #625 positively, and much more strongly than merely
proving divergence. The quantifier "for all sufficiently large \(n\)" is
essential.

### Expectation version

The same proof shows that if

\[
h_n:=\mathbb E\chi-\mathbb EX>0,
\]

then

\[
\Pr\left(\chi(G)-\zeta(G)\geq\frac{h_n}{2}\right)
\geq1-\exp\left(-\frac{h_n^2}{8(n-1)}\right).                  \tag{4.9}
\]

Thus a lower estimate \(h_n\gg\sqrt n\), uniform in \(n\), is sufficient.
An estimate \(h_n\geq c n/(\log n)^3\) would transfer to a lower bound of that
order for the original gap. It would not, by itself, prove a matching upper
bound.

---

## 5. Dependence between \(\chi(G_1)\) and \(X\)

The variables are not independent. With edge indicators ordered by inclusion,
both \(\chi(G_1)\) and \(X(G_1,G_2)\) are increasing functions of the product
bits (the former ignores the \(G_2\) bits). Harris association therefore gives

\[
\operatorname{Cov}(\chi(G_1),X)\geq0.                          \tag{5.1}
\]

For \(n=2\), if \(A,B\) are the two edge indicators, then

\[
\chi(G_1)=1+A,\qquad X=1+AB,
\]

so

\[
\operatorname{Cov}(\chi(G_1),X)=\frac18>0.                    \tag{5.2}
\]

The dependence does not obstruct Proposition 4.1 because the key variable
\(D=\chi(G_1)-X\) is pointwise nonnegative. A positive-probability lower tail
therefore gives a lower bound on \(\mathbb ED\) without any independence
assumption.

For completeness, exposing the same \(n-1\) two-graph vertex blocks changes
\(D\) by at most two. Hence

\[
\Pr(|D-\mathbb ED|\geq t)
\leq2\exp\left(-\frac{t^2}{2(n-1)}\right).                     \tag{5.3}
\]

This concentrates the surrogate gap itself, but it cannot be transferred
pathwise to \(\chi(G)-\zeta(G)\), because the coupling in Theorem 2.3 does not
preserve \(G=G_1\). The expectation argument is the valid transfer.

---

## 6. Exact fixed-profile first moments

Let a profile be a finite sequence
\(\mathbf k=(k_s)_{s\geq1}\) with

\[
\sum_{s\geq1}s k_s=n,\qquad \sum_{s\geq1}k_s=k.
\]

Put

\[
m_s:=\binom s2,\qquad
M(\mathbf k):=\sum_s k_s m_s,
\]

and let

\[
N(\mathbf k)
:=\frac{n!}{\prod_s(s!)^{k_s}k_s!}                             \tag{6.1}
\]

be the number of unordered set partitions with that profile.

### 6.1 Ordinary colourings

For a fixed partition, all its internal pairs must be absent in \(G_1\), so

\[
\mathbb E Z^{\chi}_{\mathbf k}
=N(\mathbf k)2^{-M(\mathbf k)}.                                \tag{6.2}
\]

### 6.2 Two-graph certified/assigned partitions

Suppose \(k_{s,1}+k_{s,2}=k_s\), where \(k_{s,i}\) parts of size \(s\) are
assigned to graph \(i\). The number of such assigned partitions is

\[
N(\mathbf k;\mathbf k_1,\mathbf k_2)
=\frac{n!}{\prod_s(s!)^{k_s}k_{s,1}!k_{s,2}!}.
\]

A fixed assignment requires exactly \(M(\mathbf k)\) independent good bits.
Therefore

\[
\mathbb E Z^{X,\mathrm{cert}}_{\mathbf k;\mathbf k_1,\mathbf k_2}
=N(\mathbf k;\mathbf k_1,\mathbf k_2)2^{-M(\mathbf k)}.       \tag{6.3}
\]

Summing over all assignments gives the exact identity

\[
\mathbb E Z^{X,\mathrm{cert}}_{\mathbf k}
=2^k N(\mathbf k)2^{-M(\mathbf k)}
=2^k\mathbb E Z^{\chi}_{\mathbf k}.                            \tag{6.4}
\]

This variable counts certificates, not distinct partitions. A part independent
in both graphs has two certifying labels.

### 6.3 Two-graph unassigned partitions

For a fixed part of size \(s\), inclusion-exclusion gives

\[
q_s
:=\Pr(\text{independent in }G_1\text{ or }G_2)
=2^{1-m_s}-2^{-2m_s}.                                          \tag{6.5}
\]

This formula also gives \(q_1=1\). Different parts use disjoint edge
coordinates, so their validity events are independent. Hence

\[
\boxed{
\mathbb E Z^{X,\mathrm{un}}_{\mathbf k}
=N(\mathbf k)\prod_s q_s^{k_s}.}                               \tag{6.6}
\]

Relative to ordinary colourings,

\[
\frac{\mathbb E Z^{X,\mathrm{un}}_{\mathbf k}}
     {\mathbb E Z^{\chi}_{\mathbf k}}
=\prod_s(2-2^{-m_s})^{k_s}.                                   \tag{6.7}
\]

### 6.4 Single-graph cocolourings

For a part of size \(s\geq2\), the all-absent and all-present events are
disjoint, so its homogeneous probability is

\[
r_s=2^{1-m_s}.
\]

For a singleton, \(r_1=1\), not two. Thus

\[
\mathbb E Z^{\zeta,\mathrm{un}}_{\mathbf k}
=N(\mathbf k)\prod_s r_s^{k_s}.                               \tag{6.8}
\]

If there are no singleton parts, a homogeneous part has a unique sign and

\[
\mathbb E Z^{\zeta,\mathrm{un}}_{\mathbf k}
=2^kN(\mathbf k)2^{-M(\mathbf k)},                             \tag{6.9}
\]

which is exactly the certified first moment (6.4). With singleton parts one
must either count the two duplicate signs or choose a canonical singleton
sign; failure to state this convention introduces a spurious factor
\(2^{k_1}\).

For every profile, the exact unassigned comparison is

\[
\frac{\mathbb E Z^{X,\mathrm{un}}_{\mathbf k}}
     {\mathbb E Z^{\zeta,\mathrm{un}}_{\mathbf k}}
=\prod_{s\geq2}\left(1-2^{-m_s-1}\right)^{k_s}\leq1.         \tag{6.10}
\]

The deficit is exactly the overcount caused by a two-graph part being
independent in both input graphs.

### 6.5 Large-part comparison

Suppose every non-singleton part has size at least \(r\geq2\), and let
\(k_{\geq2}=\sum_{s\geq2}k_s\). Since
\(-\ln(1-x)\leq x/(1-x)\) and \(2^{-m_s-1}\leq1/4\), (6.10)
gives the rigorous bound

\[
0\leq
\ln\frac{\mathbb E Z^{\zeta,\mathrm{un}}_{\mathbf k}}
        {\mathbb E Z^{X,\mathrm{un}}_{\mathbf k}}
\leq \frac23 k_{\geq2}2^{-\binom r2}.                         \tag{6.11}
\]

Consequently, if
\(k_{\geq2}2^{-\binom r2}=o(1)\), the unassigned first moments for \(X\)
and \(\zeta\) have ratio \(1+o(1)\). This applies overwhelmingly to profiles
whose parts all have order \(\log n\). It is a uniform, explicit statement;
it does not cover profiles containing many small parts.

### 6.6 Profile-summed generating functions

Let

\[
A(z)=\sum_{s\geq1}2^{-m_s}\frac{z^s}{s!},\quad
Q(z)=\sum_{s\geq1}q_s\frac{z^s}{s!},\quad
R(z)=z+\sum_{s\geq2}2^{1-m_s}\frac{z^s}{s!}.
\]

For exactly \(k\) nonempty unordered parts,

\[
\begin{aligned}
\mathbb E Z^{\chi}_{n,k}
 &=\frac{n!}{k!}[z^n]A(z)^k,\\
\mathbb E Z^{X,\mathrm{cert}}_{n,k}
 &=\frac{n!}{k!}[z^n](2A(z))^k
 =2^k\mathbb E Z^{\chi}_{n,k},\\
\mathbb E Z^{X,\mathrm{un}}_{n,k}
 &=\frac{n!}{k!}[z^n]Q(z)^k,\\
\mathbb E Z^{\zeta,\mathrm{un}}_{n,k}
 &=\frac{n!}{k!}[z^n]R(z)^k.
\end{aligned}                                                   \tag{6.12}
\]

The certified formula counts the two labels on singletons; the last formula
does not.

### 6.7 What these formulas rigorously say about thresholds

For a fixed no-singleton profile, the certified first moment for \(X\) and the
signed first moment for \(\zeta\) are identical and are exactly \(2^k\) times
the ordinary-colouring first moment. Thus their first moment reaches one when
the ordinary profile weight reaches \(2^{-k}\), not one. The unassigned first
moments for \(X\) and \(\zeta\) are asymptotically identical under the explicit
condition in (6.11).

Markov's inequality gives the valid nonexistence bound

\[
\Pr(X\leq k)
\leq\sum_{\ell\leq k}\ \sum_{\substack{\mathbf k:\ 
\sum_s k_s=\ell\\ \sum_s sk_s=n}}
N(\mathbf k)\prod_s q_s^{k_s}.                                \tag{6.13}
\]

An analogous formula holds for \(\zeta\). A large first moment is **not** an
existence theorem; correlations between overlapping partitions are the missing
second-moment/contiguity problem.

### 6.8 Heuristic only: the \(n/(\log n)^3\) displacement

This paragraph is not used as a proof. For balanced parts of real size
\(s=n/k\), the leading Stirling surrogate for the natural logarithm of the
ordinary first moment is

\[
F_n(k)\approx (n-k)\ln k+k-\frac{\ln2}{2}\frac{n^2}{k}
+\frac{\ln2}{2}n.
\]

When \(L=\log_2 n\) and \(k\sim n/(2L)\),

\[
F_n'(k)
=\frac nk-\ln k+\frac{\ln2}{2}\frac{n^2}{k^2}
=(2\ln2+o(1))L^2.
\]

The signed/certified advantage has logarithm \(k\ln2\sim n\ln2/(2L)\).
Equating this to \(F_n'(k)\Delta k\) predicts

\[
\Delta k\sim\frac{n}{4L^3}.
\]

This explains the conjectured order and shows that decoupling does not erase
the \(2^k\) advantage. It does **not** establish the constant or an actual
threshold: optimal integer profiles, oscillatory independence-number jumps,
and overlap correlations remain uncontrolled.

---

## 7. Additional deterministic bounds

Every valid part is independent in the intersection graph, so

\[
\chi(G_1\cap G_2)\leq X(G_1,G_2)
\leq\min\{\chi(G_1),\chi(G_2)\}.                               \tag{7.1}
\]

Here \(G_1\cap G_2\sim G(n,1/4)\). These bounds are rigorous but far too coarse
to estimate \(\mathbb EX\) to \(o(n/(\log n)^3)\).

Also, if \(\alpha_i=\alpha(G_i)\), then

\[
X\geq\frac{n}{\max(\alpha_1,\alpha_2)}.                        \tag{7.2}
\]

Together with (2.9), this recovers the first-order scale of \(X\), but not its
additive displacement from \(\chi\).

---

## 8. Exact obstruction left by this route

The coupling and concentration reduce a positive resolution to either of the
following uniform statements:

1. \(\mathbb E\chi-\mathbb EX\gg\sqrt n\); or
2. a positive-probability surrogate gap with
   \(p_na_n/\sqrt n\to\infty\).

For the conjectured scale, it would suffice to prove

\[
\mathbb E\chi-\mathbb EX\geq c\frac{n}{(\log n)^3}             \tag{8.1}
\]

for a fixed \(c>0\) and every sufficiently large \(n\). The exact first moments
show why (8.1) is plausible, but do not prove it: the unresolved step is to turn
the certified \(2^k\) first-moment advantage into actual existence/nonexistence
information uniformly through the chromatic profile transitions.

The two-graph disorder does not remove the overlap problem. Two candidate
partitions can reuse good bits in either graph, and the assigned-witness first
moment deliberately counts partitions multiple times. Any proof of (8.1) still
needs a second-moment, planted-contiguity, or comparably strong threshold
argument.

---

## 9. Adversarial audit

- **Direction:** \(\Pr(X\leq k)\leq\Pr(\zeta\leq k)\), so
  \(X\) is stochastically larger. The \(n=2\) check is decisive:
  \(\zeta=1\) always, while \(X=2\) with probability \(1/4\).
- **Type of coupling:** the theorem gives a value coupling. It gives neither
  \(X(G_1,G_2)\geq\zeta(G_1)\) nor inclusion of admissible-set families.
- **Joint-law issue:** the coupling does not preserve \(\chi(G)=\chi(G_1)\).
  Proposition 4.1 uses expectations and fresh single-graph concentration to
  avoid this invalid step.
- **Dependence:** \(\chi(G_1)\) and \(X\) are positively correlated, not
  independent. Nonnegativity of \(\chi(G_1)-X\) is what validates the
  positive-probability-to-mean implication.
- **Concentration:** (3.1) is a subgaussian \(\sqrt n\) scale. A whp interval
  needs a diverging multiplier, such as \(\sqrt{\ln n}\).
- **Quantifiers:** a uniform all-large-\(n\) hypothesis proves Problem #625;
  a hypothesis on infinitely many \(n\) proves only a subsequence result.
- **First moments:** signed/certified objects and unassigned partitions are not
  the same random variable. Singleton signs and double certification must be
  treated explicitly.
- **Threshold logic:** expectation much larger than one does not imply an
  admissible partition exists with positive or high probability.

---

## 10. Small-\(n\) enumeration check (not part of the proof)

Exhaustive enumeration gives the following count distributions; denominators
are \(2^{\binom n2}\) for \(\zeta\) and \(2^{2\binom n2}\) for \(X\):

| \(n\) | counts for \(\zeta\) | counts for \(X\) |
|---:|---|---|
| 2 | \(\{1:2\}\) | \(\{1:3,2:1\}\) |
| 3 | \(\{1:2,2:6\}\) | \(\{1:15,2:48,3:1\}\) |
| 4 | \(\{1:2,2:62\}\) | \(\{1:127,2:3686,3:282,4:1\}\) |

Every lower-tail inequality (2.3) holds in these cases.
The explicit sequential transition (2.5)--(2.7) was also exhaustively checked
on all \(4^{\binom n2}\) product outcomes for \(n=2,3,4\): its endpoint law was
uniform on the independent-bit space and \(X\) was nondecreasing on every
outcome. This is a finite verification of the implementation, not part of the
proof.

---

## Source context

The proposal audited here is Zach Hunter's comment of 15 September 2025 on the
[Erdős Problem #625 discussion thread](https://www.erdosproblems.com/forum/thread/625).
The proof above is self-contained; "McDiarmid-style" describes the one-coordinate
interpolation/coupling mechanism rather than invoking a black-box theorem.
