# Section VIII: exact global block-pairing and deficit bridge

**Purpose.** This note supplies the paper-level bridge between the exact
canonical high-skeleton sum and the shortened endpoint/all-deficit estimates.
It also separates the mathematical statement from the remaining Lean
implementation work.

This is a finite argument. No independence between unlabelled skeletons is
asserted. Factorization is used only after fixing a block-level matching
support, whose selected cells have disjoint row and column endpoints.

A crucial distinction is maintained throughout:

- a **block pairing** records which row block is paired with which column block;
- a **physical stub matching** records the actual matched vertices/stubs inside
  each selected block pair.

A partial physical stub matching generally has many full completions. The
argument below does **not** choose a unique completion. Instead, it sums the
physical stub-matching fibre exactly at each multiplicity and compares its
aggregate weight with the aggregate full-containment weight on the same fixed
block pairing.

## 1. Setup

Fix an ordered four-size profile. Its row and column block sizes lie in

\[
  \{U,U-1,U-2,U-3\},
\]

and put

\[
  R_0=\lfloor U/2\rfloor.
\]

The positive support of a canonical high skeleton is a block-level bipartite
matching \(P\) between row and column blocks. For every selected block pair
\(e\in P\), let

\[
  R_0<j_e\le m_e:=\min\{s_e,t_e\},
\]

where \(s_e,t_e\) are its endpoint block sizes. Write

\[
  d_e=|s_e-t_e|\in\{0,1,2,3\},\qquad
  h_e=m_e-j_e,
\]

and

\[
  J=\sum_{e\in P}j_e,\qquad
  J_*=\sum_{e\in P}m_e,\qquad
  H=J_*-J=\sum_{e\in P}h_e.
\]

For a fixed block pairing \(P\) and fixed multiplicity vector \(j\), summing
all physical stub matchings inside its selected cells gives the exact bare
aggregate weight

\[
 w(P,j)
 =
 \frac{\displaystyle\prod_{e\in P}
       (s_e)_{j_e}(t_e)_{j_e}}
      {\displaystyle(n)_J\prod_{e\in P}j_e!}
 \prod_{e\in P}g(j_e),
 \tag{1.1}
\]

with \(g(x)=2^{\binom x2-1}\) for every high multiplicity in the
present range. The factor

\[
  \frac{(s_e)_{j_e}(t_e)_{j_e}}{j_e!}
\]

is exactly the number of size-\(j_e\) physical matchings between the two
endpoint blocks. Thus (1.1) already includes the complete physical fibre; it is
not the weight of one arbitrarily selected stub matching.

## 2. Exact finite parameterization

Every physical canonical high skeleton determines, uniquely:

1. its block-level matching support \(P\);
2. its deficit vector \(h=(h_e)_{e\in P}\), with
   \[
     0\le h_e<m_e-R_0;
   \]
3. for each selected block pair \(e\), a size-\(m_e-h_e\) physical matching
   between its endpoint stubs.

Conversely, these three pieces of data reconstruct one physical canonical high
skeleton. Hence the physical skeleton family is a disjoint union over block
pairings and deficit choices, with a finite product of partial-stub-matching
fibres inside each pair.

After summing those inner physical fibres, the contribution of the parameter
pair \((P,h)\) is precisely \(w(P,m-h)\) from (1.1).

For comparison, define

\[
  w_{\mathrm{full}}(P):=w(P,m),
\]

where \(m=(m_e)_{e\in P}\). This is the **aggregate** weight of all
full-containment physical stub matchings on the same block support \(P\). It is
not obtained by assigning a unique full completion to each partial physical
matching.

The word “physical” remains essential: selected cells are distinguished first
by their actual paired row and column blocks. Grouping block pairings by the
sixteen endpoint types is performed only after this disjoint decomposition.
Consequently there is no additional unlabelled multiplicity beyond the exact
block-pairing fibre cardinality already present in the endpoint table formula.

## 3. Exact one-cell aggregate ratio

Assume without loss of generality that one selected block pair has endpoint
sizes \(m\) and \(m+d\), with \(0\le d\le3\), and put \(j=m-h\). Dividing the
aggregate local factor at multiplicity \(m-h\) by its aggregate
full-containment value gives

\[
 \begin{aligned}
 &\frac{(m)_{m-h}(m+d)_{m-h}}{(m-h)!}
   \frac{m!}{(m)_m(m+d)_m}
   \frac{g(m-h)}{g(m)} \\
 &\qquad=
 \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}
  2^{-hm+h(h+1)/2}
 =:R_{m,d}(h).
 \end{aligned}
 \tag{3.1}
\]

For \(h=0\), the empty product is one and \(R_{m,d}(0)=1\).

The only nonlocal change is the falling-factorial denominator. Since
\(J_*=J+H\),

\[
  \frac{(n)_{J_*}}{(n)_J}=(n-J)_H\le n^H.
 \tag{3.2}
\]

Combining (3.1) and (3.2) yields the global aggregate comparison

\[
 \boxed{
 \frac{w(P,m-h)}{w_{\mathrm{full}}(P)}
 \le
 \prod_{e\in P} n^{h_e}R_{m_e,d_e}(h_e).}
 \tag{3.3}
\]

No product-law approximation occurs in (3.3). The local aggregate ratios
factor because \(P\) is a block matching: each selected cell uses a distinct
row block and a distinct column block. The single global denominator ratio is
handled once, by (3.2).

## 4. Uniform all-deficit charge

The high condition gives \(2h<m\). The exact integer inequality

\[
 h\left\lfloor\frac{2m}{3}\right\rfloor
 \le hm-\frac{h(h+1)}2
 \tag{4.1}
\]

then implies

\[
 n^hR_{m,d}(h)
 \le
 \left(\frac{nm}{2^{\lfloor2m/3\rfloor}}\right)^h.
 \tag{4.2}
\]

Let

\[
 \rho_n=
 \max_{U-3\le m\le U}
 \frac{nm}{2^{\lfloor2m/3\rfloor}}.
 \tag{4.3}
\]

The phase relation \(2^U=\Theta(n^2/N^2)\), where \(N=\ln n\), gives

\[
 \rho_n=O\!\left(\frac{N^{7/3}}{n^{1/3}}\right)=o(1).
 \tag{4.4}
\]

For all sufficiently large \(n\), \(\rho_n\le1/2\). Therefore, for each
selected block pair,

\[
 \sum_{1\le h<m-R_0} n^hR_{m,d}(h)
 \le\sum_{h\ge1}\rho_n^h
 =\frac{\rho_n}{1-\rho_n}
 \le2\rho_n.
 \tag{4.5}
\]

This geometric estimate is the sharp interface needed for the exponent in the
concise manuscript route. Merely bounding each term by \(\rho_n\) and
multiplying by the number of allowed deficits introduces a harmless but
unnecessary extra factor \(U\).

## 5. Sum over one block-pairing fibre

For a fixed block pairing \(P\), sum the aggregate weights (1.1) over every
allowed deficit vector. Applying (3.3) and then (4.5),

\[
 \begin{aligned}
 \sum_{h:\,m-h\text{ high}} w(P,m-h)
 &\le
 w_{\mathrm{full}}(P)
 \prod_{e\in P}
   \left(1+\sum_{1\le h<m_e-R_0}n^hR_{m_e,d_e}(h)\right)\\
 &\le
 w_{\mathrm{full}}(P)(1+2\rho_n)^{|P|}\\
 &\le
 w_{\mathrm{full}}(P)(1+2\rho_n)^{k_{\mathrm{co}}}.
 \end{aligned}
 \tag{5.1}
\]

Now sum over block pairings. Grouping them by their endpoint type table \(L\),
the exact block-pairing factorial identity gives

\[
 \sum_{P}w_{\mathrm{full}}(P)=\sum_LW(L).
 \tag{5.2}
\]

The square-free endpoint transportation and termwise AM--GM estimate give

\[
 \sum_LW(L)
 \le
 (1+C\eta_n)^{k_{\mathrm{co}}}\sum_rD(r),
 \qquad
 \eta_n=O\!\left(\frac{N^{3/2}}{\sqrt n}\right).
 \tag{5.3}
\]

By the all-partial-diagonals estimate, \(\sum_rD(r)=1+o(1)\). Combining
(5.1)--(5.3),

\[
 \begin{aligned}
 \sum_{P}\sum_{h:\,m-h\text{ high}}w(P,m-h)
 &\le
 (1+2\rho_n)^{k_{\mathrm{co}}}
 (1+C\eta_n)^{k_{\mathrm{co}}}(1+o(1)) \\
 &\le
 \exp\!\left\{
 O(n^{2/3}N^{4/3})+O(\sqrt{nN})
 \right\} \\
 &=\exp\!\left\{o\!\left(\frac n{N^4}\right)\right\}.
 \end{aligned}
 \tag{5.4}
\]

The left side is the exact bare canonical high-skeleton sum because the
parameterization in Section 2 is disjoint and (1.1) has already summed every
partial physical stub-matching fibre.

This is the Section VIII bare-skeleton estimate required by the repaired
q-only Section IX attachment theorem.

## 6. Formalization boundary

The repository already contains kernel-checked finite components for:

1. the exact prescribed-demand/typed-partial-matching correspondence;
2. the exact labelled/unlabelled physical skeleton quotient;
3. the endpoint block-pairing factorial identity;
4. the squared endpoint transport inequality and square-free AM--GM bridge;
5. the one-cell aggregate ratio bound (4.2);
6. the optional-deficit product for a fixed endpoint block pairing.

The remaining Lean work is to package one global finite reindexing and one
aggregate weight comparison:

- the equivalence between canonical high physical skeletons and triples
  `(endpoint block pairing, allowed deficit choice, per-cell partial stub
  matching)`;
- the summation of the per-cell physical fibres to (1.1), followed by the
  global comparison (3.3), including the single denominator ratio (3.2);
- the identification of the full-reference block-pairing sum with
  `sum_L fourEndpointW(L)`.

There is deliberately no claimed equivalence between a partial physical
matching and a unique full physical matching.

The current generic Lean product endpoint bounds the sum by a factor of the
form

\[
  \bigl(1+(\alpha+1)\rho_n\bigr)^{|P|},
\]

which gives the weaker exponent \(O(n^{2/3}N^{7/3})\). This is still
\(o(n/N^4)\), so it is sufficient for Proposition 9.2. To match the sharper
paper exponent in (5.4), add the finite geometric-series lemma (4.5) and use
the fact that each positive deficit exponent occurs at most once in one
cell's allowed set.

## 7. Reusable abstract form

The proof above is an instance of an aggregate matching-decoration transfer
principle.

> **Aggregate matching-decoration transfer.** Suppose objects decompose
> disjointly by a block matching \(P\), one deficit \(h_e\) per selected cell,
> and a finite local physical fibre. After summing each local physical fibre,
> assume the aggregate deficit-\(h\) weight is at most \(\rho^h\) times the
> corresponding aggregate full-cell reference weight, with one global
> denominator loss distributed across the deficits. If \(|P|\le k\) and
> \(\rho\le1/2\), then the total decorated weight is at most
> \((1+2\rho)^k\) times the total aggregate reference weight.

This formulation requires no unique completion map. It is potentially
reusable in configuration-model and random-partition second moments whenever
exceptional cells form a matching and their aggregate local deficits have a
geometric charge.
