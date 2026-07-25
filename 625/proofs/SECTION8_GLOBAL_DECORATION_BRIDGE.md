# Section VIII: exact global completion-and-decoration bridge

**Purpose.** This note supplies the paper-level bridge between the exact
canonical high-skeleton sum and the shortened endpoint/all-deficit estimates.
It also separates the mathematical statement from the remaining Lean
implementation work.

This is a finite argument. No independence between unlabelled skeletons is
asserted. Independence is used only inside one fixed matching support, where
selected block pairs have disjoint row and column endpoints.

## 1. Setup

Fix an ordered four-size profile. Its row and column block sizes lie in

\[
  \{U,U-1,U-2,U-3\},
\]

and put

\[
  R_0=\lfloor U/2\rfloor.
\]

A canonical high skeleton consists of a bipartite matching
\(\mathcal M\) between row and column blocks and multiplicities

\[
  R_0<j_e\le m_e:=\min\{s_e,t_e\},\qquad e\in\mathcal M,
\]

where \(s_e,t_e\) are the endpoint block sizes. Write

\[
  d_e=|s_e-t_e|\in\{0,1,2,3\},\qquad
  h_e=m_e-j_e,
\]

and

\[
  J=\sum_{e\in\mathcal M}j_e,\qquad
  J_*=\sum_{e\in\mathcal M}m_e,\qquad
  H=J_*-J=\sum_{e\in\mathcal M}h_e.
\]

The exact bare weight is

\[
 w(\mathcal M,j)
 =
 \frac{\displaystyle\prod_{e=(a,b)\in\mathcal M}
       (s_a)_{j_e}(t_b)_{j_e}}
      {\displaystyle(n)_J\prod_{e\in\mathcal M}j_e!}
 \prod_{e\in\mathcal M}g(j_e),
 \tag{1.1}
\]

with \(g(x)=2^{\binom x2-1}\) for every high multiplicity in the
present range.

## 2. Completion/decorations bijection

For every canonical high skeleton, retain its matching support and complete
all selected cells to full containment:

\[
  (\mathcal M,j)
  \longmapsto
  \left(\mathcal M,m;\,(h_e)_{e\in\mathcal M}\right),
  \qquad m_e=\min\{s_e,t_e\}.
 \tag{2.1}
\]

Conversely, start from a full-containment endpoint matching \(\mathcal M\)
and choose, independently for each selected physical block pair,

\[
  0\le h_e<m_e-R_0.
 \tag{2.2}
\]

Then \(j_e=m_e-h_e\) is high, and the resulting table is a canonical high
skeleton. These two operations are inverse. Hence the canonical high-skeleton
family is the disjoint union, over full endpoint matchings, of their finite
decoration fibres.

The word “physical” is essential: cells are first distinguished by their
actual paired row and column blocks. Grouping by the sixteen endpoint types is
performed only after this disjoint fibre decomposition. Consequently there is
no extra unlabelled multiplicity beyond the existing block-pairing factorials.

## 3. Exact one-cell ratio

Assume without loss of generality that the endpoint sizes are \(m\) and
\(m+d\), with \(0\le d\le3\), and put \(j=m-h\). Dividing the local part of
(1.1) by its full-cell value gives

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

Combining (3.1) and (3.2) yields the exact global comparison

\[
 \boxed{
 \frac{w(\mathcal M,j)}{w(\mathcal M,m)}
 \le
 \prod_{e\in\mathcal M} n^{h_e}R_{m_e,d_e}(h_e).}
 \tag{3.3}
\]

No product-law approximation occurs in (3.3). The product appears because
\(\mathcal M\) is a matching: each selected physical cell uses a distinct row
block and a distinct column block, so all row and column descending-factorial
ratios factor cell by cell. The single global denominator ratio is handled by
(3.2).

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
selected physical cell,

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

## 5. Fibre sum

Summing (3.3) over the decoration fibre of one fixed full endpoint matching
and applying (4.5),

\[
 \sum_{j:\,(\mathcal M,j)\text{ high}}
 w(\mathcal M,j)
 \le
 w(\mathcal M,m)
 \prod_{e\in\mathcal M}(1+2\rho_n)
 \le
 w(\mathcal M,m)(1+2\rho_n)^{k_{\mathrm{co}}}.
 \tag{5.1}
\]

Now sum over full endpoint matchings. Grouping them by their endpoint type
table \(L\), the exact block-pairing factorial identity gives

\[
 \sum_{\mathcal M:\,\text{full endpoint}}
 w(\mathcal M,m)
 =\sum_L W(L).
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
 \sum_{(\mathcal M,j)}w(\mathcal M,j)
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

This is the Section VIII bare-skeleton estimate required by the repaired
q-only Section IX attachment theorem.

## 6. Formalization boundary

The repository already contains kernel-checked finite components for:

1. the exact labelled/unlabelled skeleton quotient;
2. the endpoint block-pairing factorial identity;
3. the squared endpoint transport inequality and square-free AM--GM bridge;
4. the one-cell ratio bound (4.2);
5. the optional-decoration product for a fixed endpoint block pairing.

The remaining Lean work is to package the following one global equivalence and
one weight comparison:

- the equivalence between canonical high physical skeletons and pairs
  `(full endpoint block pairing, allowed deficit choice)`;
- equation (3.3), including the single denominator ratio (3.2).

The current generic Lean product endpoint bounds the sum by a factor of the
form

\[
  \bigl(1+(\alpha+1)\rho_n\bigr)^{|\mathcal M|},
\]

which gives the weaker exponent \(O(n^{2/3}N^{7/3})\). This is still
\(o(n/N^4)\), so it is sufficient for Proposition 9.2. To match the sharper
paper exponent in (5.4), add the finite geometric-series lemma (4.5) and use
the fact that each positive deficit exponent occurs at most once in one
cell's allowed set.

## 7. Reusable abstract form

The proof above is an instance of a general matching-decoration transfer
principle.

> **Matching-decoration transfer.** Suppose base objects carry a matching of
> at most \(k\) selected cells. Completing every cell gives a unique base
> object, and a deficit \(h\ge1\) changes the global weight by at most
> \(\rho^h\), after distributing one global falling-factorial ratio across the
> deficits. If \(\rho\le1/2\), then the total weight of all decorated objects is
> at most \((1+2\rho)^k\) times the total base weight.

This lemma is potentially reusable in configuration-model and random-partition
second moments whenever exceptional cells form a matching and local deficits
have a geometric charge.
