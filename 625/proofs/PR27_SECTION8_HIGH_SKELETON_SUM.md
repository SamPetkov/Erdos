# PR #27: split high-skeleton summation

**Status.** Candidate replacement text, audited against current `main` on 24 July 2026.  Exact finite tests are recorded in the PR verification report; the asymptotic chain still requires independent review.

## Replacement block C: split form of Lemma 8.3

### Lemma 8.3A (one-cell near-containment series)

Let the smaller slot size be \(m\), the larger \(m+d\), with \(0\le d\le3\).
Replacing endpoint multiplicity \(m\) by \(m-e\) has exact local ratio

\[
 R_{m,d}(e)=
 \frac{\binom me}{(d+1)\cdots(d+e)}
 2^{-em+e(e+1)/2}.
 \tag{8.21}
\]

Let

\[
 \mathcal E_m=\{e\in\mathbb N:1\le e\text{ and }4e<m\}.
\]

After bounding the one global falling-factorial denominator by \(n^e\),

\[
 \sum_{e\in\mathcal E_m} n^eR_{m,d}(e)=O(N^3/n)
 \tag{8.25}
\]

uniformly over the four cell types.  The consecutive-ratio/log-convexity proof
is the one already displayed in (8.23)--(8.24a).

### Lemma 8.3B (typed decoration fibres and the global product)

Fix a typed full-containment table \(L=(\ell_{ij})\).  For a type
\(\tau=(i,j)\), put

\[
 m_\tau=\min(u_i,u_j),\qquad d_\tau=|u_i-u_j|,
 \qquad C_\tau=\{1,\ldots,\ell_{ij}\},
\]

and set \(E_\tau=\{0\}\cup\mathcal E_{m_\tau}\).  Temporarily distinguish the
\(\ell_{ij}\) occurrences of type \(\tau\).  A labelled decoration is a family
of maps \(\phi_\tau:C_\tau\to E_\tau\).  Define

\[
 a_\tau(0)=1,
 \qquad
 a_\tau(e)=n^eR_{m_\tau,d_\tau}(e)\quad(e>0).
\]

For a typed count array \(n_{\tau,e}\) with
\(\sum_e n_{\tau,e}=\ell_{ij}\), the fibre of the forgetting map

\[
 \phi\longmapsto n_{\tau,e}=|\phi_\tau^{-1}(e)|
\]

has the exact cardinality

\[
 \prod_\tau\frac{\ell_\tau!}{\prod_{e\in E_\tau}n_{\tau,e}!}.
 \tag{8.25a}
\]

Consequently

\[
 \sum_\phi\prod_{\tau}\prod_{c\in C_\tau}a_\tau(\phi_\tau(c))
 =\prod_\tau\left(\sum_{e\in E_\tau}a_\tau(e)\right)^{\ell_\tau}
 \tag{8.25b}
\]

and, after grouping by the arrays \((n_{\tau,e})\), the factor
\(\ell_\tau!\) in (8.25a) cancels exactly with the factor
\(1/\ell_\tau!\) already present in \(W(L)\).  The resulting coefficient is
\(1/\prod_e n_{\tau,e}!\), which is exactly the typed multinomial coefficient
of the decorated table.  There is no hidden multiplicity.

Using Lemma 8.3A and the fact that a high skeleton has at most \(k_{co}\) cells,

\[
 \sum_{\text{near decorations of }L}w(S)
 \le W(L)(1+O(N^3/n))^{k_{co}}
 =W(L)e^{O(N^2)}.
 \tag{8.26}
\]

### Lemma 8.3C (exact middle strip with large residual mass)

Fix a near-containment skeleton \(S\), let \(m_0\) be its remaining stub mass,
and let \(\nu_S\) be the uniform residual matching law.  On the event
\(\mathcal N(S)\) that no additional endpoint or near-containment cell occurs,
a further high cell of type \((i,j)\), with smaller size
\(m_{ij}=\min(u_i,u_j)\), has the exact range

\[
 R_0<r\le m_{ij}-\left\lceil\frac{m_{ij}}4\right\rceil
 =\left\lfloor\frac{3m_{ij}}4\right\rfloor
 \le\left\lfloor\frac{3a}4\right\rfloor.
 \tag{8.26a}
\]

Indeed, writing \(e=m_{ij}-r\), failure of the near condition \(4e<m_{ij}\)
means \(e\ge\lceil m_{ij}/4\rceil\).

If \(m_0\ge n/N^6\), joint expansion over distinct residual cells and their
thresholds, followed by Lemma 6.2, gives

\[
 E_{\rm mid}(S)
 :=\mathbb E_{\nu_S}\!\left[
   \mathbf1_{\mathcal N(S)}\prod_{\text{middle high }e}g(r_e)
 \right]
 \le e^{\Xi_4(S)},
 \tag{8.26b}
\]

where the exact typewise upper bound is

\[
 \Xi_4(S)\le
 \sum_{i,j}k_i k_j
 \sum_{R_0<r\le\lfloor3m_{ij}/4\rfloor}
   g(r)\frac{(ea^2/m_0)^r}{r!}
 \le k_{co}^2
 \sum_{R_0<r\le\lfloor3a/4\rfloor}
   g(r)\frac{(ea^2/m_0)^r}{r!}.
 \tag{8.27}
\]

Put \(L_2=\log_2n\).  Since \(m_0\ge n/N^6\), \(k_{co}\le n\), and
\(g(r)=2^{\binom r2-1}\) for the displayed range,

\[
 \begin{split}
 \log_2\!\left[k_{co}^2g(r)\frac{(ea^2/m_0)^r}{r!}\right]
 \le{}&2L_2+\binom r2-1\\
 &+r\{\log_2e+2\log_2a-L_2+6\log_2N\}.
 \end{split}
 \tag{8.28}
\]

Uniformly, \(a=2L_2-2\log_2L_2+O(1)\) and the exact range (8.26a) gives
\(r/L_2\in[1+o(1),3/2+o(1)]\).  The quadratic coefficient is at most
\(-3/8+o(1)\), while all remaining terms are \(O(L_2\log L_2)\).  Hence, with
the explicit universal choice \(c_0=1/8\), for all sufficiently large \(n\),

\[
 \log_2\!\left[k_{co}^2g(r)\frac{(ea^2/m_0)^r}{r!}\right]
 \le-c_0L_2^2.
 \tag{8.28a}
\]

Thus \(\Xi_4(S)=2^{-\Omega(L_2^2)}\), uniformly in \(S\).

### Lemma 8.3D (small-residual conditional completion)

Suppose \(m_0<n/N^6\).  For a residual completion \(\omega\), let
\(B_S(\omega)\) be the bare reward of the additional high cells.  Since all
factors are nonnegative,

\[
 B_S(\omega)
 \le \left(\prod_e g(r_e)\right)2^{\beta(S\cup H_{\rm res})}.
\]

Every residual degree is at most \(a\), and pointwise

\[
 \beta(S\cup H_{\rm res})\le |E(H_{\rm res})|\le m_0/2,
 \qquad
 \sum_e\binom{r_e}{2}\le(a-1)m_0/2.
 \tag{8.29}
\]

Therefore \(B_S(\omega)\le2^{am_0/2}\le e^{Cam_0}\), and the missing
pointwise-to-global step is the elementary conditional expectation chain

\[
 \begin{split}
 \mathbb E_{\nu_S}[\mathbf1_{\mathcal N(S)}B_S]
 &\le e^{Cam_0}\,\nu_S(\mathcal N(S))\\
 &\le e^{Cam_0}\le e^{Cn/N^5}.
 \end{split}
 \tag{8.29a}
\]

If the residual matching space is empty, the left side is zero and the same
bound holds.  The full local/cycle factor is used here only as a pointwise
majorant for the bare reward.

### Proposition 8.4 (explicit partition and global skeleton sum)

Let \(\mathcal H\) be the finite family of canonical high skeletons.  For a high
cell with smaller slot size \(m\), write \(e=m-r\) and classify it uniquely as

\[
 e=0\quad\text{(endpoint)},\qquad
 0<4e<m\quad\text{(near)},\qquad
 4e\ge m\quad\text{(middle)}.
 \tag{8.29b}
\]

Fix total orders on the row and column slots.  For a labelled high skeleton
\(H\), round every endpoint or near cell up to multiplicity \(m\), retain the
actual selected row--column slot pair, and order the selected pairs of each type
lexicographically.  This produces an endpoint slot matching, a typed table
\(L(H)\), and a uniquely indexed near-deficit assignment \(\phi(H)\).  The
unrounded middle cells remain in the residual matching.  Hence

\[
 H\longmapsto
 \bigl(\text{labelled endpoint witness},L(H),\phi(H),H_{\rm mid}\bigr)
 \tag{8.29c}
\]

is injective.  Its image is generally a proper subset of all formal decoration
and residual data: feasibility, cap, and no-return conditions may rule out some
formal tuples.  Enlarging to all such tuples is therefore a nonnegative
overcount, not an asserted bijection.

For a fixed labelled endpoint witness \(w\) and decoration \(\phi\), write
\(\nu_{w,\phi}\) for the corresponding standardized residual uniform law.  The
unused-stub relabelling equivalence makes the law invariant under replacement
of \(w\) by another witness with the same decorated type data.  Without using
that invariance, one may simply take the supremum over the finite witness
fibre.  The dependent disintegration (8.3b), the exact fibre count (8.25a), the
near-ratio comparison, and conditional residual summation give

\[
 \begin{split}
 \sum_{H\in\mathcal H}\operatorname{Bare}(H)
 &\le\sum_L W(L)
   \sum_{\phi\text{ near}}
      \prod_{\tau,c}a_\tau(\phi_\tau(c))\\
 &\quad\times
   \sup_{w\in\mathcal W(L,\phi)}
   \mathbb E_{\nu_{w,\phi}}[
      \mathbf1_{\mathcal N(w,\phi)}B_{w,\phi}]\\
 &\le e^{O(N^2)}\left(\sum_LW(L)\right)
       \max\{e^{\sup_S\Xi_4(S)},e^{Cn/N^5}\}.
 \end{split}
 \tag{8.29d}
\]

If a witness fibre is empty, its contribution is defined to be zero.  The first
inequality retains the exact canonical extraction and only then drops
feasibility by enlarging a finite nonnegative sum.

Lemma 8.2 and the preceding lemmas now yield

\[
 \sum_{H\in\mathcal H}\operatorname{Bare}(H)
 \le\exp\{O(\sqrt{nN})+O(N^2)+O(n/N^5)\}
 =\exp\{o(n/N^4)\}.
 \tag{8.30}
\]

This states the finite maps, typed fibre cardinalities, and the conditional
expectation step that are required before the asymptotic estimates are applied.

---
