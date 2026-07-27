# Section VIII: sharp all-deficit partition function

## Purpose

This note replaces the last avoidable loss in the concise Section VIII route.
The earlier generic Lean bound treated every admissible nonzero deficit as if
it had the same weight `rho` and then paid for the number of possible deficits.
For a cell of endpoint size of order `log n`, this produces a local factor

\[
  1+O((\log n)\rho_n).
\]

The actual deficit weights decrease geometrically. Summing them before taking
the product gives

\[
  1+O(\rho_n),
\]

with no extra phase-size factor. This yields the cleaner exponent

\[
  O\!\left(n^{2/3}(\log n)^{4/3}\right)
\]

instead of the still-sufficient but weaker

\[
  O\!\left(n^{2/3}(\log n)^{7/3}\right).
\]

The improvement is not a change of probabilistic model. It is the exact order
in which a finite partition function should be summed:

1. sum all deficits inside each distinguishable selected cell;
2. multiply the resulting cell partition functions;
3. only then sum over block supports and endpoint tables.

## 1. Exact finite product lemma

Let `C` be a finite set of distinguishable selected cells. For each cell
\(c\in C\), let \(A_c\) be its finite set of positive deficits and let
\(w_c(h)\ge0\) be the corresponding charged local weight. A global optional
deficit choice either chooses no deficit in a cell, with weight one, or chooses
one element of \(A_c\). Its weight is the product of the selected local
weights.

The exact finite identity is

\[
  \sum_{\text{global choices }\omega}
    \prod_{c\in C}w_c(\omega_c)
  =
  \prod_{c\in C}
    \left(1+\sum_{h\in A_c}w_c(h)\right).
  \tag{1.1}
\]

Here the convention is that the local factor is one when no deficit is chosen.
This is already kernel-checked as

```text
sum_nearSkeletonChoiceWeight_eq_product.
```

The new module

```text
Erdos625/Section8SharpDeficitProduct.lean
```

adds the following sharper interface. If

\[
  \sum_{h\in A_c}w_c(h)\le \sigma_c
  \qquad(c\in C),
\]

then

\[
  \boxed{
  \sum_{\omega}w(\omega)
  \le
  \prod_{c\in C}(1+\sigma_c).}
  \tag{1.2}
\]

The theorem retains the cell-dependent values \(\sigma_c\); replacing them by
one maximum is optional rather than built into the argument.

## 2. Local ratio for one high cell

Fix one selected block pair with endpoint sizes \(m\) and \(m+d\), where
\(0\le d\le3\). Its full multiplicity is \(m\). If the actual high
multiplicity is \(j=m-h\), then after summing the literal partial-stub-matching
fibre, the exact local ratio relative to full containment is

\[
  R_{m,d}(h)
  =
  \frac{\binom mh}{(d+1)(d+2)\cdots(d+h)}
  2^{-hm+h(h+1)/2}.
  \tag{2.1}
\]

For \(h=0\), the empty product is one and \(R_{m,d}(0)=1\).

For a fixed block support \(P\), put

\[
  J=\sum_{e\in P}(m_e-h_e),
  \qquad
  H=\sum_{e\in P}h_e.
\]

The only nonlocal change is the ambient falling-factorial denominator:

\[
  \frac{(n)_{J+H}}{(n)_J}
  =(n-J)_H
  \le n^H.
  \tag{2.2}
\]

Consequently the aggregate charged weight satisfies

\[
  \frac{w(P,m-h)}{w_{\mathrm{full}}(P)}
  \le
  \prod_{e\in P} n^{h_e}R_{m_e,d_e}(h_e).
  \tag{2.3}
\]

Equation (2.3) uses one global denominator estimate, not one configuration-model
normalization per cell.

## 3. Sharp geometric charge

The canonical high condition gives

\[
  2h<m.
\]

The exact integer inequality

\[
  h\left\lfloor\frac{2m}{3}\right\rfloor
  \le
  hm-\frac{h(h+1)}2
  \tag{3.1}
\]

implies

\[
  n^hR_{m,d}(h)
  \le
  \left(
    \frac{nm}{2^{\lfloor2m/3\rfloor}}
  \right)^h.
  \tag{3.2}
\]

Define the cell-dependent charge

\[
  \rho_e
  :=
  \frac{n m_e}{2^{\lfloor2m_e/3\rfloor}}.
  \tag{3.3}
\]

If \(\rho_e\le1/2\), then the entire positive-deficit fibre in cell \(e\)
satisfies

\[
  \sum_{h\ge1}n^hR_{m_e,d_e}(h)
  \le
  \sum_{h\ge1}\rho_e^h
  =
  \frac{\rho_e}{1-\rho_e}
  \le2\rho_e.
  \tag{3.4}
\]

The finite admissible deficit range is a subset of the infinite series, so no
factor counting the number of deficits is present.

Applying (1.2) gives the fixed-support estimate

\[
  \boxed{
  \sum_{h:\,m-h\text{ high}}w(P,m-h)
  \le
  w_{\mathrm{full}}(P)
  \prod_{e\in P}(1+2\rho_e).}
  \tag{3.5}
\]

This cellwise form is slightly sharper than replacing every \(\rho_e\) by
\(\rho_n=\max_e\rho_e\). The uniform corollary is

\[
  \sum_h w(P,m-h)
  \le
  w_{\mathrm{full}}(P)(1+2\rho_n)^{|P|}.
  \tag{3.6}
\]

The previous generic cardinality interface gave

\[
  (1+U\rho_n)^{|P|},
\]

where \(U=\Theta(\log n)\). Since \(2\rho_n\le U\rho_n\) for \(U\ge2\),
(3.6) is never worse and is asymptotically sharper by one factor of \(\log n\)
in the exponent.

## 4. Phase scale

For the four endpoint sizes, the phase relation gives

\[
  \rho_n
  =
  O\!\left(
    \frac{(\log n)^{7/3}}{n^{1/3}}
  \right)
  =o(1).
  \tag{4.1}
\]

The block support is a matching and therefore has at most
\(k_{\mathrm{co}}=\Theta(n/\log n)\) selected cells. From
\(\log(1+x)\le x\),

\[
  (1+2\rho_n)^{k_{\mathrm{co}}}
  \le
  \exp\{2k_{\mathrm{co}}\rho_n\}
  =
  \exp\!\left\{
    O\!\left(n^{2/3}(\log n)^{4/3}\right)
  \right\}.
  \tag{4.2}
\]

The endpoint transportation term is

\[
  \exp\{O(\sqrt{n\log n})\}.
  \tag{4.3}
\]

Both exponents are

\[
  o\!\left(\frac{n}{(\log n)^4}\right).
\]

Once the attained-demand reindexing and pointwise aggregate weight identity are
connected to this product, the bare-skeleton estimate becomes

\[
  \operatorname{BareSkeletonSum}_n
  \le
  \exp\!\left\{
    O\!\left(n^{2/3}(\log n)^{4/3}\right)
    +O(\sqrt{n\log n})
  \right\}.
  \tag{4.4}
\]

## 5. Reader-first proof of the Section VIII step

The eventual manuscript proof can be reduced to the following sequence.

### Step A: exact reindexing

Every attained canonical high demand determines uniquely:

- a block-level matching support \(P\);
- one admissible deficit \(h_e\) in each selected cell;
- the local partial-stub-matching fibre already summed into the aggregate
  weight.

This is the finite seam targeted by PR #48 and its successors.

### Step B: compare with the full endpoint reference

For fixed \((P,h)\), use (2.1) cell by cell and use (2.2) once globally to
obtain (2.3).

### Step C: sum all deficits before summing supports

Use (3.4) in each cell and the exact product identity (1.1) to obtain (3.5).
This is where the new sharp product interface is used.

### Step D: sum full references

Group full block supports by their endpoint table \(L\). The exact decorated
endpoint normalization gives \(W(L)\), and square-free AM--GM transportation
gives

\[
  \sum_LW(L)
  \le
  \exp\{O(\sqrt{n\log n})\}\sum_rD(r).
\]

The partial-diagonal sum is \(1+o(1)\). Combining these statements gives
(4.4).

This order makes the proof auditable: exact finite identities are completed
before asymptotic estimates are introduced.

## 6. Worked two-cell example

Let the selected support have two cells with

\[
  (m_1,d_1,h_1)=(8,1,1),
  \qquad
  (m_2,d_2,h_2)=(7,2,2).
\]

Then

\[
  (j_1,j_2)=(7,5),
  \qquad J=12,
  \qquad H=3.
\]

The exact aggregate ratio is

\[
  \frac{(n)_{15}}{(n)_{12}}
  R_{8,1}(1)R_{7,2}(2)
  =(n-12)_3R_{8,1}(1)R_{7,2}(2).
\]

The global denominator is bounded once:

\[
  (n-12)_3\le n^3=n^{h_1}n^{h_2}.
\]

Thus

\[
  \frac{w(P,(7,5))}{w_{\mathrm{full}}(P)}
  \le
  \bigl(nR_{8,1}(1)\bigr)
  \bigl(n^2R_{7,2}(2)\bigr).
\]

Summing every possible deficit independently in the two cells gives the product
of their two local partition functions. There is no additional ordering
factor and no second ambient denominator.

## 7. Formal and computational status

The new Lean module proves only the finite product interfaces:

```text
sum_nearSkeletonChoiceWeight_le_product_of_local_sums
sum_nearSkeletonChoiceWeight_le_uniform_local_sum
sum_nearSkeletonChoiceWeight_le_cellwise_two_rho
sum_nearSkeletonChoiceWeight_le_uniform_two_rho
```

It deliberately assumes the local estimates (3.4). The standard-library
regression script

```text
625/experiments/section8_sharp_deficit_product.py
```

checks exactly:

- the formula (2.1);
- the two-thirds charge (3.2);
- finite geometric sums and the `2 rho` bound;
- exact finite product factorization over distinguishable cells;
- the comparison between the sharp `2 rho` and old `U rho` interfaces;
- the sharp and old asymptotic error scales.

The script is evidence for arithmetic and bookkeeping. It is not a substitute
for the remaining Lean reindexing theorem or the phase asymptotics.

## 8. Remaining boundary

This note does not claim that the Erdős 625 proof is closed. The following
interfaces remain load-bearing:

1. a green attained-demand support/deficit injection on the actual midpoint
   profile;
2. the pointwise equality between `profileHighSkeletonWeight` and the aggregate
   partial-cell weight indexed by that support and deficit vector;
3. the specialization of the local geometric estimate to the attained
   endpoint cells;
4. the final composition with endpoint transportation and the q-only Section
   IX theorem.

The mathematical improvement here is narrower but exact: once those interfaces
are connected, the all-deficit cost has the sharp exponent
\(O(n^{2/3}(\log n)^{4/3})\), and the corresponding manuscript argument can be
written in four short steps instead of a near/middle case split.
