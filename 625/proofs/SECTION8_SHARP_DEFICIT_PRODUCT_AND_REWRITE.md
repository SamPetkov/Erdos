# Section VIII: sharp all-deficit partition function

## Purpose

This note makes two independent improvements to the concise Section VIII
route.

First, the earlier generic Lean bound treated every admissible nonzero deficit
as if it had the same weight `rho` and then multiplied by the number of
possible deficits.  For endpoint size of order `log n`, that produces a local
factor

\[
  1+O((\log n)\rho_n).
\]

The actual deficit weights form a geometric sequence.  Summing the complete
positive-deficit fibre in each distinguishable selected cell before taking the
product gives

\[
  1+O(\rho_n),
\]

with no extra phase-size factor.

Second, the high condition `2h<m` gives the near-sharp integer budget

\[
  h\left\lfloor\frac{3m-1}{4}\right\rfloor
  \le
  hm-\frac{h(h+1)}2,
  \tag{0.1}
\]

which is stronger than the previously used two-thirds budget.  The coefficient
in (0.1) differs from the optimal integer coefficient
\(\lfloor3m/4\rfloor\) by at most one and has the same phase asymptotics.

Together these changes improve the direct all-deficit exponent from

\[
  O\!\left(n^{2/3}(\log n)^{7/3}\right)
\]

in the old cardinality interface, first to

\[
  O\!\left(n^{2/3}(\log n)^{4/3}\right)
\]

by summing geometrically, and then to

\[
  O\!\left(\sqrt n(\log n)^{3/2}\right)
\]

by using (0.1).  Every one of these exponents is sufficient for the normalized
second moment.  The last is the strongest one-step geometric estimate and is
the recommended manuscript version.

The proof order is:

1. sum all deficits inside each distinguishable selected cell;
2. multiply the resulting local partition functions;
3. sum over block supports and endpoint tables only afterward.

## 1. Exact finite product lemma

Let `C` be a finite set of distinguishable selected cells.  For each
\(c\in C\), let \(A_c\) be its finite set of positive deficits and let
\(w_c(h)\ge0\) be the corresponding charged local weight.  A global optional
deficit choice selects either no deficit in a cell, with weight one, or one
element of \(A_c\).  Its weight is the product of the selected local weights.

The exact finite identity is

\[
  \sum_{\text{global choices }\omega}
    \prod_{c\in C}w_c(\omega_c)
  =
  \prod_{c\in C}
    \left(1+\sum_{h\in A_c}w_c(h)\right).
  \tag{1.1}
\]

This is already kernel-checked as

```text
sum_nearSkeletonChoiceWeight_eq_product.
```

The new module

```text
Erdos625/Section8SharpDeficitProduct.lean
```

adds the cellwise inequality: if

\[
  \sum_{h\in A_c}w_c(h)\le\sigma_c
  \qquad(c\in C),
\]

then

\[
  \boxed{
  \sum_\omega w(\omega)
  \le
  \prod_{c\in C}(1+\sigma_c).}
  \tag{1.2}
\]

The local bounds \(\sigma_c\) may vary with the endpoint type.  Replacing them
by one maximum is optional, not built into the argument.

The corresponding Lean declarations are

```text
sum_nearSkeletonChoiceWeight_le_product_of_local_sums
sum_nearSkeletonChoiceWeight_le_uniform_local_sum
sum_nearSkeletonChoiceWeight_le_cellwise_two_rho
sum_nearSkeletonChoiceWeight_le_uniform_two_rho.
```

## 2. Aggregate ratio for one high cell

Fix a selected block pair with endpoint sizes \(m\) and \(m+d\), where
\(0\le d\le3\).  Its full multiplicity is \(m\).  If its actual high
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

Consequently

\[
  \boxed{
  \frac{w(P,m-h)}{w_{\mathrm{full}}(P)}
  \le
  \prod_{e\in P}n^{h_e}R_{m_e,d_e}(h_e).}
  \tag{2.3}
\]

Equation (2.3) uses one global denominator estimate.  It does not introduce a
separate configuration-model normalization in every selected cell.

## 3. Three-quarter geometric charge

The high condition gives

\[
  2h<m.
\]

The kernel-checked theorem

```text
highDeficit_threeQuarter_exponent_budget
```

states (0.1).  Combining it with

\[
  \binom mh\le m^h,
  \qquad
  (d+1)\cdots(d+h)\ge1,
\]

gives

\[
  n^hR_{m,d}(h)
  \le
  \left(
    \frac{nm}{2^{\lfloor(3m-1)/4\rfloor}}
  \right)^h.
  \tag{3.1}
\]

Define the cell-dependent charge

\[
  \rho_e
  :=
  \frac{n m_e}{2^{\lfloor(3m_e-1)/4\rfloor}}.
  \tag{3.2}
\]

If \(\rho_e\le1/2\), then the complete positive-deficit fibre in cell \(e\)
satisfies

\[
  \sum_{h\ge1}n^hR_{m_e,d_e}(h)
  \le
  \sum_{h\ge1}\rho_e^h
  =
  \frac{\rho_e}{1-\rho_e}
  \le2\rho_e.
  \tag{3.3}
\]

The actual admissible range is finite, so extending it to the infinite series
only enlarges the sum.  No factor counting the admissible deficits occurs.

Applying (1.2) gives

\[
  \boxed{
  \sum_{h:\,m-h\text{ high}}w(P,m-h)
  \le
  w_{\mathrm{full}}(P)
  \prod_{e\in P}(1+2\rho_e).}
  \tag{3.4}
\]

Writing \(\rho_n=\max_e\rho_e\), one obtains the uniform corollary

\[
  \sum_h w(P,m-h)
  \le
  w_{\mathrm{full}}(P)(1+2\rho_n)^{|P|}.
  \tag{3.5}
\]

The previous generic interface gave \((1+U\rho_n)^{|P|}\), where
\(U=\Theta(\log n)\).  Since \(2\rho_n\le U\rho_n\) for \(U\ge2\), (3.5) is
never worse and avoids the artificial factor \(U\).

## 4. Phase scale

For the four endpoint sizes, the phase relation

\[
  2^{m}=\Theta\!\left(\frac{n^2}{(\log n)^2}\right)
\]

holds uniformly up to constant factors.  Therefore

\[
  \rho_n
  =
  O\!\left(
    \frac{(\log n)^{5/2}}{\sqrt n}
  \right)
  =o(1).
  \tag{4.1}
\]

The support is a matching, so
\(|P|\le k_{\mathrm{co}}=\Theta(n/\log n)\).  Using
\(\log(1+x)\le x\),

\[
  (1+2\rho_n)^{k_{\mathrm{co}}}
  \le
  \exp\{2k_{\mathrm{co}}\rho_n\}
  =
  \exp\!\left\{
    O\!\left(\sqrt n(\log n)^{3/2}\right)
  \right\}.
  \tag{4.2}
\]

The endpoint transportation term remains

\[
  \exp\{O(\sqrt{n\log n})\}.
  \tag{4.3}
\]

Both exponents are

\[
  o\!\left(\frac{n}{(\log n)^4}\right).
\]

Once the attained-demand reindexing and pointwise aggregate weight identity are
connected to this product, the resulting bare-skeleton estimate is

\[
  \operatorname{BareSkeletonSum}_n
  \le
  \exp\!\left\{
    O\!\left(\sqrt n(\log n)^{3/2}\right)
    +O(\sqrt{n\log n})
  \right\}.
  \tag{4.4}
\]

### Optional head--tail refinement

The one-step estimate (4.2) is the recommended proof because it is short.  A
further refinement is available by separating the first deficit:

\[
  nR_{m,d}(1)
  =
  \frac{nm}{d+1}2^{-m+1}
  =O\!\left(\frac{(\log n)^3}{n}\right).
  \tag{4.5}
\]

For the tail \(h\ge2\), (3.1) gives

\[
  \sum_{h\ge2}n^hR_{m,d}(h)
  \le
  \frac{\rho_n^2}{1-\rho_n}
  =O\!\left(\frac{(\log n)^5}{n}\right).
  \tag{4.6}
\]

Thus the local positive-deficit mass is
\(O((\log n)^5/n)\), and multiplying over at most \(O(n/\log n)\) cells gives
an all-deficit exponent \(O((\log n)^4)\).  This refinement is exact at the
finite head--tail level and is checked by the Python regression, but is not
needed for the main theorem or the Lean product interface.

## 5. Reader-first Section VIII proof

The eventual manuscript proof reduces to four steps.

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

### Step C: sum deficits before supports

Use (3.3) in each selected cell and the exact product identity (1.1) to obtain
(3.4).  This is the only place the new sharp product interface is needed.

### Step D: transport full references

Group full block supports by their endpoint table \(L\).  The exact decorated
endpoint normalization gives \(W(L)\), and square-free AM--GM transportation
gives

\[
  \sum_LW(L)
  \le
  \exp\{O(\sqrt{n\log n})\}\sum_rD(r).
\]

The partial-diagonal sum is \(1+o(1)\).  Combining the four steps gives (4.4).

This order separates exact finite identities from asymptotic estimates and
removes the old near/middle case split.

## 6. Worked two-cell example

Let the selected support contain two cells with

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

The ambient denominator is bounded once:

\[
  (n-12)_3\le n^3=n^{h_1}n^{h_2}.
\]

Hence

\[
  \frac{w(P,(7,5))}{w_{\mathrm{full}}(P)}
  \le
  \bigl(nR_{8,1}(1)\bigr)
  \bigl(n^2R_{7,2}(2)\bigr).
\]

Summing every possible deficit independently in the two cells gives the product
of the two local partition functions.  There is no additional ordering factor
and no second ambient denominator.

## 7. Formal and computational status

The new Lean modules prove:

```text
sum_nearSkeletonChoiceWeight_le_product_of_local_sums
sum_nearSkeletonChoiceWeight_le_uniform_local_sum
sum_nearSkeletonChoiceWeight_le_cellwise_two_rho
sum_nearSkeletonChoiceWeight_le_uniform_two_rho
highDeficit_threeQuarter_exponent_budget.
```

The standard-library regression

```text
625/experiments/section8_sharp_deficit_product.py
```

checks exactly:

- the local ratio (2.1);
- both the two-thirds and three-quarter exponent budgets;
- the charged local ratio for many finite values;
- finite geometric sums and the `2 rho` bound;
- the optional first-term plus geometric-tail refinement;
- exact partition-function factorization over distinguishable cells;
- the sharp `2 rho` versus old `U rho` comparison;
- cellwise endpoint-type retention;
- all relevant error scales compared with \(n/(\log n)^4\).

The script verifies arithmetic and bookkeeping.  It is not a substitute for
the remaining Lean reindexing theorem or the phase asymptotics.

## 8. Remaining boundary

This note does not claim that the Erdős 625 proof is closed.  The following
interfaces remain load-bearing:

1. a green attained-demand support/deficit injection on the actual midpoint
   profile;
2. the pointwise equality between `profileHighSkeletonWeight` and the aggregate
   partial-cell weight indexed by that support and deficit vector;
3. the specialization of the local geometric estimate to the attained
   endpoint cells;
4. the final composition with endpoint transportation and the q-only Section
   IX theorem.

The mathematical improvement here is exact: once those interfaces are
connected, the all-deficit contribution admits the short bound
\(\exp\{O(\sqrt n(\log n)^{3/2})\}\), with an optional head--tail refinement to
\(\exp\{O((\log n)^4)\}\).
