# Section VIII: direct half-deficit assembly

## 1. What is being simplified

After the exact physical-fibre and pointwise weight identity in PR #53, the
remaining proof should not pass through another bespoke hierarchy of

```text
exact high deficit subtype
-> optional deficit choice
-> local product expansion.
```

The analytic theorem already uses an optional choice in every distinguishable
block cell. The clean route is therefore to encode attained demands directly
into that same type.

The second simplification is a harmless enlargement. An attained high cell has
full endpoint multiplicity `m`, actual multiplicity `j`, and deficit

```text
h = m-j.
```

The canonical high condition implies

```text
2h < m.
```

For an upper bound there is no need to preserve the more complicated exact
window

```text
h <= m - (U/2+1).
```

We may sum every positive deficit satisfying `2h<m`. The extra terms are
nonnegative, and the sharper three-quarter exponent estimate is stated exactly
under this simpler hypothesis.

A third simplification is to avoid a formal geometric-series lemma. The
three-quarter cell base is already so small that paying the crude bound

```text
number of positive deficits <= alpha+1
```

still gives a subcritical exponent. Thus the finite proof can use the existing
cardinality interface instead of proving an exact finite geometric sum.

Finally, the zero-deficit reference is defined literally as the sum over full
stub decorations of one block support. The ambient type of all natural-valued
four-by-four tables is infinite, so the correct table index is the finite image
of the block-support space. Grouping over that attained table type makes

```text
sum_P reference(P) = sum_(attained L) W(L)
```

a finite reindexing theorem rather than another factorial calculation.

## 2. Direct data type

For an abstract block matching `P`, define

```text
allowed_P(e) = {h >= 1 : 2h < m_e}.
```

A support/choice datum is

```text
(P, omega),
```

where `omega(e)` is either

- `none`, representing `h_e=0` and full containment; or
- `some h`, with `h in allowed_P(e)`.

This is precisely `NearSkeletonChoice`. Decoding gives

```text
j_e = m_e                       if omega(e)=none,
j_e = m_e-h_e                   if omega(e)=some h_e.
```

The attained-demand encoding maps into this type by sending zero deficit to
`none`. The decoded table is unchanged, so injectivity follows from the already
checked injectivity of the abstract demand table.

## 3. Exact finite summation

Let `R(P)` be any nonnegative reference weight on block supports, and let

```text
q(P,e,h)
```

be the charged local deficit ratio. The charged weight of `(P,omega)` is

```text
R(P) * product_e q(P,e,omega(e)),
```

with the convention that `none` contributes one.

The direct finite assembly gives

```text
sum_(P,omega) chargedWeight(P,omega)
=
sum_P R(P) * product_e
  (1 + sum_(h in allowed_P(e)) q(P,e,h)).
```

If each attained demand weight is bounded pointwise by its encoded charged
weight, injectivity gives the same right-hand side as an upper bound for the
entire attained family. There is no extra factor for:

- the number of deficit vectors;
- identical endpoint types;
- a choice of physical full completion;
- conversion between two deficit representations.

## 4. Pay the global denominator only once

The ambient falling-factorial normalization is global. It must not be split
among the cells before the exact aggregate identity is established.

If the full support carries total multiplicity `J` and the total deficit is
`H`, the exact denominator comparison is

```text
1/(n)_(J-H) <= n^H/(n)_J.
```

The generic product module now proves the following interface. If every local
actual factor satisfies

```text
actual_e <= full_e * localRatio_e,
```

then

```text
[product_e actual_e] / (n)_(J-H)
<=
[product_e full_e] / (n)_J
  * product_e [n^(h_e) * localRatio_e].
```

Thus the single global loss `n^H` is absorbed into the local charged terms only
after it has been paid once. This is the exact logical order needed in the
pointwise charged comparison.

## 5. Coarse local charge

Define

```text
rho(n,m) = n*m / 2^floor((3m-1)/4).
```

Under `2h<m`, discard the endpoint-distance denominator in the exact ratio,
bound `choose(m,h)` by `m^h`, and apply the checked three-quarter exponent
budget. This yields

```text
nearCellTerm(n,m,d,h) <= rho(n,m)^h.
```

The bound is independent of the endpoint distance `d`.

There are only sixteen endpoint types. Define the canonical common base

```text
rho_16(n,alpha)
  = sum_(i,j in Fin 4) rho(n,m_ij).
```

Every selected cell base is automatically at most `rho_16`, so no
support-dependent domination premise remains. If `rho_16<=1`, one support
contributes at most

```text
(1 + (alpha+1)*rho_16)^|P|.
```

This is intentionally weaker than the sharp geometric estimate
`(1+2rho)^|P|`, but it is easier to formalize and remains far below the target
scale.

## 6. Direct reference grouping

For one abstract support `P`, let `R(P)` be the literal sum of the common
full-containment atom over every independent full stub matching in each
selected cell.

The finite endpoint-table type is

```text
image(
  FourEndpointAbstractBlockSkeleton,
  P |-> supportTable(P)).
```

The total decorated-support space is equivalent to

```text
Sigma L : attained endpoint table,
  FourEndpointDecoratedBlockPairing(alpha,hAlpha,k,L).
```

The existing exact normalization theorem on each endpoint table therefore
gives

```text
sum_P R(P) = sum_(attained L) W(L).
```

No new cell factorial or block-pairing cardinality formula is required, and no
sum over the infinite type `Nat^(4x4)` is introduced.

## 7. Common support-card bound

A block support is itself a partial matching of row block slots to column block
slots. Projection to the row slot is injective, hence

```text
|P| <= total number of row block slots.
```

Thus every support may be charged by the same power. Combining direct deficit
summation, the canonical common base, the support-card bound, and direct
reference grouping gives the finite reduction

```text
sum_(attained demands) weight(demand)
<=
(sum_(attained L) W(L))
  * (1 + (alpha+1)*rho_16)^(total block count),
```

provided only that each individual attained weight satisfies the pointwise
charged comparison.

## 8. A coarser phase estimate is enough

The sharp estimate

```text
rho_16 = O((log n)^(5/2)/sqrt n)
```

is not needed to close the second moment.

The phase satisfies

```text
phaseNat(n) ~ (2/log 2) log n,
```

and `2/log 2 > 5/2`. Hence eventually

```text
(5/2) log n <= phaseNat(n).
```

Every endpoint overlap size obeys

```text
m_ij >= alpha-5,
```

and the finite floor arithmetic gives

```text
3*alpha-19 <= 4*floor((3*m_ij-1)/4).
```

Using only `log 2 > 2/3`, the resulting logarithmic denominator budget is

```text
(5/4) log n - 19/6
  <=
(log 2) * floor((3*m_ij-1)/4).
```

After exponentiation this yields the much coarser bound

```text
rho(n,m_ij) = O(log n / n^(1/4)).
```

Even after paying `alpha+1=O(log n)` and a support size of order `n/log n`, the
logarithm of the global deficit factor is only

```text
O(n^(3/4) log n),
```

which is still

```text
o(n/(log n)^4).
```

Thus the phase formalization no longer needs the sharp square-root-scale local
asymptotic. It only needs an elementary exponential conversion from the checked
five-fourths logarithmic budget.

## 9. Why this route is easier to formalize

Compared with the old near/middle proof and the first all-deficit plan, the new
route removes:

1. the middle regime entirely;
2. `allHighDeficitCut` from the global analytic assembly;
3. repeated reconstruction of the global cutoff `U/2`;
4. conversion between two dependent deficit structures after summation;
5. a finite geometric-series theorem;
6. a second endpoint-table cardinality proof;
7. support-dependent exponents in the final table sum;
8. support-dependent local-base hypotheses;
9. the sharp phase estimate as a necessary prerequisite.

The analytic assembly now uses only:

- `2h<m`;
- one coarse local base;
- one trivial cardinality bound on deficits;
- one trivial cardinality bound on support size;
- the finite attained endpoint-table reference sum;
- the coarse corridor `(5/2)log n <= phaseNat(n)`.

## 10. Minimal remaining theorem

Once the finite modules on this branch are green, the only genuinely new
Section VIII algebraic theorem is the endpoint-specific pointwise charged
comparison

```text
profileHighSkeletonWeight(demand)
  <=
fullSupportReference(P)
  * choiceCharge(encoded deficits).
```

PR #53 supplies the exact aggregate formula on the left. The remaining proof
has only two ingredients:

1. identify the exact partial/full local factorial-and-reward ratio;
2. invoke the now-checked single global falling-factorial loss once.

After that theorem, the branch's finite reduction gives the complete
bare-skeleton sum in one line. The remaining asymptotic work is reduced to:

1. exponentiate the coarse endpoint budget;
2. bound the explicit sixteen-term `rho_16`;
3. apply the already checked endpoint transportation estimate.

## 11. Audit boundary

This simplification does not itself prove the bare-skeleton estimate. It
removes data conversion, geometric-series bookkeeping, endpoint regrouping,
support-card bookkeeping, and the sharp phase estimate from the necessary
proof path. The theorem remains conditional until the endpoint-specific
pointwise charged comparison and the coarse exponential conversion are
integrated and built on one branch.
