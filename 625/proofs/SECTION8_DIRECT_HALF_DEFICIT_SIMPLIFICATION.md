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
stub decorations of one block support. The total decorated-support space is
then tautologically equivalent to the dependent sum over endpoint tables of
the existing `FourEndpointDecoratedBlockPairing` fibres. This makes

```text
sum_P reference(P) = sum_L W(L)
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

The attained-demand encoding from PR #48 maps into this type by sending zero
deficit to `none`. The decoded table is unchanged, so injectivity follows from
the already checked injectivity of the abstract demand table.

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

## 4. Coarse local charge

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

If a common `rho` dominates the sixteen endpoint-type bases and `rho<=1`, then
one support contributes at most

```text
(1 + (alpha+1)*rho)^|P|.
```

This is intentionally weaker than the sharp geometric estimate
`(1+2rho)^|P|`, but it is easier to formalize and is still far below the target
scale.

## 5. Direct reference grouping

For one abstract support `P`, let `R(P)` be the literal sum of the common
full-containment atom over every independent full stub matching in each
selected cell. Then

```text
Sigma P, full decorations on P
```

is equivalent to

```text
Sigma L, FourEndpointDecoratedBlockPairing(alpha,hAlpha,k,L).
```

The existing exact normalization theorem on each endpoint table therefore
gives

```text
sum_P R(P) = sum_L W(L).
```

No new cell factorial or block-pairing cardinality formula is required.

## 6. Common support-card bound

A block support is itself a partial matching of row block slots to column block
slots. Projection to the row slot is injective, hence

```text
|P| <= total number of row block slots.
```

Thus every support may be charged by the same power. Combining direct deficit
summation, the coarse local charge, the support-card bound, and direct reference
grouping gives the finite reduction

```text
sum_(attained demands) weight(demand)
<=
(sum_L W(L))
  * (1 + (alpha+1)*rho)^(total block count),
```

provided only that each individual attained weight satisfies the pointwise
charged comparison.

## 7. Why this route is easier to formalize

Compared with the old near/middle proof and the first all-deficit plan, the new
route removes:

1. the middle regime entirely;
2. `allHighDeficitCut` from the global analytic assembly;
3. repeated reconstruction of the global cutoff `U/2`;
4. a conversion between two dependent deficit structures after summation;
5. a finite geometric-series theorem;
6. a second endpoint-table cardinality proof;
7. support-dependent exponents in the final table sum.

The analytic assembly now uses only:

- `2h<m`;
- one coarse local base;
- one trivial cardinality bound on deficits;
- one trivial cardinality bound on support size;
- the already checked endpoint-table reference sum.

## 8. Minimal remaining theorem

Once the finite modules on this branch are green, the only genuinely new
Section VIII algebraic theorem is the pointwise charged comparison

```text
profileHighSkeletonWeight(demand)
  <=
fullSupportReference(P)
  * choiceCharge(encoded deficits).
```

PR #53 supplies the exact aggregate formula on the left. The remaining proof
has only two ingredients:

1. compare every partial local factor with its full local factor;
2. apply the single global falling-factorial loss once.

After that theorem, the branch's finite reduction gives the complete
bare-skeleton sum in one line. The remaining work is then purely asymptotic:
prove the common cell base is at most

```text
O((log n)^(5/2)/sqrt n)
```

and apply endpoint transportation.

## 9. Audit boundary

This simplification does not itself prove the bare-skeleton estimate. It
removes data conversion, geometric-series bookkeeping, endpoint regrouping,
and support-card bookkeeping from the remaining proof. The theorem remains
conditional until the pointwise charged comparison and the phase
specialization are integrated and built on one branch.
