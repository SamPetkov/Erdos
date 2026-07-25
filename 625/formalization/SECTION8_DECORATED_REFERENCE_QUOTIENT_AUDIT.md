# Section VIII decorated endpoint reference audit

## Purpose

This stack closes the exact full-endpoint normalization calculation for one
four-type endpoint table. It combines three finite layers:

1. selection and pairing of row and column blocks according to the table;
2. selection and bijective matching of the physical stubs inside every chosen
   full endpoint cell;
3. multiplication by the common signed local reward and the ambient
   falling-factorial normalization.

The final result is the exact manuscript weight `fourEndpointW`. It is a finite
normalization theorem, not an asymptotic estimate.

## 1. Combined cardinality quotient

For a full endpoint table `L`, the repository already proved separately

```text
card(block pairings) * cell-table factorials
  = row block selections * column block selections,
```

and

```text
card(decorated block pairings) * cell-stub factorials
  = card(block pairings) * cell-stub selections.
```

`Section8EndpointDecoratedReferenceQuotient.lean` multiplies these identities
in the correct order and obtains

```text
card(decorated block pairings)
  * (cell-table factorials * cell-stub factorials)
=
(row block selections * column block selections)
  * cell-stub selections.
```

No cancellation is performed in `Nat`. The combined denominator is proved
positive, then cast to `ENNReal` and divided only with explicit nonzero and
finite side conditions.

The public declarations are:

1. `card_fourEndpointDecoratedBlockPairing_mul_denominator`;
2. `fourEndpointDecoratedDenominator_ne_zero`;
3. `ennreal_card_fourEndpointDecoratedBlockPairing_eq_quotient`;
4. `sum_fourEndpointDecoratedBlockPairing_const_eq_quotient_mul`.

Thus there is exactly one factorial for identical block-pair types, exactly one
factorial for every local stub bijection, and no hidden ordering multiplicity.

## 2. Common full-endpoint atom weight

`Section8EndpointDecoratedReferenceWeight.lean` defines the common contribution
of one fully decorated endpoint block pairing:

```text
full signed reward product / (n)_{J(L)}.
```

It proves that summing this constant atom over the whole decorated endpoint
family is exactly the combined quotient coefficient times that atom:

```text
sum_fourEndpointDecoratedReferenceAtomWeight_eq_quotientWeight.
```

## 3. Exact identification with `fourEndpointW`

The local quotient cannot be simplified in `ENNReal` by an unrestricted
product-of-divisions rule, because such a rule is invalid at zero and infinity.
`Section8EndpointDecoratedReferenceIdentification.lean` therefore proves the
cross-multiplied identity first:

```text
fourEndpointLocalProduct * cell-stub factorial product
  = cell-stub selection product * full signed reward product.
```

Every cancelled factorial is a positive finite natural cast. This gives

```text
fourEndpointLocalProduct
  = cell-stub selection quotient * full signed reward product,
```

and hence the exact endpoint normalization theorem

```text
sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW.
```

In words: summing over every selected block pairing and every full-cell physical
stub matching with type table `L` gives exactly `fourEndpointW n alpha hAlpha
k L`. No symmetry factor is missing and none is duplicated.

The focused Lean 4.31 workflow builds this theorem and its complete dependency
closure under `--wfail`, after rejecting placeholders and project-defined
axioms/constants. The same workflow validates the added bibliography entries.

## 4. Relation to the Section VIII closure problem

This closes the **decorated full-endpoint reference normalization**. It is the
reference measure against which the all-high deficit ratios are charged.

The repository also contains

```text
fourEndpointDecoratedBlockPairingToPhysicalFibre
```

and proves that its output is endpoint-only, block-matching, and has the
prescribed full table. A complete identification with the separately defined
`FourEndpointPhysicalFibre` still requires the reverse construction and the two
round trips, or an equivalent weighted injectivity/surjectivity theorem.

The remaining nonendpoint task is the aggregate deficit reindexing: every
attained canonical high physical skeleton must be summed over its endpoint block
support, one allowed multiplicity deficit per selected cell, and the associated
partial stub-matching fibre. The exact one-cell ratio, its cross-multiplied
normalization, and the product majorant are already present in the cumulative
stack.

## 5. Trust boundary

These results do not by themselves establish Lemma 8.3, Proposition 9.2, or
`Erdos625Statement`. They remove one previously ambiguous normalization seam
from that route. The remaining theorem is now a physical-fibre/deficit
reindexing theorem, not an unresolved endpoint factorial calculation.
