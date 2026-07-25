# Section VIII decorated endpoint reference quotient audit

## Purpose

This module combines two finite enumerations that were previously available
only as separate cross-multiplied identities:

1. selection and pairing of row and column blocks according to one full
   endpoint table;
2. selection and bijective matching of the physical stubs inside every chosen
   full endpoint cell.

The result is an exact coefficient for the full decorated endpoint reference
family. It is a normalization theorem, not an asymptotic estimate.

## Existing inputs

For a full endpoint table `L`, the repository already proves

```text
card(block pairings) * cell-table factorials
  = row block selections * column block selections,
```

and

```text
card(decorated block pairings) * cell-stub factorials
  = card(block pairings) * cell-stub selections.
```

The new module multiplies these identities in the correct order and obtains

```text
card(decorated block pairings)
  * (cell-table factorials * cell-stub factorials)
=
(row block selections * column block selections)
  * cell-stub selections.
```

No cancellation is performed in `Nat`. The denominator is then proved
nonzero and the exact quotient is cast to `ENNReal`.

## Public declarations

`Erdos625/Section8EndpointDecoratedReferenceQuotient.lean` proves:

1. `card_fourEndpointDecoratedBlockPairing_mul_denominator`;
2. `fourEndpointDecoratedDenominator_ne_zero`;
3. `ennreal_card_fourEndpointDecoratedBlockPairing_eq_quotient`;
4. `sum_fourEndpointDecoratedBlockPairing_const_eq_quotient_mul`.

The final theorem says that any weight constant across the decorated endpoint
fibre sums with precisely the combined quotient coefficient. Thus there is no
second table factorial, no hidden ordering of identical block pairs, and no
missing local-stub factorial.

## Relation to the Section VIII closure problem

This closes the finite cardinality part of the full-endpoint reference seam.
It supplies the coefficient that must be multiplied by the common local reward
and ambient falling-factorial normalization to recover the endpoint reference
weight `fourEndpointW`.

The remaining endpoint task is to connect this decorated parameterization to
the separately defined `FourEndpointPhysicalFibre`. The repository already
contains the map

```text
fourEndpointDecoratedBlockPairingToPhysicalFibre
```

and proves that its output is endpoint-only, block-matching, and has the
prescribed full table. A complete equivalence still requires the reverse map
and both round-trip identities, or an equivalent weighted-surjectivity and
injectivity proof.

After the endpoint reference fibre is closed, the nonendpoint task remains the
aggregate deficit reindexing: every attained canonical high physical skeleton
must be summed as a full endpoint block pairing with one allowed multiplicity
deficit and one partial stub-matching fibre in each selected cell. The exact
one-cell ratio and product majorant are already present elsewhere in the
cumulative stack.

## Trust boundary

The focused workflow:

- rejects `sorry`, `admit`, `sorryAx`, project-defined axioms/constants, and
  `unsafe` declarations in the new module;
- builds the exact dependency closure under the pinned Lean 4.31 project with
  warnings fatal;
- uploads the compiler log.

The theorem is finite and exact. It does not establish Lemma 8.3,
Proposition 9.2, or `Erdos625Statement` by itself.
