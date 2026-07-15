# X02 -- Density lift from one cardinality

Status: send now.  Kind: deterministic finite combinatorics.  No dependency
on Sections VIII--IX.

## Target

Let `QuarterDenseOn H S` abbreviate

\[
 |S|(|S|-1)\le 8e(H[S]).
\]

For `u >= 2`, prove that if every `u`-element subset is quarter-dense, then
every subset of cardinality at least `u` is quarter-dense:

```text
quarterDense_all_larger_of_all_exact
  (H : SimpleGraph V) (u : Nat) (hu : 2 <= u)
  (hExact : forall T, T.card = u -> QuarterDenseOn H T) :
  forall S, u <= S.card -> QuarterDenseOn H S
```

The exact isolated source is at
`.aristotle/pending-next/x02_density_lift/QuarterDensityLift/Main.lean`.

## Required proof content

Double-count pairs or induced edges over all `u`-subsets of a fixed larger
`S`.  The proof must account for the multiplicity with which each pair of
vertices occurs and must remain valid at `S.card = u`.  No probability or
choice of an exceptional graph belongs in this lemma.

## Downstream use

Together with X01 and the accepted union-cost limit, this converts success on
all exact cutoff-size sets into the one graph event controlling every larger
set.
