# Section VIII attained partial-fibre and weight identification

## Purpose

The line-by-line audit isolates one exact finite seam in the canonical proof:
the passage from an attained physical high skeleton to a block support with one
deficit and one partial stub matching in every selected cell.

The unsafe mental picture is:

> choose a full-cell completion and delete the deficit edges.

A partial physical matching usually has many full completions, and its unused
stubs may participate in residual cells.  No proof should depend on choosing one
of those completions.

The replacement is an aggregate finite theorem.

## Generic matching-demand theorem

Let

```text
demand : A -> B -> Nat
```

have positive support

```text
M = {(a,b) : demand(a,b) != 0}
```

which is a bipartite matching.  Let `row(a)` and `col(b)` be the ambient stub
degrees.  Define

```text
MatchingDemandCellDecoration demand row col
```

to be one literal one-cell partial matching of size `demand(a,b)` for every
`(a,b) in M`.

The new Lean module constructs and proves the equivalence

```text
MatchingDemandCellDecoration demand row col
  ≃
{S : UnlabelledTypedSkeleton row col // S.typeTable = demand}.
```

The forward map unions the local physical edges.  Matchingness of `M` gives
global row- and column-stub uniqueness.  The reverse map restricts a physical
skeleton to each positive type cell.  The two round trips use no full-cell
completion and no ordering of edges within a cell.

## Exact cardinality identity

For one positive cell \(e=(a,b)\), put

\[
 j_e=\operatorname{demand}(a,b).
\]

The local fibre has cardinality

\[
 rac{(\operatorname{row}(a))_{j_e}
       (\operatorname{col}(b))_{j_e}}{j_e!}.
\]

The finite equivalence therefore gives

\[
 \left|\{S:S.\operatorname{typeTable}=\operatorname{demand}\}ight|
 =
 \prod_{e\in M}
 rac{(\operatorname{row}(e_1))_{j_e}
       (\operatorname{col}(e_2))_{j_e}}{j_e!}.
\]

This is the matching-supported specialization of the global prescribed-demand
quotient.  It has one and only one factorial denominator per positive cell.

The support-matching hypothesis is essential.  If two positive cells share a
row, their row-stub selections are not independent, and the product of the
single-cell cardinalities overcounts.

## Pointwise bare-weight identity

For an attained canonical high demand \(L\), define

\[
 J(L)=\sum_{e\in\operatorname{supp}_+(L)}L_e,
 \qquad
 G(L)=\prod_{e\in\operatorname{supp}_+(L)}g(L_e).
\]

Every physical realization has common atom weight

\[
 \frac{G(L)}{(n)_{J(L)}}.
\]

Summing that atom over the exact fibre gives

\[
 w_{\mathrm{hi}}(L)
 =
 \frac{G(L)}{(n)_{J(L)}}
 \prod_{e\in\operatorname{supp}_+(L)}
 \frac{(s_e)_{L_e}(t_e)_{L_e}}{L_e!}.
\]

This is precisely the aggregate partial-cell weight.  The equality is a finite
cardinality theorem, not a heuristic completion argument.

## Four-endpoint specialization

For the four-size midpoint profile, the support/deficit encoding supplies:

```text
P       = fourEndpointDemandBlockPairing ... demand
h(e)    = fourEndpointDemandDeficit ... demand e
m(e)    = fourEndpointCellFullMultiplicity ... P e
j(e)    = m(e) - h(e).
```

The already checked reconstruction theorem gives

```text
j(e) = demand(actualRow(e), actualColumn(e)),
```

and the high condition gives

```text
2*h(e) < m(e).
```

Consequently the generic aggregate weight specializes to

```text
fourEndpointPartialAggregateWeight
  totalMass alpha hAlpha P h.
```

The next theorem after the generic equivalence is therefore the pointwise
identity

```text
profileHighSkeletonWeight k U demand
  =
fourEndpointPartialAggregateWeight
      totalMass alpha hAlpha P h.
```

Once this is green, the injective attained-demand reindexing in PR #48 and the
cellwise geometric partition function in PR #49 may be applied without an
unproved multiplicity assertion.

## Exact regression

`625/experiments/section8_attained_partial_weight_identity.py` enumerates small
matching-supported demand tables and verifies with exact integer/Fraction
arithmetic that:

1. the global prescribed-demand fibre cardinality equals the product of the
   local one-cell cardinalities;
2. the corresponding reward/incidence weights agree;
3. a deliberately nonmatching support fails the independent-cell product,
   confirming the necessity of the matching hypothesis.

The script is a regression check, not a substitute for the Lean equivalence.

## Remaining boundary

This work closes the aggregate physical-fibre ambiguity once both the generic
equivalence and the pointwise profile specialization are warning-fatally green.
It does not by itself sum all support/deficit data or prove the phase asymptotic.
The remaining order is:

1. apply the pointwise identity inside the injective support/deficit sum;
2. use the sharp complete-deficit partition function;
3. group zero-deficit references by full endpoint table;
4. apply endpoint transportation and Lemma 7.1;
5. compose with the q-only literal attachment theorem;
6. export Proposition 9.2.
