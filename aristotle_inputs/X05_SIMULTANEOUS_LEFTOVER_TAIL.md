# X05 -- Simultaneous leftover-colouring tail

Status: stage after X01--X04.  Kind: graph-probability transport and
deterministic assembly.  No dependency on Sections VIII--IX.

## Faithful event

For a real constant `C`, define one event

```text
leftoverLinearEvent C n =
  {G | forall U : Finset (Fin n),
    (chromaticNumberNat (G.induce U) : Real) <=
      C * U.card / Real.log n + (n : Real)^(1/3)}.
```

The target is the exact quantifier form of manuscript Lemma 10.1:

```text
exists C : Real, 0 < C and
  Tendsto
    (fun n => randomGraphMeasure n (leftoverLinearEvent C n))
    atTop (nhds 1)
```

Equivalently, one may exhibit a deterministic nonnegative failure sequence
`epsilon n -> 0` bounding the complement probability.  That sequence and `C`
must depend only on `n`, not on any later capacity seed or radius.

## Dependencies

- X01 supplies the fixed-cutoff-set lower-tail bound.
- The accepted `quarterDensity_unionBound_tendsto_zero` controls the union
  cost.
- X02 lifts exact cutoff density to every larger set on the same graph event.
- X03--X04 supply logarithmic independent sets.
- The accepted `simultaneous_induced_chromatic_bound` performs the greedy
  deletion and colouring.

## Critical acceptance condition

The event must contain the universal quantifier over every `U` internally.
A theorem saying “for each fixed `U`, the probability tends to one” is too
weak, because the complement of the capacity-maximizing core is selected from
the random graph.
