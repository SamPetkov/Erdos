# X03 -- Quarter-neighbourhood chain

Status: send now.  Kind: deterministic graph construction.  No dependency on
Sections VIII--IX.

## Target

Assume every complement-induced set of size at least `cutoff` is
quarter-dense.  If the explicit recurrence lower bound remains above the
cutoff for all stages below `t`, construct inside `S` an independent set of
cardinality at least `t`:

```text
exists_independentSet_of_quarterDense_chain
  (G : SimpleGraph V) (cutoff t : Nat) (hcutoff : 2 <= cutoff)
  (hDense : forall T, cutoff <= T.card -> QuarterDenseOn (complement G) T)
  (S : Finset V)
  (hSurvive : forall j < t,
    cutoff <= 4^(-j) * S.card - 1/3) :
  exists I, I subset S and t <= I.card and G.IsIndepSet I
```

The exact typed declaration is at
`.aristotle/pending-next/x03_quarter_chain/QuarterNeighborhoodChain/Main.lean`.

## Required proof content

At each stage choose a maximum-degree vertex in the complement-induced
current set, append it to the selected set, and replace the current set by
its complement-neighbourhood there.  Prove inductively both the recurrence
lower bound and that every later selected vertex is adjacent in the
complement to every earlier selected vertex.  The latter invariant is what
makes the selected vertices independent in the original graph.

## Non-goals

The numerical choices `n^(1/4)`, `n^(1/3)`, and a logarithmic `t` are X04.
The random event supplying `hDense` is X01--X02 and X05.

## Smaller fallback target

The package `.aristotle/pending-next/x03a_quarter_neighborhood_step` isolates
`exists_quarterNeighborhood_step`.  From quarter-density on one set of size at
least two, it chooses `v` in that set with

\[
 |S|-1\le 4\,|\{w\in S:(G^c).Adj(v,w)\}|.
\]

This preserves the exact denominator-cleared recurrence constant while
omitting the iterated-chain and clique/independent-set invariant.  It is a
fallback proof atom, not a substitute for X03.
