# X01 -- Fixed-subset complement-edge tail

Status: send now.  Kind: graph-probability transport.  No dependency on
Sections VIII--IX.

## Target

For `G` sampled from `G(n,1/2)` and a fixed `S : Finset (Fin n)`, let
`X_S(G)` be the number of edges of the induced complement graph on `S`.
Prove

\[
  \Pr\!\left\{X_S\le \frac{\binom{|S|}{2}}4\right\}
  \le \exp\!\left(-\frac{\binom{|S|}{2}}{16}\right).
\]

The isolated declaration is
`fixedSubset_inducedComplementEdgeCount_lowerQuarter_le_exp`; its exact source
is at
`.aristotle/pending-next/x01_fixed_subset_quarter_tail/FixedSubsetQuarterTail/Main.lean`.
The pinned Lean 4.28 Mathlib revision predates
`SimpleGraph.binomialRandom`, so this isolated package represents
`G(n,1/2)` by the exactly equivalent uniform probability measure on the
finite type of labelled graphs.  The repository port must reconnect the
result to its native `randomGraphMeasure` wrapper.

## Required proof content

- Identify the induced complement-edge count with a binomial variable having
  `choose S.card 2` trials and success probability `1/2`, or prove the same
  tail directly from independent edge coordinates.
- Keep the event under the repository-compatible `Measure.real` probability.
- Derive the displayed exponent by a valid lower-tail Chernoff/Hoeffding
  inequality.  A stronger exponent is acceptable only if the final displayed
  bound is proved explicitly.
- Handle `S.card < 2` without adding an unstated size assumption.

## Non-goals and failure modes

This target is fixed-subset only.  It does not include a union bound or an
internal universal quantifier over all subsets.  The complement graph must not
silently be replaced by an independent fresh graph unless measure invariance
or coordinate-law equality is proved.
