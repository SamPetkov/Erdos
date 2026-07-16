import Erdos625.Section10QuarterDenseChain

/-!
# Section X: quarter-chain graph adapters

Small deterministic adapters used to connect the accepted complement
quarter-density chain to the accepted greedy-colouring interface.

For exact-start subset selection, Mathlib already provides the exact statement
needed downstream:
`Finset.exists_subset_card_eq : s ≤ U.card -> ∃ S ⊆ U, S.card = s`.
This module deliberately does not duplicate that declaration.
-/

namespace Erdos625

/-- A clique in the complement graph is an independent set in the original
graph, with the same vertex-set and pairwise quantifiers. -/
theorem isIndepSet_of_compl_isClique
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : Finset V)
    (hClique : Gᶜ.IsClique (C : Set V)) :
    G.IsIndepSet (C : Set V) :=
  by simpa using hClique

#print axioms isIndepSet_of_compl_isClique

end Erdos625
