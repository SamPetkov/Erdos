import Erdos625.OrderedSignedProfileBridge

/-!
# Ordered realization of a finite coloring profile

This module supplies the deterministic feasibility direction for an ordered
profile partition.  It includes the empty vertex set and profiles with no
block slots: the sigma type may be empty, and the finite-cardinality
equivalence still gives the required realization exactly when the displayed
mass identity holds.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A profile whose vertex mass is exactly `n` admits an ordered partition of
`Fin n` with the prescribed block-slot margins. -/
theorem nonempty_orderedProfilePartition_of_vertexMass
    {b n : Nat} (k : ColoringProfile b)
    (hmass : ColoringProfile.vertexMass k = n) :
    Nonempty (OrderedProfilePartition n k) := by
  refine ⟨(fixedFiberLabelingWithOrdersEquiv (profileBlockMargin k)
    (Fintype.equivOfCardEq ?_)).1⟩
  rw [Fintype.card_fin, Fintype.card_sigma]
  simpa using (hmass.symm.trans (sum_profileBlockMargin_eq_vertexMass k).symm)

end

end Erdos625
