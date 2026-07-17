import Erdos625.Section9MarkedCycleEnumeration
import Erdos625.Section9ActualResidualENNRealPolymerBridge

/-!
# Section IX: exact simple-cycle weight partition

This module partitions the finite simple-cycle polymer exponent into the
cycles disjoint from the exposed matching and the mixed cycles meeting it.
The second part is reindexed exactly through `MixedSimpleCycle`.

This is a finite identity only.  It supplies neither a bound for the
residual-only part nor a residual law, polymer estimate, or attachment bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Exact partition of all finite simple-cycle weights into residual-only and
mixed contributions. -/
theorem sum_simpleBipartiteCycles_edgeWeight_split
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (M : Finset (A × B)) :
    (∑ C ∈ simpleBipartiteCycles A B,
        edgeWeightOutsideENN q M C) =
      (∑ C ∈ (simpleBipartiteCycles A B).filter
          (fun C => Disjoint C M),
        edgeWeightOutsideENN q M C) +
      (∑ C : MixedSimpleCycle A B M,
        edgeWeightOutsideENN q M C.1) := by
  classical
  have hmeet (C : Finset (A × B)) :
      ¬ Disjoint C M ↔ (C ∩ M).Nonempty := by
    constructor
    · intro h
      rw [Finset.disjoint_left] at h
      push Not at h
      obtain ⟨e, heC, heM⟩ := h
      exact ⟨e, Finset.mem_inter.mpr ⟨heC, heM⟩⟩
    · rintro ⟨e, he⟩ h
      exact (Finset.disjoint_left.mp h) (Finset.mem_inter.mp he).1
        (Finset.mem_inter.mp he).2
  rw [← Finset.sum_filter_add_sum_filter_not
    (simpleBipartiteCycles A B) (fun C => Disjoint C M)
    (fun C => edgeWeightOutsideENN q M C)]
  congr 1
  unfold simpleBipartiteCycles
  rw [Finset.filter_filter]
  simp_rw [hmeet]
  symm
  simpa using
    (Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset (Finset (A × B))))
      (f := fun C => edgeWeightOutsideENN q M C)
      (p := fun C => IsSimpleBipartiteCycle C ∧ (C ∩ M).Nonempty))

#print axioms sum_simpleBipartiteCycles_edgeWeight_split

end

end Erdos625
