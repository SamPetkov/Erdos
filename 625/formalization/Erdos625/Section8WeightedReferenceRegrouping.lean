import Erdos625.Section8DirectReferenceGrouping
import Mathlib.Tactic

/-!
# Section VIII: weighted realized-table reference regrouping

Any weight depending only on the endpoint table may be transported through the
existing exact equivalence between fully decorated block supports and the
sigma-type of realized endpoint tables with their decorated block-pairing
fibres.  The source expansion distributes the table weight across the finite
physical-decoration sum before applying the equivalence.

This is a finite exact identity.  It does not use a deficit estimate, endpoint
transportation, a phase assumption, or an asymptotic argument.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Carry an arbitrary `ENNReal`-valued endpoint-table weight through the exact
full-support reference regrouping. -/
theorem sum_fourEndpointFullSupportReferenceWeight_mul_tableWeight_eq_sum_realized_W_mul_tableWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (tableWeight : FourEndpointFullTable → ENNReal) :
    (∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
      fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
        tableWeight (fourEndpointSupportTable alpha hAlpha P)) =
      ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
        fourEndpointW n alpha hAlpha k L.1 * tableWeight L.1 := by
  let equivalence :=
    fourEndpointAllDecoratedSupportEquivSigmaTable alpha hAlpha k
  let targetWeight :
      (Σ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
        FourEndpointDecoratedBlockPairing alpha hAlpha k L.1) → ENNReal :=
    fun z =>
      fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha z.1.1 *
        tableWeight z.1.1
  calc
    (∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
          tableWeight (fourEndpointSupportTable alpha hAlpha P)) =
      ∑ z : FourEndpointAllDecoratedSupport alpha hAlpha k,
        fourEndpointFullSupportAtomWeight n alpha hAlpha z.1 *
          tableWeight (fourEndpointSupportTable alpha hAlpha z.1) := by
            rw [Fintype.sum_sigma]
            apply Finset.sum_congr rfl
            intro P _
            simp only [fourEndpointFullSupportReferenceWeight]
            rw [Finset.sum_mul]
    _ = ∑ z : FourEndpointAllDecoratedSupport alpha hAlpha k,
          targetWeight (equivalence z) := by
            apply Finset.sum_congr rfl
            intro z _
            rfl
    _ = ∑ z : Σ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
          FourEndpointDecoratedBlockPairing alpha hAlpha k L.1,
        targetWeight z :=
      equivalence.sum_comp targetWeight
    _ = ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
          ∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L.1,
            fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L.1 *
              tableWeight L.1 := by
            rw [Fintype.sum_sigma]
    _ = ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
          (∑ _ : FourEndpointDecoratedBlockPairing alpha hAlpha k L.1,
            fourEndpointDecoratedReferenceAtomWeight n alpha hAlpha L.1) *
              tableWeight L.1 := by
            apply Finset.sum_congr rfl
            intro L _
            rw [Finset.sum_mul]
    _ = ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
          fourEndpointW n alpha hAlpha k L.1 * tableWeight L.1 := by
            apply Finset.sum_congr rfl
            intro L _
            rw [sum_fourEndpointDecoratedReferenceAtomWeight_eq_fourEndpointW]

#print axioms
  sum_fourEndpointFullSupportReferenceWeight_mul_tableWeight_eq_sum_realized_W_mul_tableWeight

end

end Erdos625
