import Erdos625.Section8EndpointFoundation
import Mathlib.Tactic

/-!
# Target B: exact endpoint mass identities

The conclusion combines the two monotonicity facts and the exact identity
equivalent to manuscript (8.11). No `Q_ij` inequality is asserted.
-/

namespace Erdos625

set_option autoImplicit false

theorem fourEndpoint_mass_facts
    (alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    FourEndpointMassFacts alpha hAlpha L := by
  have hs (i : Fin 4) :
      fourEndpointSize alpha hAlpha i = alpha - (i.val + 2) := by
    fin_cases i <;>
      simp [fourEndpointSize, fourEndpointCoordinate, fourDeficitCoordinate,
        fourDeficit, Fin.rev, Fin.succ] <;> omega
  have hleRow (i j : Fin 4) :
      fourEndpointOverlapSize alpha hAlpha i j ≤
        fourEndpointSize alpha hAlpha i := Nat.min_le_left _ _
  have hleCol (i j : Fin 4) :
      fourEndpointOverlapSize alpha hAlpha i j ≤
        fourEndpointSize alpha hAlpha j := Nat.min_le_right _ _
  have hcell (i j : Fin 4) :
      fourEndpointSize alpha hAlpha i + fourEndpointSize alpha hAlpha j =
        2 * fourEndpointOverlapSize alpha hAlpha i j + Nat.dist i.val j.val := by
    fin_cases i <;> fin_cases j <;>
      simp [hs, fourEndpointOverlapSize, Nat.dist] <;> omega
  constructor
  · unfold fourEndpointJ fourEndpointRowMass fourEndpointMarginMass
      fourEndpointRowMargin
    simp_rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hleRow i j)
  constructor
  · unfold fourEndpointJ fourEndpointColumnMass fourEndpointMarginMass
      fourEndpointColumnMargin
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hleCol i j)
  · unfold fourEndpointJ fourEndpointRowMass fourEndpointColumnMass
      fourEndpointMarginMass fourEndpointRowMargin fourEndpointColumnMargin
      fourEndpointDisplacement
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_comm (f := fun i j => fourEndpointSize alpha hAlpha j * L.toFun i j)]
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, ← add_mul, hcell, add_mul]
    simp only [Finset.sum_add_distrib]
    simp [mul_assoc]

end Erdos625
