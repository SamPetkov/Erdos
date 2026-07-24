import Erdos625.Section8EndpointFoundation
import Mathlib.Tactic

/-!
# Target C: global falling-factorial transport

This is only the finite natural-number transport factor. It does not assert
the ENNReal geometric-mean comparison (8.8) or the local bound (8.9).
-/

namespace Erdos625

set_option autoImplicit false

theorem fourEndpoint_global_transport
    (n alpha : Nat) (hAlpha : 5 < alpha) (L : FourEndpointFullTable) :
    n.descFactorial (fourEndpointRowMass alpha hAlpha L) *
      n.descFactorial (fourEndpointColumnMass alpha hAlpha L) <=
        (n.descFactorial (fourEndpointJ alpha hAlpha L)) ^ 2 *
          (n + 1) ^ fourEndpointDisplacement L := by
  apply descFactorial_endpoint_transport_succ
  · unfold fourEndpointJ fourEndpointRowMass fourEndpointMarginMass
      fourEndpointRowMargin fourEndpointOverlapSize
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ =>
        Nat.mul_le_mul_right (L.toFun i j) (min_le_left _ _)
  · unfold fourEndpointJ fourEndpointColumnMass fourEndpointMarginMass
      fourEndpointColumnMargin fourEndpointOverlapSize
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun i _ =>
        Nat.mul_le_mul_right (L.toFun i j) (min_le_right _ _)
  · have hcell (i j : Fin 4) :
        fourEndpointSize alpha hAlpha i + fourEndpointSize alpha hAlpha j =
          2 * fourEndpointOverlapSize alpha hAlpha i j +
            Nat.dist i.val j.val := by
      fin_cases i <;> fin_cases j <;>
        simp [fourEndpointOverlapSize, fourEndpointSize,
          fourEndpointCoordinate, fourDeficitCoordinate, fourDeficit,
          Nat.dist] <;> omega
    unfold fourEndpointRowMass fourEndpointColumnMass fourEndpointMarginMass
      fourEndpointRowMargin fourEndpointColumnMargin fourEndpointJ
      fourEndpointDisplacement
    simp only [Finset.mul_sum]
    calc
      (∑ i, ∑ j, fourEndpointSize alpha hAlpha i * L.toFun i j) +
          ∑ j, ∑ i, fourEndpointSize alpha hAlpha j * L.toFun i j =
        ∑ i, ∑ j,
          (fourEndpointSize alpha hAlpha i +
            fourEndpointSize alpha hAlpha j) * L.toFun i j := by
              conv_lhs =>
                rhs
                rw [Finset.sum_comm]
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j _
              rw [add_mul]
      _ = ∑ i, ∑ j,
          (2 * fourEndpointOverlapSize alpha hAlpha i j +
            Nat.dist i.val j.val) * L.toFun i j := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [hcell]
      _ = (∑ i, ∑ j,
            2 * (fourEndpointOverlapSize alpha hAlpha i j * L.toFun i j)) +
          ∑ i, ∑ j, Nat.dist i.val j.val * L.toFun i j := by
              simp only [add_mul, mul_assoc, Finset.sum_add_distrib]

end Erdos625
