import Erdos625.Section8ExactLocalDeficitENNReal
import Mathlib.Tactic

/-!
# Section VIII: symmetric exact local deficit ratio

The one-cell algebra was first proved with endpoint sizes `m` and `m+d`.  An
actual overlap cell presents its two endpoint sizes in an arbitrary order.  This
module removes that orientation issue once and for all.

For arbitrary endpoint sizes `u,v`, put

`m = min u v`, `d = Nat.dist u v`.

The final theorem identifies the exact charged partial/full ratio using these
canonical symmetric parameters.  Consequently the global endpoint proof needs
neither a case split over the sixteen endpoint types nor an orientation choice
for every selected block pair.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- Physical matching count times signed reward for arbitrary endpoint sizes. -/
def endpointCellWeightedCount (u v j : Nat) : Nat :=
  Fintype.card (SingleCellStubMatching u v j) * localSignRewardNat j

/-- The one-cell physical matching cardinality is symmetric in its endpoints. -/
theorem card_singleCellStubMatching_comm (u v j : Nat) :
    Fintype.card (SingleCellStubMatching u v j) =
      Fintype.card (SingleCellStubMatching v u j) := by
  have huv := card_singleCellStubMatching_mul_factorial u v j
  have hvu := card_singleCellStubMatching_mul_factorial v u j
  have hmul :
      Fintype.card (SingleCellStubMatching u v j) * j.factorial =
        Fintype.card (SingleCellStubMatching v u j) * j.factorial := by
    calc
      Fintype.card (SingleCellStubMatching u v j) * j.factorial =
          u.descFactorial j * v.descFactorial j := huv
      _ = v.descFactorial j * u.descFactorial j := by rw [mul_comm]
      _ = Fintype.card (SingleCellStubMatching v u j) * j.factorial := hvu.symm
  exact Nat.mul_right_cancel (Nat.factorial_pos j) hmul

/-- The weighted one-cell count is symmetric in its endpoints. -/
theorem endpointCellWeightedCount_comm (u v j : Nat) :
    endpointCellWeightedCount u v j = endpointCellWeightedCount v u j := by
  unfold endpointCellWeightedCount
  rw [card_singleCellStubMatching_comm]

/-- The oriented and symmetric weighted-cell definitions agree. -/
theorem endpointCellWeightedCount_lowerUpper
    (m d j : Nat) :
    endpointCellWeightedCount m (m + d) j =
      lowerUpperCellWeightedCount m d j := rfl

/-- Exact charged partial/full identity for arbitrary endpoint sizes. -/
theorem endpointCellWeightedCount_cast_mul_pow_eq_full_mul_nearCellTerm
    (n u v h : Nat)
    (hh : h ≤ min u v) (hhigh : 3 ≤ min u v - h) :
    (endpointCellWeightedCount u v (min u v - h) : ENNReal) *
        (n : ENNReal) ^ h =
      (endpointCellWeightedCount u v (min u v) : ENNReal) *
        nearCellTerm n (min u v) (Nat.dist u v) h := by
  rcases le_total u v with huv | hvu
  · have huvEq : u + (v - u) = v := Nat.add_sub_of_le huv
    have hhu : h ≤ u := by simpa only [min_eq_left huv] using hh
    have hhighu : 3 ≤ u - h := by simpa only [min_eq_left huv] using hhigh
    have hcell (j : Nat) :
        endpointCellWeightedCount u v j =
          lowerUpperCellWeightedCount u (v - u) j := by
      rw [← huvEq]
      rfl
    rw [min_eq_left huv, Nat.dist_eq_sub_of_le huv,
      hcell (u - h), hcell u]
    exact lowerUpperCellWeightedCount_cast_mul_pow_eq_full_mul_nearCellTerm
      n u (v - u) h hhu hhighu
  · have hvuEq : v + (u - v) = u := Nat.add_sub_of_le hvu
    have hhv : h ≤ v := by simpa only [min_eq_right hvu] using hh
    have hhighv : 3 ≤ v - h := by simpa only [min_eq_right hvu] using hhigh
    have hcell (j : Nat) :
        endpointCellWeightedCount u v j =
          lowerUpperCellWeightedCount v (u - v) j := by
      rw [endpointCellWeightedCount_comm u v j, ← hvuEq]
      rfl
    rw [min_eq_right hvu, Nat.dist_eq_sub_of_le_right hvu,
      hcell (v - h), hcell v]
    exact lowerUpperCellWeightedCount_cast_mul_pow_eq_full_mul_nearCellTerm
      n v (u - v) h hhv hhighv

#print axioms card_singleCellStubMatching_comm
#print axioms endpointCellWeightedCount_cast_mul_pow_eq_full_mul_nearCellTerm

end

end Erdos625
