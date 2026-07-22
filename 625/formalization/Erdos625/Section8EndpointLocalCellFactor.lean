import Erdos625.Section8EndpointProfileIndexing
import Mathlib.Tactic

namespace Erdos625

open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- The diagonal local factor at a cell of lower endpoint size `u`. -/
noncomputable def fourEndpointSizeDiagonalFactor (u : Nat) : ENNReal :=
  (u.factorial : ENNReal) * (localSignRewardNat u : ENNReal)

/-- A local endpoint factor reduces to its lower diagonal factor times the
binomial choice of the distance coordinates. -/
theorem fourEndpointLocalCellFactor_eq_lowerDiagonal_mul_choose
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointLocalCellFactor alpha hAlpha i j =
      fourEndpointSizeDiagonalFactor
        (fourEndpointLowerSize alpha hAlpha i j) *
      (Nat.choose
        (fourEndpointUpperSize alpha hAlpha i j)
        (fourEndpointDistance i j) : ENNReal) := by
  have hfactor (a b : Nat) :
      ((a.descFactorial (min a b) : ENNReal) *
          (b.descFactorial (min a b) : ENNReal) /
            ((min a b).factorial : ENNReal)) =
        ((min a b).factorial : ENNReal) *
          (Nat.choose (max a b) (max a b - min a b) : ENNReal) := by
    wlog h : a ≤ b generalizing a b
    · rw [min_comm, max_comm, mul_comm]
      exact this b a (le_of_not_ge h)
    rw [min_eq_left h, max_eq_right h, Nat.descFactorial_self,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    rw [mul_div_assoc, ENNReal.mul_div_cancel]
    · rw [Nat.choose_symm h]
    · exact_mod_cast Nat.factorial_ne_zero a
    · exact ENNReal.coe_ne_top
  have hsize (k : Fin 4) :
      fourEndpointSize alpha hAlpha k = alpha - 2 - k.val := by
    unfold fourEndpointSize fourEndpointCoordinate fourDeficitCoordinate
    simp [fourDeficit]
    omega
  have hdist :
      max (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j) -
          min (fourEndpointSize alpha hAlpha i) (fourEndpointSize alpha hAlpha j) =
        fourEndpointDistance i j := by
    rw [hsize, hsize, fourEndpointDistance, Nat.dist_eq_max_sub_min]
    by_cases hij : i.val ≤ j.val
    · have hs : alpha - 2 - j.val ≤ alpha - 2 - i.val := by omega
      rw [max_eq_left hs, min_eq_right hs, max_eq_right hij, min_eq_left hij]
      omega
    · have hji : j.val ≤ i.val := by omega
      have hs : alpha - 2 - i.val ≤ alpha - 2 - j.val := by omega
      rw [max_eq_right hs, min_eq_left hs, max_eq_left hji, min_eq_right hji]
      omega
  simp only [fourEndpointLocalCellFactor]
  unfold fourEndpointOverlapSize fourEndpointSizeDiagonalFactor
    fourEndpointLowerSize fourEndpointUpperSize
  rw [hfactor, hdist]
  ac_rfl

/-- Exact diagonal-factor transport between two ordered four-endpoint sizes. -/
theorem fourEndpointSizeDiagonalFactor_ratio
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (i j : Fin 4)
    (hij : fourEndpointSize alpha hAlpha i ≤ fourEndpointSize alpha hAlpha j) :
    fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha j) =
      fourEndpointSizeDiagonalFactor (fourEndpointSize alpha hAlpha i) *
        ((fourEndpointSize alpha hAlpha j).descFactorial
          (fourEndpointDistance i j) : ENNReal) *
        (2 : ENNReal) ^
          (fourEndpointDistance i j * fourEndpointSize alpha hAlpha i +
            (fourEndpointDistance i j).choose 2) := by
  have choose_add_two (u d : Nat) :
      (u + d).choose 2 = u.choose 2 + d * u + d.choose 2 := by
    induction d with
    | zero => simp
    | succ d ih =>
        rw [Nat.add_succ, Nat.choose_succ_succ]
        simp only [Nat.choose_one_right]
        rw [ih]
        have hd : (d + 1).choose 2 = d + d.choose 2 := by
          rw [Nat.choose_succ_succ]
          simp
        rw [hd]
        simp only [Nat.add_mul, one_mul]
        omega
  have diagonal_add (u d : Nat) (hu : 3 ≤ u) :
      fourEndpointSizeDiagonalFactor (u + d) =
        fourEndpointSizeDiagonalFactor u * ((u + d).descFactorial d : ENNReal) *
          (2 : ENNReal) ^ (d * u + d.choose 2) := by
    have hud : d ≤ u + d := by omega
    have hfacNat : u.factorial * (u + d).descFactorial d = (u + d).factorial := by
      simpa using Nat.factorial_mul_descFactorial hud
    have hfac : (u.factorial : ENNReal) * ((u + d).descFactorial d : ENNReal) =
        ((u + d).factorial : ENNReal) := by
      exact_mod_cast hfacNat
    have hexp : (u + d).choose 2 - 1 =
        (u.choose 2 - 1) + (d * u + d.choose 2) := by
      rw [choose_add_two]
      have hchoose : 1 ≤ u.choose 2 := by
        have hh := Nat.choose_le_choose 2 hu
        norm_num at hh
        omega
      omega
    simp only [fourEndpointSizeDiagonalFactor, localSignRewardNat,
      if_pos hu, if_pos (by omega : 3 ≤ u + d)]
    rw [hexp, pow_add, ← hfac]
    norm_num [ENNReal.coe_pow]
    simp only [mul_assoc, mul_comm]
  have hsize (k : Fin 4) :
      fourEndpointSize alpha hAlpha k = alpha - 2 - k.val := by
    unfold fourEndpointSize fourEndpointCoordinate fourDeficitCoordinate
    simp [fourDeficit]
    omega
  have hji : j.val ≤ i.val := by
    rw [hsize i, hsize j] at hij
    omega
  have hdist : fourEndpointDistance i j = i.val - j.val := by
    simp [fourEndpointDistance, Nat.dist_eq_sub_of_le_right hji]
  have htransport :
      fourEndpointSize alpha hAlpha j =
        fourEndpointSize alpha hAlpha i + fourEndpointDistance i j := by
    rw [hsize i, hsize j, hdist]
    omega
  rw [htransport]
  apply diagonal_add
  rw [hsize i]
  omega

end

end Erdos625
