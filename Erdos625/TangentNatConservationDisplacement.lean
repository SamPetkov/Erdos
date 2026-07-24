import Erdos625.TangentRoundingCore

namespace Erdos625

open scoped BigOperators

/-- After the explicit positivity condition, conversion to naturals preserves
the exact count and deficit constraints.  Each corrected coordinate stays
within `5` of its real tangent value; this is stronger than the coarse fixed
lower bound `14` used to guarantee positivity. -/
theorem tangent_rounding_nat_conservation_and_uniform_displacement
    (K D : Nat) (p : Fin 4 → Real)
    (hCount : ∑ i, (K : Real) * p i = (K : Real))
    (hMoment : ∑ i, (tangentDeficit i : Real) * ((K : Real) * p i) =
      (D : Real))
    (hLower : ∀ i, (14 : Real) ≤ (K : Real) * p i) :
    (∑ i, tangentCorrectedNat K D p i) = K ∧
      (∑ i, tangentDeficitNat i * tangentCorrectedNat K D p i) = D ∧
      (∀ i,
        |((tangentCorrectedInt K D p i : Int) : Real) - (K : Real) * p i| ≤
          (5 : Real)) := by
  have hFloorLower : ∀ i, ((tangentRawFloors K p i : Int) : Real) ≤ (K : Real) * p i := by
    intro i
    exact Int.floor_le ((K : Real) * p i)
  have hFloorUpper : ∀ i, (K : Real) * p i < ((tangentRawFloors K p i : Int) : Real) + 1 := by
    intro i
    exact Int.lt_floor_add_one ((K : Real) * p i)
  have hl0 := hFloorLower (0 : Fin 4)
  have hl1 := hFloorLower (1 : Fin 4)
  have hl2 := hFloorLower (2 : Fin 4)
  have hl3 := hFloorLower (3 : Fin 4)
  have hu0 := hFloorUpper (0 : Fin 4)
  have hu1 := hFloorUpper (1 : Fin 4)
  have hu2 := hFloorUpper (2 : Fin 4)
  have hu3 := hFloorUpper (3 : Fin 4)
  simp only [Fin.sum_univ_four, tangentDeficit] at hCount hMoment
  norm_num at hCount hMoment hl0 hl1 hl2 hl3 hu0 hu1 hu2 hu3
  have hC0eq : ((tangentC0 K D p : Int) : Real) =
      -(↑(tangentRawFloors K p 0) - (K : Real) * p 0) +
        (↑(tangentRawFloors K p 2) - (K : Real) * p 2) +
        2 * (↑(tangentRawFloors K p 3) - (K : Real) * p 3) := by
    simp only [tangentC0, tangentC0Raw, tangentE1Raw, tangentE0Raw,
      Fin.sum_univ_four, tangentDeficit]
    norm_num
    linarith
  have hC1eq : ((tangentC1 K D p : Int) : Real) =
      -(↑(tangentRawFloors K p 1) - (K : Real) * p 1) -
        2 * (↑(tangentRawFloors K p 2) - (K : Real) * p 2) -
        3 * (↑(tangentRawFloors K p 3) - (K : Real) * p 3) := by
    simp only [tangentC1, tangentC1Raw, tangentE1Raw, tangentE0Raw,
      Fin.sum_univ_four, tangentDeficit]
    norm_num
    linarith
  have hC0lowerR : (-3 : Real) < (tangentC0 K D p : Int) := by rw [hC0eq]; linarith
  have hC0upperR : ((tangentC0 K D p : Int) : Real) < 1 := by rw [hC0eq]; linarith
  have hC1lowerR : (0 : Real) ≤ (tangentC1 K D p : Int) := by rw [hC1eq]; linarith
  have hC1upperR : ((tangentC1 K D p : Int) : Real) < 6 := by rw [hC1eq]; linarith
  have hC0lower : (-2 : Int) ≤ tangentC0 K D p := by
    have : (-3 : Int) < tangentC0 K D p := by exact_mod_cast hC0lowerR
    omega
  have hC0upper : tangentC0 K D p ≤ 0 := by
    have : tangentC0 K D p < (1 : Int) := by exact_mod_cast hC0upperR
    omega
  have hC1lower : (0 : Int) ≤ tangentC1 K D p := by exact_mod_cast hC1lowerR
  have hC1upper : tangentC1 K D p ≤ 5 := by
    have : tangentC1 K D p < (6 : Int) := by exact_mod_cast hC1upperR
    omega
  simp only [tangentC0] at hC0lower hC0upper hC0lowerR hC0upperR
  simp only [tangentC1] at hC1lower hC1upper hC1lowerR hC1upperR
  have hC0lowerCast : (-2 : Real) ≤ (tangentC0Raw (tangentRawFloors K p) K D : Int) := by
    exact_mod_cast hC0lower
  have hC0upperCast : ((tangentC0Raw (tangentRawFloors K p) K D : Int) : Real) ≤ 0 := by
    exact_mod_cast hC0upper
  have hC1lowerCast : (0 : Real) ≤ (tangentC1Raw (tangentRawFloors K p) K D : Int) := by
    exact_mod_cast hC1lower
  have hC1upperCast : ((tangentC1Raw (tangentRawFloors K p) K D : Int) : Real) ≤ 5 := by
    exact_mod_cast hC1upper
  have hDisp : ∀ i,
      |((tangentCorrectedInt K D p i : Int) : Real) - (K : Real) * p i| ≤ 5 := by
    intro i
    have hl := hFloorLower i
    have hu := hFloorUpper i
    fin_cases i
    all_goals simp only [tangentCorrectedInt, tangentCorrectedRaw,
      tangentCorrectionRaw]
    all_goals norm_num at hl hu ⊢
    all_goals rw [abs_le]
    all_goals constructor <;> linarith
  have hNonneg : ∀ i, 0 ≤ tangentCorrectedInt K D p i := by
    intro i
    have hd := hDisp i
    have hl := hLower i
    rw [abs_le] at hd
    have hr : (0 : Real) ≤ ((tangentCorrectedInt K D p i : Int) : Real) := by linarith
    exact_mod_cast hr
  have hNatInt : ∀ i, (tangentCorrectedNat K D p i : Int) = tangentCorrectedInt K D p i := by
    intro i
    simp [tangentCorrectedNat, Int.toNat_of_nonneg (hNonneg i)]
  have hSumInt : ∑ i, tangentCorrectedInt K D p i = (K : Int) := by
    simp only [tangentCorrectedInt, tangentCorrectedRaw, tangentCorrectionRaw,
      tangentC0Raw, tangentC1Raw, tangentE0Raw, tangentE1Raw]
    simp only [Fin.sum_univ_four, tangentDeficit]
    norm_num
    ring
  have hMomentInt : ∑ i, tangentDeficit i * tangentCorrectedInt K D p i = (D : Int) := by
    simp only [tangentCorrectedInt, tangentCorrectedRaw, tangentCorrectionRaw,
      tangentC0Raw, tangentC1Raw, tangentE0Raw, tangentE1Raw]
    simp only [Fin.sum_univ_four, tangentDeficit]
    norm_num
    ring
  constructor
  · apply Nat.cast_injective (R := Int)
    simp only [Nat.cast_sum]
    rw [Finset.sum_congr rfl (fun i _ ↦ hNatInt i)]
    exact hSumInt
  constructor
  · apply Nat.cast_injective (R := Int)
    simp only [Nat.cast_sum, Nat.cast_mul]
    rw [Finset.sum_congr rfl (fun i _ ↦ ?_)]
    · exact hMomentInt
    simp only [tangentDeficit, tangentDeficitNat]
    rw [hNatInt]
    norm_num
  · exact hDisp

end Erdos625
