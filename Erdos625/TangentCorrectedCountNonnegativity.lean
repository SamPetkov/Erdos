import Erdos625.TangentRoundingCore

namespace Erdos625

open scoped BigOperators

/-- The manuscript's explicit lower scale `14 ≤ K p_i` keeps every corrected
integer count nonnegative.  This deliberately asserts nonnegativity of the
*corrected counts*: the first correction `c_0` itself can be negative. -/
theorem tangent_corrected_counts_nonnegative_of_fourteen
    (K D : Nat) (p : Fin 4 → Real)
    (hCount : ∑ i, (K : Real) * p i = (K : Real))
    (hMoment : ∑ i, (tangentDeficit i : Real) * ((K : Real) * p i) =
      (D : Real))
    (hLower : ∀ i, (14 : Real) ≤ (K : Real) * p i) :
    ∀ i, (0 : Int) ≤ tangentCorrectedInt K D p i := by
  have hf_le (i : Fin 4) :
      ((Int.floor ((K : Real) * p i) : Int) : Real) ≤ (K : Real) * p i :=
    Int.floor_le _
  have hf_lt (i : Fin 4) :
      (K : Real) * p i < ((Int.floor ((K : Real) * p i) : Int) : Real) + 1 :=
    Int.lt_floor_add_one _
  have hlo0 := hLower (0 : Fin 4)
  have hlo1 := hLower (1 : Fin 4)
  have hlo2 := hLower (2 : Fin 4)
  have hlo3 := hLower (3 : Fin 4)
  have hle0 := hf_le (0 : Fin 4)
  have hle1 := hf_le (1 : Fin 4)
  have hle2 := hf_le (2 : Fin 4)
  have hle3 := hf_le (3 : Fin 4)
  have hlt0 := hf_lt (0 : Fin 4)
  have hlt1 := hf_lt (1 : Fin 4)
  have hlt2 := hf_lt (2 : Fin 4)
  have hlt3 := hf_lt (3 : Fin 4)
  simp only [Fin.sum_univ_four] at hCount hMoment
  simp [tangentDeficit] at hMoment
  intro i
  have hi : (0 : Real) ≤ (tangentCorrectedInt K D p i : Real) := by
    fin_cases i
    · simp [tangentCorrectedInt, tangentCorrectedRaw, tangentCorrectionRaw,
        tangentC0Raw, tangentE0Raw, tangentE1Raw, tangentRawFloors,
        tangentDeficit, Fin.sum_univ_four]
      linarith
    · simp [tangentCorrectedInt, tangentCorrectedRaw, tangentCorrectionRaw,
        tangentC1Raw, tangentE0Raw, tangentE1Raw, tangentRawFloors,
        tangentDeficit, Fin.sum_univ_four]
      linarith
    · simp [tangentCorrectedInt, tangentCorrectedRaw, tangentCorrectionRaw,
        tangentRawFloors]
      exact_mod_cast Int.floor_nonneg.mpr
        (show (0 : Real) ≤ (K : Real) * p (2 : Fin 4) by linarith)
    · simp [tangentCorrectedInt, tangentCorrectedRaw, tangentCorrectionRaw,
        tangentRawFloors]
      exact_mod_cast Int.floor_nonneg.mpr
        (show (0 : Real) ≤ (K : Real) * p (3 : Fin 4) by linarith)
  exact_mod_cast hi

end Erdos625
