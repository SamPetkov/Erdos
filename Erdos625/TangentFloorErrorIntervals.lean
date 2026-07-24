import Erdos625.TangentRoundingCore

namespace Erdos625

open scoped BigOperators

/-- Exact count and moment constraints force the signed floor errors into
their finite intervals.  The conclusion also records the resulting sharp
integral bounds on the two correction coordinates. -/
theorem tangent_floor_error_intervals
    (K D : Nat) (p : Fin 4 → Real)
    (hCount : ∑ i, (K : Real) * p i = (K : Real))
    (hMoment : ∑ i, (tangentDeficit i : Real) * ((K : Real) * p i) =
      (D : Real)) :
    (-3 : Int) ≤ tangentE0 K p ∧ tangentE0 K p ≤ 0 ∧
      (-13 : Int) ≤ tangentE1 K D p ∧ tangentE1 K D p ≤ 0 ∧
      (-2 : Int) ≤ tangentC0 K D p ∧ tangentC0 K D p ≤ 0 ∧
      (0 : Int) ≤ tangentC1 K D p ∧ tangentC1 K D p ≤ 5 := by
  have hle0 : ((Int.floor ((K : Real) * p 0) : Int) : Real) ≤ (K : Real) * p 0 :=
    Int.floor_le _
  have hle1 : ((Int.floor ((K : Real) * p 1) : Int) : Real) ≤ (K : Real) * p 1 :=
    Int.floor_le _
  have hle2 : ((Int.floor ((K : Real) * p 2) : Int) : Real) ≤ (K : Real) * p 2 :=
    Int.floor_le _
  have hle3 : ((Int.floor ((K : Real) * p 3) : Int) : Real) ≤ (K : Real) * p 3 :=
    Int.floor_le _
  have hlt0 : (K : Real) * p 0 < ((Int.floor ((K : Real) * p 0) : Int) : Real) + 1 :=
    Int.lt_floor_add_one _
  have hlt1 : (K : Real) * p 1 < ((Int.floor ((K : Real) * p 1) : Int) : Real) + 1 :=
    Int.lt_floor_add_one _
  have hlt2 : (K : Real) * p 2 < ((Int.floor ((K : Real) * p 2) : Int) : Real) + 1 :=
    Int.lt_floor_add_one _
  have hlt3 : (K : Real) * p 3 < ((Int.floor ((K : Real) * p 3) : Int) : Real) + 1 :=
    Int.lt_floor_add_one _
  simp [Fin.sum_univ_succ, tangentDeficit] at hCount hMoment
  have he0le : ((tangentE0 K p : Int) : Real) ≤ 0 := by
    simp [tangentE0, tangentE0Raw, tangentRawFloors, Fin.sum_univ_succ]
    linarith
  have he0gt : (-4 : Real) < ((tangentE0 K p : Int) : Real) := by
    simp [tangentE0, tangentE0Raw, tangentRawFloors, Fin.sum_univ_succ]
    linarith
  have he1le : ((tangentE1 K D p : Int) : Real) ≤ 0 := by
    simp [tangentE1, tangentE1Raw, tangentRawFloors, Fin.sum_univ_succ,
      tangentDeficit]
    linarith
  have he1gt : (-14 : Real) < ((tangentE1 K D p : Int) : Real) := by
    simp [tangentE1, tangentE1Raw, tangentRawFloors, Fin.sum_univ_succ,
      tangentDeficit]
    linarith
  have hc0le : ((tangentC0 K D p : Int) : Real) < 1 := by
    simp [tangentC0, tangentC0Raw, tangentE0Raw, tangentE1Raw,
      tangentRawFloors, Fin.sum_univ_succ, tangentDeficit]
    linarith
  have hc0gt : (-3 : Real) < ((tangentC0 K D p : Int) : Real) := by
    simp [tangentC0, tangentC0Raw, tangentE0Raw, tangentE1Raw,
      tangentRawFloors, Fin.sum_univ_succ, tangentDeficit]
    linarith
  have hc1ge : (0 : Real) ≤ ((tangentC1 K D p : Int) : Real) := by
    simp [tangentC1, tangentC1Raw, tangentE0Raw, tangentE1Raw,
      tangentRawFloors, Fin.sum_univ_succ, tangentDeficit]
    linarith
  have hc1lt : ((tangentC1 K D p : Int) : Real) < 6 := by
    simp [tangentC1, tangentC1Raw, tangentE0Raw, tangentE1Raw,
      tangentRawFloors, Fin.sum_univ_succ, tangentDeficit]
    linarith
  norm_cast at he0le he0gt he1le he1gt hc0le hc0gt hc1ge hc1lt
  omega

end Erdos625
