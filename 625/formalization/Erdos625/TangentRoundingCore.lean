import Mathlib

/-!
# Four-coordinate tangent rounding core

This source is deliberately independent of the Erdős--625 graph and
probability development.  Indices `0,1,2,3` encode manuscript deficits
`2,3,4,5`.  The four raw values are the floors `a_i = floor (K * p_i)`.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The manuscript deficit attached to coordinate `i = 0,1,2,3`. -/
def tangentDeficit (i : Fin 4) : Int := (i.1 : Int) + 2

/-- Natural-number version of `tangentDeficit`. -/
def tangentDeficitNat (i : Fin 4) : Nat := i.1 + 2

/-- The four preliminary floors `a_i = floor (K * p_i)`. -/
def tangentRawFloors (K : Nat) (p : Fin 4 → Real) : Fin 4 → Int :=
  fun i ↦ Int.floor ((K : Real) * p i)

/-- Signed error in the part-count constraint, for arbitrary integral raw data. -/
def tangentE0Raw (a : Fin 4 → Int) (K : Int) : Int :=
  (∑ i, a i) - K

/-- Signed error in the deficit constraint, for arbitrary integral raw data. -/
def tangentE1Raw (a : Fin 4 → Int) (D : Int) : Int :=
  (∑ i, tangentDeficit i * a i) - D

/-- The correction at manuscript deficit two: `c_0 = e_1 - 3 e_0`. -/
def tangentC0Raw (a : Fin 4 → Int) (K D : Int) : Int :=
  tangentE1Raw a D - 3 * tangentE0Raw a K

/-- The correction at manuscript deficit three: `c_1 = 2 e_0 - e_1`. -/
def tangentC1Raw (a : Fin 4 → Int) (K D : Int) : Int :=
  2 * tangentE0Raw a K - tangentE1Raw a D

/-- The correction vector `(c_0,c_1,0,0)`. -/
def tangentCorrectionRaw (a : Fin 4 → Int) (K D : Int) : Fin 4 → Int :=
  fun i ↦
    if i.1 = 0 then tangentC0Raw a K D
    else if i.1 = 1 then tangentC1Raw a K D
    else 0

/-- Correct arbitrary integral raw counts by the two tangent coordinates. -/
def tangentCorrectedRaw (a : Fin 4 → Int) (K D : Int) : Fin 4 → Int :=
  fun i ↦ a i + tangentCorrectionRaw a K D i

/-- Count error of the four raw floors. -/
def tangentE0 (K : Nat) (p : Fin 4 → Real) : Int :=
  tangentE0Raw (tangentRawFloors K p) (K : Int)

/-- Deficit error of the four raw floors. -/
def tangentE1 (K D : Nat) (p : Fin 4 → Real) : Int :=
  tangentE1Raw (tangentRawFloors K p) (D : Int)

/-- The first floor-rounding correction. -/
def tangentC0 (K D : Nat) (p : Fin 4 → Real) : Int :=
  tangentC0Raw (tangentRawFloors K p) (K : Int) (D : Int)

/-- The second floor-rounding correction. -/
def tangentC1 (K D : Nat) (p : Fin 4 → Real) : Int :=
  tangentC1Raw (tangentRawFloors K p) (K : Int) (D : Int)

/-- The corrected four-coordinate profile, still represented in `Int`. -/
def tangentCorrectedInt (K D : Nat) (p : Fin 4 → Real) : Fin 4 → Int :=
  tangentCorrectedRaw (tangentRawFloors K p) (K : Int) (D : Int)

/-- The corrected four-coordinate profile as natural numbers.  Its equality
with `tangentCorrectedInt` is only used after nonnegativity is proved. -/
def tangentCorrectedNat (K D : Nat) (p : Fin 4 → Real) : Fin 4 → Nat :=
  fun i ↦ (tangentCorrectedInt K D p i).toNat

end

end Erdos625
