import Erdos625.Section8EndpointSingleCellStubs
import Erdos625.Section8NearCellChoiceLink
import Erdos625.LocalSignReward
import Mathlib.Tactic

/-!
# Section VIII: exact one-cell partial/full deficit identity

For endpoint sizes `m` and `m+d`, compare a partial cell of multiplicity
`m-h` with the full-containment cell of multiplicity `m`.

The physical matching-count ratio is

`choose(m,h) / ((d+1) ... (d+h))`,

and the signed local-reward ratio is

`2^(-h*m + h*(h+1)/2)`.

This file proves the corresponding division-free identity over natural
numbers.  It is the exact local algebra needed before the single global
falling-factorial loss is applied.  No phase estimate or summation over cells
is used here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Number of literal partial stub matchings in a cell with endpoint sizes
`m` and `m+d` and prescribed multiplicity `j`. -/
def lowerUpperCellMatchingCount (m d j : Nat) : Nat :=
  Fintype.card (SingleCellStubMatching m (m + d) j)

/-- Physical matching count multiplied by the local signed reward. -/
def lowerUpperCellWeightedCount (m d j : Nat) : Nat :=
  lowerUpperCellMatchingCount m d j * localSignRewardNat j

/-- The consecutive product `(d+1) ... (d+h)` used by the deficit ratio. -/
def endpointDeficitDenominator (d h : Nat) : Nat :=
  ∏ t ∈ Finset.Icc 1 h, d + t

/-- Multiplying the consecutive endpoint-distance factors by `d!` gives the
factorial at the upper endpoint. -/
theorem factorial_mul_endpointDeficitDenominator
    (d h : Nat) :
    d.factorial * endpointDeficitDenominator d h = (d + h).factorial := by
  induction h with
  | zero => simp [endpointDeficitDenominator]
  | succ h ih =>
      rw [endpointDeficitDenominator,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ h + 1)]
      rw [← endpointDeficitDenominator, Nat.factorial_succ]
      calc
        d.factorial *
            (endpointDeficitDenominator d h * (d + (h + 1))) =
          (d.factorial * endpointDeficitDenominator d h) * (d + h + 1) := by
            ring
        _ = (d + h).factorial * (d + h + 1) := by rw [ih]
        _ = (d + h + 1).factorial := by
          rw [Nat.factorial_succ]

/-- The consecutive endpoint-distance product is a descending factorial. -/
theorem endpointDeficitDenominator_eq_descFactorial
    (d h : Nat) :
    endpointDeficitDenominator d h = (d + h).descFactorial h := by
  have hleft := factorial_mul_endpointDeficitDenominator d h
  have hright :
      d.factorial * (d + h).descFactorial h = (d + h).factorial := by
    simpa using
      (Nat.factorial_mul_descFactorial (show h ≤ d + h by omega))
  exact Nat.mul_left_cancel (hleft.trans hright.symm)

/-- Closed form for a one-cell matching count when the smaller endpoint is
`m`. -/
theorem lowerUpperCellMatchingCount_eq_choose_mul_descFactorial
    (m d j : Nat) (hj : j ≤ m) :
    lowerUpperCellMatchingCount m d j =
      m.choose j * (m + d).descFactorial j := by
  have hcard := card_singleCellStubMatching_mul_factorial m (m + d) j
  have hlower : m.descFactorial j = j.factorial * m.choose j :=
    Nat.descFactorial_eq_factorial_mul_choose
  rw [hlower] at hcard
  have hmul :
      lowerUpperCellMatchingCount m d j * j.factorial =
        (m.choose j * (m + d).descFactorial j) * j.factorial := by
    calc
      lowerUpperCellMatchingCount m d j * j.factorial =
          (j.factorial * m.choose j) * (m + d).descFactorial j := hcard
      _ = (m.choose j * (m + d).descFactorial j) * j.factorial := by
        ring
  exact Nat.mul_right_cancel hmul

/-- Splitting the upper-endpoint descending factorial at deficit `h`. -/
theorem upperEndpoint_descFactorial_full_split
    (m d h : Nat) (hh : h ≤ m) :
    (m + d).descFactorial m =
      (m + d).descFactorial (m - h) * (d + h).descFactorial h := by
  have hgap : m + d - (m - h) = d + h := by omega
  have hsum : (m - h) + h = m := Nat.sub_add_cancel hh
  calc
    (m + d).descFactorial m =
        (m + d).descFactorial ((m - h) + h) := by rw [hsum]
    _ = (m + d).descFactorial (m - h) *
          (m + d - (m - h)).descFactorial h := by
      rw [Nat.descFactorial_mul_descFactorial]
    _ = (m + d).descFactorial (m - h) *
          (d + h).descFactorial h := by rw [hgap]

/-- Exact physical matching-count ratio in cross-multiplied form. -/
theorem lowerUpperCellMatchingCount_deficit_cross_mul
    (m d h : Nat) (hh : h ≤ m) :
    lowerUpperCellMatchingCount m d (m - h) *
        endpointDeficitDenominator d h =
      lowerUpperCellMatchingCount m d m * m.choose h := by
  rw [lowerUpperCellMatchingCount_eq_choose_mul_descFactorial
      m d (m - h) (Nat.sub_le _ _),
    lowerUpperCellMatchingCount_eq_choose_mul_descFactorial m d m le_rfl,
    Nat.choose_self, one_mul, Nat.choose_symm hh,
    endpointDeficitDenominator_eq_descFactorial]
  rw [← upperEndpoint_descFactorial_full_split m d h hh]
  ring

/-- One-step identity for the quadratic binary exponent. -/
theorem deficitBinaryExponent_succ
    (m h : Nat) (hh : h + 1 ≤ m) :
    (h + 1) * m - (h + 1) * (h + 1 + 1) / 2 =
      h * m - h * (h + 1) / 2 + (m - (h + 1)) := by
  rw [tsub_eq_of_eq_add]
  zify [hh]
  rw [Nat.cast_sub] <;> push_cast <;>
    repeat nlinarith [Nat.div_mul_le_self (h * (h + 1)) 2]
  grind

/-- Removing one vertex from a high local reward costs exactly one binary
power. -/
theorem localSignRewardNat_pred_mul_pow
    (x : Nat) (hx : 4 ≤ x) :
    localSignRewardNat (x - 1) * 2 ^ (x - 1) =
      localSignRewardNat x := by
  have hx3 : 3 ≤ x := by omega
  have hpred3 : 3 ≤ x - 1 := by omega
  have hchooseRec :
      x.choose 2 = (x - 1).choose 2 + (x - 1) := by
    have hxrec : x - 1 + 1 = x := by omega
    conv_lhs => rw [← hxrec]
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    omega
  have hchoosePred : 1 ≤ (x - 1).choose 2 := by
    have hmono := Nat.choose_le_choose 2 hpred3
    norm_num at hmono
    omega
  have hexponent :
      ((x - 1).choose 2 - 1) + (x - 1) = x.choose 2 - 1 := by
    omega
  simp only [localSignRewardNat, if_pos hx3, if_pos hpred3]
  rw [← pow_add, hexponent]

/-- Exact local reward ratio across an arbitrary admissible deficit. -/
theorem localSignRewardNat_deficit_mul_pow
    (m h : Nat) (hh : h ≤ m) (hhigh : 3 ≤ m - h) :
    localSignRewardNat (m - h) *
        2 ^ (h * m - h * (h + 1) / 2) =
      localSignRewardNat m := by
  induction h with
  | zero => simp
  | succ h ih =>
      have hhPrev : h ≤ m := by omega
      have hhighPrev : 3 ≤ m - h := by omega
      have hstepHigh : 4 ≤ m - h := by omega
      have hstep := localSignRewardNat_pred_mul_pow (m - h) hstepHigh
      have hpred : m - h - 1 = m - (h + 1) := by omega
      rw [hpred] at hstep
      have hexponent := deficitBinaryExponent_succ m h (by omega)
      calc
        localSignRewardNat (m - (h + 1)) *
            2 ^ ((h + 1) * m - (h + 1) * (h + 1 + 1) / 2) =
          (localSignRewardNat (m - (h + 1)) *
            2 ^ (m - (h + 1))) *
              2 ^ (h * m - h * (h + 1) / 2) := by
                rw [hexponent, pow_add]
                ring
        _ = localSignRewardNat (m - h) *
              2 ^ (h * m - h * (h + 1) / 2) := by rw [hstep]
        _ = localSignRewardNat m := ih hhPrev hhighPrev

/-- Exact one-cell partial/full comparison, with every denominator kept in
cross-multiplied form. -/
theorem lowerUpperCellWeightedCount_deficit_cross_mul
    (m d h : Nat) (hh : h ≤ m) (hhigh : 3 ≤ m - h) :
    lowerUpperCellWeightedCount m d (m - h) *
        endpointDeficitDenominator d h *
          2 ^ (h * m - h * (h + 1) / 2) =
      lowerUpperCellWeightedCount m d m * m.choose h := by
  unfold lowerUpperCellWeightedCount
  rw [mul_assoc,
    show lowerUpperCellMatchingCount m d (m - h) *
        endpointDeficitDenominator d h =
      lowerUpperCellMatchingCount m d m * m.choose h from
        lowerUpperCellMatchingCount_deficit_cross_mul m d h hh,
    localSignRewardNat_deficit_mul_pow m h hh hhigh]
  ring

#print axioms endpointDeficitDenominator_eq_descFactorial
#print axioms lowerUpperCellMatchingCount_deficit_cross_mul
#print axioms localSignRewardNat_deficit_mul_pow
#print axioms lowerUpperCellWeightedCount_deficit_cross_mul

end

end Erdos625
