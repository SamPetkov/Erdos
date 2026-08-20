import Erdos625.MidpointProfileUniformDisplacement
import Erdos625.SignedFourSizeObjective
import Mathlib.Tactic

/-!
# Finite entropy loss under tangent rounding

This module proves the finite rounding seam needed by E625-10.  The exact
finite Gibbs optimizer on the four deficits is rounded by the existing tangent
correction.  Both the optimizer and the rounded proportions satisfy the same
total-mass and deficit-moment constraints.  Their entropy-score gap is a
relative entropy and is bounded by a coordinatewise chi-square estimate.

The final constant is explicit:

`4 * 5^2 / 14 = 50 / 7`.

No phase asymptotic, root theorem, probability estimate, partial-diagonal
bound, or final Erdős statement is used here.
-/

open Finset
open scoped BigOperators

namespace Erdos625

noncomputable section

set_option autoImplicit false

namespace ProfileEntropyS4

/-- Scalar relative-entropy term bounded by its chi-square term plus the
linear discrepancy.  The `x = 0` case is retained explicitly. -/
theorem mul_log_div_le_sq_div_add_sub
    {x y : Real} (hx : 0 ≤ x) (hy : 0 < y) :
    x * Real.log (x / y) ≤ (x - y) ^ 2 / y + (x - y) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have hyEq : y ^ 2 / y = y := by
      field_simp [hy.ne'] <;> ring
    simpa [hyEq]
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hxpos hy)
    have hscaled := mul_le_mul_of_nonneg_left hlog hx
    calc
      x * Real.log (x / y) ≤ x * (x / y - 1) := hscaled
      _ = (x - y) ^ 2 / y + (x - y) := by
        field_simp [hy.ne']
        ring

/-- For two probability vectors, summing the scalar logarithmic bound removes
the linear discrepancies. -/
theorem sum_mul_log_div_le_chiSquare
    (p r : Fin 4 → Real)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hrSum : ∑ i : Fin 4, r i = 1) :
    (∑ i : Fin 4, p i * Real.log (p i / r i)) ≤
      ∑ i : Fin 4, (p i - r i) ^ 2 / r i := by
  calc
    (∑ i : Fin 4, p i * Real.log (p i / r i)) ≤
        ∑ i : Fin 4,
          ((p i - r i) ^ 2 / r i + (p i - r i)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_log_div_le_sq_div_add_sub (hp i) (hr i)
    _ = (∑ i : Fin 4, (p i - r i) ^ 2 / r i) +
          ((∑ i : Fin 4, p i) - ∑ i : Fin 4, r i) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ i : Fin 4, (p i - r i) ^ 2 / r i := by
      rw [hpSum, hrSum]
      ring

/-- Exact Gibbs-gap identity for a competitor with the same mass and support
mean as the optimizer. -/
theorem optimizedValue_sub_entropyScore_eq_sum_mul_log_div
    (h p : Fin 4 → Real) {T : Real}
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hpMean : ∑ i : Fin 4, p i * support i = T) :
    optimizedValue h T -
        (-(∑ i : Fin 4, p i * Real.log (p i)) +
          ∑ i : Fin 4, p i * h i) =
      ∑ i : Fin 4, p i * Real.log (p i / optimizer h T i) := by
  have hratio :
      (∑ i : Fin 4, p i * Real.log (p i / optimizer h T i)) =
        (∑ i : Fin 4, p i * Real.log (p i)) -
          ∑ i : Fin 4, p i * Real.log (optimizer h T i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hpi : p i = 0
    · simp [hpi]
    · rw [Real.log_div hpi (optimizer_pos h T i).ne']
      ring
  have hlog := sum_mul_log_weight h p (tilt h T) T hpSum hpMean
  rw [hratio]
  unfold optimizedValue
  simp only [optimizer] at hlog ⊢
  linarith

/-- A feasible competitor's entropy-score loss is nonnegative and bounded by
its chi-square distance from the exact Gibbs optimizer. -/
theorem optimizedValue_sub_entropyScore_nonneg_and_le_chiSquare
    (h p : Fin 4 → Real) {T : Real}
    (hT : T ∈ Set.Ioo (2 : Real) 5)
    (hp : ∀ i, 0 ≤ p i)
    (hpSum : ∑ i : Fin 4, p i = 1)
    (hpMean : ∑ i : Fin 4, p i * support i = T) :
    0 ≤ optimizedValue h T -
        (-(∑ i : Fin 4, p i * Real.log (p i)) +
          ∑ i : Fin 4, p i * h i) ∧
    optimizedValue h T -
        (-(∑ i : Fin 4, p i * Real.log (p i)) +
          ∑ i : Fin 4, p i * h i) ≤
      ∑ i : Fin 4,
        (p i - optimizer h T i) ^ 2 / optimizer h T i := by
  constructor
  · have hle := entropy_score_le_log_partition_sub_tilt_mul_target
      h p hT hp hpSum hpMean
    unfold optimizedValue
    linarith
  · rw [optimizedValue_sub_entropyScore_eq_sum_mul_log_div h p hpSum hpMean]
    exact sum_mul_log_div_le_chiSquare p (optimizer h T)
      hp (optimizer_pos h T) hpSum (sum_optimizer h T)

end ProfileEntropyS4

/-- The natural tangent-rounded multiplicity normalized to a real probability
coordinate. -/
noncomputable def midpointRoundedProportion
    (n alpha K : Nat) (i : Fin 4) : Real :=
  (midpointMultiplicity n alpha K i : Real) / (K : Real)

theorem midpointRoundedProportion_nonneg
    (n alpha K : Nat) (i : Fin 4) :
    0 ≤ midpointRoundedProportion n alpha K i := by
  unfold midpointRoundedProportion
  positivity

/-- Exact total mass of the rounded proportions. -/
theorem sum_midpointRoundedProportion
    (n alpha K : Nat)
    (h : MidpointRoundingAdmissible n alpha K) :
    ∑ i : Fin 4, midpointRoundedProportion n alpha K i = 1 := by
  have hCountNat :=
    (midpointMultiplicity_count_deficit_intDisplacement n alpha K h).1
  have hCountReal :
      (∑ i : Fin 4, (midpointMultiplicity n alpha K i : Real)) =
        (K : Real) := by
    exact_mod_cast hCountNat
  have hK : 0 < K := h.2.1
  have hKReal : (K : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK)
  unfold midpointRoundedProportion
  rw [← Finset.sum_div, hCountReal, div_self hKReal]

/-- Exact support mean of the rounded proportions. -/
theorem sum_midpointRoundedProportion_mul_support
    (n alpha K : Nat)
    (h : MidpointRoundingAdmissible n alpha K) :
    ∑ i : Fin 4,
        midpointRoundedProportion n alpha K i *
          ProfileEntropyS4.support i =
      fourSizeTarget n alpha (K : Real) := by
  have hMomentNat :=
    (midpointMultiplicity_count_deficit_intDisplacement n alpha K h).2.1
  have hMomentReal :
      (∑ i : Fin 4,
          (tangentDeficitNat i : Real) *
            (midpointMultiplicity n alpha K i : Real)) =
        (midpointDeficit n alpha K : Real) := by
    exact_mod_cast hMomentNat
  have hK : 0 < K := h.2.1
  have hn : n ≤ alpha * K := h.2.2.1
  have hKReal : (K : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK)
  have hDeficit :=
    deficit_cast_eq_parts_mul_fourSizeTarget n alpha K hK hn
  calc
    (∑ i : Fin 4,
        midpointRoundedProportion n alpha K i *
          ProfileEntropyS4.support i) =
        ∑ i : Fin 4,
          ((midpointMultiplicity n alpha K i : Real) *
            ProfileEntropyS4.support i) / (K : Real) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold midpointRoundedProportion
      ring
    _ = (∑ i : Fin 4,
          (midpointMultiplicity n alpha K i : Real) *
            ProfileEntropyS4.support i) / (K : Real) := by
      rw [Finset.sum_div]
    _ = (∑ i : Fin 4,
          (tangentDeficitNat i : Real) *
            (midpointMultiplicity n alpha K i : Real)) / (K : Real) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      simp [tangentDeficitNat, ProfileEntropyS4.support]
      ring
    _ = (midpointDeficit n alpha K : Real) / (K : Real) := by
      rw [hMomentReal]
    _ = ((K : Real) * fourSizeTarget n alpha (K : Real)) / (K : Real) := by
      rw [midpointDeficit, hDeficit]
    _ = fourSizeTarget n alpha (K : Real) := by
      field_simp [hKReal]

/-- The tangent-rounded four-size entropy loss is nonnegative and at most
`50 / 7`, after multiplication by the number of parts. -/
theorem midpointRoundedFourSizeEntropy_loss_le
    (n alpha K : Nat)
    (h : MidpointRoundingAdmissible n alpha K) :
    0 ≤ (K : Real) *
      (fourSizeFiniteEntropy alpha
          (fourSizeTarget n alpha (K : Real)) -
        (-(∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              Real.log (midpointRoundedProportion n alpha K i)) +
          ∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              fourDeficitScore alpha i)) ∧
    (K : Real) *
      (fourSizeFiniteEntropy alpha
          (fourSizeTarget n alpha (K : Real)) -
        (-(∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              Real.log (midpointRoundedProportion n alpha K i)) +
          ∑ i : Fin 4,
            midpointRoundedProportion n alpha K i *
              fourDeficitScore alpha i)) ≤
      (50 / 7 : Real) := by
  have hK : 0 < K := h.2.1
  have hTarget :
      fourSizeTarget n alpha (K : Real) ∈ Set.Ioo (2 : Real) 5 :=
    h.2.2.2.1
  have hLower : ∀ i : Fin 4,
      (14 : Real) ≤
        (K : Real) * midpointOptimizer n alpha K i :=
    h.2.2.2.2
  have hKPos : 0 < (K : Real) := by exact_mod_cast hK
  have hKReal : (K : Real) ≠ 0 := hKPos.ne'
  have hpPos : ∀ i : Fin 4, 0 < midpointOptimizer n alpha K i := by
    intro i
    unfold midpointOptimizer
    exact ProfileEntropyS4.optimizer_pos _ _ _
  have hGap :=
    ProfileEntropyS4.optimizedValue_sub_entropyScore_nonneg_and_le_chiSquare
      (fourDeficitScore alpha)
      (midpointRoundedProportion n alpha K)
      hTarget
      (midpointRoundedProportion_nonneg n alpha K)
      (sum_midpointRoundedProportion n alpha K h)
      (sum_midpointRoundedProportion_mul_support n alpha K h)
  have hTerm : ∀ i : Fin 4,
      (K : Real) *
          ((midpointRoundedProportion n alpha K i -
              midpointOptimizer n alpha K i) ^ 2 /
            midpointOptimizer n alpha K i) ≤
        (25 / 14 : Real) := by
    intro i
    have hDisp := midpointMultiplicity_uniform_displacement n alpha K h i
    have hBounds := (abs_le.mp hDisp)
    let d : Real :=
      (midpointMultiplicity n alpha K i : Real) -
        (K : Real) * midpointOptimizer n alpha K i
    have hdLower : (-5 : Real) ≤ d := by simpa [d] using hBounds.1
    have hdUpper : d ≤ 5 := by simpa [d] using hBounds.2
    have hProd : 0 ≤ (5 - d) * (5 + d) :=
      mul_nonneg (by linarith) (by linarith)
    have hSquare : d ^ 2 ≤ (25 : Real) := by
      nlinarith
    have hEq :
        (K : Real) *
            ((midpointRoundedProportion n alpha K i -
                midpointOptimizer n alpha K i) ^ 2 /
              midpointOptimizer n alpha K i) =
          d ^ 2 /
            ((K : Real) * midpointOptimizer n alpha K i) := by
      unfold midpointRoundedProportion
      dsimp only [d]
      field_simp [hKReal, (hpPos i).ne']
    rw [hEq]
    rw [div_le_iff₀ (mul_pos hKPos (hpPos i))]
    nlinarith [hLower i]
  have hChiSquare :
      (K : Real) *
          (∑ i : Fin 4,
            (midpointRoundedProportion n alpha K i -
                midpointOptimizer n alpha K i) ^ 2 /
              midpointOptimizer n alpha K i) ≤
        (50 / 7 : Real) := by
    calc
      (K : Real) *
          (∑ i : Fin 4,
            (midpointRoundedProportion n alpha K i -
                midpointOptimizer n alpha K i) ^ 2 /
              midpointOptimizer n alpha K i) =
        ∑ i : Fin 4,
          (K : Real) *
            ((midpointRoundedProportion n alpha K i -
                midpointOptimizer n alpha K i) ^ 2 /
              midpointOptimizer n alpha K i) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _i : Fin 4, (25 / 14 : Real) := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hTerm i
      _ = (50 / 7 : Real) := by
        norm_num [Fin.sum_univ_four]
  constructor
  · apply mul_nonneg hKPos.le
    simpa [fourSizeFiniteEntropy, midpointOptimizer] using hGap.1
  · calc
      (K : Real) *
          (fourSizeFiniteEntropy alpha
              (fourSizeTarget n alpha (K : Real)) -
            (-(∑ i : Fin 4,
                midpointRoundedProportion n alpha K i *
                  Real.log (midpointRoundedProportion n alpha K i)) +
              ∑ i : Fin 4,
                midpointRoundedProportion n alpha K i *
                  fourDeficitScore alpha i)) ≤
        (K : Real) *
          (∑ i : Fin 4,
            (midpointRoundedProportion n alpha K i -
                midpointOptimizer n alpha K i) ^ 2 /
              midpointOptimizer n alpha K i) := by
          apply mul_le_mul_of_nonneg_left _ hKPos.le
          simpa [fourSizeFiniteEntropy, midpointOptimizer] using hGap.2
      _ ≤ (50 / 7 : Real) := hChiSquare

#print axioms ProfileEntropyS4.mul_log_div_le_sq_div_add_sub
#print axioms ProfileEntropyS4.sum_mul_log_div_le_chiSquare
#print axioms ProfileEntropyS4.optimizedValue_sub_entropyScore_eq_sum_mul_log_div
#print axioms ProfileEntropyS4.optimizedValue_sub_entropyScore_nonneg_and_le_chiSquare
#print axioms midpointRoundedFourSizeEntropy_loss_le

end

end Erdos625
