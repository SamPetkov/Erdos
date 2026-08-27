import Erdos625.PhaseSignedFourSizeDerivativeLowerEnvelope
import Erdos625.FourDeficitScoreConvergence
import Mathlib.Tactic

/-!
# Uniform lower bound for the finite four-size entropy term

This module isolates one explicit remainder term in the signed derivative
lower envelope.  The proof first bounds the limiting four-Gaussian optimized
value from below using Gibbs feasibility, then transports that bound to the
exact finite scores by the existing uniform optimized-value convergence.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- The limiting four-Gaussian optimized value is bounded below by its worst
coordinate score.  The entropy part of the Gibbs optimizer is nonnegative. -/
theorem fourGaussian_optimizedValue_ge_neg_twenty_five_q_div_two
    (T : Real) (hT : T ∈ Ioo (2 : Real) 5) :
    -(25 * q / 2) ≤
      ProfileEntropyS4.optimizedValue fourGaussianScore T := by
  let p : Fin 4 → Real :=
    ProfileEntropyS4.optimizer fourGaussianScore T
  have hp_pos (i : Fin 4) : 0 < p i := by
    exact ProfileEntropyS4.optimizer_pos fourGaussianScore T i
  have hp_sum : ∑ i : Fin 4, p i = 1 := by
    exact ProfileEntropyS4.sum_optimizer fourGaussianScore T
  have hp_le_one (i : Fin 4) : p i ≤ 1 := by
    rw [← hp_sum]
    exact Finset.single_le_sum
      (fun j _ ↦ (hp_pos j).le) (Finset.mem_univ i)
  have hentropy :
      0 ≤ -(∑ i : Fin 4, p i * Real.log (p i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_nonneg fun i _ ↦ by
      have hlog : Real.log (p i) ≤ 0 :=
        Real.log_nonpos (hp_pos i).le (hp_le_one i)
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hp_pos i).le hlog)
  have hscore (i : Fin 4) :
      -(25 * q / 2) ≤ fourGaussianScore i := by
    fin_cases i <;>
      simp [fourGaussianScore, ProfileEntropyS4.support] <;>
      nlinarith [q_pos]
  have hweighted :
      -(25 * q / 2) ≤ ∑ i : Fin 4, p i * fourGaussianScore i := by
    calc
      -(25 * q / 2) = ∑ i : Fin 4, p i * (-(25 * q / 2)) := by
        rw [← Finset.sum_mul, hp_sum]
        ring
      _ ≤ ∑ i : Fin 4, p i * fourGaussianScore i := by
        exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hscore i) (hp_pos i).le
  have hattain :=
    ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target
      fourGaussianScore hT
  change -(25 * q / 2) ≤
    Real.log (ProfileEntropyS4.partition fourGaussianScore
      (ProfileEntropyS4.tilt fourGaussianScore T)) -
        ProfileEntropyS4.tilt fourGaussianScore T * T
  change
    -(∑ i : Fin 4, p i * Real.log (p i)) +
        ∑ i : Fin 4, p i * fourGaussianScore i = _ at hattain
  linarith

/-- Uniformly on the compact phase-root target interval, the exact finite
four-size entropy is eventually bounded below by one unit below the explicit
limiting Gaussian bound. -/
theorem eventually_fourSizeFiniteEntropy_ge_neg_twenty_five_q_div_two_sub_one :
    ∀ᶠ alpha : Nat in atTop,
      ∀ T ∈ Icc (9 / 4 : Real) (17 / 4 : Real),
        -(25 * q / 2) - 1 ≤ fourSizeFiniteEntropy alpha T := by
  obtain ⟨N, hN⟩ :=
    eventually_uniform_fourDeficitOptimizedValue 1 (by norm_num)
  filter_upwards [eventually_ge_atTop N] with alpha halpha
  intro T hT
  have hTopen : T ∈ Ioo (2 : Real) 5 := by
    constructor <;> linarith [hT.1, hT.2]
  have hclose := hN alpha halpha T hTopen
  have hlimit :=
    fourGaussian_optimizedValue_ge_neg_twenty_five_q_div_two T hTopen
  rw [abs_lt] at hclose
  change
    -(25 * q / 2) - 1 ≤
      ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T
  linarith [hlimit, hclose.1]

end

#print axioms fourGaussian_optimizedValue_ge_neg_twenty_five_q_div_two
#print axioms eventually_fourSizeFiniteEntropy_ge_neg_twenty_five_q_div_two_sub_one

end Erdos625
