import Erdos625.FourDeficitScoreConvergence
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Uniform tilt corridor for the four-point Gaussian profile

This file ports the audited finite analytic leaf of the variable-target
tilt argument into the repository's existing four-point exponential family.
It deliberately reuses `q`, `fourGaussianScore`, `ProfileEntropyS4.mean`, and
`ProfileEntropyS4.strictMono_mean`; in particular, it does not introduce a
second exponential family or repeat the derivative/variance argument.

The conclusions below are only the analytic endpoint bracket needed later in
the proof of the uniform partition-ratio estimate.  They do not themselves
establish that finite uniform estimate or any probabilistic conclusion.
-/

namespace Erdos625

open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

private lemma fourGaussianMean_lower_value :
    ProfileEntropyS4.mean fourGaussianScore (2 * q) =
      (96 + 53 * Real.sqrt 2) / (40 + 17 * Real.sqrt 2) := by
  unfold ProfileEntropyS4.mean ProfileEntropyS4.firstNumerator
    ProfileEntropyS4.partition ProfileEntropyS4.unnormalized
    fourGaussianScore ProfileEntropyS4.support
  norm_num [Fin.sum_univ_four]
  ring
  unfold q
  norm_num [Real.exp_neg, Real.exp_mul, Real.exp_log]
  ring
  rw [show (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add'] <;> norm_num,
      show (2 : ℝ) ^ (5 / 2 : ℝ) = 2 ^ 2 * Real.sqrt 2 by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add'] <;>
          norm_num]
  ring
  grind

private lemma fourGaussianMean_lower_endpoint :
    ProfileEntropyS4.mean fourGaussianScore (2 * q) < 2 / q := by
  rw [fourGaussianMean_lower_value]
  have hqpos : 0 < q := q_pos
  have hqlt : q < 5 / 7 := by
    unfold q
    linarith [Real.log_two_lt_d9]
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_nonneg 2]
  have hden : 0 < 40 + 17 * Real.sqrt 2 := by positivity
  rw [div_lt_div_iff₀ hden hqpos]
  have hmean :
      (96 + 53 * Real.sqrt 2) * 5 <
        14 * (40 + 17 * Real.sqrt 2) := by
    linarith
  nlinarith

private lemma fourGaussianMean_upper_value :
    ProfileEntropyS4.mean fourGaussianScore (9 * q / 2) = 86 / 21 := by
  unfold ProfileEntropyS4.mean ProfileEntropyS4.firstNumerator
    ProfileEntropyS4.partition ProfileEntropyS4.unnormalized
    fourGaussianScore ProfileEntropyS4.support q
  norm_num [Fin.sum_univ_four]
  ring_nf
  norm_num
  norm_num [Real.exp_mul, Real.exp_log]

private lemma fourGaussianMean_upper_endpoint :
    1 + 2 / q <
      ProfileEntropyS4.mean fourGaussianScore (9 * q / 2) := by
  rw [fourGaussianMean_upper_value]
  have hqpos : 0 < q := q_pos
  have hq : 42 / 65 < q := by
    unfold q
    linarith [Real.log_two_gt_d9]
  have hdiv : 2 / q < 65 / 21 := by
    rw [div_lt_iff₀ hqpos]
    nlinarith
  linarith

/-- **Uniform four-size tilt corridor (analytic leaf).**

For every target in the full manuscript interval, any tilt whose existing
four-point Gaussian mean equals that target lies in the displayed strict
corridor.  The target remains variable; no selected phase value is silently
substituted.  This is an analytic input to, not a proof of, the later finite
uniform partition-ratio estimate.
-/
theorem uniform_four_size_tilt_corridor
    (target lambda : Real)
    (hTargetLower : 2 / q ≤ target)
    (hTargetUpper : target ≤ 1 + 2 / q)
    (hMean : ProfileEntropyS4.mean fourGaussianScore lambda = target) :
    2 * q < lambda ∧ lambda < 9 * q / 2 := by
  constructor <;> contrapose! hMean
  · exact ne_of_lt
      (lt_of_le_of_lt
        ((ProfileEntropyS4.strictMono_mean fourGaussianScore).monotone hMean)
        (lt_of_lt_of_le fourGaussianMean_lower_endpoint hTargetLower))
  · refine ne_of_gt
      (lt_of_lt_of_le ?_
        ((ProfileEntropyS4.strictMono_mean fourGaussianScore).monotone hMean))
    exact lt_of_le_of_lt hTargetUpper fourGaussianMean_upper_endpoint

/-- The original `delta` parameterization of the same variable-target
analytic corridor. -/
theorem uniform_four_size_tilt_corridor_for_delta
    (delta lambda : Real)
    (hDeltaLower : 0 ≤ delta)
    (hDeltaUpper : delta ≤ 1)
    (hMean :
      ProfileEntropyS4.mean fourGaussianScore lambda = 1 + 2 / q - delta) :
    2 * q < lambda ∧ lambda < 9 * q / 2 := by
  apply uniform_four_size_tilt_corridor (1 + 2 / q - delta) lambda
  · linarith
  · linarith
  · exact hMean

#print axioms uniform_four_size_tilt_corridor
#print axioms uniform_four_size_tilt_corridor_for_delta

end

end Erdos625
