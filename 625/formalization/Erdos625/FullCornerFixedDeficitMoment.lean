import Erdos625.PhaseConsequences
import Erdos625.FourDeficitScoreConvergence
import Mathlib.Tactic

/-!
# Fixed four-deficit first-moment asymptotics

This module packages the finite predecessor shifts `2, 3, 4, 5` of the
canonical phase first moment.  It is the phase-moment input for the later
full-corner activity estimate; it deliberately contains no midpoint rounding,
vertex-ratio asymptotic, partial-diagonal weight, or aggregate theorem.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- For each manuscript deficit `2,3,4,5`, the logarithmic first moment at
`phaseNat n - deficit` has the expected fixed-shift exponent. -/
theorem log_mu_phaseNat_sub_fourDeficit_div_logOrder_sub_phaseDelta_add_tendsto_zero
    (i : Fin 4) :
    Tendsto
      (fun n : Nat =>
        Real.log (mu n (phaseNat n - fourDeficit i)) / logOrder n -
          (phaseDelta n + (fourDeficit i : Real)))
      atTop
      (nhds 0) := by
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact Real.log_pos (by exact_mod_cast hn)
  -- The phase eventually exceeds every fixed threshold, so all the
  -- natural-number subtractions below are genuine.
  have hBig : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop, m < phaseNat n := by
    intro m
    have hLog : ∀ᶠ n : ℕ in atTop, (m : ℝ) < logOrder n :=
      tendsto_logOrder_atTop.eventually (eventually_gt_atTop (m : ℝ))
    filter_upwards [hLog,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n h1 h2
    exact_mod_cast h1.trans_le h2.1
  -- The class-size logarithm is negligible after normalization.
  have hL1 : ∀ m : ℕ, Tendsto
      (fun n : ℕ ↦ Real.log ((phaseNat n - m : ℕ) : ℝ) / logOrder n)
      atTop (nhds 0) := by
    intro m
    refine squeeze_zero' ?_ ?_ (tendsto_log_phaseNat_add_div_logOrder_zero 0)
    · filter_upwards [hBig m, hLogPos] with n hm hL
      have h1 : (1 : ℝ) ≤ ((phaseNat n - m : ℕ) : ℝ) := by
        have h : 1 ≤ phaseNat n - m := by omega
        exact_mod_cast h
      exact div_nonneg (Real.log_nonneg h1) hL.le
    · filter_upwards [hBig m, hLogPos] with n hm hL
      have hpos : (0 : ℝ) < ((phaseNat n - m : ℕ) : ℝ) := by
        have h : 0 < phaseNat n - m := by omega
        exact_mod_cast h
      have hle : ((phaseNat n - m : ℕ) : ℝ) ≤ ((phaseNat n + 0 : ℕ) : ℝ) := by
        have h : phaseNat n - m ≤ phaseNat n + 0 := by omega
        exact_mod_cast h
      gcongr
  -- The complementary vertex factor has normalized logarithm exactly one.
  have hL2 : ∀ m : ℕ, Tendsto
      (fun n : ℕ ↦
        Real.log ((((n - (phaseNat n - m) : ℕ) + 1 : ℕ)) : ℝ) / logOrder n)
      atTop (nhds 1) := by
    intro m
    have hRange : ∀ᶠ n : ℕ in atTop, phaseNat n + 0 ≤ n := by
      filter_upwards [eventually_two_mul_phaseNat_le] with n hn
      omega
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_log_natSub_phaseNat_add_div_logOrder_one 0 hRange)
      tendsto_const_nhds ?_ ?_
    · filter_upwards [hBig (m + 1), eventually_two_mul_phaseNat_le, hLogPos]
        with n hm h2 hL
      have hposA : (0 : ℝ) < ((n - (phaseNat n + 0) : ℕ) : ℝ) := by
        have h : 0 < n - (phaseNat n + 0) := by omega
        exact_mod_cast h
      have hle : ((n - (phaseNat n + 0) : ℕ) : ℝ) ≤
          (((n - (phaseNat n - m) : ℕ) + 1 : ℕ) : ℝ) := by
        have h : n - (phaseNat n + 0) ≤ (n - (phaseNat n - m)) + 1 := by omega
        exact_mod_cast h
      gcongr
    · filter_upwards [hBig (m + 1), eventually_two_mul_phaseNat_le, hLogPos]
        with n hm h2 hL
      have hposA : (0 : ℝ) < (((n - (phaseNat n - m) : ℕ) + 1 : ℕ) : ℝ) := by
        positivity
      have hle : (((n - (phaseNat n - m) : ℕ) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        have h : (n - (phaseNat n - m)) + 1 ≤ n := by omega
        exact_mod_cast h
      have hlog : Real.log (((n - (phaseNat n - m) : ℕ) + 1 : ℕ) : ℝ) ≤
          logOrder n := Real.log_le_log hposA hle
      rw [div_le_one hL]
      exact hlog
  -- The exact power contribution of one predecessor step.
  have hL3 : ∀ m : ℕ, Tendsto
      (fun n : ℕ ↦ (((phaseNat n - m - 1 : ℕ) : ℝ) * q) / logOrder n)
      atTop (nhds 2) := by
    intro m
    have hConst : Tendsto
        (fun n : ℕ ↦ (((m : ℝ) + 1) * q) * (logOrder n)⁻¹) atTop (nhds 0) := by
      simpa using tendsto_inv_logOrder_zero.const_mul (((m : ℝ) + 1) * q)
    have h := (tendsto_phaseNat_add_mul_q_div_logOrder_two 0).sub hConst
    rw [show (2 : ℝ) - 0 = 2 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [hBig (m + 1), hLogPos] with n hm hL
    have hcast : ((phaseNat n - m - 1 : ℕ) : ℝ) = (phaseNat n : ℝ) - m - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ phaseNat n - m),
        Nat.cast_sub (by omega : m ≤ phaseNat n), Nat.cast_one]
    (simp only [Nat.add_zero, hcast, div_eq_mul_inv]; ring)
  -- The normalized adjacent predecessor increment is exactly `+1`.
  have hStep : ∀ m : ℕ, Tendsto
      (fun n : ℕ ↦
        (Real.log (mu n (phaseNat n - (m + 1))) -
          Real.log (mu n (phaseNat n - m))) / logOrder n)
      atTop (nhds 1) := by
    intro m
    have h := ((hL1 m).sub (hL2 m)).add (hL3 m)
    rw [show (0 : ℝ) - 1 + 2 = 1 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [hBig (m + 1), eventually_two_mul_phaseNat_le, hLogPos]
      with n hm h2 hL
    have hs : 0 < phaseNat n - m := by omega
    have hsv : phaseNat n - m ≤ n := by omega
    have hsub : phaseNat n - (m + 1) = (phaseNat n - m) - 1 := by omega
    rw [hsub, log_mu_pred_sub_log_mu hs hsv]
    (push_cast; ring)
  -- Finite telescoping from the base theorem.
  have key : ∀ m : ℕ, Tendsto
      (fun n : ℕ ↦
        Real.log (mu n (phaseNat n - m)) / logOrder n -
          (phaseDelta n + (m : ℝ))) atTop (nhds 0) := by
    intro m
    induction m with
    | zero =>
        simpa using log_mu_phaseNat_div_logOrder_sub_phaseDelta_tendsto_zero
    | succ m ih =>
        have h := ih.add ((hStep m).sub_const 1)
        rw [show (0 : ℝ) + (1 - 1) = 0 by norm_num] at h
        refine h.congr fun n ↦ ?_
        rw [sub_div]
        (push_cast; ring)
  exact key (fourDeficit i)

end

end Erdos625
