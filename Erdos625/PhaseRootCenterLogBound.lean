import Erdos625.PhaseRootFiniteCommon

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem logOrder_sub_log_phaseRootCenter_isBigO :
    (fun n : ℕ ↦
      logOrder n - Real.log (phaseRootCenter n))
      =O[atTop] (fun n : ℕ ↦ logLogOrder n) := by
  apply IsBigO.of_bound 3
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1,
    tendsto_logOrder_atTop.eventually_ge_atTop 10,
    eventually_gt_atTop (0 : ℕ)] with n hn hphase hw hN hnpos
  have hs0pos : 0 < phaseRootS0 n := hn.2.1
  have hs0ne : phaseRootS0 n ≠ 0 := hs0pos.ne'
  have hnrealpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnrealne : (n : ℝ) ≠ 0 := hnrealpos.ne'
  have hs0le : phaseRootS0 n ≤ 4 * logOrder n := by
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hn.1]
    have hdelta := phaseDelta_lt_one n
    have htwoqpos : 0 < 2 / q := div_pos (by norm_num) q_pos
    linarith [hphase.2]
  have hs0ge : 1 ≤ phaseRootS0 n := by
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hn.1]
    have hdelta := phaseDelta_nonneg n
    have hqLower : (1 / 2 : ℝ) < q :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    have htwoq : 2 / q < 4 := by
      rw [div_lt_iff₀ q_pos]
      linarith
    linarith [hphase.1]
  have hlogOrderpos : 0 < logOrder n :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 10) hN
  have hlog_s0_nonneg : 0 ≤ Real.log (phaseRootS0 n) := Real.log_nonneg hs0ge
  have hlog_s0_le : Real.log (phaseRootS0 n) ≤ logLogOrder n + 2 := by
    calc
      Real.log (phaseRootS0 n) ≤ Real.log (4 * logOrder n) :=
        Real.strictMonoOn_log.monotoneOn hs0pos
          (mul_pos (by norm_num) hlogOrderpos) hs0le
      _ = Real.log 4 + logLogOrder n := by
        rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hlogOrderpos.ne']
        rfl
      _ ≤ logLogOrder n + 2 := by
        have : Real.log (4 : ℝ) ≤ 2 := by
          calc
            Real.log (4 : ℝ) ≤ Real.log (Real.exp 2) :=
              Real.strictMonoOn_log.monotoneOn (by norm_num)
                (Real.exp_pos 2)
                (by
                  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
                  nlinarith [Real.exp_one_gt_two])
            _ = 2 := Real.log_exp 2
        linarith
  rw [show phaseRootCenter n = (n : ℝ) / phaseRootS0 n from rfl,
    Real.log_div hnrealne hs0ne]
  simp only [logOrder]
  have hcancel :
      Real.log (n : ℝ) - (Real.log (n : ℝ) - Real.log (phaseRootS0 n)) =
        Real.log (phaseRootS0 n) := by ring
  rw [hcancel, Real.norm_eq_abs, abs_of_nonneg hlog_s0_nonneg,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ logLogOrder n)]
  linarith

end

end Erdos625
