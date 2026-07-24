import Erdos625.PhaseRootFiniteCommon

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

noncomputable def phaseRootAlgebraicNoLog (n : ℕ) : ℝ :=
  phaseExpansionMain n +
    phaseRootDeficitTarget n *
      (profileDeficitAffineB (phaseNat n) - logOrder n) -
    phaseRootS0 n + 1

theorem phaseRootAlgebraicNoLog_sub_logOrder_isBigO :
    (fun n : ℕ ↦ phaseRootAlgebraicNoLog n - logOrder n)
      =O[atTop] (fun n : ℕ ↦ logLogOrder n) := by
  have hOne : (fun _n : ℕ ↦ (1 : ℝ)) =O[atTop] logLogOrder := by
    apply IsBigO.of_bound 1
    filter_upwards [tendsto_logLogOrder_atTop.eventually_ge_atTop (1 : ℝ)] with n hn
    rw [norm_one, Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one hn), one_mul]
    exact hn
  have hDelta : (fun n : ℕ ↦ phaseDelta n) =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseDelta_nonneg n), norm_one, one_mul]
    exact (phaseDelta_lt_one n).le
  have hB : phaseB =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_of_nonneg (phaseB_pos n).le, norm_one, one_mul]
    exact phaseB_le_one n
  have hK : (fun n : ℕ ↦ phaseK (phaseDelta n)) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    obtain ⟨M, hM⟩ := exists_phaseK_abs_bound
    apply IsBigO.of_bound M
    filter_upwards with n
    rw [Real.norm_eq_abs, norm_one, mul_one]
    exact hM _ ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩
  have hLogPhase : (fun n : ℕ ↦ Real.log (phaseNat n : ℝ)) =O[atTop]
      logLogOrder := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      tendsto_logOrder_atTop.eventually_gt_atTop 1,
      tendsto_logLogOrder_atTop.eventually_gt_atTop (Real.log 4)] with n hp hN hw
    have hN0 : 0 < logOrder n := by linarith
    have hspos : (0 : ℝ) < phaseNat n := lt_of_lt_of_le hN0 hp.1
    have hlogpos : 0 < Real.log (phaseNat n : ℝ) := Real.log_pos (by linarith)
    have hprodpos : 0 < (4 : ℝ) * logOrder n := mul_pos (by norm_num) hN0
    have hupper : Real.log (phaseNat n : ℝ) ≤ Real.log 4 + logLogOrder n := by
      calc
        Real.log (phaseNat n : ℝ) ≤ Real.log (4 * logOrder n) :=
          Real.strictMonoOn_log.monotoneOn hspos hprodpos hp.2
        _ = Real.log 4 + logLogOrder n := by
          rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hN0.ne']
          rfl
    have hw0 : 0 < logLogOrder n :=
      lt_trans (Real.log_pos (by norm_num : (1 : ℝ) < 4)) hw
    rw [Real.norm_eq_abs, abs_of_pos hlogpos, Real.norm_eq_abs,
      abs_of_pos hw0, two_mul]
    linarith
  have hExact : ∀ᶠ n : ℕ in atTop,
      phaseRootAlgebraicNoLog n - logOrder n =
        (1 + 2 / q - phaseDelta n) * Real.log (phaseNat n : ℝ) +
        (phaseDelta n - 5 / 2) * logLogOrder n +
        phaseK (phaseDelta n) +
        (1 + 2 / q - phaseDelta n) *
          (2 * phaseC + q / 2 - q * phaseDelta n) -
        (2 * phaseC / q + phaseB n) - phaseDelta n + 2 + 2 / q := by
    filter_upwards [eventually_phaseDomain] with n hn
    have hpre : phaseRootAlgebraicNoLog n - logOrder n =
        (1 + 2 / q - phaseDelta n) * Real.log (phaseNat n : ℝ) +
        phaseK (phaseDelta n) + (2 / q - 1 / 2) * logLogOrder n +
        (1 + 2 / q - phaseDelta n) *
          (q * (phaseNat n : ℝ) - q / 2 - logOrder n) +
        phaseDelta n * (logOrder n - logLogOrder n) -
        ((phaseNat n : ℝ) + phaseDelta n - 1 - 2 / q) + 1 - logOrder n := by
      unfold phaseRootAlgebraicNoLog
      rw [show phaseRootDeficitTarget n = 1 + 2 / q - phaseDelta n by
        exact phaseRoot_target_identity hn]
      rw [show phaseRootS0 n =
          (phaseNat n : ℝ) + phaseDelta n - 1 - 2 / q by
        unfold phaseRootS0
        rw [alphaZero_eq_phaseNat_add_delta hn]]
      unfold phaseExpansionMain profileDeficitAffineB
      ring
    rw [hpre]
    have hp : (phaseNat n : ℝ) * q =
        2 * logOrder n - 2 * logLogOrder n + 2 * phaseC + q * phaseB n := by
      rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hn]
      unfold phaseS
      field_simp [q_ne_zero]
    rw [show phaseB n = 1 - phaseDelta n from rfl] at hp ⊢
    field_simp [q_ne_zero] at hp ⊢
    linear_combination (2 * q - 2 * q * phaseDelta n + 2) * hp
  have hCoeff : (fun n : ℕ ↦ 1 + 2 / q - phaseDelta n) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using ((Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left
      (1 + 2 / q)).sub hDelta
  have hCoeffTwo : (fun n : ℕ ↦ phaseDelta n - 5 / 2) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using hDelta.sub ((Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left
      (5 / 2))
  have hInner : (fun n : ℕ ↦ 2 * phaseC + q / 2 - q * phaseDelta n) =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
    simpa using ((Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left
      (2 * phaseC + q / 2)).sub (hDelta.const_mul_left q)
  have hRemainder : (fun n : ℕ ↦
        phaseK (phaseDelta n) +
        (1 + 2 / q - phaseDelta n) *
          (2 * phaseC + q / 2 - q * phaseDelta n) -
        (2 * phaseC / q + phaseB n) - phaseDelta n + 2 + 2 / q)
      =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
    have hConst (c : ℝ) : (fun _n : ℕ ↦ c) =O[atTop] (fun _n : ℕ ↦ (1 : ℝ)) := by
      simpa using (Asymptotics.isBigO_refl (fun _n : ℕ ↦ (1 : ℝ)) atTop).const_mul_left c
    have hProduct : (fun n : ℕ ↦ (1 + 2 / q - phaseDelta n) *
        (2 * phaseC + q / 2 - q * phaseDelta n)) =O[atTop]
        (fun _n : ℕ ↦ (1 : ℝ)) := by
      simpa using hCoeff.mul hInner
    have h := hK.add hProduct |>.sub ((hConst (2 * phaseC / q)).add hB)
      |>.sub hDelta |>.add (hConst 2) |>.add (hConst (2 / q))
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using h
  have hRemainderLog : (fun n : ℕ ↦
        phaseK (phaseDelta n) +
        (1 + 2 / q - phaseDelta n) *
          (2 * phaseC + q / 2 - q * phaseDelta n) -
        (2 * phaseC / q + phaseB n) - phaseDelta n + 2 + 2 / q)
      =O[atTop] logLogOrder := hRemainder.trans hOne
  have hFirst : (fun n : ℕ ↦
      (1 + 2 / q - phaseDelta n) * Real.log (phaseNat n : ℝ))
      =O[atTop] logLogOrder := by
    simpa using hCoeff.mul hLogPhase
  have hSecond : (fun n : ℕ ↦
      (phaseDelta n - 5 / 2) * logLogOrder n)
      =O[atTop] logLogOrder := by
    simpa using hCoeffTwo.mul (Asymptotics.isBigO_refl logLogOrder atTop)
  have hTotal := hFirst.add hSecond |>.add hRemainderLog
  apply hTotal.congr'
  · filter_upwards [hExact] with n hn
    rw [hn]
    ring
  · filter_upwards with n
    ring

end

end Erdos625


