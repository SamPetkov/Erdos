import Erdos625.PhaseRootCenterOpenCorridor
import Erdos625.ColoringProfilePhaseRootCenter
import Mathlib.Tactic

namespace Erdos625

open Filter Set Asymptotics

noncomputable section

set_option autoImplicit false

private theorem eventually_ten_lt_phaseNat :
    ∀ᶠ n : ℕ in atTop, 10 < phaseNat n := by
  have hLog : ∀ᶠ n : ℕ in atTop, (10 : ℝ) < logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_gt_atTop 10)
  filter_upwards [hLog,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder]
    with n hnLog hnPhase
  exact_mod_cast (hnLog.trans_le hnPhase.1)

private theorem eventually_phaseNat_sq_le_self :
    ∀ᶠ n : ℕ in atTop, (phaseNat n : ℝ) ^ 2 ≤ (n : ℝ) := by
  have hLogSq : (fun n : ℕ ↦ logOrder n ^ 2) =o[atTop] (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [logOrder, Function.comp_def, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hPhaseSq : (fun n : ℕ ↦ (phaseNat n : ℝ) ^ 2) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) :=
    (phaseNat_isTheta_logOrder.1.pow 2).trans_isLittleO hLogSq
  have hb := hPhaseSq.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with n hn
  have hnn : ‖(n : ℝ)‖ = (n : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpp : ‖(phaseNat n : ℝ) ^ 2‖ = (phaseNat n : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnn, hpp, one_mul] at hn
  exact hn

/-- The full fixed unit corridor around the reference center is eventually
positive and remains inside the finite deficit-support domain. -/
theorem eventually_phaseRoot_unitCorridor_domain :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (phaseRootCenter n - 1) (phaseRootCenter n + 1),
        0 < s ∧
          profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
            Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) := by
  have hqLower : (1 / 2 : ℝ) < q :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  have h1q : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; linarith
  have h2q : 2 / q < 4 := by rw [div_lt_iff₀ q_pos]; linarith
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_ten_lt_phaseNat, eventually_two_mul_phaseNat_le,
    eventually_phaseNat_sq_le_self, eventually_gt_atTop (2 : ℕ)]
    with n hcorr hten htwo hsq hn2
  obtain ⟨hdom, hs0pos, hmem⟩ := hcorr
  set s0 : ℝ := phaseRootS0 n with hs0def
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnNe : (n : ℝ) ≠ 0 := hnpos.ne'
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 3 ≤ n)
  have hPge11 : (11 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (by omega : 11 ≤ phaseNat n)
  have htwoR : (2 : ℝ) * (phaseNat n : ℝ) ≤ (n : ℝ) := by exact_mod_cast htwo
  have hsqR : (phaseNat n : ℝ) ^ 2 ≤ (n : ℝ) := hsq
  have hceq : phaseRootCenter n = (n : ℝ) / s0 := by rw [hs0def]; rfl
  have hncdiv : (n : ℝ) / phaseRootCenter n = s0 := by
    rw [hceq]; field_simp
  rw [Set.mem_Icc, hncdiv] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have hs0ge6 : (6 : ℝ) ≤ s0 := by linarith [hhi, hPge11, h2q]
  have hs0ltP : s0 < (phaseNat n : ℝ) := by linarith [hlo, h1q]
  have hL1 : phaseRootCenter n + 1 < (n : ℝ) := by
    have hc_lt : phaseRootCenter n < (n : ℝ) - 1 := by
      rw [hceq, div_lt_iff₀ hs0pos]
      nlinarith [hs0ge6, hn3, mul_le_mul_of_nonneg_right hs0ge6
        (show (0 : ℝ) ≤ (n : ℝ) - 1 by linarith)]
    linarith [hc_lt]
  have hL2 : (n : ℝ) < ((phaseNat n : ℝ) + 1) * (phaseRootCenter n - 1) := by
    have hPs0gt1 : (1 : ℝ) < (phaseNat n : ℝ) - s0 := by linarith [hlo, h1q]
    have hA : (n : ℝ) < (n : ℝ) * ((phaseNat n : ℝ) - s0) := by
      nlinarith [hPs0gt1, hnpos]
    have hB : (phaseNat n : ℝ) * s0 < (n : ℝ) := by
      nlinarith [hs0ltP, hsqR, hPge11, hs0pos]
    have hC : s0 < (n : ℝ) := by linarith [hs0ltP, htwoR]
    have key : (n : ℝ) * s0 < ((phaseNat n : ℝ) + 1) * ((n : ℝ) - s0) := by
      nlinarith [hA, hB, hC]
    rw [hceq]
    rw [show ((phaseNat n : ℝ) + 1) * ((n : ℝ) / s0 - 1) =
        (((phaseNat n : ℝ) + 1) * ((n : ℝ) - s0)) / s0 by field_simp <;> ring]
    rw [lt_div_iff₀ hs0pos]
    exact key
  have hcge2 : (2 : ℝ) ≤ phaseRootCenter n := by
    rw [hceq, le_div_iff₀ hs0pos]; linarith [hs0ltP, htwoR]
  intro s hs
  rw [Set.mem_Icc] at hs
  obtain ⟨hslo, hshi⟩ := hs
  have hspos : 0 < s := by linarith [hcge2, hslo]
  refine ⟨hspos, ?_⟩
  rw [profileDeficitTarget, Set.mem_Ioo]
  constructor
  · have hAlt : (n : ℝ) / s < (phaseNat n : ℝ) + 1 := by
      rw [div_lt_iff₀ hspos]
      have hmul : ((phaseNat n : ℝ) + 1) * (phaseRootCenter n - 1) ≤
          ((phaseNat n : ℝ) + 1) * s :=
        mul_le_mul_of_nonneg_left (by linarith [hslo]) (by positivity)
      linarith [hL2, hmul]
    linarith [hAlt]
  · have hBlt : (1 : ℝ) < (n : ℝ) / s := by
      rw [lt_div_iff₀ hspos, one_mul]
      linarith [hshi, hL1]
    linarith [hBlt]

end

end Erdos625
