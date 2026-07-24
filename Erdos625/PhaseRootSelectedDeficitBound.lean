import Erdos625.PhaseRootFiniteCommon

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseRootSelectedDeficitTerm_isBigO_one :
    phaseRootSelectedDeficitTerm =O[atTop]
      (fun _n : ℕ ↦ (1 : ℝ)) := by
  have hA : (-1 : ℝ) < 2 / q := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q : ℝ) ≤ 1 + 2 / q := by linarith
  obtain ⟨M, hM, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hA hAB
  rw [isBigO_iff]
  refine ⟨M * max |2 / q| |1 + 2 / q| +
      (Real.exp M + Real.exp (M ^ 2 / q) *
        (1 / (1 - Real.exp (-q / 4)))), ?_⟩
  obtain ⟨N, hN⟩ := (eventually_atTop.1 huniform)
  have hphaseLarge : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (N : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact_mod_cast hn.trans hphase.1
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
      hphaseLarge, eventually_two_le_phaseNat] with n hn hlarge hphasePos
  have htilt := (hN (phaseNat n) hlarge
    (phaseRootDeficitTarget n) (by
      simpa [phaseRootDeficitTarget] using hn.2.2)).2
  have hpartLower := one_le_profileDeficitPartition
    (phaseNat n) (by omega)
    (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))
  have hpartUpper := profileDeficitPartition_le_gaussianEnvelope
    (phaseNat n) (by omega) htilt
  have htargetAbs :
      |phaseRootDeficitTarget n| ≤ max |2 / q| |1 + 2 / q| :=
    abs_le_max_abs_abs
      (by simpa [phaseRootDeficitTarget] using hn.2.2.1)
      (by simpa [phaseRootDeficitTarget] using hn.2.2.2)
  rw [Real.norm_eq_abs, phaseRootSelectedDeficitTerm]
  calc
    |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))) -
        profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          phaseRootDeficitTarget n| ≤
        |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n)))| +
        |profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
          phaseRootDeficitTarget n| := abs_sub _ _
    _ ≤ (Real.exp M + Real.exp (M ^ 2 / q) *
          (1 / (1 - Real.exp (-q / 4)))) +
        M * max |2 / q| |1 + 2 / q| := by
      rw [abs_mul]
      gcongr
      · rw [abs_of_nonneg (Real.log_nonneg hpartLower)]
        exact (Real.log_le_sub_one_of_pos
          (profileDeficitPartition_pos _ _)).trans
            (by linarith)
    _ = (M * max |2 / q| |1 + 2 / q| +
        (Real.exp M + Real.exp (M ^ 2 / q) *
          (1 / (1 - Real.exp (-q / 4))))) * ‖(1 : ℝ)‖ := by
      norm_num
      ring

end

end Erdos625
