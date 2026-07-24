import Erdos625.PhaseRootDerivativeQuadraticLower
import Erdos625.ColoringProfilePhaseDerivative
import Erdos625.ColoringProfilePhaseObjectiveDeficitDecomposition
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- Growth control: eventually the natural phase squared (plus itself) is
dominated by `n`.  Follows from `phaseNat ≤ 4 * logOrder` and
`(log n) ^ 2 = o(n)` (`Real.isLittleO_pow_log_id_atTop`). -/
theorem eventually_phaseNat_sq_add_phaseNat_le :
    ∀ᶠ n : ℕ in atTop,
      (phaseNat n : ℝ) ^ 2 + (phaseNat n : ℝ) ≤ (n : ℝ) := by
  have hcomp : (fun n : ℕ => Real.log (n : ℝ) ^ 2) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    have := (Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, id_eq] using this
  have hlin : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    have := Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, id_eq] using this
  have hb := hcomp.def (by norm_num : (0 : ℝ) < 1 / 32)
  have hb2 := hlin.def (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [hb, hb2, eventually_ge_atTop 1,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hn2 hn1 hphase
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hn hn2
  have f1 : Real.log (n : ℝ) ^ 2 ≤ 1 / 32 * (n : ℝ) :=
    (abs_le.mp (by rwa [abs_of_nonneg hnn] at hn)).2
  have f2 : Real.log (n : ℝ) ≤ 1 / 8 * (n : ℝ) :=
    (abs_le.mp (by rwa [abs_of_nonneg hnn] at hn2)).2
  have hlogOrder : logOrder n = Real.log (n : ℝ) := rfl
  have hple : (phaseNat n : ℝ) ≤ 4 * Real.log (n : ℝ) := by
    have := hphase.2; rw [hlogOrder] at this; linarith
  have hlogpos : 0 ≤ Real.log (n : ℝ) := by
    have h := hphase.1; rw [hlogOrder] at h
    have hpnn : (0 : ℝ) ≤ phaseNat n := by positivity
    linarith
  have hpnn : (0 : ℝ) ≤ (phaseNat n : ℝ) := by positivity
  nlinarith [f1, f2, hple, hlogpos, hpnn, sq_nonneg (Real.log (n : ℝ))]

/-- A genuinely uniform eventual selected-term bound: for every deficit
`target` in a fixed compact interval strictly above `-1`, the complete
selected term is quadratically negligible, and the target lands in the
exact finite open support.  This is the corridor generalization of
`eventually_abs_phaseRootDerivativeSelectedTerm_le_quadratic`, obtained by
quantifying over the whole target interval rather than the single center
target. -/
theorem eventually_forall_mem_Icc_abs_selectedTerm_le_quadratic
    {A B : ℝ} (hA : -1 < A) (hAB : A ≤ B) :
    ∀ᶠ n : ℕ in atTop,
      ∀ target ∈ Icc A B,
        target ∈ Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) ∧
          |Real.log
              (profileDeficitPartition (phaseNat n)
                (profileDeficitTilt (phaseNat n) target)) -
            profileDeficitTilt (phaseNat n) target * (phaseNat n : ℝ)| ≤
          q / 16 * (phaseNat n : ℝ) ^ 2 := by
  obtain ⟨M, hMnn, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hA hAB
  obtain ⟨N, hN⟩ := eventually_atTop.1 huniform
  -- The constant logarithmic-partition envelope coming from the Gaussian bound.
  set CL : ℝ :=
    Real.exp M + Real.exp (M ^ 2 / q) * (1 / (1 - Real.exp (-q / 4))) with hCLdef
  -- The linear-growth threshold ensuring quadratic domination.
  set K : ℝ := 16 / q * (CL + M) with hKdef
  have hphaseN : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (N : ℝ),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact_mod_cast hn.trans hphase.1
  have hphaseK : ∀ᶠ n : ℕ in atTop, K ≤ (phaseNat n : ℝ) := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop K,
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hphase
    exact hn.trans hphase.1
  filter_upwards [hphaseN, hphaseK, eventually_two_le_phaseNat] with
    n hlarge hKle hphasePos target htarget
  have hpair := hN (phaseNat n) hlarge target htarget
  have htiltbound := hpair.2
  refine ⟨hpair.1, ?_⟩
  -- Partition corridor: lower bound `1` and Gaussian-envelope upper bound `CL`.
  have hpartLower :=
    one_le_profileDeficitPartition (phaseNat n) (by omega)
      (profileDeficitTilt (phaseNat n) target)
  have hpartUpper :=
    profileDeficitPartition_le_gaussianEnvelope (phaseNat n) (by omega) htiltbound
  rw [← hCLdef] at hpartUpper
  have hCLnn : (0 : ℝ) ≤ CL := by linarith
  have hlogPart :
      |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) target))| ≤ CL := by
    rw [abs_of_nonneg (Real.log_nonneg hpartLower)]
    exact (Real.log_le_sub_one_of_pos (profileDeficitPartition_pos _ _)).trans (by linarith)
  have hPnn : (0 : ℝ) ≤ (phaseNat n : ℝ) := by positivity
  have htiltP :
      |profileDeficitTilt (phaseNat n) target * (phaseNat n : ℝ)| ≤
        M * (phaseNat n : ℝ) := by
    rw [abs_mul, abs_of_nonneg hPnn]
    exact mul_le_mul_of_nonneg_right htiltbound hPnn
  have hqDivNn : (0 : ℝ) ≤ q / 16 := div_nonneg q_pos.le (by norm_num)
  have hstep : CL + M ≤ q / 16 * (phaseNat n : ℝ) := by
    have hK : q / 16 * K = CL + M := by
      have hqne : q ≠ 0 := q_pos.ne'
      rw [hKdef]; field_simp
    calc CL + M = q / 16 * K := hK.symm
      _ ≤ q / 16 * (phaseNat n : ℝ) := mul_le_mul_of_nonneg_left hKle hqDivNn
  have hP1 : (1 : ℝ) ≤ (phaseNat n : ℝ) := by exact_mod_cast (by omega : 1 ≤ phaseNat n)
  have hfinal :
      CL + M * (phaseNat n : ℝ) ≤ q / 16 * (phaseNat n : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hstep hPnn,
      mul_nonneg hCLnn (by linarith : (0 : ℝ) ≤ (phaseNat n : ℝ) - 1)]
  calc
    |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) target)) -
        profileDeficitTilt (phaseNat n) target * (phaseNat n : ℝ)| ≤
        |Real.log
          (profileDeficitPartition (phaseNat n)
            (profileDeficitTilt (phaseNat n) target))| +
        |profileDeficitTilt (phaseNat n) target * (phaseNat n : ℝ)| := abs_sub _ _
    _ ≤ CL + M * (phaseNat n : ℝ) := by linarith
    _ ≤ q / 16 * (phaseNat n : ℝ) ^ 2 := hfinal

/-- Pure real-analysis kernel controlling the deficit target `a - (c·s₀)/s`
over the unit corridor `s ∈ [c - 1, c + 1]` around the center `c`, where the
center target `a - s₀` already lies in `[low, high]` and the center is at
least `s₀ + 1` above the corridor floor.  The size mean `(c·s₀)/s` then
stays within `1` of `s₀`, so the target stays within `1` of its center
value. -/
theorem real_deficitTarget_corridor
    {a s0 c s low high : ℝ}
    (hs0 : 0 < s0) (hgrow : s0 + 1 ≤ c)
    (hs1 : c - 1 ≤ s) (hs2 : s ≤ c + 1)
    (hlow : low ≤ a - s0) (hhigh : a - s0 ≤ high) :
    low - 1 ≤ a - c * s0 / s ∧ a - c * s0 / s ≤ high + 1 := by
  have hcpos : 0 < c - 1 := by linarith
  have hc : 0 < c := by linarith
  have hspos : 0 < s := by linarith
  have hcs0 : 0 ≤ c * s0 := by positivity
  have hup : c * s0 / s ≤ s0 + 1 := by
    have h1 : c * s0 / s ≤ c * s0 / (c - 1) :=
      div_le_div_of_nonneg_left hcs0 hcpos hs1
    have h2 : c * s0 / (c - 1) ≤ s0 + 1 := by
      rw [div_le_iff₀ hcpos]; nlinarith [hgrow, hs0]
    linarith
  have hlo : s0 - 1 ≤ c * s0 / s := by
    have h1 : c * s0 / (c + 1) ≤ c * s0 / s :=
      div_le_div_of_nonneg_left hcs0 hspos hs2
    have h2 : s0 - 1 ≤ c * s0 / (c + 1) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < c + 1)]; nlinarith [hgrow, hs0]
    linarith
  constructor <;> [linarith; linarith]

/-- Over the fixed unit corridor around the reference center, the exact
deficit target stays inside a fixed compact interval strictly above `-1`.
This is the analytic heart: the corridor has width `2`, whereas the center
is of size `n / s₀ → ∞`, so the target `α - n/s` varies by at most `1` from
its center value `1 + 2/q - phaseDelta ∈ [2/q, 1 + 2/q]`. -/
theorem eventually_forall_unitCorridor_deficitTarget_mem :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (phaseRootCenter n - 1) (phaseRootCenter n + 1),
        profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
          Icc (2 / q - 1) (2 + 2 / q) := by
  have hqLower : (1 / 2 : ℝ) < q :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  have h2q4 : (2 / q : ℝ) < 4 := by rw [div_lt_iff₀ q_pos]; linarith
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_phaseNat_sq_add_phaseNat_le,
    eventually_five_lt_phaseNat] with n hcorr hgrowth hfive s hs
  obtain ⟨hn, hs0pos, hcentermem⟩ := hcorr
  rw [mem_Icc] at hs
  set a := (phaseNat n : ℝ) with ha
  set s0 := phaseRootS0 n with hs0
  set c := phaseRootCenter n with hc
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcne : c ≠ 0 := by
    rw [hc]; unfold phaseRootCenter; exact div_ne_zero hnpos.ne' hs0pos.ne'
  have hDivide : (n : ℝ) / c = s0 := by rw [hc, hs0]; unfold phaseRootCenter; field_simp
  have hnc : (n : ℝ) = c * s0 := by rw [div_eq_iff hcne] at hDivide; rw [hDivide, mul_comm]
  have haR : (6 : ℝ) ≤ a := by rw [ha]; exact_mod_cast (by omega : 6 ≤ phaseNat n)
  have hs0le : s0 ≤ a := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hn, ha]
    have := phaseDelta_lt_one n
    have hq1 : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; linarith
    linarith
  have hgrow : s0 + 1 ≤ c := by
    have hpn2 : s0 ^ 2 + s0 ≤ (n : ℝ) := by nlinarith [hgrowth, hs0le, hs0pos.le]
    rw [hnc] at hpn2; nlinarith [hpn2, hs0pos]
  rw [mem_Icc] at hcentermem
  rw [hDivide] at hcentermem
  have htar : profileDeficitTarget (phaseNat n) (n : ℝ) s = a - c * s0 / s := by
    rw [profileDeficitTarget, ha, hnc]
  rw [htar, mem_Icc]
  obtain ⟨hl, hr⟩ :=
    real_deficitTarget_corridor hs0pos hgrow hs.1 hs.2 hcentermem.1 hcentermem.2
  exact ⟨hl, by linarith⟩

/-- Over the unit corridor the logarithm of the size coordinate is
quadratically negligible.  Since `s ∈ [center - 1, center + 1]` and
`center → ∞`, `|log s| ≤ |log center| + log 2`, both eventually below the
quadratic scale. -/
theorem eventually_forall_unitCorridor_abs_log_le :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (phaseRootCenter n - 1) (phaseRootCenter n + 1),
        |Real.log s| ≤ q / 8 * (phaseNat n : ℝ) ^ 2 := by
  have hqLower : (1 / 2 : ℝ) < q :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := Real.log_two_lt_d9.trans (by norm_num)
  have h2q4 : (2 / q : ℝ) < 4 := by rw [div_lt_iff₀ q_pos]; linarith
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_phaseNat_sq_add_phaseNat_le,
    eventually_five_lt_phaseNat,
    eventually_abs_log_phaseRootCenter_le_quadratic] with
    n hcorr hgrowth hfive hlogc s hs
  obtain ⟨hn, hs0pos, _⟩ := hcorr
  rw [mem_Icc] at hs
  set a := (phaseNat n : ℝ) with ha
  set s0 := phaseRootS0 n with hs0
  set c := phaseRootCenter n with hc
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcne : c ≠ 0 := by
    rw [hc]; unfold phaseRootCenter; exact div_ne_zero hnpos.ne' hs0pos.ne'
  have hDivide : (n : ℝ) / c = s0 := by rw [hc, hs0]; unfold phaseRootCenter; field_simp
  have hnc : (n : ℝ) = c * s0 := by rw [div_eq_iff hcne] at hDivide; rw [hDivide, mul_comm]
  have haR : (6 : ℝ) ≤ a := by rw [ha]; exact_mod_cast (by omega : 6 ≤ phaseNat n)
  have hs0le : s0 ≤ a := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hn, ha]
    have := phaseDelta_lt_one n
    have hq1 : (1 : ℝ) < 2 / q := by rw [lt_div_iff₀ q_pos]; linarith
    linarith
  have hs0ge : (1 : ℝ) ≤ s0 := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hn]
    have := phaseDelta_nonneg n
    linarith [haR, h2q4]
  have hgrow : s0 + 1 ≤ c := by
    have hpn2 : s0 ^ 2 + s0 ≤ (n : ℝ) := by nlinarith [hgrowth, hs0le, hs0pos.le]
    rw [hnc] at hpn2; nlinarith [hpn2, hs0pos]
  have hc2 : (2 : ℝ) ≤ c := by linarith
  have ha36 : (36 : ℝ) ≤ a ^ 2 := by nlinarith [haR]
  have hqle : q ≤ q / 16 * a ^ 2 := by nlinarith [q_pos, ha36]
  have hs_pos : 0 < s := by linarith [hs.1]
  have hs_ge1 : 1 ≤ s := by linarith [hs.1]
  have hlogs_nonneg : 0 ≤ Real.log s := Real.log_nonneg hs_ge1
  have hupper : Real.log s ≤ Real.log (c + 1) := Real.log_le_log hs_pos (by linarith [hs.2])
  have h2c : Real.log (c + 1) ≤ Real.log (2 * c) := Real.log_le_log (by linarith) (by linarith)
  have hmul2 : Real.log (2 * c) = Real.log 2 + Real.log c :=
    Real.log_mul (by norm_num) (by linarith)
  have hlogc2 : Real.log c ≤ q / 16 * a ^ 2 := (abs_le.mp hlogc).2
  rw [abs_of_nonneg hlogs_nonneg]
  calc Real.log s ≤ Real.log (2 * c) := by linarith
    _ = Real.log 2 + Real.log c := hmul2
    _ = q + Real.log c := rfl
    _ ≤ q / 16 * a ^ 2 + q / 16 * a ^ 2 := by linarith
    _ ≤ q / 8 * a ^ 2 := by nlinarith [q_pos, sq_nonneg a]

/--
Upgrade the center-point derivative estimate to a fixed unit corridor.  This
is the next analytic input required before the quantitative root theorem can
be instantiated.
-/
theorem eventually_unrestrictedPhaseObjective_deriv_unitCorridor_lower :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (phaseRootCenter n - 1) (phaseRootCenter n + 1),
        q / 8 * (phaseNat n : ℝ) ^ 2 ≤
          deriv (unrestrictedPhaseObjective n) s := by
  have hAlow : (-1 : ℝ) < 2 / q - 1 := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  have hAB : (2 / q - 1 : ℝ) ≤ 2 + 2 / q := by
    have : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
    linarith
  filter_upwards [eventually_forall_mem_Icc_abs_selectedTerm_le_quadratic hAlow hAB,
    eventually_forall_unitCorridor_deficitTarget_mem,
    eventually_forall_unitCorridor_abs_log_le,
    eventually_factorialLogErrorBound_phaseNat_le_quadratic] with
    n hsel hTmem hlog hfac s hs
  -- The exact deficit target at this size coordinate.
  have hTIcc : profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
      Icc (2 / q - 1) (2 + 2 / q) := hTmem s hs
  obtain ⟨hTopen, hselbound⟩ :=
    hsel (profileDeficitTarget (phaseNat n) (n : ℝ) s) hTIcc
  -- Exact derivative up to the factorial error.
  have hderiv := abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le
    (n := n) (k := s) hTopen
  rw [abs_le] at hderiv
  have hlogbound : |Real.log s| ≤ q / 8 * (phaseNat n : ℝ) ^ 2 := hlog s hs
  have hselle := (abs_le.mp hselbound)
  have hloge := (abs_le.mp hlogbound)
  have hanonneg : (0 : ℝ) ≤ (phaseNat n : ℝ) := Nat.cast_nonneg _
  -- Combine: q/2·a² + a − (selected error) − (log error) − (factorial error) ≥ q/8·a².
  nlinarith [hderiv.1, hselle.1, hselle.2, hloge.1, hloge.2, hfac, hanonneg,
    mul_nonneg (le_of_lt q_pos) (sq_nonneg (phaseNat n : ℝ))]

end

end Erdos625
