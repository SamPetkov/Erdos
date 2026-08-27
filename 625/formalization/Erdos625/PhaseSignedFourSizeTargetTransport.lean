import Erdos625.PhaseSignedFourSizeLogLogCorridorTarget
import Mathlib.Tactic


namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

theorem real_abs_deficitTarget_sub_center_le
    {a s0 c x s : ℝ}
    (ha : 0 < a) (hs0nonneg : 0 ≤ s0) (hs0le : s0 ≤ a)
    (hc : 0 < c) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hslo : c * (1 - x) ≤ s) (hshi : s ≤ c * (1 + x)) :
    |(a - c * s0 / s) - (a - s0)| ≤ 2 * a * x := by
  have hspos : 0 < s := by
    have : 0 < c * (1 - x) := mul_pos hc (by linarith)
    exact this.trans_le hslo
  have habs : |s - c| ≤ c * x := by
    rw [abs_le]
    constructor <;> nlinarith
  have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
  have hnum : s0 * |s - c| ≤ a * (c * x) := by
    calc
      s0 * |s - c| ≤ s0 * (c * x) :=
        mul_le_mul_of_nonneg_left habs hs0nonneg
      _ ≤ a * (c * x) := mul_le_mul_of_nonneg_right hs0le hcx
  have hcs : c ≤ 2 * s := by nlinarith
  have hscale : a * (c * x) ≤ 2 * a * x * s := by
    have h := mul_le_mul_of_nonneg_left hcs (mul_nonneg ha.le hx)
    nlinarith
  rw [show (a - c * s0 / s) - (a - s0) = s0 * (s - c) / s by
    field_simp [hspos.ne']; ring]
  rw [abs_div, abs_of_pos hspos, abs_mul, abs_of_nonneg hs0nonneg]
  rw [div_le_iff₀ hspos]
  nlinarith

private theorem eventually_two_mul_mul_logLogOrder_div_phaseNat_lt
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 * C * logLogOrder n / (phaseNat n : ℝ) < ε := by
  have hOneC : 0 < 1 + C := by linarith
  have hEps : (0 : ℝ) < ε / (4 * (1 + C)) := by positivity
  have hLittle := logLogOrder_isLittleO_logOrder.bound hEps
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLogLogNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards [hLittle, hLogPos, hLogLogNonneg,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hsmall hlog hloglog hphase
  rw [Real.norm_eq_abs, abs_of_nonneg hloglog,
    Real.norm_eq_abs, abs_of_pos hlog] at hsmall
  have hphasePos : (0 : ℝ) < phaseNat n := hlog.trans_le hphase.1
  have hCLe : C ≤ 1 + C := by linarith
  have hscaled :
      2 * C * logLogOrder n ≤ ε / 2 * logOrder n := by
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ 2 * C)
    have hCbound : 2 * C ≤ 2 * (1 + C) := by linarith
    have hmono := mul_le_mul_of_nonneg_right hCbound hloglog
    calc
      2 * C * logLogOrder n ≤ 2 * (1 + C) * logLogOrder n := by
        nlinarith
      _ ≤ 2 * (1 + C) *
          (ε / (4 * (1 + C)) * logOrder n) := by
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = ε / 2 * logOrder n := by field_simp; ring
  rw [div_lt_iff₀ hphasePos]
  have hhalf : ε / 2 * logOrder n < ε * (phaseNat n : ℝ) := by
    have hlogphase : logOrder n ≤ (phaseNat n : ℝ) := hphase.1
    nlinarith
  exact hscaled.trans_lt hhalf

private theorem eventually_mul_logLogOrder_le_phaseNat_div_sixty_four_probe
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C * logLogOrder n ≤ (phaseNat n : ℝ) / 64 := by
  have hOneC : 0 < 1 + C := by linarith
  have hEps : (0 : ℝ) < 1 / (64 * (1 + C)) := by positivity
  have hLittle := logLogOrder_isLittleO_logOrder.bound hEps
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLogLogNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards [hLittle, hLogPos, hLogLogNonneg,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hsmall hlog hloglog hphase
  rw [Real.norm_eq_abs, abs_of_nonneg hloglog,
    Real.norm_eq_abs, abs_of_pos hlog] at hsmall
  have hCLe : C ≤ 1 + C := by linarith
  have hmul : C * logLogOrder n ≤ (1 + C) * logLogOrder n :=
    mul_le_mul_of_nonneg_right hCLe hloglog
  have hscaled :
      (1 + C) * logLogOrder n ≤ logOrder n / 64 := by
    calc
      (1 + C) * logLogOrder n ≤
          (1 + C) * ((1 / (64 * (1 + C))) * logOrder n) :=
        mul_le_mul_of_nonneg_left hsmall hOneC.le
      _ = logOrder n / 64 := by field_simp
  exact hmul.trans (hscaled.trans (by linarith [hphase.1]))

theorem eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center
    (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        |fourSizeTarget n (phaseNat n) s - phaseRootDeficitTarget n| < ε := by
  have hsmall :=
    eventually_two_mul_mul_logLogOrder_div_phaseNat_lt C ε hC hε
  have hscale :=
    eventually_mul_logLogOrder_le_phaseNat_div_sixty_four_probe C hC
  have hLogLogNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat, hsmall, hscale, hLogLogNonneg] with
      n hcenter hphase hsmallN hscaleN hloglog
  obtain ⟨hdom, hs0Pos, _⟩ := hcenter
  set a : ℝ := (phaseNat n : ℝ) with ha
  set s0 : ℝ := phaseRootS0 n with hs0
  set c : ℝ := phaseRootCenter n with hc
  set x : ℝ := C * logLogOrder n / a ^ 2 with hx
  have haSix : (6 : ℝ) ≤ a := by rw [ha]; exact_mod_cast hphase
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hcEq : c = (n : ℝ) / s0 := by rw [hc, hs0]; rfl
  have hcPos : 0 < c := by rw [hcEq]; exact div_pos hnPos hs0Pos
  have hnEq : (n : ℝ) = c * s0 := by
    rw [hcEq]
    field_simp [hs0Pos.ne']
  have hs0Eq : s0 = a + phaseDelta n - 1 - 2 / q := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom, ha]
  have hs0Le : s0 ≤ a := by
    have hTwoDivPos : 0 < 2 / q := div_pos (by norm_num) q_pos
    linarith [phaseDelta_lt_one n]
  have hxNonneg : 0 ≤ x := by
    rw [hx]
    positivity
  have hxHalf : x ≤ 1 / 2 := by
    rw [hx]
    rw [div_le_iff₀ haSqPos]
    have hscaleA : C * logLogOrder n ≤ a / 64 := by simpa [ha] using hscaleN
    nlinarith [sq_nonneg (a - 1)]
  intro s hs
  have hslo : c * (1 - x) ≤ s := by
    calc
      c * (1 - x) = phaseRootCenter n -
          C * logLogOrder n * phaseRootGapRadius n := by
            rw [hc, hx, phaseRootGapRadius, ha]
            ring
      _ ≤ s := hs.1
  have hshi : s ≤ c * (1 + x) := by
    calc
      s ≤ phaseRootCenter n +
          C * logLogOrder n * phaseRootGapRadius n := hs.2
      _ = c * (1 + x) := by
            rw [hc, hx, phaseRootGapRadius, ha]
            ring
  have hreal := real_abs_deficitTarget_sub_center_le
    haPos hs0Pos.le hs0Le hcPos hxNonneg hxHalf hslo hshi
  have hmove :
      fourSizeTarget n (phaseNat n) s = a - c * s0 / s := by
    rw [fourSizeTarget, ha, hnEq]
  have hcenterTarget : phaseRootDeficitTarget n = a - s0 := by
    rw [phaseRootDeficitTarget_eq hdom, hs0Eq]
    ring
  rw [hmove, hcenterTarget]
  calc
    |a - c * s0 / s - (a - s0)| ≤ 2 * a * x := hreal
    _ = 2 * C * logLogOrder n / a := by
      rw [hx]
      field_simp [haPos.ne']
    _ < ε := by simpa [ha] using hsmallN


#print axioms real_abs_deficitTarget_sub_center_le
#print axioms eventually_uniform_phaseRootLogLogCorridor_fourSizeTarget_tendsto_center

end

end Erdos625
