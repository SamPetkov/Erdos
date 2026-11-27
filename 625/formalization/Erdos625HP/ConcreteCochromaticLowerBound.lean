import Erdos625.Section11ConcreteChromaticLowerTail
import Erdos625.Section10UniformAmplificationSpecialization
import Erdos625.PhaseRootDerivativeUnitCorridor
import Erdos625HP.CochromaticLowerTail

/-!
# Unconditional Section 4 cochromatic lower bound (`P(ζ(G_n) > k_ζ^-(n)) → 1`)

This module closes Section 4 (`sec:cochromatic-lower-bound`) and the
unrestricted root separation `r_+(n) - r_+^co(n)` of Proposition 5.2
**unconditionally** in Lean 4 on top of `Erdos625HP.CochromaticLowerTail`:

1. **Sharp two-sided corridor scale and derivative asymptotics:**
   * `eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_upper` —
     `s / α² ≤ (q³ / 8 + ε) · baseScale n` uniformly on every fixed log-log
     corridor (complementing `Erdos625`'s lower bound `q³ / 8 · baseScale n`).
   * `eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_sharp` —
     `(q / 2 - ε) α² ≤ deriv (unrestrictedPhaseObjective n) s ≤ (q / 2 + ε) α²`
     uniformly on every fixed log-log corridor.
2. **Concrete unrestricted cocolouring root `r_+^co(n)` and exact separation:**
   * `cocoloringUnrestrictedPhaseObjective n s = (log 2) s + L_{S_+}(n, s)` has
     an eventually unique zero `cocoloringUnrestrictedPhaseRootSelected n`
     (`r_+^co(n)`, with `phaseRootCenter n` fallback on finite prefixes) in a
     fixed log-log corridor around `phaseRootCenter n`.
   * `tendsto_unrestricted_sub_cocoloringRoot_div_baseScale` —
     `(r_+(n) - r_+^co(n)) / baseScale n → (log 2)³ / 4`.
3. **Unconditional full-sequence cochromatic lower tail:**
   * With `phaseCochromaticLowerIndex n = (⌊r_+^co(n)⌋ - ⌈log n⌉).toNat`
     (`k_ζ^-(n)`, totalized on finite prefixes via `Int.toNat`),
     `randomGraphMeasure_cochromaticNumberAtMost_phaseCochromaticLowerIndex_tendsto_zero`
     proves `P(ζ(G_n) ≤ k_ζ^-(n)) → 0`, and
     `randomGraphMeasure_phaseCochromaticLowerIndex_lt_cochromaticNumber_tendsto_one`
     proves `P(k_ζ^-(n) < ζ(G_n)) → 1` along all integers `n → ∞`.
-/

namespace Erdos625HP

open Erdos625 Filter MeasureTheory Set Asymptotics
open scoped ENNReal Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Sharp upper corridor scale and two-sided unrestricted derivative -/

private theorem one_sub_three_mul_le_cube {u : ℝ} (hu1 : u ≤ 1) :
    1 - 3 * u ≤ (1 - u) ^ 3 := by
  have h : 0 ≤ u ^ 2 * (3 - u) := mul_nonneg (sq_nonneg u) (by linarith)
  linarith [show (1 - u) ^ 3 - (1 - 3 * u) = u ^ 2 * (3 - u) by ring]

private theorem corridor_scale_ratio_le {d : ℝ} (hd0 : 0 ≤ d) (hd4 : d ≤ 1 / 4) :
    (1 + d / 12) * (1 + d / 4) ≤ (1 + d) * (1 - 3 * (d / 8)) := by
  have h1 : d ^ 2 ≤ d / 4 := by
    have := mul_le_mul_of_nonneg_left hd4 hd0
    linarith [show d * d = d ^ 2 by ring, show (1 / 4 : ℝ) * d = d / 4 by ring]
  linarith [show (1 + d) * (1 - 3 * (d / 8)) - (1 + d / 12) * (1 + d / 4) =
    (7 / 24) * d - (19 / 48) * d ^ 2 by ring]

/-- Complement to `Erdos625.eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower`:
uniformly across every fixed log-log corridor, `s / α² ≤ (q³ / 8 + ε) · baseScale n`. -/
theorem eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_upper
    (C : ℝ) (hC : 0 ≤ C) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
        s / (phaseNat n : ℝ) ^ 2 ≤ (q ^ 3 / 8 + epsilon) * baseScale n := by
  have hq3p : 0 < q ^ 3 + 1 := add_pos (pow_pos q_pos 3) zero_lt_one
  let delta : ℝ := min (1 / 4) (epsilon / (q ^ 3 + 1))
  have hdeltaPos : 0 < delta := lt_min (by norm_num) (div_pos hepsilon hq3p)
  have hdeltaQuarter : delta ≤ 1 / 4 := min_le_left _ _
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLogLogPos : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1
  have hWConst : ∀ᶠ n : ℕ in atTop, |2 * phaseC| + 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop _
  have hLLSmall : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (delta / (12 * (C + 1))) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (div_pos hdeltaPos (by positivity))
  have hLogLarge : ∀ᶠ n : ℕ in atTop, 20 / delta ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop _
  filter_upwards
    [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_five_lt_phaseNat,
      hLogPos, hLogLogPos, hWConst, hLLSmall, hLogLarge] with
      n hcenter hphase hfive hLogPosN hLL1 hWConstN hLLSmallN hLogLargeN
  obtain ⟨hdom, hs0Pos, _⟩ := hcenter
  intro s hs
  set a : ℝ := (phaseNat n : ℝ)
  set N : ℝ := logOrder n
  set w : ℝ := logLogOrder n
  set s0 : ℝ := phaseRootS0 n
  set c : ℝ := phaseRootCenter n
  set z : ℝ := q * a / (2 * N)
  have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hNPos : 0 < N := hLogPosN
  have hwPos : 0 < w := lt_of_lt_of_le zero_lt_one hLL1
  have hNLeA : N ≤ a := hphase.1
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hcEq : c = (n : ℝ) / s0 := rfl
  have hcPos : 0 < c := by rw [hcEq]; exact div_pos hnPos hs0Pos
  rw [Real.norm_eq_abs, abs_of_pos hwPos, Real.norm_eq_abs, abs_of_pos hNPos] at hLLSmallN
  have h1 : (C + 1) * w ≤ (delta / 12) * N := by
    have hmul := mul_le_mul_of_nonneg_left hLLSmallN (by positivity : (0 : ℝ) ≤ C + 1)
    have hsimp : (C + 1) * (delta / (12 * (C + 1)) * N) = (delta / 12) * N := by
      field_simp
    linarith
  have hxLe : C * w / a ^ 2 ≤ delta / 12 := by
    rw [div_le_iff₀ haSqPos]
    have h1a : 1 ≤ a := by
      have : (6 : ℝ) ≤ a := by
        change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
      linarith
    have hCw : C * w ≤ (delta / 12) * N := by
      have := mul_le_mul_of_nonneg_right (show C ≤ C + 1 by linarith) hwPos.le
      linarith
    have hNa2 : N ≤ a ^ 2 := by
      calc N ≤ a := hNLeA
        _ = a * 1 := (mul_one a).symm
        _ ≤ a * a := mul_le_mul_of_nonneg_left h1a haPos.le
        _ = a ^ 2 := (sq a).symm
    exact hCw.trans (mul_le_mul_of_nonneg_left hNa2 (by positivity))
  have hsUpper : s ≤ c * (1 + delta / 12) := by
    have hgapEq : phaseRootGapRadius n = c / a ^ 2 := rfl
    have hs2 : s ≤ c * (1 + C * w / a ^ 2) := by
      calc s ≤ c + C * w * (c / a ^ 2) := hs.2
        _ = c * (1 + C * w / a ^ 2) := by ring
    exact hs2.trans (mul_le_mul_of_nonneg_left (by linarith) hcPos.le)
  have hqlo : (2 / 3 : ℝ) < q :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have h2q3 : 2 / q < 3 := by rw [div_lt_iff₀ q_pos]; linarith
  have hs0Lower : a - 4 ≤ s0 := by
    have hs0Eq : s0 = a + phaseDelta n - 1 - 2 / q := by
      dsimp [s0, a]; rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom]
    linarith [phaseDelta_nonneg n]
  have haLarge : 20 / delta ≤ a := hLogLargeN.trans hNLeA
  have h4a : 4 ≤ (delta / 5) * a := by
    have : 20 ≤ a * delta := (div_le_iff₀ hdeltaPos).mp haLarge
    linarith
  have hcLeNa : c ≤ ((n : ℝ) / a) * (1 + delta / 4) := by
    rw [hcEq, div_le_iff₀ hs0Pos]
    have hs0Frac : (1 - delta / 5) * a ≤ s0 := by linarith
    have hprod : 1 ≤ (1 - delta / 5) * (1 + delta / 4) := by
      have hd2 : delta ^ 2 ≤ delta / 4 := by
        have := mul_le_mul_of_nonneg_left hdeltaQuarter hdeltaPos.le
        linarith [show delta * delta = delta ^ 2 by ring,
                  show (1 / 4 : ℝ) * delta = delta / 4 by ring]
      linarith [show (1 - delta / 5) * (1 + delta / 4) - 1 =
        delta / 20 - delta ^ 2 / 20 by ring]
    have hmul1 : (n : ℝ) ≤ ((n : ℝ) / a) * (1 + delta / 4) * ((1 - delta / 5) * a) := by
      calc (n : ℝ) = ((n : ℝ) / a) * a * 1 := by field_simp [haPos.ne']
        _ ≤ ((n : ℝ) / a) * a * ((1 - delta / 5) * (1 + delta / 4)) :=
            mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = ((n : ℝ) / a) * (1 + delta / 4) * ((1 - delta / 5) * a) := by ring
    exact hmul1.trans (mul_le_mul_of_nonneg_left hs0Frac (by positivity))
  have hphaseExact : a * q = 2 * N - 2 * w + 2 * phaseC + q * phaseB n := by
    dsimp [a, N, w]
    rw [phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hdom]
    unfold phaseS
    field_simp [q_ne_zero]
  have hqaLower : 2 * N - 3 * w ≤ q * a := by
    have hBpos : 0 ≤ q * phaseB n := mul_nonneg q_pos.le (phaseB_pos n).le
    have hCabs : -w ≤ 2 * phaseC := by
      have := neg_abs_le (2 * phaseC)
      linarith [hWConstN]
    linarith
  have hwN : 3 * w ≤ (delta / 4) * N := by
    have hc1 : w ≤ (C + 1) * w := by
      have := mul_le_mul_of_nonneg_right hC hwPos.le
      linarith
    linarith
  have hzLower : 1 - delta / 8 ≤ z := by
    dsimp [z]
    rw [le_div_iff₀ (mul_pos (by norm_num) hNPos)]
    linarith
  have hzPos : 0 < z := lt_of_lt_of_le (by linarith [hdeltaQuarter]) hzLower
  have hzCubeLower : 1 - 3 * (delta / 8) ≤ z ^ 3 :=
    (one_sub_three_mul_le_cube (by linarith [hdeltaQuarter])).trans
      (pow_le_pow_left₀ (by linarith [hdeltaQuarter]) hzLower 3)
  have hlogNe : Real.log (n : ℝ) ≠ 0 := by
    have : logOrder n ≠ 0 := hNPos.ne'
    simpa [logOrder] using this
  have hBaseId : ((n : ℝ) / a) / a ^ 2 = (q ^ 3 / 8 * baseScale n) / z ^ 3 := by
    dsimp [z, N, a]
    rw [baseScale, logOrder]
    field_simp [q_ne_zero, haPos.ne', hlogNe, hzPos.ne']
    norm_num
  have hRatioBound :
      (1 + delta / 12) * (1 + delta / 4) ≤ (1 + delta) * (1 - 3 * (delta / 8)) :=
    corridor_scale_ratio_le hdeltaPos.le hdeltaQuarter
  have hBaseNonneg : 0 ≤ baseScale n := by
    rw [baseScale, ← logOrder]; exact div_nonneg hnPos.le (pow_nonneg hNPos.le 3)
  have hsDiv : s / a ^ 2 ≤ (1 + delta) * (q ^ 3 / 8 * baseScale n) := by
    have hs1 : s ≤ ((n : ℝ) / a) * ((1 + delta / 12) * (1 + delta / 4)) := by
      calc s ≤ c * (1 + delta / 12) := hsUpper
        _ ≤ (((n : ℝ) / a) * (1 + delta / 4)) * (1 + delta / 12) :=
            mul_le_mul_of_nonneg_right hcLeNa (by positivity)
        _ = ((n : ℝ) / a) * ((1 + delta / 12) * (1 + delta / 4)) := by ring
    calc s / a ^ 2 ≤ (((n : ℝ) / a) / a ^ 2) * ((1 + delta / 12) * (1 + delta / 4)) := by
          rw [← mul_div_right_comm]
          exact div_le_div_of_nonneg_right hs1 haSqPos.le
      _ = ((q ^ 3 / 8 * baseScale n) / z ^ 3) * ((1 + delta / 12) * (1 + delta / 4)) := by
          rw [hBaseId]
      _ ≤ ((q ^ 3 / 8 * baseScale n) / z ^ 3) * ((1 + delta) * z ^ 3) := by
          refine mul_le_mul_of_nonneg_left (hRatioBound.trans ?_)
            (div_nonneg (mul_nonneg (div_nonneg (pow_nonneg q_pos.le 3) (by norm_num))
              hBaseNonneg) (pow_nonneg hzPos.le 3))
          exact mul_le_mul_of_nonneg_left hzCubeLower (by positivity)
      _ = (1 + delta) * (q ^ 3 / 8 * baseScale n) := by
          field_simp [hzPos.ne']
  have hCoeff : (1 + delta) * (q ^ 3 / 8) ≤ q ^ 3 / 8 + epsilon := by
    have hd2 : delta ≤ epsilon / (q ^ 3 + 1) := min_le_right _ _
    have hmul : delta * (q ^ 3 + 1) ≤ epsilon := (le_div_iff₀ hq3p).mp hd2
    have hdq : delta * q ^ 3 ≤ delta * (q ^ 3 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hdeltaPos.le
    linarith
  calc s / a ^ 2 ≤ ((1 + delta) * (q ^ 3 / 8)) * baseScale n := by linarith
    _ ≤ (q ^ 3 / 8 + epsilon) * baseScale n :=
        mul_le_mul_of_nonneg_right hCoeff hBaseNonneg

theorem eventually_corridor_abs_log_linear (C : ℝ) (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Icc
            (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
          |Real.log s| ≤ q + K * (phaseNat n : ℝ) := by
  obtain ⟨B, hBpos, hWith⟩ := logOrder_sub_log_phaseRootCenter_isBigO.exists_pos
  refine ⟨1 + B, by linarith, ?_⟩
  have hLL1 : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ 1 * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1)
  have hLLC : ∀ᶠ n : ℕ in atTop,
      ‖logLogOrder n‖ ≤ (1 / (64 * (1 + C))) * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by positivity)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono fun _ hn ↦ hn.le
  filter_upwards
    [hWith.bound, hLL1, hLLC, hLogPos, hLLNonneg,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_five_lt_phaseNat,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
      n hb hll1 hllc hpos hllnn hcenter hfive hphase s hs
  obtain ⟨hdom, hs0Pos, _⟩ := hcenter
  set a : ℝ := (phaseNat n : ℝ)
  set c : ℝ := phaseRootCenter n
  set L : ℝ := logOrder n
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := by positivity
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hcPos : 0 < c := div_pos hnPos hs0Pos
  rw [Real.norm_eq_abs, abs_of_nonneg hllnn, Real.norm_eq_abs, abs_of_pos hpos] at hll1 hllc
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hllnn] at hb
  have hcAbs : |Real.log c| ≤ (1 + B) * a := by
    have h1 : |L - Real.log c| ≤ B * L :=
      hb.trans (by simpa [one_mul] using mul_le_mul_of_nonneg_left hll1 hBpos.le)
    have hBL : B * L ≤ B * a := mul_le_mul_of_nonneg_left hphase.1 hBpos.le
    rw [abs_le] at h1 ⊢
    exact ⟨by linarith [h1.2, hphase.1], by linarith [h1.1, hphase.1]⟩
  have hwide : C * logLogOrder n * phaseRootGapRadius n ≤ c / 2 := by
    have h1 : C * logLogOrder n ≤ (1 + C) * logLogOrder n :=
      mul_le_mul_of_nonneg_right (by linarith) hllnn
    have h2 : (1 + C) * logLogOrder n ≤ L / 64 := by
      have hm := mul_le_mul_of_nonneg_left hllc (by linarith : (0 : ℝ) ≤ 1 + C)
      have hs' : (1 + C) * (1 / (64 * (1 + C)) * L) = L / 64 := by field_simp
      linarith
    have h3 : C * logLogOrder n ≤ a / 64 := h1.trans (h2.trans (by linarith [hphase.1]))
    have hfrac : C * logLogOrder n / a ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ haSqPos]
      have haa2 : a ≤ a ^ 2 := by
        calc a = a * 1 := (mul_one a).symm
          _ ≤ a * a := mul_le_mul_of_nonneg_left (by linarith) haPos.le
          _ = a ^ 2 := (sq a).symm
      linarith
    have hrew : C * logLogOrder n * phaseRootGapRadius n = c * (C * logLogOrder n / a ^ 2) := by
      unfold phaseRootGapRadius; dsimp [c, a]; ring
    rw [hrew]
    have hm := mul_le_mul_of_nonneg_left hfrac hcPos.le
    linarith
  have hsPos : 0 < s := by linarith [hs.1, hcPos]
  have hlogUp : Real.log s ≤ q + Real.log c := by
    have h := Real.log_le_log hsPos (show s ≤ 2 * c by linarith [hs.2, hwide])
    rw [Real.log_mul two_ne_zero hcPos.ne'] at h
    dsimp [q]; linarith
  have hlogLo : Real.log c - q ≤ Real.log s := by
    have h := Real.log_le_log hcPos (show c ≤ 2 * s by linarith [hs.1, hwide])
    rw [Real.log_mul two_ne_zero hsPos.ne'] at h
    dsimp [q]; linarith
  rw [abs_le] at hcAbs ⊢
  exact ⟨by linarith [hcAbs.1], by linarith [hcAbs.2]⟩

/-- **Sharp two-sided corridor derivative for the unrestricted phase objective:**
for every `C ≥ 0` and `ε > 0`, eventually across the `C`-corridor
`(q / 2 - ε) α² ≤ deriv (unrestrictedPhaseObjective n) s ≤ (q / 2 + ε) α²`. -/
theorem eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_sharp
    (C : ℝ) (hC : 0 ≤ C) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n),
        (q / 2 - epsilon) * (phaseNat n : ℝ) ^ 2 ≤
            deriv (unrestrictedPhaseObjective n) s ∧
          deriv (unrestrictedPhaseObjective n) s ≤
            (q / 2 + epsilon) * (phaseNat n : ℝ) ^ 2 := by
  have hAlow : (-1 : ℝ) < 9 / 4 := by norm_num
  have hAB : (9 / 4 : ℝ) ≤ 17 / 4 := by norm_num
  obtain ⟨M, hMnn, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hAlow hAB
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 huniform
  set CL : ℝ := Real.exp M + Real.exp (M ^ 2 / q) * (1 / (1 - Real.exp (-q / 4)))
  obtain ⟨K, hKnn, hKlog⟩ := eventually_corridor_abs_log_linear C hC
  have hphaseN0 : ∀ᶠ n : ℕ in atTop, N0 ≤ phaseNat n := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (N0 : ℝ),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact_mod_cast hn.trans hph.1
  let Btot : ℝ := |CL| + M + K + q + 6
  have hBtotPos : 0 < Btot := by dsimp [Btot]; linarith [abs_nonneg CL, hMnn, hKnn, q_pos]
  have hphaseBig : ∀ᶠ n : ℕ in atTop, Btot / epsilon + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (Btot / epsilon + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  filter_upwards
    [hphaseN0, hphaseBig, hKlog,
      eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      eventually_five_lt_phaseNat] with
      n hN0le hBig hLogN hTarget hfive s hs
  set a : ℝ := (phaseNat n : ℝ)
  have haSix : (6 : ℝ) ≤ a := by
    change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
  have hTIcc : profileDeficitTarget (phaseNat n) (n : ℝ) s ∈ Icc (9 / 4 : ℝ) (17 / 4) :=
    hTarget s hs
  obtain ⟨hTopen, htiltBound⟩ := hN0 (phaseNat n) hN0le _ hTIcc
  have hpartLower := one_le_profileDeficitPartition (phaseNat n) (by omega)
    (profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s))
  have hpartUpper := profileDeficitPartition_le_gaussianEnvelope (phaseNat n) (by omega) htiltBound
  have hlogPart :
      |Real.log (profileDeficitPartition (phaseNat n)
        (profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s)))| ≤ |CL| := by
    rw [abs_of_nonneg (Real.log_nonneg hpartLower)]
    have h1 := (Real.log_le_sub_one_of_pos (profileDeficitPartition_pos _ _)).trans
      (show profileDeficitPartition (phaseNat n) _ - 1 ≤ CL by dsimp [CL]; linarith)
    exact h1.trans (le_abs_self CL)
  have htiltA :
      |profileDeficitTilt (phaseNat n) (profileDeficitTarget (phaseNat n) (n : ℝ) s) * a| ≤ M * a := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ a by linarith)]
    exact mul_le_mul_of_nonneg_right htiltBound (by linarith)
  have hfac : factorialLogErrorBound (phaseNat n) ≤ a + 4 := by
    have h := Real.log_le_sub_one_of_pos (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
    have hEq : factorialLogErrorBound (phaseNat n) = Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
    rw [hEq]; push_cast at h ⊢; linarith
  have hfacNonneg : 0 ≤ factorialLogErrorBound (phaseNat n) := factorialLogErrorBound_nonneg _
  have hderiv := abs_unrestrictedPhaseObjective_deriv_sub_deficitMain_le (n := n) (k := s) hTopen
  rw [abs_le] at hderiv hlogPart htiltA
  have hlogS := abs_le.mp (hLogN s hs)
  have haEps : Btot ≤ a * epsilon := by
    have hle : Btot / epsilon ≤ a := by linarith
    exact (div_le_iff₀ hepsilon).mp hle
  have hRem : (|CL| + q + 4) + (M + K + 2) * a ≤ epsilon * a ^ 2 := by
    have h1 : Btot * a ≤ (a * epsilon) * a := mul_le_mul_of_nonneg_right haEps (by linarith)
    have h2 : |CL| + q + 4 ≤ (|CL| + q + 4) * a := by
      have hnn : 0 ≤ |CL| + q + 4 := by linarith [abs_nonneg CL, q_pos]
      calc |CL| + q + 4 = (|CL| + q + 4) * 1 := (mul_one _).symm
        _ ≤ (|CL| + q + 4) * a := mul_le_mul_of_nonneg_left (by linarith) hnn
    dsimp [Btot] at h1
    linarith [show (a * epsilon) * a = epsilon * a ^ 2 by ring]
  constructor <;> linarith

/-! ## 2. Concrete unrestricted cocolouring root `r_+^co(n)` and separation -/

/-- The unrestricted cocolouring phase objective `(log 2) s + L_{S_+}(n, s)`. -/
def cocoloringUnrestrictedPhaseObjective (n : ℕ) (s : ℝ) : ℝ :=
  q * s + unrestrictedPhaseObjective n s

theorem hasDerivAt_cocoloringUnrestrictedPhaseObjective
    {n : ℕ} {s : ℝ} (hphase : 5 < phaseNat n) (hspos : 0 < s)
    (htar : fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5) :
    HasDerivAt (cocoloringUnrestrictedPhaseObjective n)
      (q + (Real.log (profileDualPartition (phaseNat n + 1)
          (profileDualTilt (phaseNat n + 1) ((n : ℝ) / s))) -
        Real.log s)) s := by
  have hb : 2 ≤ phaseNat n + 1 := by omega
  have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hphase)
  rw [fourSizeTarget, mem_Ioo] at htar
  have hcast : (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 := by push_cast; ring
  have htarget : (n : ℝ) / s ∈ Ioo (1 : ℝ) (((phaseNat n + 1 : ℕ)) : ℝ) := by
    rw [mem_Ioo, hcast]
    exact ⟨by linarith [htar.2], by linarith [htar.1]⟩
  have h1 : HasDerivAt (fun x : ℝ ↦ q * x) q s := by
    simpa using (hasDerivAt_id s).const_mul q
  exact h1.add (hasDerivAt_profileDualOptimalValue_parts hb hspos htarget)

/-- Eventual existence and uniqueness of `r_+^co(n)` in a fixed log-log corridor. -/
theorem exists_pos_eventually_existsUnique_cocoloringUnrestrictedPhaseObjective_zero_logLogCorridor :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        ∃! r : ℝ,
          r ∈ Ioo
              (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
              (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) ∧
            cocoloringUnrestrictedPhaseObjective n r = 0 := by
  obtain ⟨B, hBpos, hB⟩ :=
    unrestrictedPhaseObjective_center_div_isBigO_logLogOrder.exists_pos
  let B' : ℝ := B + q
  have hB'pos : 0 < B' := add_pos hBpos q_pos
  let C : ℝ := 16 * B' / q
  have hCpos : 0 < C := div_pos (mul_pos (by norm_num) hB'pos) q_pos
  refine ⟨C, hCpos, ?_⟩
  have hdomain := eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le
  have hderiv := eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hCpos.le
  have hLL1 : ∀ᶠ n : ℕ in atTop, 1 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop 1
  filter_upwards
    [hB.bound, hdomain, hderiv,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_five_lt_phaseNat, hLL1] with
      n hcenterBound hdomainN hderivN hcenterDomain hphase hLL
  have hLLPos : 0 < logLogOrder n := lt_of_lt_of_le zero_lt_one hLL
  have hcenterPos : 0 < phaseRootCenter n :=
    div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenterDomain.1.1)) hcenterDomain.2.1
  have hphasePos : 0 < (phaseNat n : ℝ) := by exact_mod_cast (lt_trans (by omega : 0 < 5) hphase)
  have hgapPos : 0 < phaseRootGapRadius n := div_pos hcenterPos (sq_pos_of_pos hphasePos)
  let Delta : ℝ := C * logLogOrder n * phaseRootGapRadius n
  let E : ℝ := B' * logLogOrder n * phaseRootCenter n
  let D : ℝ := q / 8 * (phaseNat n : ℝ) ^ 2
  have hDelta : 0 < Delta := mul_pos (mul_pos hCpos hLLPos) hgapPos
  have hD : 0 < D := mul_pos (div_pos q_pos (by norm_num)) (sq_pos_of_pos hphasePos)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLLPos] at hcenterBound
  have hUnrestAbs : |unrestrictedPhaseObjective n (phaseRootCenter n)| ≤
      B * logLogOrder n * phaseRootCenter n := by
    calc |unrestrictedPhaseObjective n (phaseRootCenter n)|
        = |unrestrictedPhaseObjective n (phaseRootCenter n) / phaseRootCenter n| *
            phaseRootCenter n := by
          rw [abs_div, abs_of_pos hcenterPos, div_mul_cancel₀ _ hcenterPos.ne']
      _ ≤ (B * logLogOrder n) * phaseRootCenter n :=
          mul_le_mul_of_nonneg_right hcenterBound hcenterPos.le
  have hcenterAbs : |cocoloringUnrestrictedPhaseObjective n (phaseRootCenter n)| ≤ E := by
    unfold cocoloringUnrestrictedPhaseObjective
    calc |q * phaseRootCenter n + unrestrictedPhaseObjective n (phaseRootCenter n)|
        ≤ |q * phaseRootCenter n| + |unrestrictedPhaseObjective n (phaseRootCenter n)| :=
          abs_add_le _ _
      _ ≤ q * (logLogOrder n * phaseRootCenter n) + B * logLogOrder n * phaseRootCenter n := by
          rw [abs_of_pos (mul_pos q_pos hcenterPos)]
          have hqLL : q * phaseRootCenter n ≤ q * (logLogOrder n * phaseRootCenter n) := by
            calc q * phaseRootCenter n = q * (1 * phaseRootCenter n) := by ring
              _ ≤ q * (logLogOrder n * phaseRootCenter n) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLL hcenterPos.le) q_pos.le
          exact add_le_add hqLL hUnrestAbs
      _ = E := by dsimp [E, B']; ring
  have hEpos : 0 < E := mul_pos (mul_pos hB'pos hLLPos) hcenterPos
  have hproduct : D * Delta = 2 * E := by
    dsimp [D, Delta, E, C]
    rw [phaseRootGapRadius]
    field_simp [q_ne_zero, hphasePos.ne']
    ring
  have hmargin : E < D * Delta := by linarith
  let s0 : ℝ := phaseRootCenter n
  let psi : ℝ → ℝ := fun s ↦ -cocoloringUnrestrictedPhaseObjective n s
  have hkey : ∀ s ∈ Icc (s0 - Delta) (s0 + Delta),
      HasDerivAt (cocoloringUnrestrictedPhaseObjective n)
        (q + (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / s))) - Real.log s)) s := by
    intro s hs
    obtain ⟨hspos, htar⟩ := hdomainN s (by simpa [s0, Delta] using hs)
    exact hasDerivAt_cocoloringUnrestrictedPhaseObjective hphase hspos htar
  have hcont : ContinuousOn psi (Icc (s0 - Delta) (s0 + Delta)) :=
    fun s hs ↦ ((hkey s hs).continuousAt.neg).continuousWithinAt
  have hdiff : DifferentiableOn ℝ psi (Ioo (s0 - Delta) (s0 + Delta)) :=
    fun s hs ↦ ((hkey s (Ioo_subset_Icc_self hs)).neg.differentiableAt).differentiableWithinAt
  have hupper : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta), deriv psi s ≤ -D := by
    intro s hs
    have hd := hkey s (Ioo_subset_Icc_self hs)
    have hdu := hasDerivAt_profileDualOptimalValue_parts (by omega : 2 ≤ phaseNat n + 1)
      (hdomainN s (Ioo_subset_Icc_self (by simpa [s0, Delta] using hs))).1 (by
        have htar := (hdomainN s (Ioo_subset_Icc_self (by simpa [s0, Delta] using hs))).2
        rw [fourSizeTarget, mem_Ioo] at htar
        have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hphase)
        rw [mem_Ioo, show (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 by push_cast; ring]
        exact ⟨by linarith [htar.2], by linarith [htar.1]⟩)
    have hlow := hderivN s (Ioo_subset_Icc_self (by simpa [s0, Delta] using hs))
    unfold unrestrictedPhaseObjective at hlow
    rw [hdu.deriv] at hlow
    rw [(show HasDerivAt psi _ s from hd.neg).deriv]
    dsimp [D]
    linarith [q_pos]
  have hcenterPsi : |psi s0| ≤ E := by simpa [psi, s0] using hcenterAbs
  obtain ⟨r, hr, hunique⟩ :=
    existsUnique_root_mem_corridor_of_center_bound_deriv_upper
      hDelta hD hmargin hcenterPsi hcont hdiff hupper
  refine ⟨r, ⟨by simpa [s0, Delta] using hr.1, ?_⟩, ?_⟩
  · have h := hr.2; simp only [psi, neg_eq_zero] at h; exact h
  · intro y hy
    refine hunique y ⟨by simpa [s0, Delta] using hy.1, ?_⟩
    simp only [psi, neg_eq_zero]; exact hy.2

/-- Fixed corridor coefficient for `r_+^co(n)`. -/
def cocoloringUnrestrictedRootCorridorCoefficient : ℝ :=
  Classical.choose
    exists_pos_eventually_existsUnique_cocoloringUnrestrictedPhaseObjective_zero_logLogCorridor

theorem cocoloringUnrestrictedRootCorridorCoefficient_pos :
    0 < cocoloringUnrestrictedRootCorridorCoefficient :=
  (Classical.choose_spec
    exists_pos_eventually_existsUnique_cocoloringUnrestrictedPhaseObjective_zero_logLogCorridor).1

/-- Canonical concrete sequence `r_+^co(n)` selecting the unique zero of
`(log 2) s + L_{S_+}(n, s) = 0` in the log-log corridor. -/
def cocoloringUnrestrictedPhaseRootSelected (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ r : ℝ,
      r ∈ Ioo
          (phaseRootCenter n -
            cocoloringUnrestrictedRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            cocoloringUnrestrictedRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        cocoloringUnrestrictedPhaseObjective n r = 0 then
    Classical.choose h
  else
    phaseRootCenter n

theorem eventually_cocoloringUnrestrictedPhaseRootSelected_spec_unique :
    ∀ᶠ n : ℕ in atTop,
      (cocoloringUnrestrictedPhaseRootSelected n ∈ Ioo
          (phaseRootCenter n -
            cocoloringUnrestrictedRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            cocoloringUnrestrictedRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        cocoloringUnrestrictedPhaseObjective n
          (cocoloringUnrestrictedPhaseRootSelected n) = 0) ∧
      ∀ r : ℝ,
        r ∈ Ioo
            (phaseRootCenter n -
              cocoloringUnrestrictedRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              cocoloringUnrestrictedRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n) ∧
          cocoloringUnrestrictedPhaseObjective n r = 0 →
        r = cocoloringUnrestrictedPhaseRootSelected n := by
  filter_upwards [(Classical.choose_spec
    exists_pos_eventually_existsUnique_cocoloringUnrestrictedPhaseObjective_zero_logLogCorridor).2]
    with n ⟨r, hr, hunique⟩
  have hex : ∃ r' : ℝ,
      r' ∈ Ioo
          (phaseRootCenter n -
            cocoloringUnrestrictedRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            cocoloringUnrestrictedRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        cocoloringUnrestrictedPhaseObjective n r' = 0 := ⟨r, hr⟩
  have hspec : cocoloringUnrestrictedPhaseRootSelected n ∈ Ioo
        (phaseRootCenter n -
          cocoloringUnrestrictedRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          cocoloringUnrestrictedRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n) ∧
      cocoloringUnrestrictedPhaseObjective n
        (cocoloringUnrestrictedPhaseRootSelected n) = 0 := by
    classical
    rw [cocoloringUnrestrictedPhaseRootSelected, dif_pos hex]
    exact Classical.choose_spec hex
  refine ⟨hspec, fun y hy ↦ (hunique y hy).trans (hunique _ hspec).symm⟩

private theorem cocoloring_gap_close_bounds {theta : ℝ} (htheta : 0 < theta) :
    let eps := min (q / 4) (q * min theta 1 / 16)
    q ^ 3 / 4 - theta / 2 < (q / (q / 2 + eps)) * (q ^ 3 / 8) ∧
      (q / (q / 2 - eps)) * (q ^ 3 / 8 + eps) < q ^ 3 / 4 + theta / 2 := by
  intro eps
  have hmpos : 0 < min theta 1 := lt_min htheta zero_lt_one
  have hepsPos : 0 < eps := lt_min (div_pos q_pos (by norm_num))
    (div_pos (mul_pos q_pos hmpos) (by norm_num))
  have hepsLeQ4 : eps ≤ q / 4 := min_le_left _ _
  have hepsT : eps ≤ q * min theta 1 / 16 := min_le_right _ _
  have hmleT : min theta 1 ≤ theta := min_le_left _ _
  have hDenHiPos : 0 < q / 2 + eps := by linarith [q_pos]
  have hDenLoPos : 0 < q / 2 - eps := by linarith [hepsLeQ4, q_pos]
  have hq1 : q < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hq3le1 : q ^ 3 ≤ 1 := pow_le_one₀ q_pos.le hq1.le
  have hepsLeQT : eps ≤ q * theta / 16 := by
    refine hepsT.trans ?_
    have := mul_le_mul_of_nonneg_left hmleT q_pos.le
    linarith
  constructor
  · rw [div_mul_eq_mul_div, lt_div_iff₀ hDenHiPos]
    have h1 : (q ^ 3 / 4) * eps ≤ theta * q / 64 := by
      have hm1 : (q ^ 3 / 4) * eps ≤ (1 / 4 : ℝ) * (q * theta / 16) :=
        mul_le_mul (by linarith) hepsLeQT hepsPos.le (by norm_num)
      linarith
    have h2 : 0 < (theta / 2) * eps := mul_pos (half_pos htheta) hepsPos
    have h3 : 0 < theta * q := mul_pos htheta q_pos
    linarith [show (q ^ 3 / 4 - theta / 2) * (q / 2 + eps) =
      q * (q ^ 3 / 8) + (q ^ 3 / 4) * eps - theta * q / 4 - (theta / 2) * eps by ring]
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hDenLoPos]
    have hsum : q + q ^ 3 / 4 ≤ 5 / 4 := by linarith
    have h1 : (q + q ^ 3 / 4) * eps ≤ (5 / 64) * (theta * q) := by
      have hm1 : (q + q ^ 3 / 4) * eps ≤ (5 / 4 : ℝ) * (q * theta / 16) :=
        mul_le_mul hsum hepsLeQT hepsPos.le (by norm_num)
      linarith
    have h2 : (theta / 2) * eps ≤ (1 / 8) * (theta * q) := by
      have hm2 := mul_le_mul_of_nonneg_left hepsLeQ4 (half_pos htheta).le
      linarith
    have h3 : 0 < theta * q := mul_pos htheta q_pos
    linarith [show (q ^ 3 / 4 + theta / 2) * (q / 2 - eps) - q * (q ^ 3 / 8 + eps) =
      theta * q / 4 - (q + q ^ 3 / 4) * eps - (theta / 2) * eps by ring]

/-- **Unconditional Proposition 5.2 root separation:**
`(r_+(n) - r_+^co(n)) / baseScale n → (log 2)³ / 4`. -/
theorem tendsto_unrestricted_sub_cocoloringRoot_div_baseScale :
    Tendsto
      (fun n : ℕ ↦
        (unrestrictedPhaseRootSelected n -
          cocoloringUnrestrictedPhaseRootSelected n) / baseScale n)
      atTop (nhds ((Real.log 2) ^ 3 / 4)) := by
  rw [Metric.tendsto_atTop]
  intro theta htheta
  let C : ℝ := unrestrictedPhaseRootCorridorCoefficient +
    cocoloringUnrestrictedRootCorridorCoefficient
  have hCpos : 0 < C := add_pos unrestrictedPhaseRootCorridorCoefficient_pos
    cocoloringUnrestrictedRootCorridorCoefficient_pos
  let eps : ℝ := min (q / 4) (q * min theta 1 / 16)
  have hepsPos : 0 < eps := lt_min (div_pos q_pos (by norm_num))
    (div_pos (mul_pos q_pos (lt_min htheta zero_lt_one)) (by norm_num))
  have hepsLeQ4 : eps ≤ q / 4 := min_le_left _ _
  have hphaseBig : ∀ᶠ n : ℕ in atTop, 2 * q / eps + 1 ≤ (phaseNat n : ℝ) := by
    filter_upwards [tendsto_logOrder_atTop.eventually_ge_atTop (2 * q / eps + 1),
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn hph
    exact hn.trans hph.1
  have hLLPos : ∀ᶠ n : ℕ in atTop, 0 < logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_gt_atTop 0
  have hev :=
    (eventually_unrestrictedPhaseRootSelected_spec_unique.and
      eventually_cocoloringUnrestrictedPhaseRootSelected_spec_unique).and
    ((eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_sharp C hCpos.le
        (hepsilon := half_pos hepsPos)).and
      ((eventually_phaseRootLogLogCorridor_fourSize_domain C hCpos.le).and
        ((eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower C hCpos.le).and
          ((eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_upper C hCpos.le
              (hepsilon := hepsPos)).and
            ((eventually_five_lt_phaseNat.and hphaseBig).and
              ((eventually_phaseRoot_domain_pos_and_target_corridor.and
                (eventually_ge_atTop (2 : ℕ))).and hLLPos))))))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn ↦ ?_⟩
  rcases hN n hn with
    ⟨⟨hUnrest, hCo⟩, hDeriv, hDom, hScaleLo, hScaleHi, ⟨hfive, haBig⟩, ⟨hCenterDom, hn2⟩, hLL⟩
  set rPlus : ℝ := unrestrictedPhaseRootSelected n
  set rCoPlus : ℝ := cocoloringUnrestrictedPhaseRootSelected n
  set center : ℝ := phaseRootCenter n
  set width : ℝ := logLogOrder n * phaseRootGapRadius n
  set lower : ℝ := center - C * width
  set upper : ℝ := center + C * width
  set F : ℝ → ℝ := cocoloringUnrestrictedPhaseObjective n
  set a : ℝ := (phaseNat n : ℝ)
  have haPos : 0 < a := Nat.cast_pos.mpr (lt_trans (by omega : 0 < 5) hfive)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hBasePos : 0 < baseScale n := by
    rw [baseScale]
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hnpos : 0 < (n : ℝ) := by positivity
    positivity
  have hDomCenter : 0 < center :=
    div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hCenterDom.1.1)) hCenterDom.2.1
  have hWidthPos : 0 < width := mul_pos hLL (div_pos hDomCenter haSqPos)
  have hUnrestMem : rPlus ∈ Icc lower upper := by
    have h1 := hUnrest.1.1
    have hpad : 0 ≤ cocoloringUnrestrictedRootCorridorCoefficient * width :=
      mul_nonneg cocoloringUnrestrictedRootCorridorCoefficient_pos.le hWidthPos.le
    rw [mem_Ioo] at h1; rw [mem_Icc]
    exact ⟨by dsimp [rPlus, lower, center, width, C] at h1 ⊢; linarith,
           by dsimp [rPlus, upper, center, width, C] at h1 ⊢; linarith⟩
  have hCoMem : rCoPlus ∈ Icc lower upper := by
    have h1 := hCo.1.1
    have hpad : 0 ≤ unrestrictedPhaseRootCorridorCoefficient * width :=
      mul_nonneg unrestrictedPhaseRootCorridorCoefficient_pos.le hWidthPos.le
    rw [mem_Ioo] at h1; rw [mem_Icc]
    exact ⟨by dsimp [rCoPlus, lower, center, width, C] at h1 ⊢; linarith,
           by dsimp [rCoPlus, upper, center, width, C] at h1 ⊢; linarith⟩
  have hDom' : ∀ x ∈ Icc lower upper, 0 < x ∧ fourSizeTarget n (phaseNat n) x ∈ Ioo (2 : ℝ) 5 :=
    fun x hx ↦ hDom x (by simpa [lower, upper, center, width, mul_assoc] using hx)
  have hHasDeriv : ∀ x ∈ Icc lower upper,
      HasDerivAt F
        (q + (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x)) x :=
    fun x hx ↦ hasDerivAt_cocoloringUnrestrictedPhaseObjective hfive (hDom' x hx).1 (hDom' x hx).2
  have hHasDerivU : ∀ x ∈ Icc lower upper,
      HasDerivAt (unrestrictedPhaseObjective n)
        (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x) x := by
    intro x hx
    have htar := (hDom' x hx).2
    rw [fourSizeTarget, mem_Ioo] at htar
    have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hfive)
    exact hasDerivAt_profileDualOptimalValue_parts (by omega) (hDom' x hx).1 (by
      rw [mem_Ioo, show (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 by push_cast; ring]
      exact ⟨by linarith [htar.2], by linarith [htar.1]⟩)
  have hQA2 : q ≤ (eps / 2) * a ^ 2 := by
    have hdiv : 2 * q / eps ≤ a := by linarith [haBig]
    have h1 : 2 * q ≤ a * eps := (div_le_iff₀ hepsPos).mp hdiv
    have ha1 : 1 ≤ a := by
      have : (6 : ℝ) ≤ a := by
        change (6 : ℝ) ≤ (phaseNat n : ℝ); exact_mod_cast (Nat.succ_le_of_lt hfive)
      linarith
    have h2 : (2 * q) * 1 ≤ (a * eps) * a :=
      mul_le_mul h1 ha1 zero_le_one (mul_nonneg haPos.le hepsPos.le)
    linarith [show (a * eps) * a = 2 * ((eps / 2) * a ^ 2) by ring]
  have hFDerivBounds : ∀ x ∈ Icc lower upper,
      (q / 2 - eps) * a ^ 2 ≤ deriv F x ∧ deriv F x ≤ (q / 2 + eps) * a ^ 2 := by
    intro x hx
    have hdF := (hHasDeriv x hx).deriv
    have hdU := (hHasDerivU x hx).deriv
    have hsh := hDeriv x (by simpa [lower, upper, center, width, mul_assoc] using hx)
    rw [hdU] at hsh
    rw [hdF]
    exact ⟨by linarith [hsh.1, q_pos], by linarith [hsh.2, hQA2]⟩
  have hContF : ContinuousOn F (Icc lower upper) :=
    fun x hx ↦ (hHasDeriv x hx).continuousAt.continuousWithinAt
  have hStrict : StrictMonoOn F (Icc lower upper) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc lower upper) hContF
    intro x hx
    rw [interior_Icc] at hx
    have hlo := (hFDerivBounds x ⟨hx.1.le, hx.2.le⟩).1
    have hposSlope : 0 < (q / 2 - eps) * a ^ 2 := mul_pos (by linarith [hepsLeQ4, q_pos]) haSqPos
    linarith
  have hFCo : F rCoPlus = 0 := hCo.1.2
  have hRPlusPos : 0 < rPlus := (hDom' rPlus hUnrestMem).1
  have hFPlus : F rPlus = q * rPlus := by
    dsimp [F, cocoloringUnrestrictedPhaseObjective]
    rw [hUnrest.1.2, add_zero]
  have hOrder : rCoPlus ≤ rPlus := by
    by_contra hNot
    have hMono := hStrict hUnrestMem hCoMem (lt_of_not_ge hNot)
    rw [hFCo, hFPlus] at hMono
    linarith [mul_pos q_pos hRPlusPos]
  have hSubIcc : Icc rCoPlus rPlus ⊆ Icc lower upper :=
    fun x hx ↦ ⟨hCoMem.1.trans hx.1, hx.2.trans hUnrestMem.2⟩
  have hContSub : ContinuousOn F (Icc rCoPlus rPlus) := hContF.mono hSubIcc
  have hDiffSub : DifferentiableOn ℝ F (Ioo rCoPlus rPlus) :=
    fun x hx ↦ (hHasDeriv x (hSubIcc (Ioo_subset_Icc_self hx))).differentiableAt.differentiableWithinAt
  have hDenHiPos : 0 < q / 2 + eps := by linarith [q_pos]
  have hDenLoPos : 0 < q / 2 - eps := by linarith [hepsLeQ4, q_pos]
  have hGapLo := signed_root_separation_of_advantage_and_slope
    hOrder hContSub hDiffSub (mul_pos hDenHiPos haSqPos)
    (fun x hx ↦ (hFDerivBounds x (hSubIcc (Ioo_subset_Icc_self hx))).2)
    hFCo (by rw [hFPlus, mul_comm])
  have hGapHi : rPlus - rCoPlus ≤ (q * rPlus) / ((q / 2 - eps) * a ^ 2) := by
    have hinc := derivative_lower_bound_mul_sub_le_sub hOrder hContSub hDiffSub
      (fun x hx ↦ (hFDerivBounds x (hSubIcc (Ioo_subset_Icc_self hx))).1)
    rw [hFPlus, hFCo, sub_zero] at hinc
    exact (le_div_iff₀ (mul_pos hDenLoPos haSqPos)).mpr (by linarith)
  have hSlo : q ^ 3 / 8 * baseScale n ≤ rPlus / a ^ 2 :=
    hScaleLo rPlus (by simpa [lower, upper, center, width, mul_assoc] using hUnrestMem)
  have hShi : rPlus / a ^ 2 ≤ (q ^ 3 / 8 + eps) * baseScale n :=
    hScaleHi rPlus (by simpa [lower, upper, center, width, mul_assoc] using hUnrestMem)
  have hDivLo : (q / (q / 2 + eps)) * (q ^ 3 / 8) ≤ (rPlus - rCoPlus) / baseScale n := by
    rw [le_div_iff₀ hBasePos]
    calc (q / (q / 2 + eps)) * (q ^ 3 / 8) * baseScale n
        = (q / (q / 2 + eps)) * (q ^ 3 / 8 * baseScale n) := by ring
      _ ≤ (q / (q / 2 + eps)) * (rPlus / a ^ 2) :=
          mul_le_mul_of_nonneg_left hSlo (div_nonneg q_pos.le hDenHiPos.le)
      _ = (rPlus * q) / ((q / 2 + eps) * a ^ 2) := by field_simp
      _ ≤ rPlus - rCoPlus := hGapLo
  have hDivHi : (rPlus - rCoPlus) / baseScale n ≤ (q / (q / 2 - eps)) * (q ^ 3 / 8 + eps) := by
    rw [div_le_iff₀ hBasePos]
    calc rPlus - rCoPlus ≤ (q * rPlus) / ((q / 2 - eps) * a ^ 2) := hGapHi
      _ = (q / (q / 2 - eps)) * (rPlus / a ^ 2) := by field_simp
      _ ≤ (q / (q / 2 - eps)) * ((q ^ 3 / 8 + eps) * baseScale n) :=
          mul_le_mul_of_nonneg_left hShi (div_nonneg q_pos.le hDenLoPos.le)
      _ = (q / (q / 2 - eps)) * (q ^ 3 / 8 + eps) * baseScale n := by ring
  have hqeq : (Real.log 2) ^ 3 / 4 = q ^ 3 / 4 := rfl
  obtain ⟨hLoClose, hHiClose⟩ := cocoloring_gap_close_bounds htheta
  rw [Real.dist_eq, hqeq, abs_lt]
  exact ⟨by linarith, by linarith⟩

/-! ## 3. Concrete threshold `k_ζ^-(n)` and unconditional Section 4 lower tail -/

/-- The manuscript's concrete unrestricted cocolouring lower threshold
`k_ζ^-(n) = ⌊r_+^co(n)⌋ - ⌈log n⌉`. -/
def phaseCochromaticLowerIndex (n : ℕ) : ℕ :=
  (rootChromaticIndex (cocoloringUnrestrictedPhaseRootSelected n)
    (Real.log (n : ℝ))).toNat

theorem eventually_phaseCochromaticLowerIndex_geometry :
    ∀ᶠ n : ℕ in atTop,
      0 < phaseCochromaticLowerIndex n ∧
      phaseCochromaticLowerIndex n ≤ n ∧
      (phaseCochromaticLowerIndex n : ℝ) ∈
        Icc
          (phaseRootCenter n -
            (cocoloringUnrestrictedRootCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            (cocoloringUnrestrictedRootCorridorCoefficient + 1) *
              logLogOrder n * phaseRootGapRadius n) ∧
      logOrder n ≤ cocoloringUnrestrictedPhaseRootSelected n -
        (phaseCochromaticLowerIndex n : ℝ) ∧
      0 < logLogOrder n * phaseRootGapRadius n := by
  let C0 : ℝ := cocoloringUnrestrictedRootCorridorCoefficient
  have hC0Pos : 0 < C0 := cocoloringUnrestrictedRootCorridorCoefficient_pos
  have hBudgetLt : ∀ᶠ n : ℕ in atTop, rootRoundingBudget n < q ^ 3 / 8 :=
    root_rounding_budget_spec.1.eventually
      (Iio_mem_nhds (div_pos (pow_pos q_pos 3) (by norm_num)))
  have hBudgetOne : ∀ᶠ n : ℕ in atTop, rootRoundingBudget n ≤ 1 :=
    (root_rounding_budget_spec.1.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ hn ↦ hn.le
  have hLogLogLarge : ∀ᶠ n : ℕ in atTop, 8 / q ^ 3 ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (8 / q ^ 3)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hBasePos : ∀ᶠ n : ℕ in atTop, 0 < baseScale n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn2
    rw [baseScale]
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hnpos : 0 < (n : ℝ) := by positivity
    positivity
  filter_upwards
    [eventually_cocoloringUnrestrictedPhaseRootSelected_spec_unique,
      eventually_phaseRootLogLogCorridor_fourSize_domain C0 hC0Pos.le,
      eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower C0 hC0Pos.le,
      eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower 0 (by norm_num),
      eventually_five_lt_phaseNat,
      root_rounding_budget_spec.2, hBudgetLt, hBudgetOne,
      hLogLogLarge, hLogPos, hBasePos] with
      n hCo hRootDomain hScaleCo hScaleCenter hfive hRounding hBudgetLtN
        hBudgetOneN hLogLogLargeN hLogPosN hBasePosN
  let rCoPlus : ℝ := cocoloringUnrestrictedPhaseRootSelected n
  let L : ℝ := logOrder n
  let width : ℝ := logLogOrder n * phaseRootGapRadius n
  let z : ℤ := rootChromaticIndex rCoPlus L
  have hRootMem : rCoPlus ∈ Ioo
      (phaseRootCenter n - C0 * width) (phaseRootCenter n + C0 * width) := by
    simpa [rCoPlus, C0, width, mul_assoc] using hCo.1.1
  have hRootClosed : rCoPlus ∈ Icc
      (phaseRootCenter n - C0 * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C0 * logLogOrder n * phaseRootGapRadius n) := by
    simpa [width, mul_assoc] using (show rCoPlus ∈ Icc (phaseRootCenter n - C0 * width)
      (phaseRootCenter n + C0 * width) from ⟨hRootMem.1.le, hRootMem.2.le⟩)
  have hDomR := hRootDomain rCoPlus hRootClosed
  have haSix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hfive)
  have haSqGe1 : 1 ≤ (phaseNat n : ℝ) ^ 2 := by
    calc (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ zero_le_one (by linarith) 2
  have hScaleR : q ^ 3 / 8 * baseScale n ≤ rCoPlus / (phaseNat n : ℝ) ^ 2 :=
    hScaleCo rCoPlus hRootClosed
  have hRCoLargeBase : q ^ 3 / 8 * baseScale n ≤ rCoPlus := by
    have h1 := mul_le_mul_of_nonneg_right hScaleR (sq_nonneg (phaseNat n : ℝ))
    have h2 : rCoPlus / (phaseNat n : ℝ) ^ 2 * (phaseNat n : ℝ) ^ 2 = rCoPlus :=
      div_mul_cancel₀ _ (by positivity)
    rw [h2] at h1
    have hbp : 0 ≤ q ^ 3 / 8 * baseScale n :=
      mul_nonneg (div_nonneg (pow_nonneg q_pos.le 3) (by norm_num)) hBasePosN.le
    calc q ^ 3 / 8 * baseScale n
        = (q ^ 3 / 8 * baseScale n) * 1 := (mul_one _).symm
      _ ≤ (q ^ 3 / 8 * baseScale n) * (phaseNat n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left haSqGe1 hbp
      _ ≤ rCoPlus := h1
  have hRounding' : L + 3 ≤ rootRoundingBudget n * baseScale n := by
    simpa [L, logOrder, baseScale] using hRounding
  have hBudMul : rootRoundingBudget n * baseScale n < q ^ 3 / 8 * baseScale n :=
    mul_lt_mul_of_pos_right hBudgetLtN hBasePosN
  have hRLarge : L + 3 < rCoPlus := by linarith
  have hZrealPos : (0 : ℝ) < (z : ℝ) := by
    dsimp [z, rootChromaticIndex]; push_cast
    linarith [Int.lt_floor_add_one rCoPlus, Int.ceil_lt_add_one L]
  have hZpos : 0 < z := by exact_mod_cast hZrealPos
  have hIndexCast : (phaseCochromaticLowerIndex n : ℝ) = (z : ℝ) := by
    rw [phaseCochromaticLowerIndex]; norm_cast
    simpa [z, rCoPlus, L, logOrder] using Int.toNat_of_nonneg hZpos.le
  have hIndexPos : 0 < phaseCochromaticLowerIndex n := by
    exact_mod_cast (by rw [hIndexCast]; exact hZrealPos : (0 : ℝ) < phaseCochromaticLowerIndex n)
  have hRLtN : rCoPlus < (n : ℝ) := by
    have hTarget := hDomR.2
    rw [fourSizeTarget, mem_Ioo] at hTarget
    have hOneLt : (1 : ℝ) < (n : ℝ) / rCoPlus := by linarith
    simpa using (lt_div_iff₀ hDomR.1).mp hOneLt
  have hIndexLe : phaseCochromaticLowerIndex n ≤ n := by
    have hlt : (phaseCochromaticLowerIndex n : ℝ) < (n : ℝ) := by
      rw [hIndexCast]
      calc (z : ℝ) ≤ (⌊rCoPlus⌋ : ℤ) := by
            dsimp [z, rootChromaticIndex]; push_cast
            exact_mod_cast (sub_le_self (⌊rCoPlus⌋ : ℤ) (Int.ceil_nonneg hLogPosN.le))
        _ ≤ rCoPlus := Int.floor_le rCoPlus
        _ < (n : ℝ) := hRLtN
    exact_mod_cast hlt.le
  have hScaleAtCenter : q ^ 3 / 8 * baseScale n ≤ phaseRootGapRadius n := by
    simpa [phaseRootGapRadius] using hScaleCenter (phaseRootCenter n) (by simp)
  have hQCubePos : 0 < q ^ 3 := pow_pos q_pos 3
  have hCoeffLL : 1 ≤ q ^ 3 / 8 * logLogOrder n := by
    have h8 : 8 ≤ logLogOrder n * q ^ 3 := (div_le_iff₀ hQCubePos).mp hLogLogLargeN
    linarith
  have hLLPos : 0 < logLogOrder n := by
    have : 0 < 8 / q ^ 3 := div_pos (by norm_num) hQCubePos; linarith
  have hWidthPays : L + 3 ≤ width := by
    calc L + 3 ≤ rootRoundingBudget n * baseScale n := hRounding'
      _ ≤ (q ^ 3 / 8 * logLogOrder n) * baseScale n :=
          mul_le_mul_of_nonneg_right (hBudgetOneN.trans hCoeffLL) hBasePosN.le
      _ = logLogOrder n * (q ^ 3 / 8 * baseScale n) := by ring
      _ ≤ logLogOrder n * phaseRootGapRadius n :=
          mul_le_mul_of_nonneg_left hScaleAtCenter hLLPos.le
  have hZLower : rCoPlus - L - 2 < (z : ℝ) := by
    dsimp [z, rootChromaticIndex]; push_cast
    linarith [Int.lt_floor_add_one rCoPlus, Int.ceil_lt_add_one L]
  have hZUpper : (z : ℝ) ≤ rCoPlus := by
    dsimp [z, rootChromaticIndex]; push_cast
    have hceil : (0 : ℝ) ≤ (⌈L⌉ : ℤ) := by exact_mod_cast Int.ceil_nonneg hLogPosN.le
    linarith [Int.floor_le rCoPlus]
  have hIndexCorridor : (phaseCochromaticLowerIndex n : ℝ) ∈
      Icc (phaseRootCenter n - (C0 + 1) * width) (phaseRootCenter n + (C0 + 1) * width) := by
    rw [hIndexCast, mem_Icc]
    exact ⟨by linarith [hRootMem.1, hZLower, hWidthPays],
           by linarith [hRootMem.2, hZUpper, hWidthPays, hLogPosN]⟩
  have hDisp : L ≤ rCoPlus - (phaseCochromaticLowerIndex n : ℝ) := by
    rw [hIndexCast]; dsimp [z, rootChromaticIndex]; push_cast
    linarith [Int.floor_le rCoPlus, Int.le_ceil L]
  exact ⟨hIndexPos, hIndexLe,
    by simpa [C0, width, mul_assoc] using hIndexCorridor,
    by simpa [L, rCoPlus] using hDisp,
    hLogPosN.trans_le (by linarith [hWidthPays])⟩

private theorem eventually_cocoloringEnvelope_le_neg_cubic :
    ∀ᶠ n : ℕ in atTop,
      q * (phaseCochromaticLowerIndex n : ℝ) +
        profilePhaseObjective n (phaseCochromaticLowerIndex n : ℝ) +
        factorialLogErrorBound n ≤ -(q / 32) * (logOrder n) ^ 3 := by
  let C : ℝ := cocoloringUnrestrictedRootCorridorCoefficient + 1
  have hC : 0 ≤ C := by
    dsimp [C]; linarith [cocoloringUnrestrictedRootCorridorCoefficient_pos]
  have hDomain := eventually_phaseRootLogLogCorridor_fourSize_domain C hC
  have hDeriv := eventually_unrestrictedPhaseObjective_deriv_logLogCorridor_lower C hC
  have hLogLarge : ∀ᶠ n : ℕ in atTop, 160 / q ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop (160 / q)
  have hLogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop 1
  have hFacSmall : ∀ᶠ n : ℕ in atTop,
      factorialLogErrorBound n / (logOrder n) ^ 3 < q / 32 :=
    factorialLogErrorBound_div_logOrder_cubed_tendsto_zero.eventually
      (Iio_mem_nhds (div_pos q_pos (by norm_num)))
  filter_upwards
    [eventually_phaseCochromaticLowerIndex_geometry,
      eventually_cocoloringUnrestrictedPhaseRootSelected_spec_unique,
      eventually_five_lt_phaseNat,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_ge_atTop (2 : ℕ),
      hDomain, hDeriv, hLogLarge, hLogOne, hFacSmall] with
      n hGeom hRoot hfive hPhase hn2 hDomainN hDerivN hLarge hOne hFacN
  let r : ℝ := cocoloringUnrestrictedPhaseRootSelected n
  let L : ℝ := logOrder n
  let a : ℝ := phaseCochromaticLowerIndex n
  have hLogPos : 0 < L := lt_of_lt_of_le zero_lt_one hOne
  have hRootMem : r ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    have hWidthPos := hGeom.2.2.2.2
    have hr1 := hRoot.1.1.1
    have hr2 := hRoot.1.1.2
    dsimp [C, r]
    exact ⟨by linarith, by linarith⟩
  have hAMem : a ∈ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) := by
    simpa [a, C] using hGeom.2.2.1
  have hDisp : L ≤ r - a := by simpa [L, r, a] using hGeom.2.2.2.1
  have hAR : a ≤ r := by linarith
  have hInterval : Icc a r ⊆ Icc
      (phaseRootCenter n - C * logLogOrder n * phaseRootGapRadius n)
      (phaseRootCenter n + C * logLogOrder n * phaseRootGapRadius n) :=
    fun x hx ↦ ⟨hAMem.1.trans hx.1, hx.2.trans hRootMem.2⟩
  have hKey : ∀ x ∈ Icc a r,
      HasDerivAt (cocoloringUnrestrictedPhaseObjective n)
        (q + (Real.log (profileDualPartition (phaseNat n + 1)
            (profileDualTilt (phaseNat n + 1) ((n : ℝ) / x))) - Real.log x)) x :=
    fun x hx ↦ hasDerivAt_cocoloringUnrestrictedPhaseObjective hfive
      (hDomainN x (hInterval hx)).1 (hDomainN x (hInterval hx)).2
  have hCont : ContinuousOn (cocoloringUnrestrictedPhaseObjective n) (Icc a r) :=
    fun x hx ↦ (hKey x hx).continuousAt.continuousWithinAt
  have hDiff : DifferentiableOn ℝ (cocoloringUnrestrictedPhaseObjective n) (Ioo a r) :=
    fun x hx ↦ (hKey x (Ioo_subset_Icc_self hx)).differentiableAt.differentiableWithinAt
  have hLower : ∀ x ∈ Ioo a r,
      q / 8 * (phaseNat n : ℝ) ^ 2 ≤ deriv (cocoloringUnrestrictedPhaseObjective n) x := by
    intro x hx
    have hxC := hInterval (Ioo_subset_Icc_self hx)
    have hdF := (hKey x (Ioo_subset_Icc_self hx)).deriv
    have htar := (hDomainN x hxC).2
    rw [fourSizeTarget, mem_Ioo] at htar
    have hsix : (6 : ℝ) ≤ phaseNat n := by exact_mod_cast (Nat.succ_le_of_lt hfive)
    have hdU := (hasDerivAt_profileDualOptimalValue_parts (by omega : 2 ≤ phaseNat n + 1)
      (hDomainN x hxC).1 (by
        rw [mem_Ioo, show (((phaseNat n + 1 : ℕ)) : ℝ) = (phaseNat n : ℝ) + 1 by push_cast; ring]
        exact ⟨by linarith [htar.2], by linarith [htar.1]⟩)).deriv
    have hlow := hDerivN x hxC
    unfold unrestrictedPhaseObjective at hlow
    rw [hdU] at hlow; rw [hdF]; linarith [q_pos]
  have hInc := derivative_lower_bound_mul_sub_le_sub hAR hCont hDiff hLower
  have hRootZero : cocoloringUnrestrictedPhaseObjective n r = 0 := hRoot.1.2
  have hSlopeNonneg : 0 ≤ q / 8 * (phaseNat n : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg q_pos.le (by norm_num)) (sq_nonneg _)
  have hRawAtA : cocoloringUnrestrictedPhaseObjective n a ≤
      -(q / 8 * (phaseNat n : ℝ) ^ 2) * L := by
    have hm := mul_le_mul_of_nonneg_left hDisp hSlopeNonneg
    linarith
  have hPhaseSq : L ^ 2 ≤ (phaseNat n : ℝ) ^ 2 := pow_le_pow_left₀ hLogPos.le hPhase.1 2
  have hRawCubic : cocoloringUnrestrictedPhaseObjective n a ≤ -(q / 8) * L ^ 3 := by
    have hScaled : q / 8 * (L ^ 2 * L) ≤ q / 8 * ((phaseNat n : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hPhaseSq hLogPos.le)
        (div_nonneg q_pos.le (by norm_num))
    linarith
  -- Box term `((phaseNat n + 1) : ℝ) * log(n + 1) ≤ (q / 16) * L^3`
  have hSuccLe : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hLogSucc : Real.log ((n : ℝ) + 1) ≤ 2 * L := by
    have hlog := Real.log_le_log (by positivity) hSuccLe
    rw [Real.log_mul two_ne_zero (by positivity : (n : ℝ) ≠ 0)] at hlog
    have hqLe : q ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    dsimp [q, L, logOrder] at hqLe ⊢
    linarith
  have hPhaseFive : (((phaseNat n + 1 : ℕ) : ℝ)) ≤ 5 * L := by push_cast; linarith [hPhase.2]
  have hBox10 : (((phaseNat n + 1 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 1) ≤ 10 * L ^ 2 := by
    have hm := mul_le_mul hPhaseFive hLogSucc
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))) (by positivity)
    linarith
  have hqL : 160 ≤ L * q := (div_le_iff₀ q_pos).mp hLarge
  have hBox : (((phaseNat n + 1 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 1) ≤ q / 16 * L ^ 3 := by
    have hm := mul_le_mul_of_nonneg_left hqL (div_nonneg (sq_nonneg L) (by norm_num : (0 : ℝ) ≤ 16))
    linarith [show L ^ 2 / 16 * 160 = 10 * L ^ 2 by ring,
              show L ^ 2 / 16 * (L * q) = q / 16 * L ^ 3 by ring]
  have hFac : factorialLogErrorBound n ≤ q / 32 * L ^ 3 := by
    have hL3pos : 0 < L ^ 3 := pow_pos hLogPos 3
    exact ((div_lt_iff₀ hL3pos).mp hFacN).le
  have hObjEq : q * a + profilePhaseObjective n a =
      (((phaseNat n + 1 : ℕ) : ℝ)) * Real.log ((n : ℝ) + 1) +
        cocoloringUnrestrictedPhaseObjective n a := by
    unfold profilePhaseObjective cocoloringUnrestrictedPhaseObjective unrestrictedPhaseObjective
    ring
  dsimp [a, L] at hObjEq hRawCubic hBox hFac
  linarith

/-- **Unconditional Section 4 Cochromatic Lower Tail (`P(ζ(G_n) ≤ k_ζ^-(n)) → 0`).** -/
theorem randomGraphMeasure_cochromaticNumberAtMost_phaseCochromaticLowerIndex_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        {G : LabeledGraph n | cochromaticNumber G ≤ phaseCochromaticLowerIndex n})
      atTop (nhds 0) := by
  have hExp : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-(q / 32) * (logOrder n) ^ 3)))
      atTop (nhds 0) := by
    have hL3 : Tendsto (fun n : ℕ ↦ (logOrder n) ^ 3) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_logOrder_atTop
    have hBot : Tendsto (fun n : ℕ ↦ -(q / 32) * (logOrder n) ^ 3) atTop atBot :=
      hL3.const_mul_atTop_of_neg (neg_neg_of_pos (div_pos q_pos (by norm_num)))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp hBot)
  have hMu : Tendsto
      (fun n : ℕ ↦ (2 : ℝ≥0∞) * ENNReal.ofReal (mu n (phaseNat n + 2)))
      atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (mu n (phaseNat n + 2))) atTop (nhds 0) := by
      simpa using ENNReal.tendsto_ofReal mu_phaseNat_add_two_tendsto_zero
    simpa using ENNReal.Tendsto.const_mul h0 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hUpperTendsto : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-(q / 32) * (logOrder n) ^ 3)) +
        (2 : ℝ≥0∞) * ENNReal.ofReal (mu n (phaseNat n + 2)))
      atTop (nhds 0) := by
    simpa using hExp.add hMu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hUpperTendsto
    (Filter.Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards
    [eventually_phaseCochromaticLowerIndex_geometry,
      eventually_cocoloringEnvelope_le_neg_cubic] with n hGeom hEnv
  set k : ℕ := phaseCochromaticLowerIndex n
  set b : ℕ := phaseNat n + 1
  have hkPos : 0 < k := hGeom.1
  have hkLe : k ≤ n := hGeom.2.1
  have hbPos : 0 < b := Nat.succ_pos _
  let t : ℝ := profileDualTilt b ((n : ℝ) / (k : ℝ))
  have h1 := randomGraphMeasure_cochromaticNumberAtMost_le_two_pow_mul_expectation_add_two_mu
    (b := b) hkLe
  have h2 := boundedProfileColoringExpectation_le_profileDualUpper
    (n := n) (b := b) (parts := k) hbPos hkPos t
  have hkNe : (k : ℝ) ≠ 0 := by exact_mod_cast hkPos.ne'
  have hTwoPow : (2 : ℝ≥0∞) ^ k = ENNReal.ofReal (Real.exp (q * (k : ℝ))) := by
    have hexp : Real.exp (q * (k : ℝ)) = (2 : ℝ) ^ k := by
      rw [mul_comm, Real.exp_nat_mul, q, Real.exp_log two_pos]
    rw [hexp, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  have hBoxExp : ENNReal.ofReal (((n : ℝ) + 1) ^ b) =
      ENNReal.ofReal (Real.exp ((b : ℝ) * Real.log ((n : ℝ) + 1))) := by
    congr 1
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hProdEq :
      (2 : ℝ≥0∞) ^ k *
        (ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
          ENNReal.ofReal (Real.exp (profileDualUpper b (n : ℝ) (k : ℝ) t +
            factorialLogErrorBound n))) =
      ENNReal.ofReal (Real.exp (q * (k : ℝ) + profilePhaseObjective n (k : ℝ) +
        factorialLogErrorBound n)) := by
    rw [hTwoPow, hBoxExp, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← Real.exp_add]
    congr 2
    have hcore := profilePhaseObjective_eq_selected_core n hkNe
    dsimp [b, t] at hcore ⊢
    linarith
  have hExpMono :
      ENNReal.ofReal (Real.exp (q * (k : ℝ) + profilePhaseObjective n (k : ℝ) +
        factorialLogErrorBound n)) ≤
      ENNReal.ofReal (Real.exp (-(q / 32) * (logOrder n) ^ 3)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hEnv)
  calc randomGraphMeasure n {G : LabeledGraph n | cochromaticNumber G ≤ k}
      ≤ (2 : ℝ≥0∞) ^ k * boundedProfileColoringExpectation n b k +
          2 * ENNReal.ofReal (mu n (b + 1)) := h1
    _ ≤ (2 : ℝ≥0∞) ^ k *
          (ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
            ENNReal.ofReal (Real.exp (profileDualUpper b (n : ℝ) (k : ℝ) t +
              factorialLogErrorBound n))) +
          2 * ENNReal.ofReal (mu n (b + 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left h2 zero_le) le_rfl
    _ = ENNReal.ofReal (Real.exp (q * (k : ℝ) + profilePhaseObjective n (k : ℝ) +
          factorialLogErrorBound n)) +
          (2 : ℝ≥0∞) * ENNReal.ofReal (mu n (phaseNat n + 2)) := by
        rw [hProdEq]
    _ ≤ ENNReal.ofReal (Real.exp (-(q / 32) * (logOrder n) ^ 3)) +
          (2 : ℝ≥0∞) * ENNReal.ofReal (mu n (phaseNat n + 2)) :=
        add_le_add hExpMono le_rfl

/-- **Unconditional Section 4 Cochromatic Lower Bound (`P(k_ζ^-(n) < ζ(G_n)) → 1`).** -/
theorem randomGraphMeasure_phaseCochromaticLowerIndex_lt_cochromaticNumber_tendsto_one :
    Tendsto
      (fun n : ℕ ↦ randomGraphMeasure n
        {G : LabeledGraph n | phaseCochromaticLowerIndex n < cochromaticNumber G})
      atTop (nhds 1) := by
  have hAtMost :=
    randomGraphMeasure_cochromaticNumberAtMost_phaseCochromaticLowerIndex_tendsto_zero
  have hAtMostReal : Tendsto
      (fun n : ℕ ↦ (randomGraphMeasure n
        {G : LabeledGraph n | cochromaticNumber G ≤ phaseCochromaticLowerIndex n}).toReal)
      atTop (nhds 0) := by
    simpa using (ENNReal.tendsto_toReal_iff
      (fun n ↦ measure_ne_top _ _) ENNReal.zero_ne_top).mpr hAtMost
  apply tendsto_measure_one_of_compl_real_tendsto_zero randomGraphMeasure _
    (fun n ↦ (Set.toFinite _).measurableSet)
  refine hAtMostReal.congr (fun n ↦ ?_)
  have hcompl :
      ({G : LabeledGraph n | phaseCochromaticLowerIndex n < cochromaticNumber G})ᶜ =
        {G : LabeledGraph n | cochromaticNumber G ≤ phaseCochromaticLowerIndex n} := by
    ext G; simp [not_lt]
  rw [Measure.real, hcompl]

end

end Erdos625HP
