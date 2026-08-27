import Erdos625.PhaseRootSelectors
import Erdos625.Section11AsymptoticAssembly
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

theorem eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower
    (C : ℝ) (_hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        q ^ 3 / 8 * baseScale n ≤
          s / (phaseNat n : ℝ) ^ 2 := by
  have hconstant : ∀ᶠ n : ℕ in atTop,
      2 * phaseC + q ≤ logLogOrder n :=
    tendsto_logLogOrder_atTop.eventually_ge_atTop (2 * phaseC + q)
  have hLogPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  have hLogLogNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ logLogOrder n :=
    (tendsto_logLogOrder_atTop.eventually_gt_atTop 0).mono
      fun _ hn => hn.le
  have hCorridorCoefficient : ∀ᶠ n : ℕ in atTop,
      2 * C ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually_ge_atTop (2 * C)
  filter_upwards
    [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      hconstant, hLogPos, hLogLogNonneg, hCorridorCoefficient] with
      n hcenter hphase hconstantN hLogPosN hLogLogNonnegN hCoeffN
  obtain ⟨hdom, hs0Pos, _⟩ := hcenter
  intro s hs
  set a : ℝ := (phaseNat n : ℝ) with ha
  set N : ℝ := logOrder n with hN
  set w : ℝ := logLogOrder n with hw
  set s0 : ℝ := phaseRootS0 n with hs0
  set c : ℝ := phaseRootCenter n with hc
  set x : ℝ := C * w / a ^ 2 with hx
  set y : ℝ := w / (2 * N) with hy
  set z : ℝ := q * a / (2 * N) with hz
  have haPos : 0 < a := by
    rw [ha]
    exact_mod_cast (show 0 < phaseNat n by
      have : (0 : ℝ) < phaseNat n := hLogPosN.trans_le hphase.1
      exact_mod_cast this)
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos haPos
  have hNPos : 0 < N := by simpa [hN] using hLogPosN
  have hwNonneg : 0 ≤ w := by simpa [hw] using hLogLogNonnegN
  have hNLeA : N ≤ a := by simpa [hN, ha] using hphase.1
  have hTwoCLeN : 2 * C ≤ N := by simpa [hN] using hCoeffN
  have hs0Eq : s0 = a + phaseDelta n - 1 - 2 / q := by
    rw [hs0, phaseRootS0, alphaZero_eq_phaseNat_add_delta hdom, ha]
  have hs0LeA : s0 ≤ a := by
    have hTwoDivPos : 0 < 2 / q := div_pos (by norm_num) q_pos
    linarith [phaseDelta_lt_one n]
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hdom.1)
  have hcEq : c = (n : ℝ) / s0 := by rw [hc, hs0]; rfl
  have hcPos : 0 < c := by rw [hcEq]; exact div_pos hnPos hs0Pos
  have hphaseExact :
      a * q = 2 * N - 2 * w + 2 * phaseC + q * phaseB n := by
    rw [ha, hN, hw, phaseNat_cast_eq_two_phaseS_div_q_add_phaseB hdom]
    unfold phaseS
    field_simp [q_ne_zero]
  have hPhaseBTerm : q * phaseB n ≤ q :=
    by simpa using mul_le_mul_of_nonneg_left (phaseB_le_one n) q_pos.le
  have hqaUpper : q * a ≤ 2 * N - w := by
    rw [mul_comm]
    have hconstantN' : 2 * phaseC + q ≤ w := by
      simpa [hw] using hconstantN
    linarith
  have hTwoNsubWPos : 0 < 2 * N - w :=
    (mul_pos q_pos haPos).trans_le hqaUpper
  have hyNonneg : 0 ≤ y := by rw [hy]; positivity
  have hyLtOne : y < 1 := by
    rw [hy, div_lt_one (mul_pos (by norm_num) hNPos)]
    linarith
  have hzNonneg : 0 ≤ z := by
    rw [hz]
    exact div_nonneg (mul_nonneg q_pos.le haPos.le)
      (mul_pos (by norm_num) hNPos).le
  have hzLe : z ≤ 1 - y := by
    calc
      z = q * a / (2 * N) := hz
      _ ≤ (2 * N - w) / (2 * N) :=
        div_le_div_of_nonneg_right hqaUpper
          (mul_pos (by norm_num) hNPos).le
      _ = 1 - y := by
        rw [hy]
        field_simp [hNPos.ne']
  have haSqLower : 2 * C * N ≤ a ^ 2 := by
    have hNSq : 2 * C * N ≤ N ^ 2 := by
      nlinarith
    have hASq : N ^ 2 ≤ a ^ 2 :=
      pow_le_pow_left₀ hNPos.le hNLeA 2
    exact hNSq.trans hASq
  have hxLeY : x ≤ y := by
    rw [hx, hy, div_le_div_iff₀ haSqPos
      (mul_pos (by norm_num) hNPos)]
    nlinarith
  have hxLtOne : x < 1 := hxLeY.trans_lt hyLtOne
  have hOneSubYNonneg : 0 ≤ 1 - y := by linarith
  have hOneSubYLeOne : 1 - y ≤ 1 := by linarith
  have hpow : z ^ 3 ≤ (1 - y) ^ 3 :=
    pow_le_pow_left₀ hzNonneg hzLe 3
  have hsq : (1 - y) ^ 2 ≤ 1 - y := by
    nlinarith [mul_le_mul_of_nonneg_left hOneSubYLeOne hOneSubYNonneg]
  have hcube : (1 - y) ^ 3 ≤ (1 - y) ^ 2 := by
    calc
      (1 - y) ^ 3 = (1 - y) * (1 - y) ^ 2 := by ring
      _ ≤ (1 - y) * (1 - y) :=
        mul_le_mul_of_nonneg_left hsq hOneSubYNonneg
      _ = (1 - y) ^ 2 := by ring
  have hzCubeLe : z ^ 3 ≤ 1 - x :=
    hpow.trans (hcube.trans (hsq.trans (by linarith)))
  have hgapEq : phaseRootGapRadius n = c / a ^ 2 := by
    rw [phaseRootGapRadius, hc, ha]
  have hsLower : c * (1 - x) ≤ s := by
    calc
      c * (1 - x) = phaseRootCenter n -
          C * logLogOrder n * phaseRootGapRadius n := by
            rw [hc, hx, hw, hgapEq]
            ring
      _ ≤ s := hs.1
  have hcLower : (n : ℝ) / a ≤ c := by
    rw [hcEq, div_le_div_iff₀ haPos hs0Pos]
    nlinarith
  have hOneSubXNonneg : 0 ≤ 1 - x := by linarith
  have hsLower' : ((n : ℝ) / a) * (1 - x) ≤ s :=
    (mul_le_mul_of_nonneg_right hcLower hOneSubXNonneg).trans hsLower
  calc
    q ^ 3 / 8 * baseScale n =
        (((n : ℝ) / a) * z ^ 3) / a ^ 2 := by
      rw [baseScale, hz, hN, logOrder]
      field_simp [q_ne_zero, haPos.ne', hNPos.ne']
      ring
    _ ≤ (((n : ℝ) / a) * (1 - x)) / a ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hzCubeLe
          (div_nonneg hnPos.le haPos.le)) haSqPos.le
    _ ≤ s / a ^ 2 := div_le_div_of_nonneg_right hsLower' haSqPos.le

#print axioms eventually_phaseRootLogLogCorridor_part_div_phaseNat_sq_lower

end

end Erdos625
