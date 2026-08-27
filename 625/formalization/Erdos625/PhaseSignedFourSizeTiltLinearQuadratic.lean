import Erdos625.PhaseSignedFourSizeCompactControl
import Erdos625.PhaseSignedFourSizeEntropyLower
import Erdos625.PhaseEstimates
import Mathlib.Tactic

/-!
# Uniform quadratic control of the signed four-size tilt-linear term

This module bounds the remaining tilt-linear term in the derivative
lower envelope.  Compact-target convergence supplies a uniform finite tilt
bound; the exact target identity then turns `n / s` into a quantity at most
the phase parameter.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- On the native phase-root gap corridor, the absolute tilt-linear term in
the exact signed four-size derivative is eventually at most one thirty-second
of the quadratic main scale. -/
theorem eventually_abs_phaseRootGapCorridor_fourSize_tilt_linear_le_quadratic :
    ∀ᶠ n : Nat in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n))
              (fourSizeTarget n (phaseNat n) s) *
            (n : Real) / s| ≤
          q / 32 * (phaseNat n : Real) ^ 2 := by
  let L : Real :=
    max
      |ProfileEntropyS4.tilt fourGaussianScore (9 / 4 : Real)|
      |ProfileEntropyS4.tilt fourGaussianScore (17 / 4 : Real)|
  let M : Real := 1 + L
  have hL_nonneg : 0 ≤ L := by
    exact (abs_nonneg _).trans (le_max_left _ _)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    linarith
  have hlimitingTilt {T : Real}
      (hT : T ∈ Icc (9 / 4 : Real) (17 / 4 : Real)) :
      |ProfileEntropyS4.tilt fourGaussianScore T| ≤ L := by
    have hleftInterior : (9 / 4 : Real) ∈ Ioo (2 : Real) 5 := by
      norm_num
    have hrightInterior : (17 / 4 : Real) ∈ Ioo (2 : Real) 5 := by
      norm_num
    have hTInterior : T ∈ Ioo (2 : Real) 5 := by
      constructor <;> linarith [hT.1, hT.2]
    have hleftMean :
        ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore (9 / 4 : Real)) ≤
          ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore T) := by
      rw [ProfileEntropyS4.mean_tilt_eq fourGaussianScore hleftInterior,
        ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTInterior]
      exact hT.1
    have hrightMean :
        ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore T) ≤
          ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore (17 / 4 : Real)) := by
      rw [ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTInterior,
        ProfileEntropyS4.mean_tilt_eq fourGaussianScore hrightInterior]
      exact hT.2
    have hleft :
        ProfileEntropyS4.tilt fourGaussianScore (9 / 4 : Real) ≤
          ProfileEntropyS4.tilt fourGaussianScore T :=
      (ProfileEntropyS4.strictMono_mean fourGaussianScore).le_iff_le.mp hleftMean
    have hright :
        ProfileEntropyS4.tilt fourGaussianScore T ≤
          ProfileEntropyS4.tilt fourGaussianScore (17 / 4 : Real) :=
      (ProfileEntropyS4.strictMono_mean fourGaussianScore).le_iff_le.mp hrightMean
    exact (abs_le_max_abs_abs hleft hright).trans_eq rfl
  obtain ⟨_c, _hc, hcompactControl⟩ :=
    exists_pos_eventually_phaseRootGapCorridor_fourSize_compact_control
  have hcontrol := hcompactControl 1 (by norm_num)
  have hphaseLarge :
      ∀ᶠ n : Nat in atTop, 32 * M / q ≤ (phaseNat n : Real) := by
    filter_upwards
      [tendsto_logOrder_atTop.eventually_ge_atTop (32 * M / q),
        eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with
        n hn hphase
    exact hn.trans hphase.1
  filter_upwards [hcontrol,
    eventually_phaseRootGapCorridor_fourSize_domain,
    eventually_phaseRootGapCorridor_fourSize_target_mem_Icc,
    hphaseLarge] with n hcontrolN hdomain htarget hlarge
  intro s hs
  let T : Real := fourSizeTarget n (phaseNat n) s
  have hT : T ∈ Icc (9 / 4 : Real) (17 / 4 : Real) := htarget s hs
  have hclose := (hcontrolN s hs).1
  have hfiniteTilt :
      |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| ≤ M := by
    calc
      |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| =
          |(ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T -
              ProfileEntropyS4.tilt fourGaussianScore T) +
            ProfileEntropyS4.tilt fourGaussianScore T| := by ring_nf
      _ ≤ |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T -
              ProfileEntropyS4.tilt fourGaussianScore T| +
            |ProfileEntropyS4.tilt fourGaussianScore T| := abs_add_le _ _
      _ ≤ 1 + L := add_le_add (le_of_lt hclose) (hlimitingTilt hT)
      _ = M := rfl
  have hs_pos : 0 < s := (hdomain s hs).1
  have hratio_nonneg : 0 ≤ (n : Real) / s :=
    div_nonneg (Nat.cast_nonneg n) hs_pos.le
  have hratio_eq :
      (n : Real) / s = (phaseNat n : Real) - T := by
    dsimp [T, fourSizeTarget]
    ring
  have hratio_le : (n : Real) / s ≤ (phaseNat n : Real) := by
    rw [hratio_eq]
    linarith [hT.1]
  have hphase_nonneg : 0 ≤ (phaseNat n : Real) := Nat.cast_nonneg _
  have hMphase :
      M * (phaseNat n : Real) ≤ q / 32 * (phaseNat n : Real) ^ 2 := by
    have hMq : 32 * M ≤ (phaseNat n : Real) * q := by
      rw [div_le_iff₀ q_pos] at hlarge
      exact hlarge
    nlinarith [mul_le_mul_of_nonneg_right hMq hphase_nonneg, q_pos]
  change
    |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T *
        (n : Real) / s| ≤ _
  have habs :
      |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T *
          (n : Real) / s| =
        |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| *
          ((n : Real) / s) := by
    rw [abs_div, abs_mul]
    have hnabs : |(n : Real)| = (n : Real) :=
      abs_of_nonneg (Nat.cast_nonneg n)
    have hsabs : |s| = s := abs_of_pos hs_pos
    rw [hnabs, hsabs]
    ring
  rw [habs]
  calc
    |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| *
          ((n : Real) / s) ≤
        M * ((n : Real) / s) := by
      exact mul_le_mul_of_nonneg_right hfiniteTilt hratio_nonneg
    _ ≤ M * (phaseNat n : Real) := by
      exact mul_le_mul_of_nonneg_left hratio_le hM_nonneg
    _ ≤ q / 32 * (phaseNat n : Real) ^ 2 := hMphase

end

#print axioms eventually_abs_phaseRootGapCorridor_fourSize_tilt_linear_le_quadratic

end Erdos625
