import Erdos625.PhaseRootDisplacementScale
import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.SignedFourSizeObjective
import Mathlib.Tactic

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- Across the full manuscript-scale phase-root corridor, the four-size target
is uniformly asymptotic to its exact value at the reference center. -/
theorem eventually_uniform_phaseRoot_gapCorridor_target_close :
    ∀ epsilon > 0,
      ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Icc (phaseRootCenter n - phaseRootGapRadius n)
            (phaseRootCenter n + phaseRootGapRadius n),
          |fourSizeTarget n (phaseNat n) s -
              (1 + 2 / q - phaseDelta n)| < epsilon := by
  intro epsilon hepsilon
  -- The uniform gap bound tends to zero.
  have hphasetop : Tendsto (fun n : ℕ => (phaseNat n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_logOrder_atTop
    filter_upwards [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder]
      with n h using h.1
  have hmaj : Tendsto (fun n : ℕ => 2 * (phaseNat n : ℝ)⁻¹) atTop (nhds 0) := by
    have h0 := hphasetop.inv_tendsto_atTop
    simpa using h0.const_mul (2 : ℝ)
  have htend :
      Tendsto (fun n : ℕ => phaseRootS0 n / ((phaseNat n : ℝ) ^ 2 - 1))
        atTop (nhds 0) := by
    apply squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
        eventually_five_lt_phaseNat] with n hdom hα
      have hs0 : 0 < phaseRootS0 n := hdom.2.1
      have hαR : (2 : ℝ) ≤ (phaseNat n : ℝ) := by
        have h5 : (5 : ℕ) < phaseNat n := hα
        have : (2 : ℕ) ≤ phaseNat n := by omega
        exact_mod_cast this
      have hden : 0 < (phaseNat n : ℝ) ^ 2 - 1 := by nlinarith [hαR]
      exact div_nonneg hs0.le hden.le
    · filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
        eventually_five_lt_phaseNat] with n hdom hα
      obtain ⟨hPD, hs0, _⟩ := hdom
      have hαR : (2 : ℝ) ≤ (phaseNat n : ℝ) := by
        have h5 : (5 : ℕ) < phaseNat n := hα
        have : (2 : ℕ) ≤ phaseNat n := by omega
        exact_mod_cast this
      have hαpos : 0 < (phaseNat n : ℝ) := by linarith
      have hden : 0 < (phaseNat n : ℝ) ^ 2 - 1 := by nlinarith [hαR]
      -- phaseRootS0 n ≤ phaseNat n
      have hs0le : phaseRootS0 n ≤ (phaseNat n : ℝ) := by
        rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hPD]
        have h2q : (0 : ℝ) < 2 / q := div_pos (by norm_num) q_pos
        linarith [phaseDelta_lt_one n]
      -- phaseRootS0/(α²-1) ≤ 2/α
      rw [div_le_iff₀ hden]
      rw [show (2 : ℝ) * (phaseNat n : ℝ)⁻¹ * ((phaseNat n : ℝ) ^ 2 - 1)
            = 2 * ((phaseNat n : ℝ) ^ 2 - 1) / (phaseNat n : ℝ) by
          field_simp]
      rw [le_div_iff₀ hαpos]
      nlinarith [hs0le, hs0, hαR, hαpos]
  have hsmall : ∀ᶠ n : ℕ in atTop,
      phaseRootS0 n / ((phaseNat n : ℝ) ^ 2 - 1) < epsilon :=
    htend.eventually (Iio_mem_nhds hepsilon)
  -- Assemble.
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor,
    eventually_five_lt_phaseNat, hsmall] with n hdom hα hsmalln
  obtain ⟨hPD, hs0pos, _⟩ := hdom
  intro s hs
  have hnpos : 0 < n := lt_trans Nat.zero_lt_one hPD.1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hnRne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hs0ne : phaseRootS0 n ≠ 0 := ne_of_gt hs0pos
  have hαR : (2 : ℝ) ≤ (phaseNat n : ℝ) := by
    have h5 : (5 : ℕ) < phaseNat n := hα
    have : (2 : ℕ) ≤ phaseNat n := by omega
    exact_mod_cast this
  have hαpos : 0 < (phaseNat n : ℝ) := by linarith
  have hα2 : (1 : ℝ) < (phaseNat n : ℝ) ^ 2 := by nlinarith [hαR]
  have hden : 0 < (phaseNat n : ℝ) ^ 2 - 1 := by linarith
  have hcpos : 0 < phaseRootCenter n := by
    rw [phaseRootCenter]; exact div_pos hnR hs0pos
  -- abbreviations
  set c := phaseRootCenter n with hc
  set r := phaseRootGapRadius n with hr
  have hr_eq : r = c / (phaseNat n : ℝ) ^ 2 := by
    rw [hr, hc, phaseRootGapRadius]
  have hrpos : 0 < r := by rw [hr_eq]; exact div_pos hcpos (pow_pos hαpos 2)
  -- c - r > 0
  have hcmr : c - r = c * ((phaseNat n : ℝ) ^ 2 - 1) / (phaseNat n : ℝ) ^ 2 := by
    rw [hr_eq]; field_simp
  have hcmrpos : 0 < c - r := by
    rw [hcmr]; positivity
  have hspos : 0 < s := lt_of_lt_of_le hcmrpos hs.1
  -- rewrite difference
  have hnc : (n : ℝ) / phaseRootCenter n = phaseRootS0 n := by
    rw [phaseRootCenter]; field_simp
  have hid := phaseRoot_target_identity hPD
  rw [hnc] at hid
  have hdiff : fourSizeTarget n (phaseNat n) s - (1 + 2 / q - phaseDelta n)
      = phaseRootS0 n - (n : ℝ) / s := by
    rw [fourSizeTarget, ← hid]; ring
  rw [hdiff]
  -- n = phaseRootS0 * c
  have hn_eq : (n : ℝ) = phaseRootS0 n * c := by
    rw [hc, phaseRootCenter]; field_simp
  -- phaseRootS0 - n/s = phaseRootS0 * (s - c)/s
  have hval : phaseRootS0 n - (n : ℝ) / s = phaseRootS0 n * (s - c) / s := by
    rw [hn_eq]; field_simp
  rw [hval]
  -- bound the absolute value
  have habs : |phaseRootS0 n * (s - c) / s|
      = phaseRootS0 n * |s - c| / s := by
    rw [abs_div, abs_mul, abs_of_pos hs0pos, abs_of_pos hspos]
  rw [habs]
  -- |s - c| ≤ r
  have hsc : |s - c| ≤ r := by
    rw [abs_le]
    constructor
    · linarith [hs.1]
    · linarith [hs.2]
  -- core: phaseRootS0 * |s-c| / s ≤ phaseRootS0/(α²-1) < epsilon
  have hkey : phaseRootS0 n * |s - c| / s
      ≤ phaseRootS0 n / ((phaseNat n : ℝ) ^ 2 - 1) := by
    have hr_alpha : r * (phaseNat n : ℝ) ^ 2 = c := by
      rw [hr_eq]; field_simp
    have hcore : |s - c| * ((phaseNat n : ℝ) ^ 2 - 1) ≤ s := by
      have h1 : |s - c| * ((phaseNat n : ℝ) ^ 2 - 1)
          ≤ r * ((phaseNat n : ℝ) ^ 2 - 1) :=
        mul_le_mul_of_nonneg_right hsc hden.le
      nlinarith [h1, hs.1, hr_alpha, hrpos]
    rw [div_le_iff₀ hspos,
      show phaseRootS0 n / ((phaseNat n : ℝ) ^ 2 - 1) * s
          = phaseRootS0 n * s / ((phaseNat n : ℝ) ^ 2 - 1) by ring,
      le_div_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hcore hs0pos.le]
  exact lt_of_le_of_lt hkey hsmalln

/-- Across the full phase-root corridor, the four-size target is eventually
trapped in the fixed neighborhood `[2/q - eta, 1 + 2/q + eta]`, using the
closeness to `1 + 2/q - phaseDelta n` together with `0 ≤ phaseDelta n < 1`. -/
theorem eventually_phaseRoot_gapCorridor_target_mem_neighborhood
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Set.Icc (phaseRootCenter n - phaseRootGapRadius n)
          (phaseRootCenter n + phaseRootGapRadius n),
        fourSizeTarget n (phaseNat n) s ∈
          Set.Icc (2 / q - eta) (1 + 2 / q + eta) := by
  filter_upwards
    [eventually_uniform_phaseRoot_gapCorridor_target_close eta heta] with n hn
  intro s hs
  have hclose := hn s hs
  rw [abs_lt] at hclose
  have hlo := phaseDelta_nonneg n
  have hhi := phaseDelta_lt_one n
  constructor <;> [linarith [hclose.1]; linarith [hclose.2]]

end

end Erdos625
