import Erdos625.PhaseSignedFourSizeLogLogCorridorDerivativeUpper
import Mathlib.Tactic

/-!
# Sharp leading coefficient for the signed derivative on the log-log corridor

The coarse corridor bound `signedFourSizeObjectiveDerivative ≤ q * alpha ^ 2`
is refined here to the sharp leading coefficient `q / 2`.  Every lower-order
contribution of the exact affine-core rewrite -- the linear term `alpha`, the
factorial-log error, the corridor logarithm, the finite entropy constant and
the tilt-linear term -- is shown to be at most an affine function of `alpha`
with fixed coefficients, hence eventually at most `epsilon * alpha ^ 2` for an
arbitrary positive `epsilon`.
-/

namespace Erdos625

open Filter Set

open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The phase parameter tends to infinity. -/
private theorem tendsto_phaseNat_atTop_sharp :
    Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ)) atTop atTop :=
  tendsto_atTop_mono' atTop
    (show (logOrder : ℕ → ℝ) ≤ᶠ[atTop] fun n : ℕ ↦ (phaseNat n : ℝ) by
      filter_upwards
        [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
      exact hn.1)
    tendsto_logOrder_atTop

/-- The corridor half-width multiplier is eventually a small fraction of the
phase parameter. -/
private theorem eventually_sharp_logLogCorridor_multiplier_le
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
  have hscaled : (1 + C) * logLogOrder n ≤ logOrder n / 64 := by
    calc
      (1 + C) * logLogOrder n ≤
          (1 + C) * ((1 / (64 * (1 + C))) * logOrder n) :=
        mul_le_mul_of_nonneg_left hsmall hOneC.le
      _ = logOrder n / 64 := by field_simp
  exact hmul.trans (hscaled.trans (by linarith [hphase.1]))

/-- Every corridor point is within a factor two of the reference center, so its
logarithm differs from the center logarithm by at most `q`. -/
private theorem eventually_sharp_corridor_abs_log_le_center
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        |Real.log s| ≤ q + |Real.log (phaseRootCenter n)| := by
  filter_upwards
    [eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_five_lt_phaseNat,
      eventually_sharp_logLogCorridor_multiplier_le C hC]
      with n hcenter hphase hscale
  intro s hs
  obtain ⟨hn, hs0Pos, _⟩ := hcenter
  set a : ℝ := (phaseNat n : ℝ) with ha
  set c : ℝ := phaseRootCenter n with hc
  set gap : ℝ := phaseRootGapRadius n with hgap
  set wide : ℝ := C * logLogOrder n * gap with hwide
  have haSix : (6 : ℝ) ≤ a := by
    rw [ha]
    exact_mod_cast hphase
  have haPos : 0 < a := by linarith
  have haSqPos : 0 < a ^ 2 := by positivity
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcPos : 0 < c := by
    rw [hc]
    unfold phaseRootCenter
    exact div_pos hnPos hs0Pos
  have hgapEq : gap = c / a ^ 2 := by
    rw [hgap, hc, ha]
    rfl
  have hscale' : C * logLogOrder n ≤ a / 64 := by
    simpa [ha] using hscale
  have hfrac : C * logLogOrder n / a ^ 2 ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ haSqPos]
    nlinarith [hscale']
  have hwideEq : wide = c * (C * logLogOrder n / a ^ 2) := by
    rw [hwide, hgapEq]
    ring
  have hwideLeHalf : wide ≤ c / 2 := by
    rw [hwideEq]
    nlinarith [mul_le_mul_of_nonneg_left hfrac hcPos.le]
  rw [mem_Icc] at hs
  have hsPos : 0 < s := by linarith [hs.1, hcPos]
  have hsUpper : s ≤ 2 * c := by linarith [hs.2, hwideLeHalf, hcPos]
  have hcUpper : c ≤ 2 * s := by linarith [hs.1, hwideLeHalf, hcPos]
  have hlogUpper : Real.log s ≤ Real.log (2 * c) :=
    Real.log_le_log hsPos hsUpper
  have hlogLower : Real.log c ≤ Real.log (2 * s) :=
    Real.log_le_log hcPos hcUpper
  have hlogTwoCenter : Real.log (2 * c) = q + Real.log c := by
    rw [Real.log_mul (by norm_num) hcPos.ne']
    rfl
  have hlogTwoS : Real.log (2 * s) = q + Real.log s := by
    rw [Real.log_mul (by norm_num) hsPos.ne']
    rfl
  rw [hlogTwoCenter] at hlogUpper
  rw [hlogTwoS] at hlogLower
  have hcAbs := le_abs_self (Real.log c)
  have hcAbs' := neg_abs_le (Real.log c)
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The logarithm of the reference center is eventually bounded by a fixed
multiple of the phase parameter. -/
private theorem exists_bound_abs_log_phaseRootCenter_linear :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop,
        |Real.log (phaseRootCenter n)| ≤ K * (phaseNat n : ℝ) := by
  obtain ⟨C, hCpos, hWith⟩ :=
    logOrder_sub_log_phaseRootCenter_isBigO.exists_pos
  refine ⟨1 + C, by linarith, ?_⟩
  have hLL : ∀ᶠ n : ℕ in atTop, ‖logLogOrder n‖ ≤ 1 * ‖logOrder n‖ :=
    logLogOrder_isLittleO_logOrder.bound (by norm_num : (0 : ℝ) < 1)
  have hPos : ∀ᶠ n : ℕ in atTop, 0 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 0
  filter_upwards [hWith.bound, hLL,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder, hPos] with
      n hb hll hphase hpos
  set L := logOrder n with hLdef
  set P := (phaseNat n : ℝ) with hPdef
  set M := Real.log (phaseRootCenter n) with hMdef
  have hLnorm : ‖L‖ = L := by rw [Real.norm_eq_abs, abs_of_pos hpos]
  have hll' : ‖logLogOrder n‖ ≤ L := by rw [← hLnorm]; linarith [hll]
  have hb' : |L - M| ≤ C * L := by
    have hbb : ‖L - M‖ ≤ C * ‖logLogOrder n‖ := hb
    rw [Real.norm_eq_abs] at hbb
    calc
      |L - M| ≤ C * ‖logLogOrder n‖ := hbb
      _ ≤ C * L := by nlinarith [hll', hCpos.le]
  have h1 : |M| ≤ (1 + C) * L := by
    rw [abs_le] at hb' ⊢
    obtain ⟨hlo, hhi⟩ := hb'
    exact ⟨by nlinarith [hpos.le], by nlinarith [hpos.le]⟩
  have h2 : L ≤ P := hphase.1
  exact h1.trans (by nlinarith [hCpos.le])

/-- The tilt-linear contribution is eventually bounded by a fixed multiple of
the phase parameter, uniformly on the corridor. -/
private theorem exists_bound_corridor_tilt_linear
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ s ∈ Icc
            (phaseRootCenter n -
              C * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              C * logLogOrder n * phaseRootGapRadius n),
          |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n))
                (fourSizeTarget n (phaseNat n) s) *
              (n : ℝ) / s| ≤ M * (phaseNat n : ℝ) := by
  set L : ℝ :=
    max
      |ProfileEntropyS4.tilt fourGaussianScore (9 / 4 : ℝ)|
      |ProfileEntropyS4.tilt fourGaussianScore (17 / 4 : ℝ)| with hLdef
  have hL_nonneg : 0 ≤ L := (abs_nonneg _).trans (le_max_left _ _)
  refine ⟨1 + L, by linarith, ?_⟩
  have hlimitingTilt {T : ℝ} (hT : T ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ)) :
      |ProfileEntropyS4.tilt fourGaussianScore T| ≤ L := by
    have hleftInterior : (9 / 4 : ℝ) ∈ Ioo (2 : ℝ) 5 := by norm_num
    have hrightInterior : (17 / 4 : ℝ) ∈ Ioo (2 : ℝ) 5 := by norm_num
    have hTInterior : T ∈ Ioo (2 : ℝ) 5 := by
      constructor <;> linarith [hT.1, hT.2]
    have hleftMean :
        ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore (9 / 4 : ℝ)) ≤
          ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore T) := by
      rw [ProfileEntropyS4.mean_tilt_eq fourGaussianScore hleftInterior,
        ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTInterior]
      exact hT.1
    have hrightMean :
        ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore T) ≤
          ProfileEntropyS4.mean fourGaussianScore
            (ProfileEntropyS4.tilt fourGaussianScore (17 / 4 : ℝ)) := by
      rw [ProfileEntropyS4.mean_tilt_eq fourGaussianScore hTInterior,
        ProfileEntropyS4.mean_tilt_eq fourGaussianScore hrightInterior]
      exact hT.2
    have hleft :
        ProfileEntropyS4.tilt fourGaussianScore (9 / 4 : ℝ) ≤
          ProfileEntropyS4.tilt fourGaussianScore T :=
      (ProfileEntropyS4.strictMono_mean fourGaussianScore).le_iff_le.mp hleftMean
    have hright :
        ProfileEntropyS4.tilt fourGaussianScore T ≤
          ProfileEntropyS4.tilt fourGaussianScore (17 / 4 : ℝ) :=
      (ProfileEntropyS4.strictMono_mean fourGaussianScore).le_iff_le.mp hrightMean
    exact (abs_le_max_abs_abs hleft hright).trans_eq hLdef.symm
  obtain ⟨_c, _hc, hcompactControl⟩ :=
    exists_pos_eventually_phaseRootLogLogCorridor_fourSize_compact_control C hC
  have hcontrol := hcompactControl 1 (by norm_num)
  filter_upwards [hcontrol,
    eventually_phaseRootLogLogCorridor_fourSize_domain C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC] with
      n hcontrolN hdomain htarget
  intro s hs
  set T : ℝ := fourSizeTarget n (phaseNat n) s with hTdef
  have hT : T ∈ Icc (9 / 4 : ℝ) (17 / 4 : ℝ) := htarget s hs
  have hclose := (hcontrolN s hs).1
  have hfiniteTilt :
      |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| ≤ 1 + L := by
    calc
      |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| =
          |(ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T -
              ProfileEntropyS4.tilt fourGaussianScore T) +
            ProfileEntropyS4.tilt fourGaussianScore T| := by ring_nf
      _ ≤ |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T -
              ProfileEntropyS4.tilt fourGaussianScore T| +
            |ProfileEntropyS4.tilt fourGaussianScore T| := abs_add_le _ _
      _ ≤ 1 + L := add_le_add (le_of_lt hclose) (hlimitingTilt hT)
  have hs_pos : 0 < s := (hdomain s hs).1
  have hratio_nonneg : 0 ≤ (n : ℝ) / s :=
    div_nonneg (Nat.cast_nonneg n) hs_pos.le
  have hratio_eq : (n : ℝ) / s = (phaseNat n : ℝ) - T := by
    rw [hTdef]
    dsimp [fourSizeTarget]
    ring
  have hratio_le : (n : ℝ) / s ≤ (phaseNat n : ℝ) := by
    rw [hratio_eq]
    linarith [hT.1]
  have habs :
      |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T *
          (n : ℝ) / s| =
        |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| *
          ((n : ℝ) / s) := by
    rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      abs_of_pos hs_pos]
    ring
  rw [habs]
  calc
    |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n)) T| *
          ((n : ℝ) / s) ≤ (1 + L) * ((n : ℝ) / s) :=
      mul_le_mul_of_nonneg_right hfiniteTilt hratio_nonneg
    _ ≤ (1 + L) * (phaseNat n : ℝ) :=
      mul_le_mul_of_nonneg_left hratio_le (by linarith)

/-- The signed four-size derivative has leading coefficient `q/2`, uniformly
on every fixed log-log root corridor. -/
theorem eventually_signedFourSizeObjectiveDerivative_logLogCorridor_upper_sharp
    (C : ℝ) (hC : 0 ≤ C) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc
          (phaseRootCenter n -
            C * logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            C * logLogOrder n * phaseRootGapRadius n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤
          (q / 2 + epsilon) * (phaseNat n : ℝ) ^ 2 := by
  obtain ⟨K, hK, hKbound⟩ := exists_bound_abs_log_phaseRootCenter_linear
  obtain ⟨M, hM, hMbound⟩ := exists_bound_corridor_tilt_linear C hC
  have hphaseSix : ∀ᶠ n : ℕ in atTop, 5 < phaseNat n := by
    have hcast : Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ)) atTop atTop :=
      tendsto_phaseNat_atTop_sharp
    rw [tendsto_natCast_atTop_iff] at hcast
    exact hcast.eventually_gt_atTop 5
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (2 + K + M + 4 + 4 * q) / epsilon + 1 ≤ (phaseNat n : ℝ) :=
    tendsto_phaseNat_atTop_sharp.eventually_ge_atTop _
  filter_upwards [hKbound, hMbound,
    eventually_sharp_corridor_abs_log_le_center C hC,
    eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
    hphaseSix, hlarge] with
      n hKn hMn hlogn htarget hsix hlarge
  intro s hs
  have halphaPos : 0 < phaseNat n := by omega
  -- the affine core
  have hcore :=
    abs_profileDeficitAffineCore_sub_quadratic_le (phaseNat n) halphaPos
  rw [abs_le] at hcore
  -- the factorial-log error is at most `alpha + 4`
  have hfactorial :
      factorialLogErrorBound (phaseNat n) ≤ (phaseNat n : ℝ) + 4 := by
    have h := Real.log_le_sub_one_of_pos
      (x := ((phaseNat n + 1 : ℕ) : ℝ)) (by positivity)
    have hEq : factorialLogErrorBound (phaseNat n) =
        Real.log ((phaseNat n + 1 : ℕ) : ℝ) + 4 := rfl
    rw [hEq]
    push_cast at h ⊢
    linarith
  -- the finite entropy is at most `2 * q`
  have hTargetClosed := htarget s hs
  have hTargetOpen :
      fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5 := by
    constructor <;> linarith [hTargetClosed.1, hTargetClosed.2]
  have hEntropy :=
    fourSizeFiniteEntropy_le_two_q (phaseNat n) hsix hTargetOpen
  -- the corridor logarithm
  have hLogCorridor := hlogn s hs
  have hLog : |Real.log s| ≤ q + K * (phaseNat n : ℝ) := by
    linarith [hKn]
  have hLogLower : -(q + K * (phaseNat n : ℝ)) ≤ Real.log s :=
    (abs_le.mp hLog).1
  -- the tilt-linear term
  have hTiltLower :
      -(M * (phaseNat n : ℝ)) ≤
        ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n))
          (fourSizeTarget n (phaseNat n) s) * (n : ℝ) / s :=
    (abs_le.mp (hMn s hs)).1
  -- collecting the lower-order contributions
  have haOne : (1 : ℝ) ≤ (phaseNat n : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ (2 + K + M + 4 + 4 * q) / epsilon := by
      have : (0 : ℝ) ≤ 2 + K + M + 4 + 4 * q := by linarith [q_pos]
      positivity
    linarith
  have haBig : (2 + K + M + 4 + 4 * q) ≤ epsilon * (phaseNat n : ℝ) := by
    have hdiv : (2 + K + M + 4 + 4 * q) / epsilon ≤ (phaseNat n : ℝ) := by
      linarith
    rw [div_le_iff₀ hepsilon] at hdiv
    linarith
  have hRemainder :
      (2 + K + M) * (phaseNat n : ℝ) + (4 + 4 * q) ≤
        epsilon * (phaseNat n : ℝ) ^ 2 := by
    have h1 : (2 + K + M + 4 + 4 * q) * (phaseNat n : ℝ) ≤
        epsilon * (phaseNat n : ℝ) * (phaseNat n : ℝ) :=
      mul_le_mul_of_nonneg_right haBig (by linarith)
    have h2 : (4 + 4 * q) ≤ (4 + 4 * q) * (phaseNat n : ℝ) := by
      nlinarith [q_pos]
    nlinarith [h1, h2]
  rw [signedFourSizeObjectiveDerivative_eq_affineCore_sub_tiltTerm]
  linarith [hcore.2, hfactorial, hEntropy, hLogLower, hTiltLower, hRemainder]

#print axioms eventually_signedFourSizeObjectiveDerivative_logLogCorridor_upper_sharp

end

end Erdos625
