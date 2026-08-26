import Erdos625.SignedFourDerivativeCorridor
import Erdos625.CompactUnrestrictedEntropyConvergence
import Erdos625.UnrestrictedPhaseRootCenterLocalization
import Mathlib.Tactic

/-!
# Concrete unrestricted phase-objective derivative corridor

The unrestricted profile derivative has the same quadratic main term as the
signed four-size derivative. After changing from size to deficit coordinates,
its exact derivative is

`A_alpha + B_alpha * alpha - lambda * alpha + log Z_alpha(lambda) - log parts`.

The affine core contributes `(q/2) * alpha^2 + O(alpha)`. Uniform compact-
target bounds for the selected finite deficit tilt and the attained finite
unrestricted entropy control `lambda` and `log Z_alpha(lambda)`. Target
membership also forces `1 <= parts <= n`, hence `|log parts| <= log n`.

This module constructs explicit lower and upper derivative slopes, proves that
both normalize to `2/q`, and packages the complete unrestricted derivative
corridor needed for root localization. It does not construct the root or
prove endpoint signs, root uniqueness, signed-root existence, the chromatic
lower tail, partial diagonals, skeletons, second moments, or the final Erdős
statement.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Lower-order remainder after extracting the quadratic affine core from the
unrestricted profile derivative. -/
noncomputable def unrestrictedDerivativeRemainder
    (alpha : ℕ) (n parts : ℝ) : ℝ :=
  (alpha : ℝ) -
    profileDeficitTilt alpha (profileDeficitTarget alpha n parts) *
      (alpha : ℝ) +
    Real.log
      (profileDeficitPartition alpha
        (profileDeficitTilt alpha
          (profileDeficitTarget alpha n parts))) -
    Real.log parts

/-- Exact deficit-coordinate cancellation for the unrestricted derivative. -/
theorem unrestrictedDerivativeExpression_eq_quadraticMain_add_errors
    (alpha : ℕ) (n parts : ℝ) :
    Real.log
        (profileDualPartition (alpha + 1)
          (profileDualTilt (alpha + 1) (n / parts))) -
        Real.log parts =
      q / 2 * (alpha : ℝ) ^ 2 +
        (profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
            (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))) +
        unrestrictedDerivativeRemainder alpha n parts := by
  have hTilt :
      profileDualTilt (alpha + 1) (n / parts) =
        profileDeficitAffineB alpha -
          profileDeficitTilt alpha
            (profileDeficitTarget alpha n parts) := by
    calc
      profileDualTilt (alpha + 1) (n / parts) =
          profileDualTilt (alpha + 1)
            ((alpha : ℝ) - profileDeficitTarget alpha n parts) := by
              congr 1
              unfold profileDeficitTarget
              ring
      _ = profileDeficitAffineB alpha -
          profileDeficitTilt alpha
            (profileDeficitTarget alpha n parts) :=
        (profileDeficitAffineB_sub_profileDeficitTilt
          alpha (profileDeficitTarget alpha n parts)).symm
  rw [hTilt, log_profileDualPartition_eq_deficitCentered]
  unfold unrestrictedDerivativeRemainder
  ring

private theorem abs_sub_add_sub_le
    (a b c d : ℝ) :
    |a - b + c - d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a - b + c - d| ≤ |a - b + c| + |d| := abs_sub _ _
    _ ≤ (|a - b| + |c|) + |d| := by
      linarith [abs_add_le (a - b) c]
    _ ≤ ((|a| + |b|) + |c|) + |d| := by
      linarith [abs_sub a b]
    _ = |a| + |b| + |c| + |d| := rfl

/-- Finite absolute envelope for the unrestricted derivative remainder. -/
theorem abs_unrestrictedDerivativeRemainder_le
    (alpha : ℕ) (n parts : ℝ) :
    |unrestrictedDerivativeRemainder alpha n parts| ≤
      (alpha : ℝ) +
        |profileDeficitTilt alpha (profileDeficitTarget alpha n parts)| *
          (alpha : ℝ) +
        |Real.log
          (profileDeficitPartition alpha
            (profileDeficitTilt alpha
              (profileDeficitTarget alpha n parts)))| +
        |Real.log parts| := by
  unfold unrestrictedDerivativeRemainder
  have h := abs_sub_add_sub_le
    (alpha : ℝ)
    (profileDeficitTilt alpha (profileDeficitTarget alpha n parts) *
      (alpha : ℝ))
    (Real.log
      (profileDeficitPartition alpha
        (profileDeficitTilt alpha
          (profileDeficitTarget alpha n parts))))
    (Real.log parts)
  have hAlphaNonneg : 0 ≤ (alpha : ℝ) := by positivity
  simpa only [abs_mul, abs_of_nonneg hAlphaNonneg] using h

/-- Exact finite quadratic-main error bound for the unrestricted derivative
expression. -/
theorem abs_unrestrictedDerivativeExpression_sub_quadraticMain_le
    (alpha : ℕ) (n parts : ℝ) (halpha : 0 < alpha) :
    |(Real.log
        (profileDualPartition (alpha + 1)
          (profileDualTilt (alpha + 1) (n / parts))) -
          Real.log parts) -
        q / 2 * (alpha : ℝ) ^ 2| ≤
      factorialLogErrorBound alpha +
        ((alpha : ℝ) +
          |profileDeficitTilt alpha
              (profileDeficitTarget alpha n parts)| * (alpha : ℝ) +
          |Real.log
            (profileDeficitPartition alpha
              (profileDeficitTilt alpha
                (profileDeficitTarget alpha n parts)))| +
          |Real.log parts|) := by
  have hCore :=
    abs_profileDeficitAffineCore_sub_quadratic_le alpha halpha
  have hRemainder :=
    abs_unrestrictedDerivativeRemainder_le alpha n parts
  calc
    |(Real.log
        (profileDualPartition (alpha + 1)
          (profileDualTilt (alpha + 1) (n / parts))) -
          Real.log parts) -
        q / 2 * (alpha : ℝ) ^ 2| =
      |(profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
            (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))) +
        unrestrictedDerivativeRemainder alpha n parts| := by
          rw [unrestrictedDerivativeExpression_eq_quadraticMain_add_errors]
          congr 1
          ring
    _ ≤
      |profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * (alpha : ℝ) -
            (q / 2 * (alpha : ℝ) ^ 2 + (alpha : ℝ))| +
        |unrestrictedDerivativeRemainder alpha n parts| := abs_add_le _ _
    _ ≤
      factorialLogErrorBound alpha +
        ((alpha : ℝ) +
          |profileDeficitTilt alpha
              (profileDeficitTarget alpha n parts)| * (alpha : ℝ) +
          |Real.log
            (profileDeficitPartition alpha
              (profileDeficitTilt alpha
                (profileDeficitTarget alpha n parts)))| +
          |Real.log parts|) :=
      add_le_add hCore hRemainder

/-- Continuity of the limiting unrestricted entropy on the fixed manuscript
corridor. -/
theorem continuousOn_extendedGaussianEntropyValue_admissibilityTargetCorridor :
    ContinuousOn extendedGaussianEntropyValue
      signedFourAdmissibilityTargetCorridor := by
  intro T hT
  have hContinuousAt : ContinuousAt extendedGaussianEntropyValue T := by
    change Tendsto extendedGaussianEntropyValue
      (𝓝 T) (𝓝 (extendedGaussianEntropyValue T))
    simpa only [id_eq] using
      (tendsto_extendedGaussianEntropyValue_of_target id tendsto_id
        (signedFourAdmissibilityTargetCorridor_subset_Ioo hT))
  exact hContinuousAt.continuousWithinAt

/-- The limiting unrestricted entropy has a finite absolute maximum on the
fixed manuscript corridor. -/
theorem exists_uniform_abs_extendedGaussianEntropyValue_bound :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ T ∈ signedFourAdmissibilityTargetCorridor,
        |extendedGaussianEntropyValue T| ≤ M := by
  have hContinuous : ContinuousOn
      (fun T ↦ |extendedGaussianEntropyValue T|)
      signedFourAdmissibilityTargetCorridor :=
    continuousOn_extendedGaussianEntropyValue_admissibilityTargetCorridor.abs
  obtain ⟨T₀, _hT₀, hMax⟩ :=
    signedFourAdmissibilityTargetCorridor_compact.exists_isMaxOn
      signedFourAdmissibilityTargetCorridor_nonempty hContinuous
  refine ⟨|extendedGaussianEntropyValue T₀|, abs_nonneg _, ?_⟩
  intro T hT
  exact hMax hT

/-- Uniform bounds for the selected finite unrestricted tilt and its finite
partition logarithm on the full target corridor. -/
theorem
    exists_eventually_uniform_profileDeficit_tilt_and_logPartition_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
      ∀ alpha ≥ N, ∀ T ∈ signedFourAdmissibilityTargetCorridor,
        |profileDeficitTilt alpha T| ≤ C ∧
        |Real.log
          (profileDeficitPartition alpha
            (profileDeficitTilt alpha T))| ≤ C := by
  obtain ⟨Mtilt, hMtilt, hTilt⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      (by norm_num : (-(1 : ℝ)) < 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 9 / 2)
  obtain ⟨Mentropy, hMentropy, hEntropyLimit⟩ :=
    exists_uniform_abs_extendedGaussianEntropyValue_bound
  have hEntropyUniform :=
    tendstoUniformlyOn_finiteUnrestrictedDeficitEntropy
      (by norm_num : (2 : ℝ) < 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 9 / 2)
      (by norm_num : (9 / 2 : ℝ) < 5)
  rw [Metric.tendstoUniformlyOn_iff] at hEntropyUniform
  have hEntropyClose := hEntropyUniform 1 (by norm_num)
  rw [eventually_atTop] at hTilt hEntropyClose
  obtain ⟨Ntilt, hNtilt⟩ := hTilt
  obtain ⟨Nentropy, hNentropy⟩ := hEntropyClose
  let C : ℝ :=
    Mtilt + (Mentropy + 1) + Mtilt * (9 / 2)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, max Ntilt Nentropy, ?_⟩
  intro alpha halpha T hT
  have hTiltAlpha := hNtilt alpha (by omega) T hT
  have hEntropyAlpha := hNentropy alpha (by omega) T hT
  have hTiltBound : |profileDeficitTilt alpha T| ≤ Mtilt :=
    hTiltAlpha.2
  have hEntropyBound :
      |finiteUnrestrictedDeficitEntropy alpha T| ≤ Mentropy + 1 := by
    have hLimitBound := hEntropyLimit T hT
    rw [Real.dist_eq] at hEntropyAlpha
    have hEntropyDifference :
        |finiteUnrestrictedDeficitEntropy alpha T -
            extendedGaussianEntropyValue T| < 1 := by
      rw [abs_sub_comm]
      exact hEntropyAlpha
    calc
      |finiteUnrestrictedDeficitEntropy alpha T| =
          |(finiteUnrestrictedDeficitEntropy alpha T -
              extendedGaussianEntropyValue T) +
            extendedGaussianEntropyValue T| := by
              congr 1
              ring
      _ ≤
          |finiteUnrestrictedDeficitEntropy alpha T -
            extendedGaussianEntropyValue T| +
          |extendedGaussianEntropyValue T| := abs_add_le _ _
      _ ≤ Mentropy + 1 := by
        linarith [hEntropyDifference, hLimitBound]
  have hTargetAbs : |T| ≤ (9 / 2 : ℝ) := by
    have hT' := hT
    simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hT'
    rw [abs_of_nonneg (by linarith [hT'.1])]
    exact hT'.2
  have hTiltTarget :
      |profileDeficitTilt alpha T| * |T| ≤
        Mtilt * (9 / 2 : ℝ) :=
    mul_le_mul hTiltBound hTargetAbs (abs_nonneg T) hMtilt
  have hLogIdentity :
      Real.log
          (profileDeficitPartition alpha
            (profileDeficitTilt alpha T)) =
        finiteUnrestrictedDeficitEntropy alpha T +
          profileDeficitTilt alpha T * T := by
    unfold finiteUnrestrictedDeficitEntropy
    ring
  have hLogBound :
      |Real.log
          (profileDeficitPartition alpha
            (profileDeficitTilt alpha T))| ≤
        (Mentropy + 1) + Mtilt * (9 / 2 : ℝ) := by
    rw [hLogIdentity]
    calc
      |finiteUnrestrictedDeficitEntropy alpha T +
          profileDeficitTilt alpha T * T| ≤
        |finiteUnrestrictedDeficitEntropy alpha T| +
          |profileDeficitTilt alpha T * T| := abs_add_le _ _
      _ = |finiteUnrestrictedDeficitEntropy alpha T| +
          |profileDeficitTilt alpha T| * |T| := by rw [abs_mul]
      _ ≤ (Mentropy + 1) + Mtilt * (9 / 2 : ℝ) :=
        add_le_add hEntropyBound hTiltTarget
  constructor
  · exact hTiltBound.trans (by
      dsimp only [C]
      linarith [hMentropy])
  · exact hLogBound.trans (by
      dsimp only [C]
      linarith [hMtilt])

/-- Sequence-level uniform profile bounds along the exact integer phase. -/
theorem
    exists_eventually_uniform_phaseProfileDeficit_tilt_and_logPartition_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ T ∈ signedFourAdmissibilityTargetCorridor,
          |profileDeficitTilt (phaseNat n) T| ≤ C ∧
          |Real.log
            (profileDeficitPartition (phaseNat n)
              (profileDeficitTilt (phaseNat n) T))| ≤ C := by
  obtain ⟨C, hC, N, hN⟩ :=
    exists_eventually_uniform_profileDeficit_tilt_and_logPartition_bound
  refine ⟨C, hC, ?_⟩
  have hPhaseN : ∀ᶠ n : ℕ in atTop, N ≤ phaseNat n :=
    tendsto_phaseNat_atTop_nat (eventually_ge_atTop N)
  filter_upwards [hPhaseN] with n hn
  exact fun T hT ↦ hN (phaseNat n) hn T hT

/-- The exact unrestricted objective derivative is the finite profile
derivative expression under the compact-target domain hypotheses. -/
theorem deriv_unrestrictedPhaseObjective_eq_expression
    (n : ℕ) {parts : ℝ}
    (hPhase : 6 ≤ phaseNat n)
    (hparts : 0 < parts)
    (hTarget : profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
      signedFourAdmissibilityTargetCorridor) :
    deriv (unrestrictedPhaseObjective n) parts =
      Real.log
        (profileDualPartition (phaseNat n + 1)
          (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts))) -
        Real.log parts := by
  have hDeficitInterior :
      profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
        Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) := by
    have hBounds := hTarget
    simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hBounds
    constructor
    · linarith [hBounds.1]
    · have hPhaseReal : (6 : ℝ) ≤ (phaseNat n : ℝ) := by
        exact_mod_cast hPhase
      linarith [hBounds.2]
  have hSizeInterior :
      (n : ℝ) / parts ∈
        Ioo (1 : ℝ) (((phaseNat n + 1 : ℕ) : ℝ)) := by
    have h :=
      (deficitTarget_mem_Ioo_iff_sizeTarget_mem_Ioo
        (phaseNat n)
        (profileDeficitTarget (phaseNat n) (n : ℝ) parts)).mp
        hDeficitInterior
    convert h using 1 <;> ring
  have hb : 2 ≤ phaseNat n + 1 := by omega
  change deriv
      (fun k ↦ profileDualOptimalValue (phaseNat n + 1) (n : ℝ) k)
      parts = _
  exact
    (hasDerivAt_profileDualOptimalValue_parts hb hparts hSizeInterior).deriv

noncomputable def unrestrictedDerivativeCorridorRadius
    (C : ℝ) (n : ℕ) : ℝ :=
  (13 + 5 * C) * logOrder n

noncomputable def unrestrictedDerivativeSlopeLower
    (C : ℝ) (n : ℕ) : ℝ :=
  signedFourDerivativeQuadraticMain n -
    unrestrictedDerivativeCorridorRadius C n

noncomputable def unrestrictedDerivativeSlopeUpper
    (C : ℝ) (n : ℕ) : ℝ :=
  signedFourDerivativeQuadraticMain n +
    unrestrictedDerivativeCorridorRadius C n

/-- Finite uniform unrestricted derivative error on the compact target
corridor. -/
theorem abs_deriv_unrestrictedPhaseObjective_sub_quadraticMain_le_corridorRadius
    (n : ℕ) (parts C : ℝ)
    (hC : 0 ≤ C)
    (hPhase : 6 ≤ phaseNat n)
    (hTwo : 2 * phaseNat n ≤ n)
    (hPhaseLog : (phaseNat n : ℝ) ≤ 4 * logOrder n)
    (hLogOne : 1 ≤ logOrder n)
    (hparts : 0 < parts)
    (hTarget : profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
      signedFourAdmissibilityTargetCorridor)
    (hProfile :
      |profileDeficitTilt (phaseNat n)
          (profileDeficitTarget (phaseNat n) (n : ℝ) parts)| ≤ C ∧
      |Real.log
        (profileDeficitPartition (phaseNat n)
          (profileDeficitTilt (phaseNat n)
            (profileDeficitTarget (phaseNat n) (n : ℝ) parts)))| ≤ C) :
    |deriv (unrestrictedPhaseObjective n) parts -
        signedFourDerivativeQuadraticMain n| ≤
      unrestrictedDerivativeCorridorRadius C n := by
  have hExpression :=
    deriv_unrestrictedPhaseObjective_eq_expression n hPhase hparts hTarget
  rw [hExpression]
  have hBase :=
    abs_unrestrictedDerivativeExpression_sub_quadraticMain_le
      (phaseNat n) (n : ℝ) parts (by omega)
  have hRange :=
    one_le_parts_and_parts_le_natCast_of_fourSizeTarget_mem_admissibilityCorridor
      n (phaseNat n) parts hPhase hTwo hparts
      (by simpa only [fourSizeTarget_eq_profileDeficitTarget] using hTarget)
  have hLogParts :=
    abs_log_parts_le_logOrder_of_range n parts hparts hRange
  have hFactorial :=
    factorialLogErrorBound_le_cast_add_four (phaseNat n)
  have hTiltTerm :
      |profileDeficitTilt (phaseNat n)
          (profileDeficitTarget (phaseNat n) (n : ℝ) parts)| *
          (phaseNat n : ℝ) ≤
        C * (phaseNat n : ℝ) :=
    mul_le_mul_of_nonneg_right hProfile.1 (Nat.cast_nonneg _)
  have hRemainder :
      (phaseNat n : ℝ) +
          |profileDeficitTilt (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) parts)| *
            (phaseNat n : ℝ) +
          |Real.log
            (profileDeficitPartition (phaseNat n)
              (profileDeficitTilt (phaseNat n)
                (profileDeficitTarget (phaseNat n) (n : ℝ) parts)))| +
          |Real.log parts| ≤
        (phaseNat n : ℝ) + C * (phaseNat n : ℝ) + C +
          logOrder n := by
    linarith [hTiltTerm, hProfile.2, hLogParts]
  have hCPhase : C * (phaseNat n : ℝ) ≤
      C * (4 * logOrder n) :=
    mul_le_mul_of_nonneg_left hPhaseLog hC
  have hConstantNonneg : 0 ≤ C + 4 := by positivity
  have hConstantScale : C + 4 ≤ (C + 4) * logOrder n := by
    calc
      C + 4 = (C + 4) * 1 := by ring
      _ ≤ (C + 4) * logOrder n :=
        mul_le_mul_of_nonneg_left hLogOne hConstantNonneg
  unfold signedFourDerivativeQuadraticMain
  calc
    |(Real.log
        (profileDualPartition (phaseNat n + 1)
          (profileDualTilt (phaseNat n + 1) ((n : ℝ) / parts))) -
          Real.log parts) -
        q / 2 * (phaseNat n : ℝ) ^ 2| ≤
      factorialLogErrorBound (phaseNat n) +
        ((phaseNat n : ℝ) +
          |profileDeficitTilt (phaseNat n)
              (profileDeficitTarget (phaseNat n) (n : ℝ) parts)| *
            (phaseNat n : ℝ) +
          |Real.log
            (profileDeficitPartition (phaseNat n)
              (profileDeficitTilt (phaseNat n)
                (profileDeficitTarget (phaseNat n) (n : ℝ) parts)))| +
          |Real.log parts|) := hBase
    _ ≤ ((phaseNat n : ℝ) + 4) +
        ((phaseNat n : ℝ) + C * (phaseNat n : ℝ) + C +
          logOrder n) := add_le_add hFactorial hRemainder
    _ ≤ (13 + 5 * C) * logOrder n := by
      nlinarith [hPhaseLog, hCPhase, hConstantScale]

/-- One constant controls the unrestricted derivative error uniformly on the
full manuscript target corridor. -/
theorem exists_eventually_uniform_unrestrictedDerivative_corridorRadius :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ parts : ℝ,
          0 < parts →
          profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
            signedFourAdmissibilityTargetCorridor →
          |deriv (unrestrictedPhaseObjective n) parts -
              signedFourDerivativeQuadraticMain n| ≤
            unrestrictedDerivativeCorridorRadius C n := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_eventually_uniform_phaseProfileDeficit_tilt_and_logPartition_bound
  refine ⟨C, hC, ?_⟩
  have hLogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hProfile, eventually_five_lt_phaseNat,
    eventually_two_mul_phaseNat_le,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hLogOne] with n hnProfile hnPhase hnTwo hnPhaseLog hnLogOne
  intro parts hparts hTarget
  exact
    abs_deriv_unrestrictedPhaseObjective_sub_quadraticMain_le_corridorRadius
      n parts C hC (by omega) hnTwo hnPhaseLog.2 hnLogOne
      hparts hTarget (hnProfile _ hTarget)

/-- The normalized unrestricted derivative radius vanishes. -/
theorem tendsto_signedFourNormalizedUnrestrictedDerivativeCorridorRadius_zero
    (C : ℝ) :
    Tendsto
      (signedFourNormalizedSlope
        (unrestrictedDerivativeCorridorRadius C))
      atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹)
      atTop (𝓝 0) :=
    tendsto_logOrder_atTop.inv_tendsto_atTop
  have hScaled :
      Tendsto
        (fun n : ℕ ↦ (13 + 5 * C) * (logOrder n)⁻¹)
        atTop (𝓝 0) := by
    simpa only [mul_zero] using hInv.const_mul (13 + 5 * C)
  refine hScaled.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope unrestrictedDerivativeCorridorRadius
  field_simp [hlog]

/-- Explicit lower and upper unrestricted derivative slopes have normalized
limit `2/q`. -/
theorem tendsto_signedFourNormalizedUnrestrictedDerivativeSlopeLower
    (C : ℝ) :
    Tendsto
      (signedFourNormalizedSlope
        (unrestrictedDerivativeSlopeLower C))
      atTop (𝓝 (2 / q)) := by
  have h := tendsto_signedFourNormalizedDerivativeQuadraticMain.sub
    (tendsto_signedFourNormalizedUnrestrictedDerivativeCorridorRadius_zero C)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope unrestrictedDerivativeSlopeLower
    signedFourDerivativeQuadraticMain unrestrictedDerivativeCorridorRadius
  field_simp [hlog]

theorem tendsto_signedFourNormalizedUnrestrictedDerivativeSlopeUpper
    (C : ℝ) :
    Tendsto
      (signedFourNormalizedSlope
        (unrestrictedDerivativeSlopeUpper C))
      atTop (𝓝 (2 / q)) := by
  have h := tendsto_signedFourNormalizedDerivativeQuadraticMain.add
    (tendsto_signedFourNormalizedUnrestrictedDerivativeCorridorRadius_zero C)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope unrestrictedDerivativeSlopeUpper
    signedFourDerivativeQuadraticMain unrestrictedDerivativeCorridorRadius
  field_simp [hlog]

/-- Concrete unrestricted derivative corridor, with matching normalized slope
limits, valid uniformly on the full manuscript target interval. -/
theorem exists_unrestrictedDerivativeCorridor :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ n : ℕ in atTop,
        ∀ parts : ℝ,
          0 < parts →
          profileDeficitTarget (phaseNat n) (n : ℝ) parts ∈
            signedFourAdmissibilityTargetCorridor →
          unrestrictedDerivativeSlopeLower C n ≤
              deriv (unrestrictedPhaseObjective n) parts ∧
            deriv (unrestrictedPhaseObjective n) parts ≤
              unrestrictedDerivativeSlopeUpper C n) ∧
      Tendsto
        (signedFourNormalizedSlope
          (unrestrictedDerivativeSlopeLower C))
        atTop (𝓝 (2 / q)) ∧
      Tendsto
        (signedFourNormalizedSlope
          (unrestrictedDerivativeSlopeUpper C))
        atTop (𝓝 (2 / q)) := by
  obtain ⟨C, hC, hError⟩ :=
    exists_eventually_uniform_unrestrictedDerivative_corridorRadius
  refine ⟨C, hC, ?_,
    tendsto_signedFourNormalizedUnrestrictedDerivativeSlopeLower C,
    tendsto_signedFourNormalizedUnrestrictedDerivativeSlopeUpper C⟩
  filter_upwards [hError] with n hn
  intro parts hparts hTarget
  have hAbs := hn parts hparts hTarget
  rw [abs_le] at hAbs
  unfold unrestrictedDerivativeSlopeLower unrestrictedDerivativeSlopeUpper
  constructor <;> linarith [hAbs.1, hAbs.2]

#print axioms unrestrictedDerivativeExpression_eq_quadraticMain_add_errors
#print axioms abs_unrestrictedDerivativeRemainder_le
#print axioms abs_unrestrictedDerivativeExpression_sub_quadraticMain_le
#print axioms continuousOn_extendedGaussianEntropyValue_admissibilityTargetCorridor
#print axioms exists_uniform_abs_extendedGaussianEntropyValue_bound
#print axioms exists_eventually_uniform_profileDeficit_tilt_and_logPartition_bound
#print axioms exists_eventually_uniform_phaseProfileDeficit_tilt_and_logPartition_bound
#print axioms deriv_unrestrictedPhaseObjective_eq_expression
#print axioms abs_deriv_unrestrictedPhaseObjective_sub_quadraticMain_le_corridorRadius
#print axioms exists_eventually_uniform_unrestrictedDerivative_corridorRadius
#print axioms tendsto_signedFourNormalizedUnrestrictedDerivativeCorridorRadius_zero
#print axioms tendsto_signedFourNormalizedUnrestrictedDerivativeSlopeLower
#print axioms tendsto_signedFourNormalizedUnrestrictedDerivativeSlopeUpper
#print axioms exists_unrestrictedDerivativeCorridor

end

end Erdos625
