import Erdos625.SignedFourDerivativeCompactBounds
import Erdos625.FirstMomentFromCenterAndDerivativeCorridor
import Erdos625.PhaseEstimates
import Mathlib.Tactic

/-!
# Concrete signed four-size derivative corridor

The exact quadratic-main reduction and the compact profile bounds imply a
uniform derivative corridor on the manuscript target interval.  The only
remaining variable term is `log parts`.  Target membership, positivity of the
part count, and the standard phase range force

`1 ≤ parts ≤ n`,

so `|log parts| ≤ log n`.  The complete finite error is then bounded by one
constant multiple of `log n`, whereas the quadratic main term is of order
`(log n)^2`.

This module constructs explicit lower and upper slope sequences, proves that
both normalize to `2/q`, and discharges the derivative-corridor hypotheses in
the E625-10 first-moment endpoint.  It does not construct either root, prove
their equations or ordering, establish unrestricted-root center localization,
or address the chromatic lower tail, partial diagonals, skeletons, second
moments, or the final Erdős statement.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Quadratic main term in the signed four-size derivative along the exact
integer phase. -/
noncomputable def signedFourDerivativeQuadraticMain (n : ℕ) : ℝ :=
  q / 2 * (phaseNat n : ℝ) ^ 2

/-- A coarse but uniform `O(log n)` derivative radius.  The coefficient `13`
absorbs two phase terms, one logarithmic part-count term, and the finite
factorial constant; `5*C` absorbs the compact tilt and partition bounds. -/
noncomputable def signedFourDerivativeCorridorRadius
    (C : ℝ) (n : ℕ) : ℝ :=
  (13 + 5 * C + |q|) * logOrder n

noncomputable def signedFourDerivativeSlopeLower
    (C : ℝ) (n : ℕ) : ℝ :=
  signedFourDerivativeQuadraticMain n -
    signedFourDerivativeCorridorRadius C n

noncomputable def signedFourDerivativeSlopeUpper
    (C : ℝ) (n : ℕ) : ℝ :=
  signedFourDerivativeQuadraticMain n +
    signedFourDerivativeCorridorRadius C n

/-- The compact deficit-target corridor and the usual phase range force every
positive admissible real part count into `[1,n]`. -/
theorem one_le_parts_and_parts_le_natCast_of_fourSizeTarget_mem_admissibilityCorridor
    (n alpha : ℕ) (parts : ℝ)
    (halpha : 6 ≤ alpha) (hTwo : 2 * alpha ≤ n)
    (hparts : 0 < parts)
    (hTarget : fourSizeTarget n alpha parts ∈
      signedFourAdmissibilityTargetCorridor) :
    1 ≤ parts ∧ parts ≤ (n : ℝ) := by
  have hn : 0 < n := by omega
  have halphaReal : (6 : ℝ) ≤ (alpha : ℝ) := by
    exact_mod_cast halpha
  have hTargetBounds := hTarget
  simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hTargetBounds
  unfold fourSizeTarget at hTargetBounds
  have hRatioLower : 1 ≤ (n : ℝ) / parts := by
    linarith [hTargetBounds.2]
  have hPartsUpper : parts ≤ (n : ℝ) := by
    have h := (le_div_iff₀ hparts).mp hRatioLower
    simpa only [one_mul] using h
  have hRatioUpper : (n : ℝ) / parts ≤ (alpha : ℝ) := by
    linarith [hTargetBounds.1]
  have hAlphaN : (alpha : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show alpha ≤ n by omega)
  have hMul : (n : ℝ) ≤ (n : ℝ) * parts :=
    (div_le_iff₀ hparts).mp (hRatioUpper.trans hAlphaN)
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  constructor
  · nlinarith
  · exact hPartsUpper

/-- Hence the part-count logarithm is bounded by the ambient logarithmic
order. -/
theorem abs_log_parts_le_logOrder_of_range
    (n : ℕ) (parts : ℝ) (hparts : 0 < parts)
    (hRange : 1 ≤ parts ∧ parts ≤ (n : ℝ)) :
    |Real.log parts| ≤ logOrder n := by
  have hLogNonneg : 0 ≤ Real.log parts := Real.log_nonneg hRange.1
  have hLogUpper : Real.log parts ≤ Real.log (n : ℝ) :=
    Real.log_le_log hparts hRange.2
  rw [abs_of_nonneg hLogNonneg]
  simpa only [logOrder] using hLogUpper

/-- The explicit factorial-log error is at most the phase plus four. -/
theorem factorialLogErrorBound_le_cast_add_four (alpha : ℕ) :
    factorialLogErrorBound alpha ≤ (alpha : ℝ) + 4 := by
  have hLog := Real.log_le_sub_one_of_pos
    (show 0 < (alpha : ℝ) + 1 by positivity)
  unfold factorialLogErrorBound
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Finite uniform derivative error bound on the compact target corridor. -/
theorem abs_signedFourSizeObjectiveDerivative_sub_quadraticMain_le_corridorRadius
    (n alpha : ℕ) (parts C : ℝ)
    (hC : 0 ≤ C)
    (halpha : 6 ≤ alpha) (hTwo : 2 * alpha ≤ n)
    (hAlphaLog : (alpha : ℝ) ≤ 4 * logOrder n)
    (hLogOne : 1 ≤ logOrder n)
    (hparts : 0 < parts)
    (hTarget : fourSizeTarget n alpha parts ∈
      signedFourAdmissibilityTargetCorridor)
    (hProfile :
      |ProfileEntropyS4.tilt (fourDeficitScore alpha)
          (fourSizeTarget n alpha parts)| ≤ C ∧
      |Real.log
        (ProfileEntropyS4.partition (fourDeficitScore alpha)
          (ProfileEntropyS4.tilt (fourDeficitScore alpha)
            (fourSizeTarget n alpha parts)))| ≤ C) :
    |signedFourSizeObjectiveDerivative n alpha parts -
        q / 2 * (alpha : ℝ) ^ 2| ≤
      (13 + 5 * C + |q|) * logOrder n := by
  have halphaPos : 0 < alpha := by omega
  have hBase :=
    abs_signedFourSizeObjectiveDerivative_sub_quadraticMain_le
      n alpha parts halphaPos
  have hRange :=
    one_le_parts_and_parts_le_natCast_of_fourSizeTarget_mem_admissibilityCorridor
      n alpha parts halpha hTwo hparts hTarget
  have hLogParts :=
    abs_log_parts_le_logOrder_of_range n parts hparts hRange
  have hFactorial := factorialLogErrorBound_le_cast_add_four alpha
  have hTiltTerm :
      |ProfileEntropyS4.tilt (fourDeficitScore alpha)
          (fourSizeTarget n alpha parts)| * (alpha : ℝ) ≤
        C * (alpha : ℝ) :=
    mul_le_mul_of_nonneg_right hProfile.1 (Nat.cast_nonneg alpha)
  have hRemainder :
      (alpha : ℝ) + |Real.log parts| +
          |ProfileEntropyS4.tilt (fourDeficitScore alpha)
              (fourSizeTarget n alpha parts)| * (alpha : ℝ) +
          |Real.log
            (ProfileEntropyS4.partition (fourDeficitScore alpha)
              (ProfileEntropyS4.tilt (fourDeficitScore alpha)
                (fourSizeTarget n alpha parts)))| + |q| ≤
        (alpha : ℝ) + logOrder n + C * (alpha : ℝ) + C + |q| := by
    linarith [hLogParts, hTiltTerm, hProfile.2]
  have hCPhase : C * (alpha : ℝ) ≤ C * (4 * logOrder n) :=
    mul_le_mul_of_nonneg_left hAlphaLog hC
  have hConstantNonneg : 0 ≤ 4 + C + |q| := by
    positivity
  have hConstantScale :
      4 + C + |q| ≤ (4 + C + |q|) * logOrder n := by
    calc
      4 + C + |q| = (4 + C + |q|) * 1 := by ring
      _ ≤ (4 + C + |q|) * logOrder n :=
        mul_le_mul_of_nonneg_left hLogOne hConstantNonneg
  calc
    |signedFourSizeObjectiveDerivative n alpha parts -
        q / 2 * (alpha : ℝ) ^ 2| ≤
      factorialLogErrorBound alpha +
        ((alpha : ℝ) + |Real.log parts| +
          |ProfileEntropyS4.tilt (fourDeficitScore alpha)
              (fourSizeTarget n alpha parts)| * (alpha : ℝ) +
          |Real.log
            (ProfileEntropyS4.partition (fourDeficitScore alpha)
              (ProfileEntropyS4.tilt (fourDeficitScore alpha)
                (fourSizeTarget n alpha parts)))| + |q|) := hBase
    _ ≤ ((alpha : ℝ) + 4) +
        ((alpha : ℝ) + logOrder n + C * (alpha : ℝ) + C + |q|) :=
      add_le_add hFactorial hRemainder
    _ ≤ (13 + 5 * C + |q|) * logOrder n := by
      nlinarith [hAlphaLog, hCPhase, hConstantScale]

/-- One compactness constant controls the derivative error for all positive
part counts with target in the manuscript corridor. -/
theorem exists_eventually_uniform_signedFourDerivative_corridorRadius :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ parts : ℝ,
          0 < parts →
          fourSizeTarget n (phaseNat n) parts ∈
            signedFourAdmissibilityTargetCorridor →
          |signedFourSizeObjectiveDerivative n (phaseNat n) parts -
              signedFourDerivativeQuadraticMain n| ≤
            signedFourDerivativeCorridorRadius C n := by
  obtain ⟨C, hC, hProfile⟩ :=
    exists_eventually_uniform_phaseFourDeficit_tilt_and_logPartition_bound
  refine ⟨C, hC, ?_⟩
  have hLogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [hProfile,
    eventually_five_lt_phaseNat,
    eventually_two_mul_phaseNat_le,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hLogOne] with n hnProfile hnPhase hnTwo hnPhaseLog hnLogOne
  intro parts hparts hTarget
  have hFinite :=
    abs_signedFourSizeObjectiveDerivative_sub_quadraticMain_le_corridorRadius
      n (phaseNat n) parts C hC (by omega) hnTwo hnPhaseLog.2
      hnLogOne hparts hTarget (hnProfile _ hTarget)
  simpa only [signedFourDerivativeQuadraticMain,
    signedFourDerivativeCorridorRadius] using hFinite

/-- Exact ratio asymptotic for the integer phase. -/
theorem tendsto_phaseNat_cast_div_logOrder :
    Tendsto (fun n : ℕ ↦ (phaseNat n : ℝ) / logOrder n)
      atTop (𝓝 (2 / q)) := by
  have hDenom : ∀ᶠ n : ℕ in atTop,
      (2 / q) * logOrder n ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hlog : 0 < logOrder n :=
      Real.log_pos (by exact_mod_cast hn)
    exact mul_ne_zero (div_ne_zero (by norm_num) q_ne_zero) hlog.ne'
  have hRatioOne : Tendsto
      ((fun n : ℕ ↦ (phaseNat n : ℝ)) /
        (fun n : ℕ ↦ (2 / q) * logOrder n))
      atTop (𝓝 1) :=
    (isEquivalent_iff_tendsto_one hDenom).mp
      phaseNat_isEquivalent_scaled_logOrder
  have hScaled := hRatioOne.const_mul (2 / q)
  convert hScaled using 1
  · funext n
    by_cases hlog : logOrder n = 0
    · simp [hlog]
    · change (phaseNat n : ℝ) / logOrder n =
          (2 / q) *
            ((phaseNat n : ℝ) / ((2 / q) * logOrder n))
      field_simp [q_ne_zero]
  · simp

/-- The normalized quadratic main derivative converges to the manuscript
coefficient `2/q`. -/
theorem tendsto_signedFourNormalizedDerivativeQuadraticMain :
    Tendsto
      (signedFourNormalizedSlope signedFourDerivativeQuadraticMain)
      atTop (𝓝 (2 / q)) := by
  have h := (tendsto_phaseNat_cast_div_logOrder.pow 2).const_mul (q / 2)
  have hLimit : q / 2 * (2 / q) ^ 2 = 2 / q := by
    field_simp [q_ne_zero]
    ring
  rw [hLimit] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope signedFourDerivativeQuadraticMain
  field_simp [hlog]
  ring

/-- The normalized corridor radius vanishes. -/
theorem tendsto_signedFourNormalizedDerivativeCorridorRadius_zero
    (C : ℝ) :
    Tendsto
      (signedFourNormalizedSlope
        (signedFourDerivativeCorridorRadius C))
      atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (logOrder n)⁻¹)
      atTop (𝓝 0) :=
    tendsto_logOrder_atTop.inv_tendsto_atTop
  have h := hInv.const_mul (13 + 5 * C + |q|)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope signedFourDerivativeCorridorRadius
  field_simp [hlog]
  ring

/-- Both explicit derivative corridor slopes have the required normalized
limit. -/
theorem tendsto_signedFourNormalizedDerivativeSlopeLower
    (C : ℝ) :
    Tendsto
      (signedFourNormalizedSlope
        (signedFourDerivativeSlopeLower C))
      atTop (𝓝 (2 / q)) := by
  have h := tendsto_signedFourNormalizedDerivativeQuadraticMain.sub
    (tendsto_signedFourNormalizedDerivativeCorridorRadius_zero C)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope signedFourDerivativeSlopeLower
    signedFourDerivativeQuadraticMain signedFourDerivativeCorridorRadius
  field_simp [hlog]
  ring

theorem tendsto_signedFourNormalizedDerivativeSlopeUpper
    (C : ℝ) :
    Tendsto
      (signedFourNormalizedSlope
        (signedFourDerivativeSlopeUpper C))
      atTop (𝓝 (2 / q)) := by
  have h := tendsto_signedFourNormalizedDerivativeQuadraticMain.add
    (tendsto_signedFourNormalizedDerivativeCorridorRadius_zero C)
  simp only [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hlog : logOrder n ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  unfold signedFourNormalizedSlope signedFourDerivativeSlopeUpper
    signedFourDerivativeQuadraticMain signedFourDerivativeCorridorRadius
  field_simp [hlog]
  ring

/-- Concrete lower and upper derivative corridors, with matching normalized
limits, valid uniformly throughout the compact manuscript target corridor. -/
theorem exists_signedFourDerivativeCorridor :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ n : ℕ in atTop,
        ∀ parts : ℝ,
          0 < parts →
          fourSizeTarget n (phaseNat n) parts ∈
            signedFourAdmissibilityTargetCorridor →
          signedFourDerivativeSlopeLower C n ≤
              signedFourSizeObjectiveDerivative n (phaseNat n) parts ∧
            signedFourSizeObjectiveDerivative n (phaseNat n) parts ≤
              signedFourDerivativeSlopeUpper C n) ∧
      Tendsto
        (signedFourNormalizedSlope
          (signedFourDerivativeSlopeLower C))
        atTop (𝓝 (2 / q)) ∧
      Tendsto
        (signedFourNormalizedSlope
          (signedFourDerivativeSlopeUpper C))
        atTop (𝓝 (2 / q)) := by
  obtain ⟨C, hC, hError⟩ :=
    exists_eventually_uniform_signedFourDerivative_corridorRadius
  refine ⟨C, hC, ?_,
    tendsto_signedFourNormalizedDerivativeSlopeLower C,
    tendsto_signedFourNormalizedDerivativeSlopeUpper C⟩
  filter_upwards [hError] with n hn
  intro parts hparts hTarget
  have hAbs := hn parts hparts hTarget
  rw [abs_le] at hAbs
  unfold signedFourDerivativeSlopeLower signedFourDerivativeSlopeUpper
    signedFourDerivativeQuadraticMain signedFourDerivativeCorridorRadius
  constructor <;> linarith [hAbs.1, hAbs.2]

/-- E625-10 with the derivative corridor and both slope limits constructed
internally from the exact finite four-size calculus. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_positiveGap_rootEquations_centerLocalization_and_compactFeasibility
    (rCo rPlus : ℕ → ℝ)
    (hRightCenter : signedFourNormalizedRightRootCenterDisplacement rPlus
      =O[atTop] logLogOrder)
    (hGap : ∀ᶠ n : ℕ in atTop, 0 < rPlus n - rCo n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧
          fourSizeTarget n (phaseNat n) s ∈
            signedFourAdmissibilityTargetCorridor)
    (hCoRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hPlusRoot : ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (rPlus n) = 0) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  obtain ⟨C, _hC, hDerivative, hSlopeLower, hSlopeUpper⟩ :=
    exists_signedFourDerivativeCorridor
  have hFeasibleIoo : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5 := by
    filter_upwards [hFeasible] with n hn
    intro s hs
    exact ⟨(hn s hs).1,
      signedFourAdmissibilityTargetCorridor_subset_Ioo (hn s hs).2⟩
  have hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourDerivativeSlopeLower C n ≤
          signedFourSizeObjectiveDerivative n (phaseNat n) s := by
    filter_upwards [hFeasible, hDerivative] with n hnFeasible hnDerivative
    intro s hs
    have hsClosed : s ∈ Icc (rCo n) (rPlus n) :=
      Ioo_subset_Icc_self hs
    exact (hnDerivative s (hnFeasible s hsClosed).1
      (hnFeasible s hsClosed).2).1
  have hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤
          signedFourDerivativeSlopeUpper C n := by
    filter_upwards [hFeasible, hDerivative] with n hnFeasible hnDerivative
    intro s hs
    have hsClosed : s ∈ Icc (rCo n) (rPlus n) :=
      Ioo_subset_Icc_self hs
    exact (hnDerivative s (hnFeasible s hsClosed).1
      (hnFeasible s hsClosed).2).2
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_positiveGap_rootEquations_centerLocalization_and_derivativeCorridor
      rCo rPlus
      (signedFourDerivativeSlopeLower C)
      (signedFourDerivativeSlopeUpper C)
      hRightCenter hGap hFeasibleIoo hDerivLower hDerivUpper
      hCoRoot hPlusRoot hSlopeLower hSlopeUpper

#print axioms one_le_parts_and_parts_le_natCast_of_fourSizeTarget_mem_admissibilityCorridor
#print axioms abs_log_parts_le_logOrder_of_range
#print axioms factorialLogErrorBound_le_cast_add_four
#print axioms abs_signedFourSizeObjectiveDerivative_sub_quadraticMain_le_corridorRadius
#print axioms exists_eventually_uniform_signedFourDerivative_corridorRadius
#print axioms tendsto_phaseNat_cast_div_logOrder
#print axioms tendsto_signedFourNormalizedDerivativeQuadraticMain
#print axioms tendsto_signedFourNormalizedDerivativeCorridorRadius_zero
#print axioms tendsto_signedFourNormalizedDerivativeSlopeLower
#print axioms tendsto_signedFourNormalizedDerivativeSlopeUpper
#print axioms exists_signedFourDerivativeCorridor
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_positiveGap_rootEquations_centerLocalization_and_compactFeasibility

end

end Erdos625
