import Erdos625.UnrestrictedPhaseRootConstructionCorridor
import Erdos625.PhaseRootObjectiveCenterBound
import Erdos625.UnrestrictedPhaseRootCenterLocalization
import Erdos625.DeficitTargetDomain
import Mathlib.Tactic

/-!
# Construction and localization of the unrestricted phase root

The unrestricted objective at the exact manuscript center, divided by the
center, is `O(log log n)` and hence `o(log n)`.  The concrete unrestricted
derivative floor has normalized limit `2/q`, while the explicit construction
radius is `phaseRootCenter/(10*phaseNat)`.  Since `phaseNat <= 4 log n`
eventually, the integrated derivative margin across that radius is a fixed
multiple of `phaseRootCenter * log n`, and therefore dominates the center
residual.

This module instantiates the finite unrestricted-root IVT theorem, selects the
unique root in the construction corridor, proves its exact equation and
corridor data eventually, and derives the manuscript `O(log log n)` center
localization on the natural `n/(log n)^3` scale.

No signed root, signed/unrestricted root ordering, chromatic lower tail,
partial diagonal, skeleton, second moment, or final Erdős statement is proved
here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The normalized unrestricted center residual is little-o of `log n`. -/
theorem unrestrictedPhaseObjective_center_div_isLittleO_logOrder :
    (fun n : ℕ ↦
        unrestrictedPhaseObjective n (phaseRootCenter n) /
          phaseRootCenter n) =o[atTop] logOrder :=
  unrestrictedPhaseObjective_center_div_isBigO_logLogOrder.trans_isLittleO
    logLogOrder_isLittleO_logOrder

/-- A concrete center-value envelope small enough for the construction
corridor. -/
noncomputable def unrestrictedPhaseRootCenterEnvelope (n : ℕ) : ℝ :=
  phaseRootCenter n * ((1 / (100 * q)) * logOrder n)

private theorem unrestrictedPhaseRootCenterCoefficient_pos :
    0 < (1 / (100 * q) : ℝ) := by
  exact one_div_pos.mpr (mul_pos (by norm_num) q_pos)

private theorem unrestrictedPhaseRootCenterEnvelope_nonneg
    (n : ℕ) (hCenter : 0 ≤ phaseRootCenter n)
    (hLog : 0 ≤ logOrder n) :
    0 ≤ unrestrictedPhaseRootCenterEnvelope n := by
  unfold unrestrictedPhaseRootCenterEnvelope
  exact mul_nonneg hCenter
    (mul_nonneg unrestrictedPhaseRootCenterCoefficient_pos.le hLog)

/-- The exact unrestricted objective at the center is eventually bounded by
the explicit construction envelope. -/
theorem eventually_abs_unrestrictedPhaseObjective_center_le_envelope :
    ∀ᶠ n : ℕ in atTop,
      |unrestrictedPhaseObjective n (phaseRootCenter n)| ≤
        unrestrictedPhaseRootCenterEnvelope n := by
  have hEpsilon : 0 < (1 / (100 * q) : ℝ) :=
    unrestrictedPhaseRootCenterCoefficient_pos
  have hBound :=
    unrestrictedPhaseObjective_center_div_isLittleO_logOrder.bound hEpsilon
  filter_upwards [hBound, eventually_phaseRootCenter_pos,
    eventually_gt_atTop (1 : ℕ)] with n hn hCenterPos hnOne
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hnOne)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogPos] at hn
  have hRatioAbs :
      |unrestrictedPhaseObjective n (phaseRootCenter n) /
          phaseRootCenter n| =
        |unrestrictedPhaseObjective n (phaseRootCenter n)| /
          phaseRootCenter n := by
    rw [abs_div, abs_of_pos hCenterPos]
  calc
    |unrestrictedPhaseObjective n (phaseRootCenter n)| =
        phaseRootCenter n *
          (|unrestrictedPhaseObjective n (phaseRootCenter n)| /
            phaseRootCenter n) := by
      field_simp [hCenterPos.ne']
    _ = phaseRootCenter n *
        |unrestrictedPhaseObjective n (phaseRootCenter n) /
          phaseRootCenter n| := by rw [hRatioAbs]
    _ ≤ phaseRootCenter n *
        ((1 / (100 * q)) * logOrder n) :=
      mul_le_mul_of_nonneg_left hn hCenterPos.le
    _ = unrestrictedPhaseRootCenterEnvelope n := rfl

/-- The explicit center envelope is eventually strictly smaller than the
integrated concrete derivative floor across the construction radius. -/
theorem
    eventually_unrestrictedPhaseRootCenterEnvelope_lt_slopeLower_mul_radius
    (C : ℝ)
    (hSlope : Tendsto
      (signedFourNormalizedSlope (unrestrictedDerivativeSlopeLower C))
      atTop (𝓝 (2 / q))) :
    ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseRootCenterEnvelope n <
        unrestrictedDerivativeSlopeLower C n *
          unrestrictedPhaseRootConstructionRadius n := by
  have hLimitLower : (1 / q : ℝ) < 2 / q := by
    rw [div_lt_div_iff_of_pos_right q_pos]
    norm_num
  have hSlopeBand : ∀ᶠ n : ℕ in atTop,
      1 / q <
        signedFourNormalizedSlope
          (unrestrictedDerivativeSlopeLower C) n :=
    hSlope.eventually (Ioi_mem_nhds hLimitLower)
  filter_upwards [hSlopeBand,
    eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible,
    eventually_phaseRootCenter_pos,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    eventually_five_lt_phaseNat, eventually_gt_atTop (1 : ℕ)] with
    n hnSlope hnConstruction hCenterPos hnPhaseLog hnPhase hnOne
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hnOne)
  have hlogSqPos : 0 < (logOrder n) ^ 2 := pow_pos hlogPos 2
  have hAlphaPos : 0 < (phaseNat n : ℝ) := by
    exact_mod_cast (show 0 < phaseNat n by omega)
  have hSlopeMain :
      (1 / q) * (logOrder n) ^ 2 <
        unrestrictedDerivativeSlopeLower C n := by
    unfold signedFourNormalizedSlope at hnSlope
    exact (lt_div_iff₀ hlogSqPos).mp hnSlope
  have hPhaseDenomPos : 0 < 10 * (phaseNat n : ℝ) :=
    mul_pos (by norm_num) hAlphaPos
  have hRatio :
      (1 / 40 : ℝ) ≤
        logOrder n / (10 * (phaseNat n : ℝ)) := by
    rw [le_div_iff₀ hPhaseDenomPos]
    nlinarith [hnPhaseLog.2]
  have hBaseNonneg :
      0 ≤ phaseRootCenter n * logOrder n / q :=
    div_nonneg (mul_nonneg hCenterPos.le hlogPos.le) q_pos.le
  have hGeometric :
      phaseRootCenter n * logOrder n / (40 * q) ≤
        ((1 / q) * (logOrder n) ^ 2) *
          unrestrictedPhaseRootConstructionRadius n := by
    calc
      phaseRootCenter n * logOrder n / (40 * q) =
          (phaseRootCenter n * logOrder n / q) * (1 / 40) := by
        field_simp [q_ne_zero]
      _ ≤ (phaseRootCenter n * logOrder n / q) *
          (logOrder n / (10 * (phaseNat n : ℝ))) :=
        mul_le_mul_of_nonneg_left hRatio hBaseNonneg
      _ = ((1 / q) * (logOrder n) ^ 2) *
          unrestrictedPhaseRootConstructionRadius n := by
        unfold unrestrictedPhaseRootConstructionRadius
        field_simp [q_ne_zero, hAlphaPos.ne']
  have hIntegrated :
      phaseRootCenter n * logOrder n / (40 * q) <
        unrestrictedDerivativeSlopeLower C n *
          unrestrictedPhaseRootConstructionRadius n := by
    exact hGeometric.trans_lt
      (mul_lt_mul_of_pos_right hSlopeMain hnConstruction.1)
  have h100qPos : 0 < (100 : ℝ) * q :=
    mul_pos (by norm_num) q_pos
  have h40qPos : 0 < (40 : ℝ) * q :=
    mul_pos (by norm_num) q_pos
  have hCoefficient :
      (1 / (100 * q) : ℝ) < 1 / (40 * q) := by
    rw [div_lt_div_iff₀ h100qPos h40qPos]
    nlinarith [q_pos]
  have hBasePos : 0 < phaseRootCenter n * logOrder n :=
    mul_pos hCenterPos hlogPos
  calc
    unrestrictedPhaseRootCenterEnvelope n =
        (phaseRootCenter n * logOrder n) * (1 / (100 * q)) := by
      unfold unrestrictedPhaseRootCenterEnvelope
      ring
    _ < (phaseRootCenter n * logOrder n) * (1 / (40 * q)) :=
      mul_lt_mul_of_pos_left hCoefficient hBasePos
    _ = phaseRootCenter n * logOrder n / (40 * q) := by ring
    _ < unrestrictedDerivativeSlopeLower C n *
          unrestrictedPhaseRootConstructionRadius n := hIntegrated

/-- Complete finite data returned for the selected unrestricted root. -/
def UnrestrictedPhaseRootData (n : ℕ) (r : ℝ) : Prop :=
  r ∈ Ioo
      (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
      (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n) ∧
    0 < r ∧
    profileDeficitTarget (phaseNat n) (n : ℝ) r ∈
      signedFourAdmissibilityTargetCorridor ∧
    unrestrictedPhaseObjective n r = 0

/-- The concrete derivative corridor and center envelope produce a unique
unrestricted root in the explicit construction interval eventually. -/
theorem eventually_existsUnique_unrestrictedPhaseRootData :
    ∀ᶠ n : ℕ in atTop,
      ∃! r : ℝ, UnrestrictedPhaseRootData n r := by
  obtain ⟨C, _hC, hDerivative, hSlopeLower, _hSlopeUpper⟩ :=
    exists_unrestrictedDerivativeCorridor
  have hMargin :=
    eventually_unrestrictedPhaseRootCenterEnvelope_lt_slopeLower_mul_radius
      C hSlopeLower
  filter_upwards [
    eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible,
    eventually_phaseRootCenter_pos,
    eventually_abs_unrestrictedPhaseObjective_center_le_envelope,
    hDerivative, hMargin, eventually_five_lt_phaseNat,
    eventually_gt_atTop (1 : ℕ)] with
    n hnConstruction hCenterPos hnCenter hnDerivative hnMargin
      hnPhase hnOne
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hnOne)
  have hEnvelopeNonneg :
      0 ≤ unrestrictedPhaseRootCenterEnvelope n :=
    unrestrictedPhaseRootCenterEnvelope_nonneg
      n hCenterPos.le hlogPos.le
  have hProductPos :
      0 < unrestrictedDerivativeSlopeLower C n *
        unrestrictedPhaseRootConstructionRadius n :=
    lt_of_le_of_lt hEnvelopeNonneg hnMargin
  have hSlopePos : 0 < unrestrictedDerivativeSlopeLower C n := by
    rcases mul_pos_iff.mp hProductPos with h | h
    · exact h.1
    · exact (not_lt_of_ge hnConstruction.1.le h.2).elim
  have hDerivLower :
      ∀ s ∈ Ioo
          (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
          (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n),
        unrestrictedDerivativeSlopeLower C n ≤
          deriv (unrestrictedPhaseObjective n) s := by
    intro s hs
    have hsData := hnConstruction.2 s (Ioo_subset_Icc_self hs)
    exact (hnDerivative s hsData.1 hsData.2).1
  simpa only [UnrestrictedPhaseRootData] using
    existsUnique_unrestrictedPhaseRoot_of_center_and_deriv_lower
      n (phaseRootCenter n)
      (unrestrictedPhaseRootConstructionRadius n)
      (unrestrictedPhaseRootCenterEnvelope n)
      (unrestrictedDerivativeSlopeLower C n)
      (by omega) hnConstruction.1 hSlopePos hnMargin hnCenter
      hnConstruction.2 hDerivLower

/-- A total selected unrestricted root, with the phase center used only as a
fallback outside the eventual construction range. -/
noncomputable def unrestrictedPhaseRoot (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, UnrestrictedPhaseRootData n r then
    Classical.choose h
  else
    phaseRootCenter n

/-- Selection correctness whenever unrestricted-root data exists. -/
theorem unrestrictedPhaseRoot_spec_of_exists
    (n : ℕ) (h : ∃ r : ℝ, UnrestrictedPhaseRootData n r) :
    UnrestrictedPhaseRootData n (unrestrictedPhaseRoot n) := by
  classical
  rw [unrestrictedPhaseRoot, dif_pos h]
  exact Classical.choose_spec h

/-- The selected unrestricted root has all construction data eventually. -/
theorem eventually_unrestrictedPhaseRootData :
    ∀ᶠ n : ℕ in atTop,
      UnrestrictedPhaseRootData n (unrestrictedPhaseRoot n) := by
  filter_upwards [eventually_existsUnique_unrestrictedPhaseRootData] with n hn
  exact unrestrictedPhaseRoot_spec_of_exists n hn.exists

/-- In particular, the selected unrestricted root satisfies its exact phase
objective equation eventually. -/
theorem eventually_unrestrictedPhaseRoot_equation :
    ∀ᶠ n : ℕ in atTop,
      unrestrictedPhaseObjective n (unrestrictedPhaseRoot n) = 0 :=
  eventually_unrestrictedPhaseRootData.mono fun _ hn ↦ hn.2.2.2

/-- Construction feasibility and the concrete derivative floor imply the
manuscript `O(log log n)` localization of the selected unrestricted root. -/
theorem unrestrictedPhaseRoot_centerLocalization :
    signedFourNormalizedRightRootCenterDisplacement unrestrictedPhaseRoot
      =O[atTop] logLogOrder := by
  obtain ⟨C, _hC, hDerivative, hSlopeLower, _hSlopeUpper⟩ :=
    exists_unrestrictedDerivativeCorridor
  have hSegmentData : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (min (phaseRootCenter n) (unrestrictedPhaseRoot n))
          (max (phaseRootCenter n) (unrestrictedPhaseRoot n)),
        0 < s ∧
          profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
            signedFourAdmissibilityTargetCorridor := by
    filter_upwards [eventually_unrestrictedPhaseRootData,
      eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible]
      with n hnRoot hnConstruction
    intro s hs
    have hLower :
        phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n ≤
          min (phaseRootCenter n) (unrestrictedPhaseRoot n) := by
      exact le_min
        (by linarith [hnConstruction.1]) hnRoot.1.1.le
    have hUpper :
        max (phaseRootCenter n) (unrestrictedPhaseRoot n) ≤
          phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n := by
      exact max_le
        (by linarith [hnConstruction.1]) hnRoot.1.2.le
    exact hnConstruction.2 s
      ⟨hLower.trans hs.1, hs.2.trans hUpper⟩
  have hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (min (phaseRootCenter n) (unrestrictedPhaseRoot n))
          (max (phaseRootCenter n) (unrestrictedPhaseRoot n)),
        0 < s ∧
          (n : ℝ) / s ∈
            Ioo (1 : ℝ) ((((phaseNat n) + 1 : ℕ) : ℝ)) := by
    filter_upwards [hSegmentData, eventually_five_lt_phaseNat] with
      n hnSegment hnPhase
    intro s hs
    have hsData := hnSegment s hs
    have hDeficitInterior :
        profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
          Ioo (-1 : ℝ) ((phaseNat n : ℝ) - 1) := by
      have hBounds := hsData.2
      simp only [signedFourAdmissibilityTargetCorridor, mem_Icc] at hBounds
      have hPhaseReal : (6 : ℝ) ≤ (phaseNat n : ℝ) := by
        exact_mod_cast (show 6 ≤ phaseNat n by omega)
      constructor <;> linarith
    exact ⟨hsData.1,
      (phaseDeficitTarget_domain_coordinates hDeficitInterior).1⟩
  have hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (min (phaseRootCenter n) (unrestrictedPhaseRoot n))
          (max (phaseRootCenter n) (unrestrictedPhaseRoot n)),
        unrestrictedDerivativeSlopeLower C n ≤
          deriv (unrestrictedPhaseObjective n) s := by
    filter_upwards [hSegmentData, hDerivative] with
      n hnSegment hnDerivative
    intro s hs
    have hsData := hnSegment s (Ioo_subset_Icc_self hs)
    exact (hnDerivative s hsData.1 hsData.2).1
  exact
    signedFourNormalizedRightRootCenterDisplacement_isBigO_logLogOrder
      unrestrictedPhaseRoot (unrestrictedDerivativeSlopeLower C)
      hFeasible hDerivLower eventually_unrestrictedPhaseRoot_equation
      hSlopeLower

#print axioms unrestrictedPhaseObjective_center_div_isLittleO_logOrder
#print axioms eventually_abs_unrestrictedPhaseObjective_center_le_envelope
#print axioms eventually_unrestrictedPhaseRootCenterEnvelope_lt_slopeLower_mul_radius
#print axioms eventually_existsUnique_unrestrictedPhaseRootData
#print axioms unrestrictedPhaseRoot_spec_of_exists
#print axioms eventually_unrestrictedPhaseRootData
#print axioms eventually_unrestrictedPhaseRoot_equation
#print axioms unrestrictedPhaseRoot_centerLocalization

end

end Erdos625
