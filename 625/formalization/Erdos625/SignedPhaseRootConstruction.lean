import Erdos625.UnrestrictedPhaseRootConstruction
import Erdos625.PhaseSignedFourSizeRootCorridor
import Erdos625.SignedFourDerivativeCorridor
import Erdos625.SignedUnrestrictedObjectiveGapIdentity
import Erdos625.NormalizedRootGapAssembly
import Mathlib.Tactic

/-!
# Construction of the signed four-size phase root

The signed objective is constructed in the same broad part-count corridor as
the unrestricted objective.  At the manuscript phase center its difference
from the unrestricted objective is the exact finite signed margin.  Compact-
uniform convergence bounds that margin, while the signed derivative corridor
provides an integrated margin of order `phaseRootCenter * log n`.

This module constructs and selects the unique signed root in the broad
corridor.  Root ordering, inter-root feasibility, the root-gap asymptotic, and
the final signed first-moment instantiation are deliberately left to the next
short assembly layer.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Along the exact phase target, the finite signed margin converges to the
phase-varying limiting margin. -/
theorem tendsto_phaseFiniteSignedFourMargin_sub_phaseMargin :
    Tendsto
      (fun n : ℕ ↦
        finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n) -
          signedFourPhaseMargin n)
      atTop (𝓝 0) := by
  have hTarget : ∀ᶠ n : ℕ in atTop,
      signedFourPhaseTarget n ∈ Icc (5 / 2 : ℝ) (9 / 2 : ℝ) :=
    Filter.Eventually.of_forall
      signedFourPhaseTarget_mem_admissibilityTargetCorridor
  have hLimiting : Tendsto
      (fun n : ℕ ↦
        (q - fourEntropyLoss (signedFourPhaseTarget n)) -
          signedFourPhaseMargin n)
      atTop (𝓝 0) := by
    have hZero : Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    exact hZero.congr' (Filter.Eventually.of_forall fun n ↦ by
      unfold signedFourPhaseMargin
      ring)
  exact
    tendsto_finiteSignedFourMargin_sub_phaseMargin_of_compactTarget
      (by norm_num : (2 : ℝ) < 5 / 2)
      (by norm_num : (5 / 2 : ℝ) ≤ 9 / 2)
      (by norm_num : (9 / 2 : ℝ) < 5)
      phaseNat signedFourPhaseTarget tendsto_phaseNat_atTop_nat
      hTarget hLimiting

/-- The exact finite signed margin at the phase target is eventually bounded
by the limiting upper bound plus one. -/
theorem eventually_abs_phaseFiniteSignedFourMargin_le_q_add_one :
    ∀ᶠ n : ℕ in atTop,
      |finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n)| ≤
        q + 1 := by
  have hClose : ∀ᶠ n : ℕ in atTop,
      finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n) -
          signedFourPhaseMargin n ∈ Ioo (-1 : ℝ) 1 :=
    tendsto_phaseFiniteSignedFourMargin_sub_phaseMargin.eventually
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hClose] with n hn
  have hPhase := signedFourPhaseMargin_mem_Icc n
  rw [abs_le]
  constructor
  · have hFiniteLower :
        (-1 : ℝ) <
          finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n) := by
      linarith [hn.1, hPhase.1]
    have hEnvelopeLower : -(q + 1) ≤ (-1 : ℝ) := by
      linarith [q_pos]
    exact hEnvelopeLower.trans hFiniteLower.le
  · have hFiniteUpper :
        finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n) <
          q + 1 := by
      linarith [hn.2, hPhase.2]
    exact hFiniteUpper.le

/-- Exact finite signed objective at the phase center: unrestricted residual
plus the phase-center part count times the finite signed margin. -/
theorem phaseSignedFourSizeObjective_phaseRootCenter_eq
    (n : ℕ) (hn : PhaseDomain n)
    (hCenterPos : 0 < phaseRootCenter n) :
    phaseSignedFourSizeObjective n (phaseRootCenter n) =
      unrestrictedPhaseObjective n (phaseRootCenter n) +
        phaseRootCenter n *
          finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n) := by
  have hGap :=
    phaseSignedFourSizeObjective_div_sub_unrestrictedPhaseObjective_div_eq_finiteMargin
      n hCenterPos.ne'
  have hTarget :
      fourSizeTarget n (phaseNat n) (phaseRootCenter n) =
        signedFourPhaseTarget n := by
    unfold fourSizeTarget
    simpa only [signedFourPhaseTarget] using phaseRoot_target_identity hn
  rw [hTarget] at hGap
  calc
    phaseSignedFourSizeObjective n (phaseRootCenter n) =
        unrestrictedPhaseObjective n (phaseRootCenter n) +
          phaseRootCenter n *
            (phaseSignedFourSizeObjective n (phaseRootCenter n) /
                phaseRootCenter n -
              unrestrictedPhaseObjective n (phaseRootCenter n) /
                phaseRootCenter n) := by
      field_simp [hCenterPos.ne']
      ring
    _ = unrestrictedPhaseObjective n (phaseRootCenter n) +
        phaseRootCenter n *
          finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n) := by
      rw [hGap]

/-- Explicit center envelope for the signed root construction. -/
noncomputable def signedPhaseRootCenterEnvelope (n : ℕ) : ℝ :=
  unrestrictedPhaseRootCenterEnvelope n +
    phaseRootCenter n * (q + 1)

/-- The exact signed objective at the manuscript center is eventually bounded
by the explicit signed construction envelope. -/
theorem eventually_abs_phaseSignedFourSizeObjective_center_le_envelope :
    ∀ᶠ n : ℕ in atTop,
      |phaseSignedFourSizeObjective n (phaseRootCenter n)| ≤
        signedPhaseRootCenterEnvelope n := by
  filter_upwards [eventually_phaseDomain, eventually_phaseRootCenter_pos,
    eventually_abs_unrestrictedPhaseObjective_center_le_envelope,
    eventually_abs_phaseFiniteSignedFourMargin_le_q_add_one] with
    n hn hCenterPos hUnrestricted hMargin
  rw [phaseSignedFourSizeObjective_phaseRootCenter_eq n hn hCenterPos]
  calc
    |unrestrictedPhaseObjective n (phaseRootCenter n) +
        phaseRootCenter n *
          finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n)| ≤
      |unrestrictedPhaseObjective n (phaseRootCenter n)| +
        |phaseRootCenter n *
          finiteSignedFourMargin (phaseNat n) (signedFourPhaseTarget n)| :=
      abs_add_le _ _
    _ = |unrestrictedPhaseObjective n (phaseRootCenter n)| +
        phaseRootCenter n *
          |finiteSignedFourMargin (phaseNat n)
            (signedFourPhaseTarget n)| := by
      rw [abs_mul, abs_of_pos hCenterPos]
    _ ≤ unrestrictedPhaseRootCenterEnvelope n +
        phaseRootCenter n * (q + 1) :=
      add_le_add hUnrestricted
        (mul_le_mul_of_nonneg_left hMargin hCenterPos.le)
    _ = signedPhaseRootCenterEnvelope n := rfl

/-- Any slope with the manuscript normalization integrates to more than
`phaseRootCenter * log n / (40*q)` across the broad construction radius. -/
private theorem
    eventually_phaseRootCenter_log_div_40q_lt_slope_mul_constructionRadius
    (slope : ℕ → ℝ)
    (hSlope : Tendsto (signedFourNormalizedSlope slope)
      atTop (𝓝 (2 / q))) :
    ∀ᶠ n : ℕ in atTop,
      phaseRootCenter n * logOrder n / (40 * q) <
        slope n * unrestrictedPhaseRootConstructionRadius n := by
  have hLimitLower : (1 / q : ℝ) < 2 / q := by
    rw [div_lt_div_iff_of_pos_right q_pos]
    norm_num
  have hSlopeBand : ∀ᶠ n : ℕ in atTop,
      1 / q < signedFourNormalizedSlope slope n :=
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
      (1 / q) * (logOrder n) ^ 2 < slope n := by
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
  exact hGeometric.trans_lt
    (mul_lt_mul_of_pos_right hSlopeMain hnConstruction.1)

/-- The signed center envelope is eventually smaller than the integrated
signed derivative floor across the broad construction radius. -/
theorem eventually_signedPhaseRootCenterEnvelope_lt_slopeLower_mul_radius
    (C : ℝ)
    (hSlope : Tendsto
      (signedFourNormalizedSlope (signedFourDerivativeSlopeLower C))
      atTop (𝓝 (2 / q))) :
    ∀ᶠ n : ℕ in atTop,
      signedPhaseRootCenterEnvelope n <
        signedFourDerivativeSlopeLower C n *
          unrestrictedPhaseRootConstructionRadius n := by
  have hIntegrated :=
    eventually_phaseRootCenter_log_div_40q_lt_slope_mul_constructionRadius
      (signedFourDerivativeSlopeLower C) hSlope
  have hLogLarge : ∀ᶠ n : ℕ in atTop,
      100 * q * (q + 1) < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop (100 * q * (q + 1))
  filter_upwards [hIntegrated, hLogLarge, eventually_phaseRootCenter_pos,
    eventually_gt_atTop (1 : ℕ)] with
    n hnIntegrated hnLog hCenterPos hnOne
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hnOne)
  have h100qPos : 0 < (100 : ℝ) * q :=
    mul_pos (by norm_num) q_pos
  have h50qPos : 0 < (50 : ℝ) * q :=
    mul_pos (by norm_num) q_pos
  have h40qPos : 0 < (40 : ℝ) * q :=
    mul_pos (by norm_num) q_pos
  have hSmall :
      q + 1 < logOrder n / (100 * q) := by
    rw [lt_div_iff₀ h100qPos]
    nlinarith [hnLog]
  have h50lt40 :
      logOrder n / (50 * q) < logOrder n / (40 * q) := by
    rw [div_lt_div_iff₀ h50qPos h40qPos]
    nlinarith [hlogPos, q_pos]
  have hCoefficient :
      (1 / (100 * q)) * logOrder n + (q + 1) <
        logOrder n / (40 * q) := by
    calc
      (1 / (100 * q)) * logOrder n + (q + 1) =
          logOrder n / (100 * q) + (q + 1) := by ring
      _ < logOrder n / (100 * q) +
          logOrder n / (100 * q) := by
        linarith [hSmall]
      _ = logOrder n / (50 * q) := by
        field_simp [q_ne_zero]
        norm_num
      _ < logOrder n / (40 * q) := h50lt40
  calc
    signedPhaseRootCenterEnvelope n =
        phaseRootCenter n *
          ((1 / (100 * q)) * logOrder n + (q + 1)) := by
      unfold signedPhaseRootCenterEnvelope
        unrestrictedPhaseRootCenterEnvelope
      ring
    _ < phaseRootCenter n * (logOrder n / (40 * q)) :=
      mul_lt_mul_of_pos_left hCoefficient hCenterPos
    _ = phaseRootCenter n * logOrder n / (40 * q) := by ring
    _ < signedFourDerivativeSlopeLower C n *
          unrestrictedPhaseRootConstructionRadius n := hnIntegrated

/-- Complete finite data returned for the selected signed phase root. -/
def SignedPhaseRootData (n : ℕ) (r : ℝ) : Prop :=
  r ∈ Ioo
      (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
      (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n) ∧
    0 < r ∧
    fourSizeTarget n (phaseNat n) r ∈
      signedFourAdmissibilityTargetCorridor ∧
    phaseSignedFourSizeObjective n r = 0

/-- The signed derivative corridor and signed center envelope produce a unique
signed root in the explicit broad interval eventually. -/
theorem eventually_existsUnique_signedPhaseRootData :
    ∀ᶠ n : ℕ in atTop,
      ∃! r : ℝ, SignedPhaseRootData n r := by
  obtain ⟨C, _hC, hDerivative, hSlopeLower, _hSlopeUpper⟩ :=
    exists_signedFourDerivativeCorridor
  have hMargin :=
    eventually_signedPhaseRootCenterEnvelope_lt_slopeLower_mul_radius
      C hSlopeLower
  filter_upwards [
    eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible,
    eventually_phaseRootCenter_pos,
    eventually_abs_phaseSignedFourSizeObjective_center_le_envelope,
    hDerivative, hMargin, eventually_five_lt_phaseNat,
    eventually_gt_atTop (1 : ℕ)] with
    n hnConstruction hCenterPos hnCenter hnDerivative hnMargin
      hnPhase hnOne
  have hlogPos : 0 < logOrder n :=
    Real.log_pos (by exact_mod_cast hnOne)
  have hCoefficientNonneg : 0 ≤ (1 / (100 * q) : ℝ) := by
    exact (one_div_pos.mpr (mul_pos (by norm_num) q_pos)).le
  have hUnrestrictedEnvelopeNonneg :
      0 ≤ unrestrictedPhaseRootCenterEnvelope n := by
    unfold unrestrictedPhaseRootCenterEnvelope
    exact mul_nonneg hCenterPos.le
      (mul_nonneg hCoefficientNonneg hlogPos.le)
  have hQAddOneNonneg : 0 ≤ q + 1 := by
    linarith [q_pos]
  have hEnvelopeNonneg : 0 ≤ signedPhaseRootCenterEnvelope n := by
    unfold signedPhaseRootCenterEnvelope
    exact add_nonneg hUnrestrictedEnvelopeNonneg
      (mul_nonneg hCenterPos.le hQAddOneNonneg)
  have hProductPos :
      0 < signedFourDerivativeSlopeLower C n *
        unrestrictedPhaseRootConstructionRadius n :=
    lt_of_le_of_lt hEnvelopeNonneg hnMargin
  have hSlopePos : 0 < signedFourDerivativeSlopeLower C n := by
    rcases mul_pos_iff.mp hProductPos with h | h
    · exact h.1
    · exact (not_lt_of_ge hnConstruction.1.le h.2).elim
  have hFeasible :
      ∀ s ∈ Icc
          (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
          (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n),
        0 < s ∧
          fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5 := by
    intro s hs
    have hsData := hnConstruction.2 s hs
    have hsTarget :
        fourSizeTarget n (phaseNat n) s ∈
          signedFourAdmissibilityTargetCorridor := by
      simpa only [fourSizeTarget_eq_profileDeficitTarget] using hsData.2
    exact ⟨hsData.1,
      signedFourAdmissibilityTargetCorridor_subset_Ioo hsTarget⟩
  have hDerivLower :
      ∀ s ∈ Ioo
          (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
          (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n),
        signedFourDerivativeSlopeLower C n ≤
          signedFourSizeObjectiveDerivative n (phaseNat n) s := by
    intro s hs
    have hsData := hnConstruction.2 s (Ioo_subset_Icc_self hs)
    have hsTarget :
        fourSizeTarget n (phaseNat n) s ∈
          signedFourAdmissibilityTargetCorridor := by
      simpa only [fourSizeTarget_eq_profileDeficitTarget] using hsData.2
    exact (hnDerivative s hsData.1 hsTarget).1
  obtain ⟨r, hr, hunique⟩ :=
    existsUnique_phaseSignedFourSizeRoot_of_center_and_deriv_lower
      n (phaseRootCenter n)
      (unrestrictedPhaseRootConstructionRadius n)
      (signedPhaseRootCenterEnvelope n)
      (signedFourDerivativeSlopeLower C n)
      hnConstruction.1 hSlopePos hnMargin hnCenter hFeasible hDerivLower
  refine ⟨r, ?_, ?_⟩
  · have hrClosed : r ∈ Icc
        (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
        (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n) :=
      Ioo_subset_Icc_self hr.1
    have hrConstruction := hnConstruction.2 r hrClosed
    have hrTarget :
        fourSizeTarget n (phaseNat n) r ∈
          signedFourAdmissibilityTargetCorridor := by
      simpa only [fourSizeTarget_eq_profileDeficitTarget] using
        hrConstruction.2
    exact ⟨hr.1, hrConstruction.1, hrTarget, by
      simpa [IsPhaseSignedFourSizeRoot, IsSignedFourSizeRoot,
        phaseSignedFourSizeObjective] using hr.2.2.2⟩
  · intro y hy
    apply hunique y
    exact ⟨hy.1, hy.2.1,
      signedFourAdmissibilityTargetCorridor_subset_Ioo hy.2.2.1,
      by simpa [phaseSignedFourSizeObjective] using hy.2.2.2⟩

/-- A total selected signed phase root, with the phase center used only as a
fallback outside the eventual construction range. -/
noncomputable def signedPhaseRoot (n : ℕ) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, SignedPhaseRootData n r then
    Classical.choose h
  else
    phaseRootCenter n

/-- Selection correctness whenever signed-root data exists. -/
theorem signedPhaseRoot_spec_of_exists
    (n : ℕ) (h : ∃ r : ℝ, SignedPhaseRootData n r) :
    SignedPhaseRootData n (signedPhaseRoot n) := by
  classical
  rw [signedPhaseRoot, dif_pos h]
  exact Classical.choose_spec h

/-- The selected signed root has all construction data eventually. -/
theorem eventually_signedPhaseRootData :
    ∀ᶠ n : ℕ in atTop,
      SignedPhaseRootData n (signedPhaseRoot n) := by
  filter_upwards [eventually_existsUnique_signedPhaseRootData] with n hn
  exact signedPhaseRoot_spec_of_exists n hn.exists

/-- In particular, the selected signed root satisfies its exact phase
objective equation eventually. -/
theorem eventually_signedPhaseRoot_equation :
    ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (signedPhaseRoot n) = 0 :=
  eventually_signedPhaseRootData.mono fun _ hn ↦ hn.2.2.2

#print axioms tendsto_phaseFiniteSignedFourMargin_sub_phaseMargin
#print axioms eventually_abs_phaseFiniteSignedFourMargin_le_q_add_one
#print axioms phaseSignedFourSizeObjective_phaseRootCenter_eq
#print axioms eventually_abs_phaseSignedFourSizeObjective_center_le_envelope
#print axioms eventually_signedPhaseRootCenterEnvelope_lt_slopeLower_mul_radius
#print axioms eventually_existsUnique_signedPhaseRootData
#print axioms signedPhaseRoot_spec_of_exists
#print axioms eventually_signedPhaseRootData
#print axioms eventually_signedPhaseRoot_equation

end

end Erdos625
