import Erdos625.UnrestrictedPhaseRootCorridor
import Erdos625.SignedFourMidpointTargetCorridor
import Mathlib.Tactic

/-!
# Concrete construction corridor around the unrestricted phase center

The fixed target corridor `[5/2,9/2]` contains the exact phase-center target
with a uniform margin.  This module converts that target margin into an
explicit symmetric interval in the part-count coordinate.

The construction radius is

`phaseRootCenter n / (10 * phaseNat n)`.

For every sufficiently large graph order, every positive part count in that
closed interval has deficit target in `[5/2,9/2]`.  This is a finite geometric
statement; it does not use the objective, its derivative, endpoint signs, or
root existence.  It therefore introduces no assumption equivalent to the
missing unrestricted-root theorem.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A broad `Theta(n/(log n)^2)` construction radius around the manuscript
part-count center. -/
noncomputable def unrestrictedPhaseRootConstructionRadius (n : ℕ) : ℝ :=
  phaseRootCenter n / (10 * (phaseNat n : ℝ))

/-- Finite target geometry for the explicit construction radius. -/
theorem unrestrictedPhaseRootConstructionRadius_pos_and_feasible
    (n : ℕ)
    (hn : PhaseDomain n)
    (hCenterPos : 0 < phaseRootCenter n)
    (hPhase : 6 ≤ phaseNat n) :
    0 < unrestrictedPhaseRootConstructionRadius n ∧
      ∀ s ∈ Icc
          (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
          (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n),
        0 < s ∧
          profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
            signedFourAdmissibilityTargetCorridor := by
  let alpha : ℝ := phaseNat n
  let center : ℝ := phaseRootCenter n
  let target0 : ℝ := signedFourPhaseTarget n
  have hAlpha : (6 : ℝ) ≤ alpha := by
    dsimp only [alpha]
    exact_mod_cast hPhase
  have hAlphaPos : 0 < alpha := by linarith
  have hDenomPos : 0 < 10 * alpha := by positivity
  have hTargetCenter :
      profileDeficitTarget (phaseNat n) (n : ℝ) (phaseRootCenter n) =
        signedFourPhaseTarget n := by
    unfold profileDeficitTarget
    simpa only [signedFourPhaseTarget] using phaseRoot_target_identity hn
  have hTargetBounds : target0 ∈ Icc (14 / 5 : ℝ) 4 := by
    simpa only [target0] using signedFourPhaseTarget_mem_explicit_Icc n
  have hOrderIdentity :
      (n : ℝ) = center * (alpha - target0) := by
    have h := hTargetCenter
    dsimp only [alpha, center, target0] at h ⊢
    unfold profileDeficitTarget at h
    field_simp [hCenterPos.ne'] at h
    nlinarith
  have hRadiusPos : 0 < unrestrictedPhaseRootConstructionRadius n := by
    unfold unrestrictedPhaseRootConstructionRadius
    exact div_pos hCenterPos (by
      dsimp only [alpha] at hDenomPos
      simpa only [alpha] using hDenomPos)
  have hDenomGtOne : 1 < 10 * alpha := by nlinarith
  have hRadiusLtCenter :
      unrestrictedPhaseRootConstructionRadius n < phaseRootCenter n := by
    unfold unrestrictedPhaseRootConstructionRadius
    rw [div_lt_iff₀ (by
      dsimp only [alpha] at hDenomPos
      simpa only [alpha] using hDenomPos)]
    have hMul := mul_lt_mul_of_pos_left hDenomGtOne hCenterPos
    dsimp only [alpha] at hMul
    simpa only [mul_one] using hMul
  have hFracLower :
      (alpha - 5 / 2) / (10 * alpha) ≤ (1 / 10 : ℝ) := by
    rw [div_le_iff₀ hDenomPos]
    nlinarith
  have hFracUpper :
      (alpha - 9 / 2) / (10 * alpha) ≤ (1 / 10 : ℝ) := by
    rw [div_le_iff₀ hDenomPos]
    nlinarith
  have hInnerLower :
      alpha - target0 ≤
        (alpha - 5 / 2) * (1 - 1 / (10 * alpha)) := by
    have hRewrite :
        (alpha - 5 / 2) * (1 - 1 / (10 * alpha)) =
          alpha - 5 / 2 - (alpha - 5 / 2) / (10 * alpha) := by
      ring
    rw [hRewrite]
    nlinarith [hTargetBounds.1, hFracLower]
  have hInnerUpper :
      (alpha - 9 / 2) * (1 + 1 / (10 * alpha)) ≤
        alpha - target0 := by
    have hRewrite :
        (alpha - 9 / 2) * (1 + 1 / (10 * alpha)) =
          alpha - 9 / 2 + (alpha - 9 / 2) / (10 * alpha) := by
      ring
    rw [hRewrite]
    nlinarith [hTargetBounds.2, hFracUpper]
  have hLeftProduct :
      (n : ℝ) ≤
        (alpha - 5 / 2) *
          (center - unrestrictedPhaseRootConstructionRadius n) := by
    rw [hOrderIdentity]
    have hMul := mul_le_mul_of_nonneg_left hInnerLower hCenterPos.le
    calc
      center * (alpha - target0) ≤
          center * ((alpha - 5 / 2) * (1 - 1 / (10 * alpha))) := hMul
      _ = (alpha - 5 / 2) *
          (center - unrestrictedPhaseRootConstructionRadius n) := by
        unfold unrestrictedPhaseRootConstructionRadius
        dsimp only [alpha, center]
        ring
  have hRightProduct :
      (alpha - 9 / 2) *
          (center + unrestrictedPhaseRootConstructionRadius n) ≤
        (n : ℝ) := by
    rw [hOrderIdentity]
    have hMul := mul_le_mul_of_nonneg_left hInnerUpper hCenterPos.le
    calc
      (alpha - 9 / 2) *
          (center + unrestrictedPhaseRootConstructionRadius n) =
        center * ((alpha - 9 / 2) * (1 + 1 / (10 * alpha))) := by
          unfold unrestrictedPhaseRootConstructionRadius
          dsimp only [alpha, center]
          ring
      _ ≤ center * (alpha - target0) := hMul
  refine ⟨hRadiusPos, ?_⟩
  intro s hs
  have hLeftPos :
      0 < phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n := by
    linarith
  have hsPos : 0 < s := hLeftPos.trans_le hs.1
  have hLowerCoefficient : 0 ≤ alpha - 5 / 2 := by linarith
  have hUpperCoefficient : 0 ≤ alpha - 9 / 2 := by linarith
  have hOrderLeLowerMulS :
      (n : ℝ) ≤ (alpha - 5 / 2) * s := by
    have hScale := mul_le_mul_of_nonneg_left hs.1 hLowerCoefficient
    have hScale' :
        (alpha - 5 / 2) *
            (center - unrestrictedPhaseRootConstructionRadius n) ≤
          (alpha - 5 / 2) * s := by
      simpa only [center] using hScale
    exact hLeftProduct.trans hScale'
  have hUpperMulSLeOrder :
      (alpha - 9 / 2) * s ≤ (n : ℝ) := by
    have hScale := mul_le_mul_of_nonneg_left hs.2 hUpperCoefficient
    have hScale' :
        (alpha - 9 / 2) * s ≤
          (alpha - 9 / 2) *
            (center + unrestrictedPhaseRootConstructionRadius n) := by
      simpa only [center] using hScale
    exact hScale'.trans hRightProduct
  have hRatioUpper :
      (n : ℝ) / s ≤ alpha - 5 / 2 :=
    (div_le_iff₀ hsPos).2 hOrderLeLowerMulS
  have hRatioLower :
      alpha - 9 / 2 ≤ (n : ℝ) / s :=
    (le_div_iff₀ hsPos).2 hUpperMulSLeOrder
  constructor
  · exact hsPos
  · simp only [signedFourAdmissibilityTargetCorridor, mem_Icc,
      profileDeficitTarget]
    dsimp only [alpha] at hRatioUpper hRatioLower ⊢
    constructor <;> linarith

/-- The concrete construction corridor is eventually positive and uniformly
feasible on the full sequence. -/
theorem
    eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible :
    ∀ᶠ n : ℕ in atTop,
      0 < unrestrictedPhaseRootConstructionRadius n ∧
        ∀ s ∈ Icc
            (phaseRootCenter n - unrestrictedPhaseRootConstructionRadius n)
            (phaseRootCenter n + unrestrictedPhaseRootConstructionRadius n),
          0 < s ∧
            profileDeficitTarget (phaseNat n) (n : ℝ) s ∈
              signedFourAdmissibilityTargetCorridor := by
  filter_upwards [eventually_phaseDomain, eventually_phaseRootCenter_pos,
    eventually_five_lt_phaseNat] with n hn hCenter hPhase
  exact unrestrictedPhaseRootConstructionRadius_pos_and_feasible
    n hn hCenter (by omega)

#print axioms unrestrictedPhaseRootConstructionRadius_pos_and_feasible
#print axioms eventually_unrestrictedPhaseRootConstructionRadius_pos_and_feasible

end

end Erdos625
