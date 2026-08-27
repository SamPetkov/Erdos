import Erdos625.PhaseSignedFourSizeLogLogCorridorTarget
import Erdos625.ProfileOptimizerUniformS4
import Erdos625.FourDeficitScoreConvergence
import Mathlib.Tactic

/-!
# Uniform finite-four control on the logarithmic-logarithmic root corridor

The enlarged corridor has already been placed in the fixed compact target
interval `[9/4, 17/4]`.  This module specializes the existing uniform score,
tilt, and optimizer-positivity APIs to that corridor.  It makes no derivative
or root-existence claim.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- On every fixed nonnegative multiple of the logarithmic-logarithmic root
corridor, the finite four-deficit tilt is eventually uniformly close to the
limiting Gaussian tilt, and all four finite optimizer coordinates have one
common positive lower bound. -/
theorem exists_pos_eventually_phaseRootLogLogCorridor_fourSize_compact_control
    (C : Real) (hC : 0 ≤ C) :
    ∃ c > 0, ∀ ε > 0,
      ∀ᶠ n : Nat in atTop,
        ∀ s ∈ Icc
            (phaseRootCenter n -
              C * logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              C * logLogOrder n * phaseRootGapRadius n),
          |ProfileEntropyS4.tilt (fourDeficitScore (phaseNat n))
                (fourSizeTarget n (phaseNat n) s) -
              ProfileEntropyS4.tilt fourGaussianScore
                (fourSizeTarget n (phaseNat n) s)| < ε ∧
            ∀ i : Fin 4,
              c ≤ ProfileEntropyS4.optimizer
                (fourDeficitScore (phaseNat n))
                (fourSizeTarget n (phaseNat n) s) i := by
  let K : Set Real := Icc (9 / 4 : Real) (17 / 4 : Real)
  have hKcompact : IsCompact K := isCompact_Icc
  have hKinterior : K ⊆ Ioo (2 : Real) 5 := by
    intro T hT
    change T ∈ Icc (9 / 4 : Real) (17 / 4 : Real) at hT
    constructor <;> linarith [hT.1, hT.2]
  obtain ⟨c, hc, Npos, hNpos⟩ :=
    ProfileEntropyS4.eventually_uniform_optimizer_pos_on_compact
      fourDeficitScore fourGaussianScore K hKcompact hKinterior
        eventually_uniform_fourDeficitScore
  have hle : (logOrder : Nat → Real) ≤ᶠ[atTop]
      fun n : Nat ↦ (phaseNat n : Real) := by
    filter_upwards
      [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
    exact hn.1
  have hphaseReal : Tendsto (fun n : Nat ↦ (phaseNat n : Real)) atTop atTop :=
    tendsto_atTop_mono' atTop hle tendsto_logOrder_atTop
  have hphase : Tendsto (fun n : Nat ↦ phaseNat n) atTop atTop := by
    rwa [tendsto_natCast_atTop_iff] at hphaseReal
  refine ⟨c, hc, fun ε hε ↦ ?_⟩
  obtain ⟨Ntilt, hNtilt⟩ :=
    ProfileEntropyS4.eventually_uniformOn_tilt_of_uniform_scores
      fourDeficitScore fourGaussianScore K hKcompact hKinterior
        eventually_uniform_fourDeficitScore ε hε
  filter_upwards
    [eventually_phaseRootLogLogCorridor_fourSize_target_mem_Icc C hC,
      hphase.eventually (eventually_ge_atTop Ntilt),
      hphase.eventually (eventually_ge_atTop Npos)] with
      n htarget hnTilt hnPos
  intro s hs
  have hT : fourSizeTarget n (phaseNat n) s ∈ K := htarget s hs
  constructor
  · exact hNtilt (phaseNat n) hnTilt
      (fourSizeTarget n (phaseNat n) s) hT
  · exact hNpos (phaseNat n) hnPos
      (fourSizeTarget n (phaseNat n) s) hT

end

#print axioms exists_pos_eventually_phaseRootLogLogCorridor_fourSize_compact_control

end Erdos625
