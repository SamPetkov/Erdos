import Erdos625.PhaseRootScalarLogLogScale
import Erdos625.PhaseSignedFourSizeEntropyLower
import Erdos625.PhaseSignedFourSizeCompactTargetCorridor
import Mathlib.Tactic

/-!
# Signed four-size objective at the current reference center

This module analyzes the reference center used by the signed-root corridor.
It proves the exact normalized decomposition and shows that the normalized
signed objective diverges to `+∞` there. Consequently, a bounded center-value
margin at `phaseRootCenter` cannot supply a root-existence input; the
center/root interface therefore uses a different reference scale.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- Exact normalized signed-objective decomposition at `phaseRootCenter`. -/
theorem phaseSignedFourSizeObjective_referenceCenter_div_decomposition
    {n : Nat} (hn : PhaseDomain n) (hs0 : 0 < phaseRootS0 n) :
    phaseSignedFourSizeObjective n (phaseRootCenter n) /
          phaseRootCenter n =
      phaseRootScalarTerm n +
        fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) + q := by
  have hnPos : (0 : Real) < n := by
    exact_mod_cast (lt_trans Nat.zero_lt_one hn.1)
  have hcNe : phaseRootCenter n ≠ 0 := by
    exact div_ne_zero hnPos.ne' hs0.ne'
  simp only [phaseSignedFourSizeObjective, signedFourSizeObjective,
    signedFourSizeObjectiveAtTarget, phaseRootScalarTerm,
    phaseRootDeficitTarget, fourSizeTarget]
  field_simp [hcNe]
  ring

/-- The signed four-size objective divided by the reference center tends to
`+∞`. This rules out a constant normalized center-error bound at the present
reference center. -/
theorem tendsto_phaseSignedFourSizeObjective_referenceCenter_div_atTop :
    Tendsto
      (fun n : Nat ↦
        phaseSignedFourSizeObjective n (phaseRootCenter n) /
          phaseRootCenter n)
      atTop atTop := by
  have hphaseReal :
      Tendsto (fun n : Nat ↦ (phaseNat n : Real)) atTop atTop :=
    tendsto_atTop_mono' atTop
      (show (logOrder : Nat → Real) ≤ᶠ[atTop]
        fun n : Nat ↦ (phaseNat n : Real) by
        filter_upwards
          [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder] with n hn
        exact hn.1)
      tendsto_logOrder_atTop
  have hphaseNat : Tendsto phaseNat atTop atTop := by
    rwa [tendsto_natCast_atTop_iff] at hphaseReal
  have hentropy := hphaseNat.eventually
    eventually_fourSizeFiniteEntropy_ge_neg_twenty_five_q_div_two_sub_one
  refine tendsto_atTop.2 ?_
  intro B
  filter_upwards
    [tendsto_phaseRootScalarTerm_atTop.eventually_ge_atTop
      (B + 25 * q / 2 + 1 - q),
      hentropy,
      eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_phaseRootGapCorridor_fourSize_target_mem_Icc,
      eventually_five_lt_phaseNat] with n hscalar hentropyN hcenter htarget hphase
  have hphasePos : (0 : Real) < phaseNat n := by
    exact_mod_cast (lt_trans (by norm_num : 0 < 5) hphase)
  have hcenterPos : 0 < phaseRootCenter n := by
    exact div_pos (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenter.1.1)) hcenter.2.1
  have hgapNonneg : 0 ≤ phaseRootGapRadius n := by
    rw [phaseRootGapRadius]
    exact div_nonneg hcenterPos.le (sq_nonneg _)
  have hcenterMem : phaseRootCenter n ∈
      Icc (phaseRootCenter n - phaseRootGapRadius n)
        (phaseRootCenter n + phaseRootGapRadius n) := by
    constructor <;> linarith
  have htargetCenter := htarget (phaseRootCenter n) hcenterMem
  have hentropyCenter := hentropyN (phaseRootDeficitTarget n) (by
    simpa [phaseRootDeficitTarget, fourSizeTarget] using htargetCenter)
  rw [phaseSignedFourSizeObjective_referenceCenter_div_decomposition
    hcenter.1 hcenter.2.1]
  linarith

end

#print axioms phaseSignedFourSizeObjective_referenceCenter_div_decomposition
#print axioms tendsto_phaseSignedFourSizeObjective_referenceCenter_div_atTop

end Erdos625
