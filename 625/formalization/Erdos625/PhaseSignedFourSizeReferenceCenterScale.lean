import Erdos625.PhaseSignedFourSizeReferenceCenterAudit
import Erdos625.FiniteFourVsExtendedEntropyLoss
import Erdos625.PhaseRootObjectiveCenterBound
import Mathlib.Tactic

/-!
# The signed four-size reference-center scale

The preceding analysis shows that the normalized signed objective at
`phaseRootCenter` tends to `+∞`.  This module supplies the matching upper
scale: the same normalized value is `O(logLogOrder)`.  Together these facts
identify the width required by a correct root-search corridor without
claiming that the reference center is itself a root.
-/

namespace Erdos625

open Filter Asymptotics Set

noncomputable section

set_option autoImplicit false

/-- The finite four-size entropy contribution at the reference-center target,
including the signed bonus `q`, is uniformly bounded. -/
private theorem phaseReferenceCenter_finiteEntropy_add_q_isBigO_one :
    (fun n : Nat ↦
        fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) + q)
      =O[atTop] (fun _n : Nat ↦ (1 : Real)) := by
  let lower : Real := -(25 * q / 2) - 1 + q
  let upper : Real := Real.log (extendedGaussianPartition q 0) + q
  let M : Real := |lower| + |upper|
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
  have hlower := hphaseNat.eventually
    eventually_fourSizeFiniteEntropy_ge_neg_twenty_five_q_div_two_sub_one
  apply IsBigO.of_bound M
  filter_upwards
    [hlower, eventually_phaseRoot_domain_pos_and_target_corridor,
      eventually_phaseRootGapCorridor_fourSize_target_mem_Icc,
      eventually_five_lt_phaseNat] with n hlowerN hcenter htarget hphase
  have hcenterPos : 0 < phaseRootCenter n := by
    exact div_pos
      (by exact_mod_cast (lt_trans Nat.zero_lt_one hcenter.1.1)) hcenter.2.1
  have hgapNonneg : 0 ≤ phaseRootGapRadius n := by
    rw [phaseRootGapRadius]
    exact div_nonneg hcenterPos.le (sq_nonneg _)
  have hcenterMem : phaseRootCenter n ∈
      Icc (phaseRootCenter n - phaseRootGapRadius n)
        (phaseRootCenter n + phaseRootGapRadius n) := by
    constructor <;> linarith
  have htargetIcc := htarget (phaseRootCenter n) hcenterMem
  have htargetCenterOpen :
      fourSizeTarget n (phaseNat n) (phaseRootCenter n) ∈
        Ioo (2 : Real) 5 := by
    constructor <;> linarith [htargetIcc.1, htargetIcc.2]
  have htargetOpen : phaseRootDeficitTarget n ∈ Ioo (2 : Real) 5 := by
    simpa [phaseRootDeficitTarget, fourSizeTarget] using htargetCenterOpen
  have hlowerCenter := hlowerN (phaseRootDeficitTarget n) (by
    simpa [phaseRootDeficitTarget, fourSizeTarget] using htargetIcc)
  have hfiniteExtended := finiteFourVsExtendedEntropyLoss_nonneg
    (phaseNat n) hphase htargetOpen
  have hextendedUpper := extendedGaussianEntropyValue_le_dual_interior
    (target := phaseRootDeficitTarget n) (tilt := 0) htargetOpen
  have hupperCenter :
      fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) + q ≤
        upper := by
    change 0 ≤ extendedGaussianEntropyValue (phaseRootDeficitTarget n) -
      fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) at hfiniteExtended
    dsimp [upper, extendedGaussianDualTestValue] at hextendedUpper ⊢
    simp only [zero_mul, sub_zero] at hextendedUpper
    linarith
  have hlowerCenter' :
      lower ≤
        fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) + q := by
    dsimp [lower]
    simpa [add_comm] using add_le_add_right hlowerCenter q
  rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
  constructor
  · have hMlower : |lower| ≤ M := by
      dsimp [M]
      exact le_add_of_nonneg_right (abs_nonneg upper)
    exact (neg_le_neg hMlower).trans ((neg_abs_le lower).trans hlowerCenter')
  · have hupperM : upper ≤ M := by
      exact (le_abs_self upper).trans (by
        dsimp [M]
        exact le_add_of_nonneg_left (abs_nonneg lower))
    exact hupperCenter.trans hupperM

/-- The signed four-size objective divided by the manuscript reference center
has the exact logarithmic-logarithmic upper scale. -/
theorem phaseSignedFourSizeObjective_referenceCenter_div_isBigO_logLogOrder :
    (fun n : Nat ↦
        phaseSignedFourSizeObjective n (phaseRootCenter n) /
          phaseRootCenter n) =O[atTop] logLogOrder := by
  have hEntropy :
      (fun n : Nat ↦
          fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) + q)
        =O[atTop] logLogOrder :=
    phaseReferenceCenter_finiteEntropy_add_q_isBigO_one.trans
      one_isBigO_logLogOrder
  have hSum :
      (fun n : Nat ↦
          phaseRootScalarTerm n +
            (fourSizeFiniteEntropy (phaseNat n) (phaseRootDeficitTarget n) + q))
        =O[atTop] logLogOrder :=
    phaseRootScalarTerm_isBigO_logLogOrder.add hEntropy
  refine hSum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_phaseRoot_domain_pos_and_target_corridor] with n hn
  simpa [add_assoc] using
    (phaseSignedFourSizeObjective_referenceCenter_div_decomposition
      hn.1 hn.2.1).symm

end

#print axioms phaseSignedFourSizeObjective_referenceCenter_div_isBigO_logLogOrder

end Erdos625
