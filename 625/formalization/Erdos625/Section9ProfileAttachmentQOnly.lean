import Erdos625.Section9MatchingRestrictionQOnly
import Erdos625.Section9CanonicalDemandProductSpecialization
import Erdos625.Section8ProfileSkeletonWeight
import Erdos625.Section9ERealENNRealExpTransport
import Erdos625.PhaseEstimates
import Mathlib.Tactic

/-!
# Section IX: attained-profile q-only attachment endpoint

This module transports the q-only finite residual bound to every attained
canonical high skeleton and then specializes the exponent to the phase scale.
The large branch is stated using its intrinsic finite hypothesis
`2^U <= m^3`; no artificial `n / (log n)^6` cutoff is needed here.
-/

namespace Erdos625

open Filter
open scoped BigOperators ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- One absolute q-only constant controls every attained profile high-skeleton
attachment whenever its residual mass satisfies the finite quadratic regime. -/
theorem exists_absolute_profileHighSkeletonAttachment_le_qOnlyEnvelope :
    ∃ kappa : ENNReal, 0 < kappa ∧ kappa ≠ ∞ ∧
      ∀ {b n : ℕ} {k : ColoringProfile b}
          (row0 : OrderedProfilePartition n k) (U m : ℕ)
          (_hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
          (demand : ProfileCanonicalHighSkeleton k U),
        m = canonicalDemandResidualTotal
          (profileBlockMargin k) (profileBlockMargin k) U demand →
        0 < m →
        2 ^ U ≤ m ^ 3 →
        profileHighSkeletonAttachment row0 U demand ≤
          EReal.exp ((((kappa * (U : ENNReal) ^ 2 : ENNReal)) : EReal)) := by
  obtain ⟨kappa, hkpos, hktop, hbound⟩ :=
    exists_absolute_residualActualAttachmentNumerator_le_qOnlyEnvelope
  refine ⟨kappa, hkpos, hktop, ?_⟩
  intro b n k row0 U m hcap demand hm hmpos hpow
  let witness := canonicalDemandReferenceWitness
    (profileBlockMargin k) (profileBlockMargin k) U demand
  have hparameters := canonicalReference_residual_parameters
    (profileBlockMargin k) (profileBlockMargin k) U
    (profileBlockMargin_total_eq_self row0) hcap hcap demand
  have hrowSum : (∑ a, residualRowDegree witness a) = m := by
    simpa only [canonicalDemandResidualTotal, witness] using hm.symm
  have hcolSum : (∑ a, residualColumnDegree witness a) = m := by
    exact hparameters.2.2.2.symm.trans hrowSum
  have hactual := hbound (positiveDemandSupport demand.1) U m
    (residualRowDegree witness) (residualColumnDegree witness)
    (sum_residualRowDegree_eq_sum_residualColumnDegree
      (profileBlockMargin_total_eq_self row0) witness)
    hparameters.1 hmpos hrowSum hcolSum hparameters.2.1 hparameters.2.2.1 hpow
  unfold profileHighSkeletonAttachment
  simpa only [witness] using hactual

/-- The q-only exponent is finite for every finite constant and natural cap. -/
theorem qOnlyEnvelope_ne_top
    (kappa : ENNReal) (U : Nat) (hkappaTop : kappa ≠ ∞) :
    kappa * (U : ENNReal) ^ 2 ≠ ∞ :=
  ENNReal.mul_ne_top hkappaTop
    (ENNReal.pow_ne_top (ENNReal.natCast_ne_top U))

/-- In the intrinsic quadratic regime, every attained profile high-skeleton
attachment is uniformly `exp(O((log n)^2))`. -/
theorem eventually_profileHighSkeletonAttachment_le_qOnly_logScale :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ {b : ℕ} {k : ColoringProfile b}
          (row0 : OrderedProfilePartition n k) (U : ℕ),
          U ≤ phaseNat n →
          (∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) →
          ∀ demand : ProfileCanonicalHighSkeleton k U,
            2 ^ U ≤
              (canonicalDemandResidualTotal (profileBlockMargin k)
                (profileBlockMargin k) U demand) ^ 3 →
            profileHighSkeletonAttachment row0 U demand ≤
              ENNReal.ofReal
                (Real.exp (C * Real.log (n : ℝ) ^ 2)) := by
  obtain ⟨kappa, hkpos, hktop, hfinite⟩ :=
    exists_absolute_profileHighSkeletonAttachment_le_qOnlyEnvelope
  let C : ℝ := kappa.toReal * 4 ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards
    [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_gt_atTop (1 : ℕ)] with n hphase hn
  intro b k row0 U hU hcap demand hpow
  let m := canonicalDemandResidualTotal (profileBlockMargin k)
    (profileBlockMargin k) U demand
  change 2 ^ U ≤ m ^ 3 at hpow
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have htwoPos : 0 < (2 : Nat) ^ U := pow_pos (by decide) U
    exact (not_le_of_gt htwoPos) (by simpa [hm0] using hpow)
  have hbase := hfinite row0 U m hcap demand rfl hmpos hpow
  let exponent : ENNReal := kappa * (U : ENNReal) ^ 2
  have hexponent : exponent ≠ ∞ := by
    exact qOnlyEnvelope_ne_top kappa U hktop
  have hbaseReal :
      profileHighSkeletonAttachment row0 U demand ≤
        ENNReal.ofReal (Real.exp exponent.toReal) := by
    apply ennreal_le_of_coe_le_ereal_exp_toReal _ _ hexponent
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hbase
  apply hbaseReal.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hUreal : (U : ℝ) ≤ 4 * Real.log (n : ℝ) :=
    (Nat.cast_le.mpr hU).trans hphase.2
  have hU2 : (U : ℝ) ^ 2 ≤ (4 * Real.log (n : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg U) hUreal 2
  have hbound : kappa.toReal * (U : ℝ) ^ 2 ≤
      C * Real.log (n : ℝ) ^ 2 := by
    calc
      kappa.toReal * (U : ℝ) ^ 2 ≤
          kappa.toReal * (4 * Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hU2 ENNReal.toReal_nonneg
      _ = C * Real.log (n : ℝ) ^ 2 := by
        simp [C]
        ring
  have hexponentReal : exponent.toReal = kappa.toReal * (U : ℝ) ^ 2 := by
    simp [exponent]
  rw [hexponentReal]
  exact hbound

#print axioms exists_absolute_profileHighSkeletonAttachment_le_qOnlyEnvelope
#print axioms qOnlyEnvelope_ne_top
#print axioms eventually_profileHighSkeletonAttachment_le_qOnly_logScale

end

end Erdos625
