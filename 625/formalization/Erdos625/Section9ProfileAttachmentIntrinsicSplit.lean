import Erdos625.Section9ProfileAttachmentQOnly
import Erdos625.Section9SmallResidualAttachmentBound
import Erdos625.Section8ProfileSkeletonWeight
import Mathlib.Tactic

/-!
# Section IX: intrinsic finite residual dichotomy

The q-only estimate requires exactly `2^U <= m^3`.  Rather than introduce an
external cutoff in `m`, this module splits on that finite proposition itself.
Its negation forces `m < 2^(ceil(U/3))`, where the deterministic residual bound
applies directly.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- One absolute q-only constant gives an exact finite dichotomy for every
attained profile high skeleton.

In the quadratic branch the attachment is bounded by `exp(kappa * U^2)`.  In
the complementary branch the residual mass is below `2^(ceil(U/3))` and the
literal deterministic bound `2^(U*m/2)` is retained. -/
theorem exists_absolute_profileHighSkeletonAttachment_intrinsic_split :
    ∃ kappa : ENNReal, 0 < kappa ∧ kappa ≠ ∞ ∧
      ∀ {b n : ℕ} {k : ColoringProfile b}
          (row0 : OrderedProfilePartition n k) (U : ℕ)
          (_hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
          (demand : ProfileCanonicalHighSkeleton k U),
        let m := canonicalDemandResidualTotal
          (profileBlockMargin k) (profileBlockMargin k) U demand
        (2 ^ U ≤ m ^ 3 ∧
          profileHighSkeletonAttachment row0 U demand ≤
            EReal.exp ((((kappa * (U : ENNReal) ^ 2 : ENNReal)) : EReal))) ∨
        (¬ 2 ^ U ≤ m ^ 3 ∧
          m < 2 ^ residualCeilThird U ∧
          profileHighSkeletonAttachment row0 U demand ≤
            (2 : ENNReal) ^ (U * m / 2)) := by
  obtain ⟨kappa, hkpos, hktop, hlarge⟩ :=
    exists_absolute_profileHighSkeletonAttachment_le_qOnlyEnvelope
  refine ⟨kappa, hkpos, hktop, ?_⟩
  intro b n k row0 U hcap demand
  dsimp only
  let m := canonicalDemandResidualTotal
    (profileBlockMargin k) (profileBlockMargin k) U demand
  by_cases hpow : 2 ^ U ≤ m ^ 3
  · left
    have hmpos : 0 < m := by
      by_contra hm
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      simp at hpow
    exact ⟨hpow, hlarge row0 U m hcap demand rfl hmpos hpow⟩
  · right
    have hmass := residualMass_lt_two_pow_ceilThird_of_not_cube U m hpow
    let witness := canonicalDemandReferenceWitness
      (profileBlockMargin k) (profileBlockMargin k) U demand
    have hmatching :
        IsBipartiteMatching (positiveDemandSupport demand.1) :=
      profileHighSkeleton_positiveSupport_isBipartiteMatching k U hcap demand
    have htotal :
        (∑ a, residualRowDegree witness a) =
          ∑ a, residualColumnDegree witness a :=
      sum_residualRowDegree_eq_sum_residualColumnDegree
        (profileBlockMargin_total_eq_self row0) witness
    have hrowSum : (∑ a, residualRowDegree witness a) = m := by
      simp only [m, canonicalDemandResidualTotal, witness]
    have hsmall := residualActualAttachmentNumerator_le_two_pow_of_small_mass
      (positiveDemandSupport demand.1) (U / 2) U m
      (residualRowDegree witness) (residualColumnDegree witness)
      htotal hmatching rfl hrowSum
    refine ⟨hpow, hmass, ?_⟩
    unfold profileHighSkeletonAttachment
    simpa only [m, witness] using hsmall

#print axioms exists_absolute_profileHighSkeletonAttachment_intrinsic_split

end

end Erdos625
