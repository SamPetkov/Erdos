import Erdos625.Section9GlobalTaggedAttachmentAssembly
import Erdos625.Section9CanonicalRewardSupportSplit
import Erdos625.Section9ActualResidualCycleRankAssembly
import Erdos625.Section6SignedOverlapLocalFactor
import Erdos625.ProfileOverlapConfigurationBridge

/-!
# Section IX: exact signed-overlap canonical decomposition

This module supplies the finite equality behind the manuscript's equation
(9.2).  A uniform configuration matching is transported through its attained
canonical high-demand table, its labelled witness, and the corresponding
cap/no-return residual configuration.  On every tagged state, the full signed
overlap reward splits exactly into

* the local reward of the exposed high-demand support;
* the residual local reward; and
* the literal binary cycle-space factor of the union support graph.

The final two theorems provide both the raw configuration-model statement and
the profile-overlap version transported by
`ProfileOverlapConfigurationBridge`.  They are finite identities only: no
asymptotic estimate, cap probability division, or rare-event conclusion is
asserted here.
-/

namespace Erdos625

noncomputable section

local instance instFintypeCanonicalResidualCellEventRewardBridge
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → Nat} {row : A → Nat} {col : B → Nat}
    (witness : PrescribedDemandWitness demand row col) (U : Nat) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

abbrev CanonicalRewardState
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → Nat) (col : B → Nat) (U : Nat) :=
  Sigma fun demand : canonicalDemandImage row col U =>
    Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
      canonicalResidualCellEvent witness U

noncomputable def canonicalRewardStateFullMatching
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → Nat) (col : B → Nat) (U : Nat)
    (z : CanonicalRewardState row col U) : ConfigurationMatching row col :=
  (configurationMatchingEquivSigmaCanonicalDemandResidual row col U).symm z

noncomputable def canonicalRewardStateExtension
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (z : CanonicalRewardState row col U) : fixedWitnessExtensionEvent z.2.1 :=
  (fixedWitnessExtensionEquivResidual z.2.1).symm z.2.2.1

theorem canonicalRewardStateFullMatching_eq_extension
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (z : CanonicalRewardState row col U) :
    canonicalRewardStateFullMatching row col U z =
      (canonicalRewardStateExtension z).1 := by
  rfl

theorem canonicalRewardStateExtension_mem_canonical
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (z : CanonicalRewardState row col U) :
    canonicalRewardStateExtension z ∈
      fixedWitnessCanonicalDemandEvent z.2.1 U := by
  rw [mem_fixedWitnessCanonicalDemandEvent_iff_residual z.2.1 U
    (canonicalDemandImage_high row col U z.1)]
  change (fixedWitnessExtensionEquivResidual z.2.1
    ((fixedWitnessExtensionEquivResidual z.2.1).symm z.2.2.1)) ∈
      canonicalResidualCellEvent z.2.1 U
  simp

noncomputable def canonicalDemandLocalReward
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (demand : canonicalDemandImage row col U) : Nat :=
  ∏ e ∈ positiveDemandSupport demand.1,
    localSignRewardNat (demand.1 e.1 e.2)

noncomputable def canonicalRewardStateAttachment
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (z : CanonicalRewardState row col U) : ENNReal :=
  (canonicalDemandLocalReward z.1 : ENNReal) *
    taggedResidualAttachmentValue z.1.1 U z.2.1 z.2.2

/-- Under the usual ambient degree caps, the positive support attached to
every canonical state is a bipartite matching.  The decomposition theorems
below do not need this additional hypothesis, but this is the precise link
between an attained high-demand tag and the manuscript's high skeleton. -/
theorem canonicalRewardState_positiveSupport_isBipartiteMatching
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (z : CanonicalRewardState row col U) :
    IsBipartiteMatching (positiveDemandSupport z.1.1) := by
  exact positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage
    U hrowCap hcolCap z.1

theorem canonicalRewardState_residual_eq
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (z : CanonicalRewardState row col U) :
    fixedWitnessExtensionEquivResidual z.2.1
      (canonicalRewardStateExtension z) = z.2.2.1 := by
  simp [canonicalRewardStateExtension]

theorem signedOverlapReward_canonicalRewardState_eq_attachment
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (hU : 2 ≤ U) (z : CanonicalRewardState row col U) :
    (signedOverlapReward
      (configurationCellCount (canonicalRewardStateFullMatching row col U z)) : ENNReal) =
      canonicalRewardStateAttachment z := by
  let extension := canonicalRewardStateExtension z
  let residual := fixedWitnessExtensionEquivResidual z.2.1 extension
  have hcanonical : extension ∈ fixedWitnessCanonicalDemandEvent z.2.1 U := by
    exact canonicalRewardStateExtension_mem_canonical z
  have hsplit := fixedWitnessCanonical_reward_support_split U hU z.1 z.2.1
    extension hcanonical
  have hfull : canonicalRewardStateFullMatching row col U z = extension.1 := by
    exact canonicalRewardStateFullMatching_eq_extension z
  have hresidual : residual = z.2.2.1 := by
    exact canonicalRewardState_residual_eq z
  have hlocal :
      (∏ a : A, ∏ b : B,
        localSignRewardNat
          (configurationCellCount (canonicalRewardStateFullMatching row col U z) a b)) =
        canonicalDemandLocalReward z.1 *
          (∏ a : A, ∏ b : B,
            residualReward (configurationCellCount z.2.2.1 a b)) := by
    rw [hfull]
    simp_rw [← residualReward_eq_localSignRewardNat]
    rw [hsplit.1]
    simp [canonicalDemandLocalReward, residual, hresidual]
  have hcycle :
      2 ^ cycleRank
        (signedOverlapSupportGraph
          (configurationCellCount (canonicalRewardStateFullMatching row col U z))) =
        (actualResidualEvenEdgeSets (positiveDemandSupport z.1.1) z.2.2.1).card := by
    change 2 ^ cycleRank
        (bipartiteGraph fun a b =>
          2 ≤ configurationCellCount
            (canonicalRewardStateFullMatching row col U z) a b) = _
    rw [hfull]
    rw [hsplit.2]
    rw [← bipartiteGraph_or_eq_sup]
    simpa [residual, hresidual] using
      (card_actualResidualEvenEdgeSets_eq_two_pow_cycleRank
        (positiveDemandSupport z.1.1) z.2.2.1).symm
  unfold signedOverlapReward canonicalRewardStateAttachment taggedResidualAttachmentValue
  rw [hlocal, hcycle]
  simp only [Nat.cast_mul, Nat.cast_prod]
  ac_rfl

private theorem canonicalRewardState_sum_pmf_mul_comp_eq_sum_pmf_map
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (weight : β → ENNReal) :
    (∑ x : α, p x * weight (f x)) =
      ∑ y : β, (p.map f) y * weight y := by
  classical
  calc
    (∑ x : α, p x * weight (f x)) =
        ∑ x : α, ∑ y : β,
          (if y = f x then p x else 0) * weight y := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (f x)]
      simp
    _ = ∑ y : β, ∑ x : α,
          (if y = f x then p x else 0) * weight y := Finset.sum_comm
    _ = ∑ y : β,
        (∑ x : α, if y = f x then p x else 0) * weight y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
    _ = ∑ y : β, (p.map f) y * weight y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [PMF.map_apply, tsum_fintype]

theorem sum_uniformConfigurationMatching_signedOverlapReward_eq_sum_canonicalRewardStateAttachment
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → Nat) (col : B → Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hU : 2 ≤ U) :
    (∑ matching : ConfigurationMatching row col,
      uniformConfigurationMatching row col htotal matching *
        (signedOverlapReward (configurationCellCount matching) : ENNReal)) =
      ∑ z : CanonicalRewardState row col U,
        uniformSigmaCanonicalDemandResidual row col U htotal z *
          canonicalRewardStateAttachment z := by
  classical
  let equivalence := configurationMatchingEquivSigmaCanonicalDemandResidual row col U
  let p := uniformConfigurationMatching row col htotal
  let weight : CanonicalRewardState row col U → ENNReal := fun z =>
    (signedOverlapReward
      (configurationCellCount (canonicalRewardStateFullMatching row col U z)) : ENNReal)
  have hweight : ∀ matching : ConfigurationMatching row col,
      (signedOverlapReward (configurationCellCount matching) : ENNReal) =
        weight (equivalence matching) := by
    intro matching
    simp [weight, equivalence, canonicalRewardStateFullMatching]
  calc
    (∑ matching : ConfigurationMatching row col,
        uniformConfigurationMatching row col htotal matching *
          (signedOverlapReward (configurationCellCount matching) : ENNReal)) =
        ∑ matching : ConfigurationMatching row col,
          p matching * weight (equivalence matching) := by
      apply Finset.sum_congr rfl
      intro matching _
      rw [hweight]
    _ = ∑ z : CanonicalRewardState row col U,
        (p.map equivalence) z * weight z :=
      canonicalRewardState_sum_pmf_mul_comp_eq_sum_pmf_map p equivalence weight
    _ = ∑ z : CanonicalRewardState row col U,
        uniformSigmaCanonicalDemandResidual row col U htotal z * weight z := by
      rw [uniformConfigurationMatching_map_sigmaCanonicalDemandResidual]
    _ = ∑ z : CanonicalRewardState row col U,
        uniformSigmaCanonicalDemandResidual row col U htotal z *
          canonicalRewardStateAttachment z := by
      apply Finset.sum_congr rfl
      intro z _
      change uniformSigmaCanonicalDemandResidual row col U htotal z *
          (signedOverlapReward
            (configurationCellCount (canonicalRewardStateFullMatching row col U z)) : ENNReal) = _
      rw [signedOverlapReward_canonicalRewardState_eq_attachment hU z]

theorem sum_uniformConfigurationMatching_signedOverlapReward_eq_skeletonAttachmentSum
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → Nat) (col : B → Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hU : 2 ≤ U) :
    (∑ matching : ConfigurationMatching row col,
      uniformConfigurationMatching row col htotal matching *
        (signedOverlapReward (configurationCellCount matching) : ENNReal)) =
      ∑ demand : canonicalDemandImage row col U,
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 row col *
            residualActualAttachmentNumerator
              (positiveDemandSupport demand.1) (U / 2)
              (residualRowDegree
                (canonicalDemandReferenceWitness row col U demand))
              (residualColumnDegree
                (canonicalDemandReferenceWitness row col U demand))
              (sum_residualRowDegree_eq_sum_residualColumnDegree htotal
                (canonicalDemandReferenceWitness row col U demand))) := by
  rw [sum_uniformConfigurationMatching_signedOverlapReward_eq_sum_canonicalRewardStateAttachment
    row col U htotal hU]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro demand _
  calc
    ∑ z : Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
        canonicalResidualCellEvent witness U,
        uniformSigmaCanonicalDemandResidual row col U htotal ⟨demand, z⟩ *
          canonicalRewardStateAttachment ⟨demand, z⟩ =
      (canonicalDemandLocalReward demand : ENNReal) *
        ∑ z : Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          canonicalResidualCellEvent witness U,
          uniformSigmaCanonicalDemandResidual row col U htotal ⟨demand, z⟩ *
            taggedResidualAttachmentValue demand.1 U z.1 z.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [canonicalRewardStateAttachment]
      ac_rfl
    _ =
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 row col *
            residualActualAttachmentNumerator
              (positiveDemandSupport demand.1) (U / 2)
              (residualRowDegree
                (canonicalDemandReferenceWitness row col U demand))
              (residualColumnDegree
                (canonicalDemandReferenceWitness row col U demand))
              (sum_residualRowDegree_eq_sum_residualColumnDegree htotal
                (canonicalDemandReferenceWitness row col U demand))) := by
      rw [sum_taggedResidualAttachmentValue_eq_incidence_mul_numerator
        row col U htotal demand
          (canonicalDemandReferenceWitness row col U demand)]
    _ = _ := rfl

theorem sum_uniformProfile_signedOverlapReward_eq_skeletonAttachmentSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : Nat)
    (hU : 2 ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) =
      ∑ demand : canonicalDemandImage (profileBlockMargin k) (profileBlockMargin k) U,
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k) *
            residualActualAttachmentNumerator
              (positiveDemandSupport demand.1) (U / 2)
              (residualRowDegree
                (canonicalDemandReferenceWitness (profileBlockMargin k)
                  (profileBlockMargin k) U demand))
              (residualColumnDegree
                (canonicalDemandReferenceWitness (profileBlockMargin k)
                  (profileBlockMargin k) U demand))
              (sum_residualRowDegree_eq_sum_residualColumnDegree
                (profileBlockMargin_total_eq_self row₀)
                (canonicalDemandReferenceWitness (profileBlockMargin k)
                  (profileBlockMargin k) U demand))) := by
  calc
    (∑ column : OrderedProfilePartition n k,
        uniformOrderedProfilePartition row₀ column *
          (signedOverlapReward
            (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) =
        ∑ matching : ConfigurationMatching (profileBlockMargin k)
          (profileBlockMargin k),
          uniformConfigurationMatching (profileBlockMargin k)
            (profileBlockMargin k) (profileBlockMargin_total_eq_self row₀) matching *
            (signedOverlapReward
              (profileOverlapTableOfConfigurationMatching row₀ matching).tableNat : ENNReal) := by
      exact (weightedExpectation_uniformConfigurationMatching_eq_uniformProfile row₀
        (fun r => (signedOverlapReward r : ENNReal))).symm
    _ = ∑ matching : ConfigurationMatching (profileBlockMargin k)
          (profileBlockMargin k),
          uniformConfigurationMatching (profileBlockMargin k)
            (profileBlockMargin k) (profileBlockMargin_total_eq_self row₀) matching *
            (signedOverlapReward (configurationCellCount matching) : ENNReal) := by
      apply Finset.sum_congr rfl
      intro matching _
      congr 2
      congr 1
      funext a q
      exact profileOverlapTableOfConfigurationMatching_tableNat_eq_cellCount
        row₀ matching a q
    _ = _ :=
      sum_uniformConfigurationMatching_signedOverlapReward_eq_skeletonAttachmentSum
        (profileBlockMargin k) (profileBlockMargin k) U
        (profileBlockMargin_total_eq_self row₀) hU

theorem sum_uniformConfigurationMatching_signedOverlapReward_eq_skeletonCycleRankSum
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → Nat) (col : B → Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hU : 2 ≤ U) :
    (∑ matching : ConfigurationMatching row col,
      uniformConfigurationMatching row col htotal matching *
        (signedOverlapReward (configurationCellCount matching) : ENNReal)) =
      ∑ demand : canonicalDemandImage row col U,
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 row col *
            residualCycleRankExpectation
              (positiveDemandSupport demand.1) (U / 2)
              (residualRowDegree
                (canonicalDemandReferenceWitness row col U demand))
              (residualColumnDegree
                (canonicalDemandReferenceWitness row col U demand))
              (sum_residualRowDegree_eq_sum_residualColumnDegree htotal
                (canonicalDemandReferenceWitness row col U demand))) := by
  rw [sum_uniformConfigurationMatching_signedOverlapReward_eq_skeletonAttachmentSum
    row col U htotal hU]
  apply Finset.sum_congr rfl
  intro demand _
  rw [residualActualAttachmentNumerator_eq_cycleRankExpectation]

theorem sum_uniformProfile_signedOverlapReward_eq_skeletonCycleRankSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : Nat)
    (hU : 2 ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) =
      ∑ demand : canonicalDemandImage (profileBlockMargin k) (profileBlockMargin k) U,
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k) *
            residualCycleRankExpectation
              (positiveDemandSupport demand.1) (U / 2)
              (residualRowDegree
                (canonicalDemandReferenceWitness (profileBlockMargin k)
                  (profileBlockMargin k) U demand))
              (residualColumnDegree
                (canonicalDemandReferenceWitness (profileBlockMargin k)
                  (profileBlockMargin k) U demand))
              (sum_residualRowDegree_eq_sum_residualColumnDegree
                (profileBlockMargin_total_eq_self row₀)
                (canonicalDemandReferenceWitness (profileBlockMargin k)
                  (profileBlockMargin k) U demand))) := by
  rw [sum_uniformProfile_signedOverlapReward_eq_skeletonAttachmentSum row₀ U hU]
  apply Finset.sum_congr rfl
  intro demand _
  rw [residualActualAttachmentNumerator_eq_cycleRankExpectation]

#print axioms canonicalRewardStateFullMatching_eq_extension
#print axioms canonicalRewardStateExtension_mem_canonical
#print axioms canonicalRewardState_positiveSupport_isBipartiteMatching
#print axioms canonicalRewardState_residual_eq
#print axioms signedOverlapReward_canonicalRewardState_eq_attachment
#print axioms sum_uniformConfigurationMatching_signedOverlapReward_eq_sum_canonicalRewardStateAttachment
#print axioms sum_uniformConfigurationMatching_signedOverlapReward_eq_skeletonAttachmentSum
#print axioms sum_uniformConfigurationMatching_signedOverlapReward_eq_skeletonCycleRankSum
#print axioms sum_uniformProfile_signedOverlapReward_eq_skeletonAttachmentSum
#print axioms sum_uniformProfile_signedOverlapReward_eq_skeletonCycleRankSum

end

end Erdos625
