import Erdos625.Section9SignedOverlapCanonicalDecomposition
import Erdos625.Section9ActualAttachmentPolymerBridge
import Erdos625.Section9ZeroResidualActualAttachment
import Erdos625.Section9SmallResidualDeterministic

/-!
# Section IX: profile attachment polymer assembly

This transports the fixed-residual-fibre polymer estimate through the actual
dependent canonical-demand family. The cap/no-return indicator remains inside
`residualActualAttachmentNumerator`; no conditioned event mass is divided out.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance instFintypeCanonicalResidualCellEventProfilePolymer
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

/-- The finite polymer majorant attached to one attained canonical demand. -/
noncomputable def canonicalDemandPolymerMajorant
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (demand : canonicalDemandImage row col U) : ENNReal :=
  let witness := canonicalDemandReferenceWitness row col U demand
  (∏ a : A, ∏ b : B,
      (1 + residualLambda (positiveDemandSupport demand.1) (U / 2)
        (residualRowDegree witness) (residualColumnDegree witness) a b)) *
    (∏ C ∈ simpleBipartiteCycles A B,
      (1 + edgeWeightOutsideENN
        (residualQ (positiveDemandSupport demand.1) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness))
        (positiveDemandSupport demand.1) C))

/-- Strict-regime transport over the full dependent tagged residual family. -/
theorem sum_global_taggedResidualAttachmentValue_le_sum_incidence_mul_polymerMajorant
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hpositive : ∀ demand : canonicalDemandImage row col U,
      0 < Finset.univ.sum
        (residualRowDegree
          (canonicalDemandReferenceWitness row col U demand))) :
    (Finset.univ.sum fun z :
      Sigma fun demand : canonicalDemandImage row col U =>
        Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
          canonicalResidualCellEvent witness U =>
      uniformSigmaCanonicalDemandResidual row col U htotal z *
        taggedResidualAttachmentValue z.1.1 U z.2.1 z.2.2) ≤
      Finset.univ.sum fun demand : canonicalDemandImage row col U =>
        labelledWitnessIncidence demand.1 row col *
          canonicalDemandPolymerMajorant row col U demand := by
  rw [sum_global_taggedResidualAttachmentValue_eq_sum_incidence_mul_numerator
    row col U htotal]
  apply Finset.sum_le_sum
  intro demand _
  apply mul_le_mul_right
  unfold canonicalDemandPolymerMajorant
  exact residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
    (positiveDemandSupport demand.1) (U / 2)
    (residualRowDegree
      (canonicalDemandReferenceWitness row col U demand))
    (residualColumnDegree
      (canonicalDemandReferenceWitness row col U demand))
    (sum_residualRowDegree_eq_sum_residualColumnDegree htotal
      (canonicalDemandReferenceWitness row col U demand))
    (hpositive demand)

/-- Ordered-profile specialization in the uniform strict residual regime. -/
theorem sum_uniformProfile_signedOverlapReward_le_skeletonPolymerSum
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ)
    (hU : 2 ≤ U)
    (hpositive : ∀ demand : canonicalDemandImage
        (profileBlockMargin k) (profileBlockMargin k) U,
      0 < Finset.univ.sum
        (residualRowDegree
          (canonicalDemandReferenceWitness (profileBlockMargin k)
            (profileBlockMargin k) U demand))) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) ≤
      ∑ demand : canonicalDemandImage
          (profileBlockMargin k) (profileBlockMargin k) U,
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k) *
            canonicalDemandPolymerMajorant
              (profileBlockMargin k) (profileBlockMargin k) U demand) := by
  rw [sum_uniformProfile_signedOverlapReward_eq_skeletonAttachmentSum
    row₀ U hU]
  apply Finset.sum_le_sum
  intro demand _
  apply mul_le_mul_right
  apply mul_le_mul_right
  unfold canonicalDemandPolymerMajorant
  exact residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
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
        (profileBlockMargin k) U demand))
    (hpositive demand)

/-- Residual stub mass attached to an attained canonical demand. -/
noncomputable def canonicalDemandResidualTotal
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (demand : canonicalDemandImage row col U) : ℕ :=
  ∑ a, residualRowDegree
    (canonicalDemandReferenceWitness row col U demand) a

/-- The raw attachment summand in the exact canonical decomposition. The
cap/no-return indicator remains inside the numerator. -/
noncomputable def canonicalDemandRawAttachmentTerm
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (demand : canonicalDemandImage row col U) : ENNReal :=
  (canonicalDemandLocalReward demand : ENNReal) *
    (labelledWitnessIncidence demand.1 row col *
      residualActualAttachmentNumerator
        (positiveDemandSupport demand.1) (U / 2)
        (residualRowDegree
          (canonicalDemandReferenceWitness row col U demand))
        (residualColumnDegree
          (canonicalDemandReferenceWitness row col U demand))
        (sum_residualRowDegree_eq_sum_residualColumnDegree htotal
          (canonicalDemandReferenceWitness row col U demand)))

/-- Exact two-regime reindexing of the attained canonical-demand family. The
zero-residual and positive-residual sums retain the literal raw attachment
numerator; no event probability is divided out. -/
theorem sum_uniformProfile_signedOverlapReward_eq_zeroResidual_add_positiveResidual
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ)
    (hU : 2 ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) =
      (∑ demand ∈ (Finset.univ.filter fun demand : canonicalDemandImage
          (profileBlockMargin k) (profileBlockMargin k) U =>
            canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand = 0),
        canonicalDemandRawAttachmentTerm (profileBlockMargin k)
          (profileBlockMargin k) U (profileBlockMargin_total_eq_self row₀) demand) +
      (∑ demand ∈ (Finset.univ.filter fun demand : canonicalDemandImage
          (profileBlockMargin k) (profileBlockMargin k) U =>
            0 < canonicalDemandResidualTotal (profileBlockMargin k)
              (profileBlockMargin k) U demand),
        canonicalDemandRawAttachmentTerm (profileBlockMargin k)
          (profileBlockMargin k) U (profileBlockMargin_total_eq_self row₀) demand) := by
  classical
  rw [sum_uniformProfile_signedOverlapReward_eq_skeletonAttachmentSum row₀ U hU]
  unfold canonicalDemandRawAttachmentTerm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun demand : canonicalDemandImage (profileBlockMargin k)
      (profileBlockMargin k) U =>
        canonicalDemandResidualTotal (profileBlockMargin k)
          (profileBlockMargin k) U demand = 0)]
  simp only [Nat.pos_iff_ne_zero]

#print axioms sum_global_taggedResidualAttachmentValue_le_sum_incidence_mul_polymerMajorant
#print axioms sum_uniformProfile_signedOverlapReward_le_skeletonPolymerSum
#print axioms sum_uniformProfile_signedOverlapReward_eq_zeroResidual_add_positiveResidual

end

end Erdos625
