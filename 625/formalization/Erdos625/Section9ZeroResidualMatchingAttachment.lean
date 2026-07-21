import Erdos625.Section9ZeroResidualActualAttachment
import Erdos625.Section9CanonicalSupportMatching
import Erdos625.Section9ProfileAttachmentPolymerAssembly
import Erdos625.Section8ProfileSkeletonWeight
import Mathlib.Tactic

/-!
# Section IX: zero-residual attained-skeleton branch

This closes the zero-residual branch omitted by the strict-regime polymer
estimate. An even bipartite edge set contained in a matching is empty, so at
zero residual mass the literal actual attachment numerator is one even when
the attained high skeleton is nonempty. The canonical polymer majorant is at
least one, hence the same majorization used in the positive branch holds
without a residual-positivity hypothesis.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- An even bipartite edge set contained in a bipartite matching is empty. -/
theorem bipartiteEven_subset_matching_eq_empty
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {F M : Finset (A × B)}
    (hF : IsBipartiteEven F) (hFM : F ⊆ M)
    (hM : IsBipartiteMatching M) :
    F = ∅ := by
  by_contra hne
  obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hfilter : F.filter (fun x => x.1 = e.1) = {e} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hxF, hxrow⟩
      have heM : (x.1, e.2) ∈ M := by
        rw [hxrow]
        exact hFM he
      have hsnd : x.2 = e.2 := hM.1 x.1 x.2 e.2 (hFM hxF) heM
      exact Prod.ext hxrow hsnd
    · rintro rfl
      exact ⟨he, rfl⟩
  have heven := hF.1 e.1
  rw [hfilter] at heven
  simp only [Finset.card_singleton] at heven
  exact Nat.not_even_one heven

/-- At zero residual mass, the literal attachment numerator is one for every
exposed bipartite matching. The cap/no-return indicator and actual even-family
cardinality are evaluated directly; no conditioning or division is used. -/
theorem residualActualAttachmentNumerator_eq_one_of_total_zero_of_matching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hrowTotal : Finset.univ.sum row = 0)
    (hM : IsBipartiteMatching M) :
    residualActualAttachmentNumerator M R row col htotal = 1 := by
  classical
  have hrowzero : ∀ a : A, row a = 0 := by
    intro a
    exact (Finset.sum_eq_zero_iff.mp hrowTotal) a (Finset.mem_univ a)
  have hcellzero : ∀ (matching : ConfigurationMatching row col) (a : A) (b : B),
      configurationCellCount matching a b = 0 := by
    intro matching a b
    have hsum : (∑ b', configurationCellCount matching a b') = 0 := by
      rw [sum_configurationCellCount_row, hrowzero a]
    exact (Finset.sum_eq_zero_iff.mp hsum) b (Finset.mem_univ b)
  have hevent : ∀ matching : ConfigurationMatching row col,
      matching ∈ ResidualCapNoReturnEvent M R row col := by
    intro matching
    constructor
    · intro a b
      simp [hcellzero matching a b]
    · intro e he
      simp [hcellzero matching e.1 e.2]
  have hfamily : ∀ matching : ConfigurationMatching row col,
      actualResidualEvenEdgeSets M matching = {∅} := by
    intro matching
    ext F
    constructor
    · intro hF
      simp only [actualResidualEvenEdgeSets, Finset.mem_filter,
        bipartiteEvenEdgeSets, Finset.mem_univ, true_and] at hF
      have hsubset : F ⊆ M := by
        intro e he
        simpa [hcellzero matching e.1 e.2] using hF.2 e he
      have hFempty := bipartiteEven_subset_matching_eq_empty hF.1 hsubset hM
      simp [hFempty]
    · intro hF
      have hFempty : F = ∅ := by simpa using hF
      subst F
      simp [actualResidualEvenEdgeSets, bipartiteEvenEdgeSets, IsBipartiteEven]
  unfold residualActualAttachmentNumerator
  simp_rw [hevent, if_pos, hfamily, hcellzero]
  simp [residualReward]
  simpa only [tsum_fintype] using
    (uniformConfigurationMatching row col htotal).tsum_coe

/-- A zero-residual canonical raw attachment term is exactly its bare
reward-incidence factor when the exposed positive support is a matching.

The proof was returned by Aristotle project
`0b749129-9b66-4f12-b932-6dabeb7a7c81`, task
`cad19486-ee21-4bcf-ae17-9b123954453b`, and independently audited before
integration. -/
theorem canonicalDemandRawAttachmentTerm_eq_bare_of_residualTotal_zero_of_matching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (demand : canonicalDemandImage row col U)
    (hzero : canonicalDemandResidualTotal row col U demand = 0)
    (hmatching : IsBipartiteMatching (positiveDemandSupport demand.1)) :
    canonicalDemandRawAttachmentTerm row col U htotal demand =
      (canonicalDemandLocalReward demand : ENNReal) *
        labelledWitnessIncidence demand.1 row col := by
  let witness := canonicalDemandReferenceWitness row col U demand
  have hrowTotal : Finset.univ.sum (residualRowDegree witness) = 0 := by
    simpa only [canonicalDemandResidualTotal, witness] using hzero
  have hatt :
      residualActualAttachmentNumerator
          (positiveDemandSupport demand.1) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness)
          (sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness) = 1 :=
    residualActualAttachmentNumerator_eq_one_of_total_zero_of_matching
      (positiveDemandSupport demand.1) (U / 2)
      (residualRowDegree witness) (residualColumnDegree witness)
      (sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness)
      hrowTotal hmatching
  unfold canonicalDemandRawAttachmentTerm
  change (canonicalDemandLocalReward demand : ENNReal) *
      (labelledWitnessIncidence demand.1 row col *
        residualActualAttachmentNumerator
          (positiveDemandSupport demand.1) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness)
          (sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness)) = _
  rw [hatt, mul_one]

/-- Every canonical polymer majorant is at least one. -/
theorem one_le_canonicalDemandPolymerMajorant
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (demand : canonicalDemandImage row col U) :
    1 ≤ canonicalDemandPolymerMajorant row col U demand := by
  unfold canonicalDemandPolymerMajorant
  apply one_le_mul
  · apply Finset.one_le_prod
    intro a _
    apply Finset.one_le_prod
    intro b _
    exact le_add_right (le_refl 1)
  · apply Finset.one_le_prod
    intro C _
    exact le_add_right (le_refl 1)

/-- The literal residual attachment is bounded by its canonical polymer
majorant in both residual regimes. -/
theorem profileHighSkeletonAttachment_le_polymerMajorant
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U)
    (demand : ProfileCanonicalHighSkeleton k U) :
    profileHighSkeletonAttachment row₀ U demand ≤
      canonicalDemandPolymerMajorant
        (profileBlockMargin k) (profileBlockMargin k) U demand := by
  let witness := canonicalDemandReferenceWitness (profileBlockMargin k)
    (profileBlockMargin k) U demand
  let M := positiveDemandSupport demand.1
  let row := residualRowDegree witness
  let col := residualColumnDegree witness
  let htotal := sum_residualRowDegree_eq_sum_residualColumnDegree
    (profileBlockMargin_total_eq_self row₀) witness
  by_cases hm : 0 < Finset.univ.sum row
  · unfold profileHighSkeletonAttachment
    exact residualActualAttachmentNumerator_le_lambdaProduct_mul_polymerProduct
      M (U / 2) row col htotal hm
  · have hmzero : Finset.univ.sum row = 0 := Nat.eq_zero_of_not_pos hm
    have hM : IsBipartiteMatching M :=
      profileHighSkeleton_positiveSupport_isBipartiteMatching k U hcap demand
    unfold profileHighSkeletonAttachment
    rw [residualActualAttachmentNumerator_eq_one_of_total_zero_of_matching
      M (U / 2) row col htotal hmzero hM]
    exact one_le_canonicalDemandPolymerMajorant
      (profileBlockMargin k) (profileBlockMargin k) U demand

/-- Attained-demand polymer majorization with the zero- and positive-residual
cases discharged internally. The structural degree-cap hypothesis remains
explicit because it makes each attained high support a matching. -/
theorem sum_uniformProfile_signedOverlapReward_le_skeletonPolymerSum_unconditional
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ)
    (hU : 2 ≤ U)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) :
    (∑ column : OrderedProfilePartition n k,
      uniformOrderedProfilePartition row₀ column *
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) ≤
      ∑ demand : ProfileCanonicalHighSkeleton k U,
        (canonicalDemandLocalReward demand : ENNReal) *
          (labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k) *
            canonicalDemandPolymerMajorant
              (profileBlockMargin k) (profileBlockMargin k) U demand) := by
  rw [sum_uniformProfile_signedOverlapReward_eq_sum_profileHighSkeletonContribution
    row₀ U hU]
  unfold profileHighSkeletonContribution profileHighSkeletonWeight
  apply Finset.sum_le_sum
  intro demand _
  calc
    (canonicalDemandLocalReward demand : ENNReal) *
          labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k) *
        profileHighSkeletonAttachment row₀ U demand =
      (canonicalDemandLocalReward demand : ENNReal) *
        (labelledWitnessIncidence demand.1 (profileBlockMargin k)
          (profileBlockMargin k) *
          profileHighSkeletonAttachment row₀ U demand) := by rw [mul_assoc]
    _ ≤ (canonicalDemandLocalReward demand : ENNReal) *
        (labelledWitnessIncidence demand.1 (profileBlockMargin k)
          (profileBlockMargin k) *
          canonicalDemandPolymerMajorant
            (profileBlockMargin k) (profileBlockMargin k) U demand) := by
      exact mul_le_mul_right
        (mul_le_mul_right
          (profileHighSkeletonAttachment_le_polymerMajorant
            row₀ U hcap demand)
          (labelledWitnessIncidence demand.1 (profileBlockMargin k)
            (profileBlockMargin k)))
        (canonicalDemandLocalReward demand : ENNReal)

#print axioms bipartiteEven_subset_matching_eq_empty
#print axioms residualActualAttachmentNumerator_eq_one_of_total_zero_of_matching
#print axioms canonicalDemandRawAttachmentTerm_eq_bare_of_residualTotal_zero_of_matching
#print axioms one_le_canonicalDemandPolymerMajorant
#print axioms profileHighSkeletonAttachment_le_polymerMajorant
#print axioms sum_uniformProfile_signedOverlapReward_le_skeletonPolymerSum_unconditional

end

end Erdos625
