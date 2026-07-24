import Erdos625.SignedProfileWitness
import Erdos625.RandomGraphMixedEdgePrescription
import Erdos625.ProfileOverlapDuplicateEdges
import Erdos625.Section6SignedOverlapLocalFactor
import Erdos625.Section6PairSignCompatibility
import Mathlib.Tactic

/-!
# Section VI: exact joint mass of two signed profile witnesses

This file connects the graph-level signed witness event to the finite local
factor.  Every assertion is pointwise on the finite graph sample space.
-/

namespace Erdos625

open MeasureTheory SimpleGraph
open scoped BigOperators ENNReal symmDiff

noncomputable section

/-- Internal edges required absent by a signed profile witness. -/
def signedProfileAbsentGraph {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) : LabeledGraph n :=
  P.1.parts.attach.sup fun B => if σ B then ⊥ else completeOn B.1

/-- The required-present and required-absent graphs of one witness are
edge-disjoint. -/
theorem signedProfileInternalGraph_disjoint_absent
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    Disjoint (signedProfileInternalGraph P σ) (signedProfileAbsentGraph P σ) := by
  classical
  unfold signedProfileInternalGraph signedProfileAbsentGraph
  rw [Finset.disjoint_sup_left]
  intro A hA
  rw [Finset.disjoint_sup_right]
  intro B hB
  by_cases hAB : A = B
  · subst B
    cases hsign : σ A <;> simp
  · by_cases hAtrue : σ A
    · rw [if_pos hAtrue]
      by_cases hBtrue : σ B
      · simp [hBtrue]
      · rw [if_neg hBtrue]
        exact disjoint_completeOn_of_disjoint
          (P.1.disjoint A.2 B.2 (by simpa using hAB))
    · simp [hAtrue]

/-- Together the two signed prescription graphs are exactly all internal
edges of the underlying partition. -/
theorem signedProfileInternalGraph_sup_absent
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    signedProfileInternalGraph P σ ⊔ signedProfileAbsentGraph P σ =
      partitionInternalGraph P.1 := by
  classical
  apply le_antisymm
  · apply sup_le
    · exact signedProfileInternalGraph_le_partitionInternalGraph P σ
    · unfold signedProfileAbsentGraph partitionInternalGraph
      rw [Finset.sup_le_iff]
      intro B hB
      cases hsign : σ B with
      | false =>
          simp only [Bool.false_eq]
          exact Finset.le_sup
            (f := fun C : Finset (Fin n) => completeOn C) B.2
      | true => simp
  · unfold partitionInternalGraph
    rw [Finset.sup_le_iff]
    intro B hB
    let B' : P.1.parts := ⟨B, hB⟩
    cases hsign : σ B' with
    | false =>
        apply le_sup_of_le_right
        unfold signedProfileAbsentGraph
        refine Finset.le_sup_of_le (Finset.mem_attach P.1.parts B') ?_
        simp [hsign, B']
    | true =>
        apply le_sup_of_le_left
        exact completeOn_le_signedProfileInternalGraph_of_sign_true
          P σ B' hsign

/-- A false-signed part contributes its complete graph to the absent
prescription. -/
theorem completeOn_le_signedProfileAbsentGraph_of_sign_false
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool)
    (B : P.1.parts) (hB : σ B = false) :
    completeOn B.1 ≤ signedProfileAbsentGraph P σ := by
  classical
  unfold signedProfileAbsentGraph
  refine Finset.le_sup_of_le (Finset.mem_attach P.1.parts B) ?_
  simp [hB]

private theorem completeOn_adj_iff_mem {V : Type*} [DecidableEq V]
    (S : Finset V) (v w : V) :
    (completeOn S).Adj v w ↔ v ≠ w ∧ v ∈ S ∧ w ∈ S := by
  rw [completeOn, SimpleGraph.map_adj]
  constructor
  · rintro ⟨v', w', hvw', rfl, rfl⟩
    exact ⟨by simpa using hvw', v'.2, w'.2⟩
  · rintro ⟨hvw, hv, hw⟩
    exact ⟨⟨v, hv⟩, ⟨w, hw⟩, by simpa using hvw, rfl, rfl⟩

private theorem disjoint_completeOn_of_inter_card_lt_two
    {V : Type*} [DecidableEq V] (A B : Finset V)
    (hcard : (A ∩ B).card < 2) :
    Disjoint (completeOn A) (completeOn B) := by
  rw [SimpleGraph.disjoint_left]
  intro v w hA hB
  obtain ⟨hvw, hvA, hwA⟩ := (completeOn_adj_iff_mem A v w).mp hA
  obtain ⟨_, hvB, hwB⟩ := (completeOn_adj_iff_mem B v w).mp hB
  have hsubset : ({v, w} : Finset V) ⊆ A ∩ B := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hvA, hvB⟩
    · exact Finset.mem_inter.mpr ⟨hwA, hwB⟩
  have htwo : 2 ≤ (A ∩ B).card := by
    rw [← Finset.card_pair hvw]
    exact Finset.card_le_card hsubset
  omega

private theorem not_disjoint_completeOn_of_two_le_inter_card
    {V : Type*} [DecidableEq V] (A B : Finset V)
    (hcard : 2 ≤ (A ∩ B).card) :
    ¬ Disjoint (completeOn A) (completeOn B) := by
  intro hdis
  obtain ⟨v, hv, w, hw, hvw⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (A ∩ B).card)
  have hA : (completeOn A).Adj v w :=
    (completeOn_adj_iff_mem A v w).mpr
      ⟨hvw, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hw).1⟩
  have hB : (completeOn B).Adj v w :=
    (completeOn_adj_iff_mem B v w).mpr
      ⟨hvw, (Finset.mem_inter.mp hv).2, (Finset.mem_inter.mp hw).2⟩
  exact (SimpleGraph.disjoint_left.mp hdis v w hA) hB

/-- A fixed signed witness is precisely its mixed present/absent edge
prescription. -/
theorem signedProfileWitnessEvent_eq_mixedEdgePrescriptionEvent
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    signedProfileWitnessEvent P σ =
      mixedEdgePrescriptionEvent
        (signedProfileInternalGraph P σ) (signedProfileAbsentGraph P σ) := by
  ext G
  rw [signedProfileWitnessEvent, Set.mem_setOf_eq,
    mixedEdgePrescriptionEvent, Set.mem_setOf_eq]
  constructor
  · intro hvalid
    constructor
    · unfold signedProfileInternalGraph
      rw [Finset.sup_le_iff]
      intro B hB
      cases hsign : σ B with
      | false => simp
      | true =>
          simp only [↓reduceIte]
          exact (isClique_iff_completeOn_le G B.1).mp
            (by simpa [hsign] using hvalid B)
    · apply le_compl_iff_disjoint_right.mpr
      unfold signedProfileAbsentGraph
      rw [Finset.disjoint_sup_right]
      intro B hB
      cases hsign : σ B with
      | false =>
          simp only [Bool.false_eq]
          exact (isIndepSet_iff_disjoint_completeOn G B.1).mp
            (by simpa [hsign] using hvalid B)
      | true => simp
  · rintro ⟨hpresent, habsent⟩ B
    cases hsign : σ B with
    | false =>
        have hdis : Disjoint G (signedProfileAbsentGraph P σ) :=
          le_compl_iff_disjoint_right.mp habsent
        have hpart : Disjoint G (completeOn B.1) := by
          apply hdis.mono_right
          unfold signedProfileAbsentGraph
          refine Finset.le_sup_of_le
            (Finset.mem_attach P.1.parts B) ?_
          simp [hsign]
        simpa [hsign] using
          (isIndepSet_iff_disjoint_completeOn G B.1).mpr hpart
    | true =>
        have hpart : completeOn B.1 ≤ signedProfileInternalGraph P σ :=
          completeOn_le_signedProfileInternalGraph_of_sign_true P σ B hsign
        simpa [hsign] using
          (isClique_iff_completeOn_le G B.1).mpr (hpart.trans hpresent)

/-- The joint event of two fixed signed witnesses. -/
def signedProfilePairEvent {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    Set (LabeledGraph n) :=
  signedProfileWitnessEvent P σ ∩ signedProfileWitnessEvent Q τ

/-- Combined required-present internal edges. -/
def signedProfilePairPresentGraph {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    LabeledGraph n :=
  signedProfileInternalGraph P σ ⊔ signedProfileInternalGraph Q τ

/-- Combined required-absent internal edges. -/
def signedProfilePairAbsentGraph {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    LabeledGraph n :=
  signedProfileAbsentGraph P σ ⊔ signedProfileAbsentGraph Q τ

private theorem signedInternal_disjoint_signedAbsent_of_compatible
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool)
    (hcompat : ∀ A B, 2 ≤ P.overlapCellCount Q A B → σ A = τ B) :
    Disjoint (signedProfileInternalGraph P σ)
      (signedProfileAbsentGraph Q τ) := by
  classical
  unfold signedProfileInternalGraph signedProfileAbsentGraph
  rw [Finset.disjoint_sup_left]
  intro A hA
  rw [Finset.disjoint_sup_right]
  intro B hB
  cases hσ : σ A with
  | false => simp
  | true =>
      cases hτ : τ B with
      | true => simp
      | false =>
          change Disjoint (completeOn A.1) (completeOn B.1)
          apply disjoint_completeOn_of_inter_card_lt_two
          have hn : ¬ 2 ≤ P.overlapCellCount Q A B := by
            intro htwo
            have := hcompat A B htwo
            simp [hσ, hτ] at this
          have hn' : ¬ 2 ≤ (A.1 ∩ B.1).card := by
            simpa [ProfilePartition.overlapCellCount,
              profileOverlapCellCount] using hn
          omega

private theorem signedAbsent_disjoint_signedInternal_of_compatible
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool)
    (hcompat : ∀ A B, 2 ≤ P.overlapCellCount Q A B → σ A = τ B) :
    Disjoint (signedProfileAbsentGraph P σ)
      (signedProfileInternalGraph Q τ) := by
  apply Disjoint.symm
  apply signedInternal_disjoint_signedAbsent_of_compatible Q P τ σ
  intro B A htwo
  have htwo' : 2 ≤ P.overlapCellCount Q A B := by
    simpa [ProfilePartition.overlapCellCount, profileOverlapCellCount,
      Finset.inter_comm] using htwo
  exact (hcompat A B htwo').symm

/-- Cellwise sign compatibility is exactly edge-disjointness of the combined
present and absent prescriptions. -/
theorem signedProfilePair_prescriptions_disjoint_iff_compatible
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    Disjoint (signedProfilePairPresentGraph P Q σ τ)
        (signedProfilePairAbsentGraph P Q σ τ) ↔
      ∀ A B, 2 ≤ P.overlapCellCount Q A B → σ A = τ B := by
  constructor
  · intro hdis A B htwo
    cases hσ : σ A with
    | false =>
        cases hτ : τ B with
        | false => rfl
        | true =>
            exfalso
            apply not_disjoint_completeOn_of_two_le_inter_card B.1 A.1
              (by simpa [ProfilePartition.overlapCellCount,
                profileOverlapCellCount, Finset.inter_comm] using htwo)
            apply hdis.mono
            · apply le_sup_of_le_right
              exact completeOn_le_signedProfileInternalGraph_of_sign_true
                Q τ B hτ
            · apply le_sup_of_le_left
              exact completeOn_le_signedProfileAbsentGraph_of_sign_false
                P σ A hσ
    | true =>
        cases hτ : τ B with
        | true => rfl
        | false =>
            exfalso
            apply not_disjoint_completeOn_of_two_le_inter_card A.1 B.1
              (by simpa [ProfilePartition.overlapCellCount,
                profileOverlapCellCount] using htwo)
            apply hdis.mono
            · apply le_sup_of_le_left
              exact completeOn_le_signedProfileInternalGraph_of_sign_true
                P σ A hσ
            · apply le_sup_of_le_right
              exact completeOn_le_signedProfileAbsentGraph_of_sign_false
                Q τ B hτ
  · intro hcompat
    rw [signedProfilePairPresentGraph, signedProfilePairAbsentGraph,
      disjoint_sup_left, disjoint_sup_right, disjoint_sup_right]
    exact ⟨⟨signedProfileInternalGraph_disjoint_absent P σ,
      signedInternal_disjoint_signedAbsent_of_compatible P Q σ τ hcompat⟩,
      (signedAbsent_disjoint_signedInternal_of_compatible P Q σ τ hcompat).symm,
      signedProfileInternalGraph_disjoint_absent Q τ⟩

/-- Intersecting two signed witness events combines their present and absent
prescriptions.  No compatibility assumption is needed for this identity. -/
theorem signedProfilePairEvent_eq_mixedEdgePrescriptionEvent
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    signedProfilePairEvent P Q σ τ =
      mixedEdgePrescriptionEvent
        (signedProfilePairPresentGraph P Q σ τ)
        (signedProfilePairAbsentGraph P Q σ τ) := by
  rw [signedProfilePairEvent,
    signedProfileWitnessEvent_eq_mixedEdgePrescriptionEvent P σ,
    signedProfileWitnessEvent_eq_mixedEdgePrescriptionEvent Q τ]
  ext G
  simp only [Set.mem_inter_iff, mixedEdgePrescriptionEvent, Set.mem_setOf_eq,
    signedProfilePairPresentGraph, signedProfilePairAbsentGraph,
    sup_le_iff, compl_sup]
  constructor
  · rintro ⟨⟨hp, ha⟩, hq, hb⟩
    exact ⟨⟨hp, hq⟩, le_inf ha hb⟩
  · rintro ⟨⟨hp, hq⟩, hab⟩
    exact ⟨⟨hp, hab.trans inf_le_left⟩, hq, hab.trans inf_le_right⟩

/-- Incompatible row/column signs impose a contradictory edge prescription,
so the joint witness event is empty. -/
theorem signedProfilePairEvent_eq_empty_of_incompatible
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool)
    (hincompat : ¬ ∀ A B,
      2 ≤ P.overlapCellCount Q A B → σ A = τ B) :
    signedProfilePairEvent P Q σ τ = ∅ := by
  rw [signedProfilePairEvent_eq_mixedEdgePrescriptionEvent]
  ext G
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hG
  have hforced : Disjoint
      (signedProfilePairPresentGraph P Q σ τ)
      (signedProfilePairAbsentGraph P Q σ τ) := by
    rw [mixedEdgePrescriptionEvent, Set.mem_setOf_eq] at hG
    exact (le_compl_iff_disjoint_right.mp hG.2).mono_left hG.1
  exact hincompat
    ((signedProfilePair_prescriptions_disjoint_iff_compatible P Q σ τ).mp
      hforced)

/-- The combined present and absent graphs exhaust the union of the two
partition-internal graphs. -/
theorem signedProfilePairPresent_sup_absent
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    signedProfilePairPresentGraph P Q σ τ ⊔
        signedProfilePairAbsentGraph P Q σ τ =
      partitionInternalGraph P.1 ⊔ partitionInternalGraph Q.1 := by
  rw [signedProfilePairPresentGraph, signedProfilePairAbsentGraph]
  calc
    (signedProfileInternalGraph P σ ⊔ signedProfileInternalGraph Q τ) ⊔
        (signedProfileAbsentGraph P σ ⊔ signedProfileAbsentGraph Q τ) =
      (signedProfileInternalGraph P σ ⊔ signedProfileAbsentGraph P σ) ⊔
        (signedProfileInternalGraph Q τ ⊔ signedProfileAbsentGraph Q τ) := by
          ac_rfl
    _ = partitionInternalGraph P.1 ⊔ partitionInternalGraph Q.1 := by
      rw [signedProfileInternalGraph_sup_absent,
        signedProfileInternalGraph_sup_absent]

private theorem overlapDuplicateEdgeCount_profile_eq
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) :
    overlapDuplicateEdgeCount (fun A B => P.overlapCellCount Q A B) =
      ∑ A ∈ P.1.parts, ∑ B ∈ Q.1.parts,
        (profileOverlapCellCount A B).choose 2 := by
  classical
  simp [overlapDuplicateEdgeCount, ProfilePartition.overlapCellCount,
    profileOverlapCellCount]
  calc
    (∑ A ∈ P.1.parts.attach, ∑ B ∈ Q.1.parts.attach,
        (A.1 ∩ B.1).card.choose 2) =
      ∑ A ∈ P.1.parts.attach, ∑ B ∈ Q.1.parts,
        (A.1 ∩ B).card.choose 2 := by
          apply Finset.sum_congr rfl
          intro A hA
          exact Finset.sum_attach Q.1.parts
            (fun B => (A.1 ∩ B).card.choose 2)
    _ = ∑ A ∈ P.1.parts, ∑ B ∈ Q.1.parts,
        (A ∩ B).card.choose 2 :=
      Finset.sum_attach P.1.parts
        (fun A => ∑ B ∈ Q.1.parts, (A ∩ B).card.choose 2)

/-- For compatible signs the total number of prescribed edge bits is exactly
`2 B_k - W`, stated without truncated subtraction. -/
theorem signedProfilePair_prescribedEdgeCount_add_overlap
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool)
    (hcompat : ∀ A B,
      2 ≤ P.overlapCellCount Q A B → σ A = τ B) :
    (signedProfilePairPresentGraph P Q σ τ).edgeSet.ncard +
        (signedProfilePairAbsentGraph P Q σ τ).edgeSet.ncard +
        overlapDuplicateEdgeCount (fun A B => P.overlapCellCount Q A B) =
      2 * ColoringProfile.forbiddenEdges k := by
  have hdis : Disjoint
      (signedProfilePairPresentGraph P Q σ τ)
      (signedProfilePairAbsentGraph P Q σ τ) :=
    (signedProfilePair_prescriptions_disjoint_iff_compatible P Q σ τ).mpr
      hcompat
  have hcard :
      (signedProfilePairPresentGraph P Q σ τ ⊔
          signedProfilePairAbsentGraph P Q σ τ).edgeSet.ncard =
        (signedProfilePairPresentGraph P Q σ τ).edgeSet.ncard +
          (signedProfilePairAbsentGraph P Q σ τ).edgeSet.ncard := by
    rw [SimpleGraph.edgeSet_sup]
    exact Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr hdis)
  rw [← hcard, signedProfilePairPresent_sup_absent,
    overlapDuplicateEdgeCount_profile_eq]
  exact ncard_profilePartitionInternalGraph_edgeSet_union_add_overlap P Q

/-- Subtraction form of the exact prescribed-bit count. -/
theorem signedProfilePair_prescribedEdgeCount
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool)
    (hcompat : ∀ A B,
      2 ≤ P.overlapCellCount Q A B → σ A = τ B) :
    (signedProfilePairPresentGraph P Q σ τ).edgeSet.ncard +
        (signedProfilePairAbsentGraph P Q σ τ).edgeSet.ncard =
      2 * ColoringProfile.forbiddenEdges k -
        overlapDuplicateEdgeCount (fun A B => P.overlapCellCount Q A B) := by
  have h := signedProfilePair_prescribedEdgeCount_add_overlap P Q σ τ hcompat
  omega

/-- Exact joint probability for a compatible pair of signs. -/
theorem randomGraphMeasure_signedProfilePairEvent_of_compatible
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool)
    (hcompat : ∀ A B,
      2 ≤ P.overlapCellCount Q A B → σ A = τ B) :
    randomGraphMeasure n (signedProfilePairEvent P Q σ τ) =
      (1 / 2 : ENNReal) ^
        (2 * ColoringProfile.forbiddenEdges k -
          overlapDuplicateEdgeCount (fun A B => P.overlapCellCount Q A B)) := by
  rw [signedProfilePairEvent_eq_mixedEdgePrescriptionEvent,
    randomGraphMeasure_mixedEdgePrescriptionEvent _ _
      ((signedProfilePair_prescriptions_disjoint_iff_compatible P Q σ τ).mpr
        hcompat),
    signedProfilePair_prescribedEdgeCount P Q σ τ hcompat]

/-- Joint mass summed over every row-sign and column-sign assignment for a
fixed pair of profile partitions. -/
noncomputable def signedProfilePairMassSum
    {b : ℕ} (n : ℕ) {k : ColoringProfile b}
    (P Q : ProfilePartition n k) : ENNReal :=
  ∑ σ : P.1.parts → Bool, ∑ τ : Q.1.parts → Bool,
    randomGraphMeasure n (signedProfilePairEvent P Q σ τ)

/-- Exact sign-summed joint mass before applying the local-factor identity. -/
theorem signedProfilePairMassSum_eq_compatibleCard_mul
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) :
    signedProfilePairMassSum n P Q =
      (Nat.card (CompatiblePairSignAssignments
        (fun A B => P.overlapCellCount Q A B)) : ENNReal) *
      (1 / 2 : ENNReal) ^
        (2 * ColoringProfile.forbiddenEdges k -
          overlapDuplicateEdgeCount
            (fun A B => P.overlapCellCount Q A B)) := by
  classical
  let r := fun A B => P.overlapCellCount Q A B
  let p : ENNReal := (1 / 2 : ENNReal) ^
    (2 * ColoringProfile.forbiddenEdges k - overlapDuplicateEdgeCount r)
  have hterm (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
      randomGraphMeasure n (signedProfilePairEvent P Q σ τ) =
        if (∀ A B, 2 ≤ r A B → σ A = τ B) then p else 0 := by
    by_cases hcompat : ∀ A B, 2 ≤ r A B → σ A = τ B
    · rw [if_pos hcompat]
      simpa [r, p] using
        randomGraphMeasure_signedProfilePairEvent_of_compatible
          P Q σ τ hcompat
    · rw [if_neg hcompat,
        signedProfilePairEvent_eq_empty_of_incompatible P Q σ τ hcompat]
      simp
  unfold signedProfilePairMassSum
  simp_rw [hterm]
  rw [← Fintype.sum_prod_type']
  change (∑ s : PairBoolSignAssignments P.1.parts Q.1.parts,
      if (∀ A B, 2 ≤ r A B → s.1 A = s.2 B) then p else 0) =
    (Nat.card (CompatiblePairSignAssignments r) : ENNReal) * p
  let T := (Finset.univ : Finset
    (PairBoolSignAssignments P.1.parts Q.1.parts)).filter
      fun s => ∀ A B, 2 ≤ r A B → s.1 A = s.2 B
  let e : {s // s ∈ T} ≃ CompatiblePairSignAssignments r := {
    toFun := fun s => ⟨s.1, by simpa [T] using s.2⟩
    invFun := fun s => ⟨s.1, by simpa [T] using s.2⟩
    left_inv := fun s => by apply Subtype.ext; rfl
    right_inv := fun s => by apply Subtype.ext; rfl }
  have hTcard : T.card = Nat.card (CompatiblePairSignAssignments r) := by
    calc
      T.card = Nat.card {s // s ∈ T} := by
        rw [Nat.card_eq_fintype_card]
        simp
      _ = Nat.card (CompatiblePairSignAssignments r) := Nat.card_congr e
  calc
    _ = ∑ _s ∈ T, p := by
      simpa only [T] using
        (Finset.sum_filter
          (fun s : PairBoolSignAssignments P.1.parts Q.1.parts =>
            ∀ A B, 2 ≤ r A B → s.1 A = s.2 B)
          (fun _s => p)).symm
    _ = (T.card : ENNReal) * p := by simp [nsmul_eq_mul]
    _ = (Nat.card (CompatiblePairSignAssignments r) : ENNReal) * p := by
      rw [hTcard]

private theorem half_pow_sub_mul_two_pow
    (a w : ℕ) (hw : w ≤ a) :
    (1 / 2 : ENNReal) ^ (a - w) * (2 : ENNReal) ^ a =
      (2 : ENNReal) ^ w := by
  conv_lhs =>
    rhs
    rw [show a = (a - w) + w by omega, pow_add]
  rw [← mul_assoc, ← mul_pow]
  rw [div_eq_mul_inv, one_mul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- Denominator-free normalized pair mass.  Multiplication by `2^(2B_k)`
clears the common one-witness edge probability, and the remaining factor is
exactly the signed-overlap reward. -/
theorem signedProfilePairMassSum_mul_two_pow_forbiddenEdges
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k) :
    signedProfilePairMassSum n P Q *
        (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
      (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) *
        (signedOverlapReward
          (fun A B => P.overlapCellCount Q A B) : ENNReal) := by
  classical
  let r := fun A B => P.overlapCellCount Q A B
  let W := overlapDuplicateEdgeCount r
  let Bk := ColoringProfile.forbiddenEdges k
  let K := ColoringProfile.partCount k
  have hW : W ≤ 2 * Bk := by
    have h := ncard_profilePartitionInternalGraph_edgeSet_union_add_overlap P Q
    rw [← overlapDuplicateEdgeCount_profile_eq P Q] at h
    change (partitionInternalGraph P.1 ⊔
      partitionInternalGraph Q.1).edgeSet.ncard + W = 2 * Bk at h
    omega
  have hPc : Fintype.card P.1.parts = K := by
    simpa [K] using P.card_parts_eq
  have hQc : Fintype.card Q.1.parts = K := by
    simpa [K] using Q.card_parts_eq
  have hPairCard :
      Nat.card (CompatiblePairSignAssignments r) =
        Nat.card (CompatibleOverlapSignAssignments r) :=
    natCard_compatiblePairSignAssignments_eq_overlap r
  have hNat :
      Nat.card (CompatiblePairSignAssignments r) * 2 ^ W =
        2 ^ (2 * K) * signedOverlapReward r := by
    rw [hPairCard]
    have hlocal := signedOverlapLocalFactor_cross r
    simpa [W, K, hPc, hQc, two_mul] using hlocal
  have hCast := congrArg (fun x : ℕ => (x : ENNReal)) hNat
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hCast
  rw [signedProfilePairMassSum_eq_compatibleCard_mul]
  change ((Nat.card (CompatiblePairSignAssignments r) : ENNReal) *
      (1 / 2 : ENNReal) ^ (2 * Bk - W)) *
      (2 : ENNReal) ^ (2 * Bk) =
    (2 : ENNReal) ^ (2 * K) * (signedOverlapReward r : ENNReal)
  rw [mul_assoc, half_pow_sub_mul_two_pow (2 * Bk) W hW]
  exact hCast

#print axioms signedProfileWitnessEvent_eq_mixedEdgePrescriptionEvent
#print axioms signedProfilePair_prescriptions_disjoint_iff_compatible
#print axioms signedProfilePairEvent_eq_empty_of_incompatible
#print axioms signedProfilePair_prescribedEdgeCount_add_overlap
#print axioms randomGraphMeasure_signedProfilePairEvent_of_compatible
#print axioms signedProfilePairMassSum_eq_compatibleCard_mul
#print axioms signedProfilePairMassSum_mul_two_pow_forbiddenEdges

end

end Erdos625
