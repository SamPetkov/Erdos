import Erdos625.ColoringProfileFirstMoment
import Mathlib.Tactic

/-!
# Signed profile witnesses

This file contains the deterministic graph-level layer of the signed
cocolouring count used in the second-moment argument.  A witness is an
unordered profile partition together with one Boolean sign per nonempty part:
`false` requires that part to be independent and `true` requires it to be a
clique.

The key point here is deliberately finite and pointwise: a valid signed
witness produces an actual `CoColoring`, and hence positivity of the count
implies cocolourability with the advertised number of parts.  No
probabilistic estimate is hidden in this implication.
-/

namespace Erdos625

open MeasureTheory SimpleGraph
open scoped BigOperators ENNReal symmDiff

noncomputable section

/-- A sign assignment is valid when every signed profile part is respectively
an independent set (`false`) or a clique (`true`). -/
def profileSignValid {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) : Prop :=
  ∀ B : P.1.parts,
    match σ B with
    | false => G.IsIndepSet (B.1 : Set (Fin n))
    | true => G.IsClique (B.1 : Set (Fin n))

/-- An unordered profile partition together with a Boolean independent/clique
sign on each of its nonempty parts. -/
abbrev SignedProfileWitness {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) :=
  Σ P : ProfilePartition n k, P.1.parts → Bool

/-- Validity of a signed profile witness in a labelled graph. -/
def validSignedProfileWitness {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (w : SignedProfileWitness n k) : Prop :=
  profileSignValid G w.1 w.2

/-- The number of valid signed witnesses of the fixed profile. -/
noncomputable def signedProfileCount {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) : ℕ := by
  classical
  exact (Finset.univ.filter fun w : SignedProfileWitness n k =>
    validSignedProfileWitness G w).card

/-- The graph made of precisely the internal complete graphs of the parts
given clique sign.  It is the edge-toggle used to reduce a mixed signed
witness to the all-independent event for the same partition. -/
noncomputable def signedProfileInternalGraph {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) : LabeledGraph n :=
  P.1.parts.attach.sup fun B => if σ B then completeOn B.1 else ⊥

/-- The signed internal graph is contained in the graph of all internal
partition edges. -/
theorem signedProfileInternalGraph_le_partitionInternalGraph
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    signedProfileInternalGraph P σ ≤ partitionInternalGraph P.1 := by
  classical
  unfold signedProfileInternalGraph partitionInternalGraph
  refine Finset.sup_le_iff.mpr ?_
  intro B hB
  by_cases hσ : σ B
  · simp only [hσ, ite_true]
    exact Finset.le_sup B.2
  · simp [hσ]

/-- A clique-signed part contributes its entire internal complete graph to the
toggle graph. -/
theorem completeOn_le_signedProfileInternalGraph_of_sign_true
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool)
    (B : P.1.parts) (hB : σ B = true) :
    completeOn B.1 ≤ signedProfileInternalGraph P σ := by
  classical
  unfold signedProfileInternalGraph
  refine Finset.le_sup_of_le
    (s := P.1.parts.attach)
    (f := fun C => if σ C then completeOn C.1 else ⊥)
    (Finset.mem_attach P.1.parts B) ?_
  simp [hB]

/-- A part carrying the independent sign is edge-disjoint from the toggle
graph.  The proof uses disjointness of distinct `Finpartition` parts, rather
than treating the signed graph as an informal edge list. -/
theorem signedProfileInternalGraph_disjoint_completeOn_of_sign_false
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool)
    (B : P.1.parts) (hB : σ B = false) :
    Disjoint (signedProfileInternalGraph P σ) (completeOn B.1) := by
  classical
  unfold signedProfileInternalGraph
  rw [Finset.disjoint_sup_left]
  intro C hC
  by_cases hCsign : σ C
  · rw [if_pos hCsign]
    apply disjoint_completeOn_of_disjoint
    apply P.1.disjoint C.2 B.2
    intro hCB
    have hCB' : C = B := Subtype.ext hCB
    subst C
    simp [hB] at hCsign
  · simp [hCsign]

/-- A finite set is a clique exactly when its supported complete graph is a
subgraph of the ambient graph. -/
theorem isClique_iff_completeOn_le {n : ℕ} (G : LabeledGraph n)
    (S : Finset (Fin n)) :
    G.IsClique (S : Set (Fin n)) ↔ completeOn S ≤ G := by
  constructor
  · intro h x y hxy
    rw [completeOn, SimpleGraph.map_adj] at hxy
    obtain ⟨x', y', hne, rfl, rfl⟩ := hxy
    exact h x'.property y'.property (by simpa using hne)
  · intro h x hx y hy hxy
    apply h
    rw [completeOn, SimpleGraph.map_adj]
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, by simpa using hxy, rfl, rfl⟩

/-- Toggling all clique-signed internal edges leaves no edge of that clique
part in the toggle remainder. -/
theorem signedProfileInternalGraph_symmDiff_completeOn_disjoint_of_sign_true
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool)
    (B : P.1.parts) (hB : σ B = true) :
    Disjoint
      (signedProfileInternalGraph P σ ∆ completeOn B.1)
      (completeOn B.1) := by
  have hle : completeOn B.1 ≤ signedProfileInternalGraph P σ :=
    completeOn_le_signedProfileInternalGraph_of_sign_true P σ B hB
  rw [symmDiff_of_ge hle]
  exact disjoint_sdiff_self_left

/-- On an independently signed part, toggling clique-signed internal edges
does not alter the independence condition. -/
theorem isIndepSet_symmDiff_signedProfileInternalGraph_iff_of_sign_false
    {b n : ℕ} {k : ColoringProfile b} (G : LabeledGraph n)
    (P : ProfilePartition n k) (σ : P.1.parts → Bool)
    (B : P.1.parts) (hB : σ B = false) :
    (G ∆ signedProfileInternalGraph P σ).IsIndepSet (B.1 : Set (Fin n)) ↔
      G.IsIndepSet (B.1 : Set (Fin n)) := by
  rw [isIndepSet_iff_disjoint_completeOn,
    isIndepSet_iff_disjoint_completeOn]
  have hdis : Disjoint (signedProfileInternalGraph P σ) (completeOn B.1) :=
    signedProfileInternalGraph_disjoint_completeOn_of_sign_false P σ B hB
  constructor
  · intro h
    have h' : Disjoint
        ((G ∆ signedProfileInternalGraph P σ) ∆
          signedProfileInternalGraph P σ)
        (completeOn B.1) := h.symmDiff_left hdis
    simpa using h'
  · intro h
    exact h.symmDiff_left hdis

/-- On a clique-signed part, toggling the complete internal graph turns the
clique condition into the independent-set condition. -/
theorem isIndepSet_symmDiff_signedProfileInternalGraph_iff_isClique_of_sign_true
    {b n : ℕ} {k : ColoringProfile b} (G : LabeledGraph n)
    (P : ProfilePartition n k) (σ : P.1.parts → Bool)
    (B : P.1.parts) (hB : σ B = true) :
    (G ∆ signedProfileInternalGraph P σ).IsIndepSet (B.1 : Set (Fin n)) ↔
      G.IsClique (B.1 : Set (Fin n)) := by
  rw [isIndepSet_iff_disjoint_completeOn,
    isClique_iff_completeOn_le]
  let H := signedProfileInternalGraph P σ
  let C := completeOn B.1
  have hHC : Disjoint (H ∆ C) C := by
    simpa only [H, C] using
      (signedProfileInternalGraph_symmDiff_completeOn_disjoint_of_sign_true
        P σ B hB)
  have hswap : (G ∆ H) ∆ (H ∆ C) = G ∆ C := by
    rw [symmDiff_assoc]
    simp
  have hswap' : (G ∆ C) ∆ (H ∆ C) = G ∆ H := by
    calc
      (G ∆ C) ∆ (H ∆ C) = G ∆ (C ∆ (H ∆ C)) :=
        symmDiff_assoc G C (H ∆ C)
      _ = G ∆ ((C ∆ H) ∆ C) :=
        congrArg (fun X => G ∆ X) (symmDiff_assoc C H C).symm
      _ = G ∆ ((H ∆ C) ∆ C) :=
        congrArg (fun X => G ∆ (X ∆ C)) (symmDiff_comm C H)
      _ = G ∆ H := by simp
  constructor
  · intro h
    have hrem : Disjoint (G ∆ C) C := by
      rw [← hswap]
      exact h.symmDiff_left hHC
    have hle : C ≤ (G ∆ C) ∆ C :=
      Iff.mpr (le_symmDiff_iff_right (G ∆ C) C) hrem
    simpa using hle
  · intro h
    have hGC : Disjoint (G ∆ C) C := by
      rw [symmDiff_of_ge h]
      exact disjoint_sdiff_self_left
    rw [← hswap']
    exact hGC.symmDiff_left hHC

/-- A mixed independent/clique signed witness is valid exactly when toggling
its clique-signed internal edges yields an ordinary proper partition. -/
theorem profileSignValid_iff_mem_partitionColoringEvent_symmDiff
    {b n : ℕ} {k : ColoringProfile b} (G : LabeledGraph n)
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    profileSignValid G P σ ↔
      G ∆ signedProfileInternalGraph P σ ∈ partitionColoringEvent P.1 := by
  constructor
  · intro h
    change ∀ B ∈ P.1.parts,
      (G ∆ signedProfileInternalGraph P σ).IsIndepSet (B : Set (Fin n))
    intro B hB
    let B' : P.1.parts := ⟨B, hB⟩
    cases hsign : σ B' with
    | false =>
        exact (isIndepSet_symmDiff_signedProfileInternalGraph_iff_of_sign_false
          G P σ B' hsign).mpr (by simpa [hsign] using h B')
    | true =>
        exact
          (isIndepSet_symmDiff_signedProfileInternalGraph_iff_isClique_of_sign_true
            G P σ B' hsign).mpr (by simpa [hsign] using h B')
  · intro h B
    have hB : (G ∆ signedProfileInternalGraph P σ).IsIndepSet
        (B.1 : Set (Fin n)) := h B.1 B.2
    cases hsign : σ B with
    | false =>
        exact (isIndepSet_symmDiff_signedProfileInternalGraph_iff_of_sign_false
          G P σ B hsign).mp hB
    | true =>
        exact
          (isIndepSet_symmDiff_signedProfileInternalGraph_iff_isClique_of_sign_true
            G P σ B hsign).mp hB

/-- Symmetric difference with a fixed labelled graph is a measure-preserving
involution of the half-random-graph space.  This is the mixed
present/absent-edge analogue of global complementation. -/
theorem randomGraphMeasure_map_symmDiff (n : ℕ) (H : LabeledGraph n) :
    (randomGraphMeasure n).map (fun G : LabeledGraph n => G ∆ H) =
      randomGraphMeasure n := by
  classical
  apply Measure.ext_of_singleton
  intro G
  rw [Measure.map_apply (measurable_of_finite _) (MeasurableSet.singleton G)]
  have hpre :
      (fun K : LabeledGraph n => K ∆ H) ⁻¹' ({G} : Set (LabeledGraph n)) =
        {G ∆ H} := by
    ext K
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      calc
        K = (K ∆ H) ∆ H := (symmDiff_symmDiff_cancel_right H K).symm
        _ = G ∆ H := congrArg (fun X => X ∆ H) h
    · intro h
      calc
        K ∆ H = (G ∆ H) ∆ H := congrArg (fun X => X ∆ H) h
        _ = G := symmDiff_symmDiff_cancel_right H G
  rw [hpre, randomGraphMeasure_singleton_uniform,
    randomGraphMeasure_singleton_uniform]

/-- Event probabilities are unchanged after translating every graph by a
fixed symmetric difference. -/
theorem randomGraphMeasure_symmDiff_preimage_eq
    (n : ℕ) (H : LabeledGraph n) (A : Set (LabeledGraph n)) :
    randomGraphMeasure n {G | G ∆ H ∈ A} = randomGraphMeasure n A := by
  calc
    randomGraphMeasure n {G | G ∆ H ∈ A} =
        randomGraphMeasure n ((fun G : LabeledGraph n => G ∆ H) ⁻¹' A) := rfl
    _ = ((randomGraphMeasure n).map
        (fun G : LabeledGraph n => G ∆ H)) A :=
      (Measure.map_apply (measurable_of_finite _)
        (Set.toFinite A |>.measurableSet)).symm
    _ = randomGraphMeasure n A := by rw [randomGraphMeasure_map_symmDiff]

/-- The event on which one fixed signed profile witness is valid. -/
def signedProfileWitnessEvent {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    Set (LabeledGraph n) :=
  {G | profileSignValid G P σ}

/-- The exact half-random-graph mass of a fixed signed witness.  It is
independent of the sign assignment: symmetric-difference translation changes
the mixed present/absent requirements into the all-absent internal-edge event. -/
theorem randomGraphMeasure_signedProfileWitnessEvent
    {b n : ℕ} {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) :
    randomGraphMeasure n (signedProfileWitnessEvent P σ) =
      (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k := by
  have hevent : signedProfileWitnessEvent P σ =
      {G | G ∆ signedProfileInternalGraph P σ ∈
        partitionColoringEvent P.1} := by
    ext G
    exact profileSignValid_iff_mem_partitionColoringEvent_symmDiff G P σ
  rw [hevent, randomGraphMeasure_symmDiff_preimage_eq,
    randomGraphMeasure_partitionColoringEvent]

/-- The natural-valued indicator of validity for one fixed signed witness. -/
noncomputable def signedProfileWitnessIndicator {b n : ℕ}
    (G : LabeledGraph n) {k : ColoringProfile b}
    (P : ProfilePartition n k) (σ : P.1.parts → Bool) : ℕ := by
  classical
  exact if profileSignValid G P σ then 1 else 0

/-- Expanding the filtered cardinality into its finite sum of witness
indicators. -/
theorem signedProfileCount_eq_sum_indicator {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) :
    signedProfileCount G k =
      ∑ P : ProfilePartition n k, ∑ σ : P.1.parts → Bool,
        signedProfileWitnessIndicator G P σ := by
  classical
  unfold signedProfileCount signedProfileWitnessIndicator
  rw [Finset.card_filter, Fintype.sum_sigma]
  rfl

/-- Summing the finite indicator of one signed witness against singleton
masses recovers precisely its witness event. -/
theorem sum_signedProfileWitnessIndicator_measure {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) :
    (∑ G : LabeledGraph n,
      (signedProfileWitnessIndicator G P σ : ENNReal) *
        randomGraphMeasure n {G}) =
      randomGraphMeasure n (signedProfileWitnessEvent P σ) := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter
    fun G => profileSignValid G P σ
  calc
    _ = ∑ G : LabeledGraph n,
        if profileSignValid G P σ then randomGraphMeasure n {G} else 0 := by
      apply Finset.sum_congr rfl
      intro G _
      by_cases h : profileSignValid G P σ <;>
        simp [signedProfileWitnessIndicator, h]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      simp only [T, Finset.sum_filter]
    _ = randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = randomGraphMeasure n (signedProfileWitnessEvent P σ) := by
      congr 1
      ext G
      simp [T, signedProfileWitnessEvent]

/-- The finite weighted first moment of the signed-profile count. -/
noncomputable def signedProfileExpectation {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ENNReal :=
  ∑ G : LabeledGraph n,
    (signedProfileCount G k : ENNReal) * randomGraphMeasure n {G}

/-- Exact first moment of the signed-profile count.  The factor `2^k` occurs
only after averaging: a fixed graph need not support every sign assignment on
a proper profile partition. -/
theorem signedProfileExpectation_eq {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    signedProfileExpectation n k =
      (2 : ENNReal) ^ ColoringProfile.partCount k *
        profileColoringExpectation n k := by
  classical
  let p : ENNReal := (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k
  have hsign (P : ProfilePartition n k) :
      (∑ _σ : P.1.parts → Bool, p) =
        (2 : ENNReal) ^ ColoringProfile.partCount k * p := by
    simp [p, nsmul_eq_mul, P.card_parts_eq]
  unfold signedProfileExpectation
  simp_rw [signedProfileCount_eq_sum_indicator, Nat.cast_sum,
    Finset.sum_mul]
  calc
    (∑ G : LabeledGraph n,
      ∑ P : ProfilePartition n k, ∑ σ : P.1.parts → Bool,
        (signedProfileWitnessIndicator G P σ : ENNReal) *
          randomGraphMeasure n {G}) =
        ∑ P : ProfilePartition n k, ∑ σ : P.1.parts → Bool,
          ∑ G : LabeledGraph n,
            (signedProfileWitnessIndicator G P σ : ENNReal) *
              randomGraphMeasure n {G} := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro P _
          rw [Finset.sum_comm]
    _ = ∑ P : ProfilePartition n k, ∑ σ : P.1.parts → Bool, p := by
          apply Finset.sum_congr rfl
          intro P _
          apply Finset.sum_congr rfl
          intro σ _
          rw [sum_signedProfileWitnessIndicator_measure,
            randomGraphMeasure_signedProfileWitnessEvent]
    _ = (2 : ENNReal) ^ ColoringProfile.partCount k *
        profileColoringExpectation n k := by
          simp_rw [hsign]
          rw [profileColoringExpectation_eq_card_mul]
          simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card,
            p, mul_assoc, mul_comm]

/-- The canonical cocolouring induced by a valid signed profile witness,
before relabelling its palette by `Fin (partCount k)`. -/
noncomputable def profileSignCoColoring {b n : ℕ} {k : ColoringProfile b}
    {G : LabeledGraph n} (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) (hσ : profileSignValid G P σ) :
    CoColoring G P.1.parts := by
  classical
  let color : Fin n → P.1.parts := fun v =>
    ⟨P.1.part v, P.1.part_mem.mpr (Finset.mem_univ v)⟩
  have hclass (B : P.1.parts) :
      {v | color v = B} = (B.1 : Set (Fin n)) := by
    ext v
    dsimp [color]
    constructor
    · intro h
      exact (P.1.part_eq_iff_mem B.2).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (P.1.part_eq_iff_mem B.2).mpr h
  exact
    { color := color
      kind := fun B => if σ B then .clique else .independent
      valid := by
        intro B
        rw [hclass B]
        cases hB : σ B with
        | false => simpa [hB] using hσ B
        | true => simpa [hB] using hσ B }

/-- A valid signed partition is a cocolouring with exactly its profile's
number of nonempty parts; the palette is relabelled only after the finite
partition has supplied the exact cardinality. -/
theorem profileSignValid_coColorable {b n : ℕ} {k : ColoringProfile b}
    {G : LabeledGraph n} (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) (hσ : profileSignValid G P σ) :
    CoColorable G (ColoringProfile.partCount k) := by
  classical
  have hcard : P.1.parts.card = ColoringProfile.partCount k :=
    P.card_parts_eq
  exact ⟨(profileSignCoColoring P σ hσ).relabel
    (Finset.equivFinOfCardEq hcard)⟩

/-- Positivity of the signed-profile count supplies an actual cocolouring.
This is the deterministic witness implication needed before applying any
second-moment inequality. -/
theorem signedProfileCount_pos_implies_coColorable
    {b n : ℕ} {G : LabeledGraph n} {k : ColoringProfile b} :
    0 < signedProfileCount G k →
      CoColorable G (ColoringProfile.partCount k) := by
  classical
  intro hpos
  unfold signedProfileCount at hpos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hw
  exact profileSignValid_coColorable w.1 w.2 hw.2

end

end Erdos625
