import Erdos625.PrescribedDemandTools
import Erdos625.MatchingExtensionTools

/-!
# Prescribed cells inside the configuration model

This module supplies the finite types and injective maps needed to interpret a
`PrescribedDemandWitness` as a family of distinct row--column stub pairs.  It
also proves both directions of the witness/event bridge and counts the full
matchings extending one fixed witness.  The aggregate union bound and the
probability estimate (6.8) remain separate obligations.
-/

namespace Erdos625

open scoped BigOperators

private def sigmaSecondCast
    {I : Type*} {f : I → Type*}
    (z : Σ i, f i) {i : I} (h : z.1 = i) : f i :=
  h ▸ z.2

private theorem sigma_eq_mk_sigmaSecondCast
    {I : Type*} {f : I → Type*}
    (z : Σ i, f i) {i : I} (h : z.1 = i) :
    z = ⟨i, sigmaSecondCast z h⟩ := by
  cases z with
  | mk j x =>
      simp only at h
      subst i
      rfl

/-- Row stubs, indexed by their row class. -/
abbrev RowStub {A : Type*} [Fintype A] (row : A → ℕ) :=
  Σ a, Fin (row a)

/-- Column stubs, indexed by their column class. -/
abbrev ColumnStub {B : Type*} [Fintype B] (col : B → ℕ) :=
  Σ b, Fin (col b)

/-- A configuration matching is a bijection from all row stubs to all column
stubs.  The type is empty when the two total stub counts differ. -/
abbrev ConfigurationMatching
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) :=
  RowStub row ≃ ColumnStub col

noncomputable instance instFintypeConfigurationMatching
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) :
    Fintype (ConfigurationMatching row col) := by
  unfold ConfigurationMatching
  infer_instance

/-- The total number of row stubs is the sum of the row sizes. -/
theorem card_rowStub
    {A : Type*} [Fintype A] (row : A → ℕ) :
    Fintype.card (RowStub row) = Finset.univ.sum row := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.card_fin]

/-- The total number of column stubs is the sum of the column sizes. -/
theorem card_columnStub
    {B : Type*} [Fintype B] (col : B → ℕ) :
    Fintype.card (ColumnStub col) = Finset.univ.sum col := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_fin]

/-- When the two total stub counts agree, the full configuration-matching
space has the expected factorial cardinality. -/
theorem card_configurationMatching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    Fintype.card (ConfigurationMatching row col) =
      (Finset.univ.sum row).factorial := by
  let e : RowStub row ≃ ColumnStub col :=
    Fintype.equivOfCardEq (by
      rw [card_rowStub, card_columnStub, htotal])
  calc
    Fintype.card (ConfigurationMatching row col) =
        (Fintype.card (RowStub row)).factorial :=
      Fintype.card_equiv e
    _ = (Finset.univ.sum row).factorial := by rw [card_rowStub]

/-- A selected row atom remembers its row class, its target column class, and
the selected row stub in that cell. -/
abbrev WitnessRowAtom
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :=
  Σ a, Σ b, ↑((witness.1 a).1 b)

/-- A selected column atom has the same cell indices and remembers the
selected column stub in that cell. -/
abbrev WitnessColumnAtom
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :=
  Σ a, Σ b, ↑((witness.2.1 b).1 a)

/-- The within-cell bijections in a witness pair its selected row atoms with
its selected column atoms. -/
noncomputable def witnessAtomEquiv
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    WitnessRowAtom witness ≃ WitnessColumnAtom witness where
  toFun atom :=
    ⟨atom.1, atom.2.1, witness.2.2 atom.1 atom.2.1 atom.2.2⟩
  invFun atom :=
    ⟨atom.1, atom.2.1, (witness.2.2 atom.1 atom.2.1).symm atom.2.2⟩
  left_inv atom := by
    obtain ⟨a, b, stub⟩ := atom
    simp
  right_inv atom := by
    obtain ⟨a, b, stub⟩ := atom
    simp

/-- Distinct witness row atoms use distinct global row stubs. -/
def witnessRowEmbedding
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    WitnessRowAtom witness ↪ RowStub row where
  toFun atom := ⟨atom.1, atom.2.2.1⟩
  inj' := by
    rintro ⟨a, b, stub⟩ ⟨a', b', stub'⟩ h
    have ha : a = a' := (Sigma.mk.inj_iff.mp h).1
    subst a'
    have hstub : (stub : Fin (row a)) = stub' :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    by_cases hbb : b = b'
    · subst b'
      exact Sigma.ext rfl <| heq_of_eq <|
        Sigma.ext rfl <| heq_of_eq <| Subtype.ext hstub
    · have hdisjoint := (witness.1 a).2.2 b b' hbb
      have hmem : (stub : Fin (row a)) ∈ (witness.1 a).1 b' := by
        rw [hstub]
        exact stub'.2
      exact False.elim <|
        (Finset.disjoint_left.mp hdisjoint) stub.2 hmem

/-- Distinct witness column atoms use distinct global column stubs. -/
def witnessColumnEmbedding
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    WitnessColumnAtom witness ↪ ColumnStub col where
  toFun atom := ⟨atom.2.1, atom.2.2.1⟩
  inj' := by
    rintro ⟨a, b, stub⟩ ⟨a', b', stub'⟩ h
    have hb : b = b' := (Sigma.mk.inj_iff.mp h).1
    subst b'
    have hstub : (stub : Fin (col b)) = stub' :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    by_cases haa : a = a'
    · subst a'
      exact Sigma.ext rfl <| heq_of_eq <|
        Sigma.ext rfl <| heq_of_eq <| Subtype.ext hstub
    · have hdisjoint := (witness.2.1 b).2.2 a a' haa
      have hmem : (stub : Fin (col b)) ∈ (witness.2.1 b).1 a' := by
        rw [hstub]
        exact stub'.2
      exact False.elim <|
        (Finset.disjoint_left.mp hdisjoint) stub.2 hmem

/-- The selected row atoms are counted by the total prescribed demand. -/
theorem card_witnessRowAtom
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Fintype.card (WitnessRowAtom witness) =
      Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a)) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_coe, (witness.1 a).2.1 b]

/-- The selected column atoms have the same total prescribed-demand count. -/
theorem card_witnessColumnAtom
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Fintype.card (WitnessColumnAtom witness) =
      Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a)) := by
  calc
    Fintype.card (WitnessColumnAtom witness) =
        Fintype.card (WitnessRowAtom witness) :=
      (Fintype.card_congr (witnessAtomEquiv witness)).symm
    _ = _ := card_witnessRowAtom witness

/-- The number of row stubs from class `a` that a configuration matching sends
to column class `b`. -/
def configurationCellCount
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (a : A) (b : B) : ℕ :=
  (Finset.univ.filter
    (fun stub : Fin (row a) ↦ (matching ⟨a, stub⟩).1 = b)).card

/-- The event that every configuration-model cell contains at least its
prescribed demand.  Demands outside a manuscript support set may simply be
set to zero. -/
def prescribedCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :
    Set (ConfigurationMatching row col) :=
  {matching | ∀ a b, demand a b ≤ configurationCellCount matching a b}

/-- Compose the witness's cellwise pairing with its injective column-stub
encoding. -/
noncomputable def witnessColumnPairingEmbedding
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    WitnessRowAtom witness ↪ ColumnStub col :=
  (witnessAtomEquiv witness).toEmbedding.trans
    (witnessColumnEmbedding witness)

/-- A full configuration matching extends a witness when it realizes every
selected cellwise stub pair. -/
def ExtendsPrescribedDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (witness : PrescribedDemandWitness demand row col) : Prop :=
  ∀ atom : WitnessRowAtom witness,
    matching (witnessRowEmbedding witness atom) =
      witnessColumnPairingEmbedding witness atom

/-- The embedding-indexed extension predicate is exactly the transparent
cellwise condition. -/
theorem extendsPrescribedDemandWitness_iff_cellwise
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (witness : PrescribedDemandWitness demand row col) :
    ExtendsPrescribedDemandWitness matching witness ↔
      ∀ a b (stub : ↑((witness.1 a).1 b)),
        matching ⟨a, stub.1⟩ =
          ⟨b, (witness.2.2 a b stub).1⟩ := by
  constructor
  · intro h a b stub
    exact h ⟨a, b, stub⟩
  · rintro h ⟨a, b, stub⟩
    exact h a b stub

/-- Every matching extending a prescribed-demand witness belongs to the
corresponding prescribed-cell event. -/
theorem extendsWitness_mem_prescribedCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    {matching : ConfigurationMatching row col}
    {witness : PrescribedDemandWitness demand row col}
    (hextends : ExtendsPrescribedDemandWitness matching witness) :
    matching ∈ prescribedCellEvent demand row col := by
  intro a b
  rw [← (witness.1 a).2.1 b]
  apply Finset.card_le_card
  intro stub hstub
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hpair :=
    (extendsPrescribedDemandWitness_iff_cellwise matching witness).1
      hextends a b ⟨stub, hstub⟩
  exact congrArg Sigma.fst hpair

/-- Every matching satisfying the prescribed cell lower bounds extends a
concrete prescribed-demand witness.  The witness is obtained by choosing the
required number of row stubs inside each cell, transporting them through the
matching, and retaining the induced cellwise bijections. -/
theorem exists_extendingWitness_of_mem_prescribedCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    {matching : ConfigurationMatching row col}
    (hEvent : matching ∈ prescribedCellEvent demand row col) :
    ∃ witness : PrescribedDemandWitness demand row col,
      ExtendsPrescribedDemandWitness matching witness := by
  classical
  have hselect : ∀ a b,
      ∃ s : Finset (Fin (row a)),
        s ⊆ Finset.univ.filter
          (fun stub : Fin (row a) ↦ (matching ⟨a, stub⟩).1 = b) ∧
        s.card = demand a b := by
    intro a b
    apply Finset.exists_subset_card_eq
    simpa [configurationCellCount] using hEvent a b
  choose selected hsubset hcard using hselect
  have hlabel : ∀ a b (stub : ↑(selected a b)),
      (matching ⟨a, stub.1⟩).1 = b := by
    intro a b stub
    have h := hsubset a b stub.2
    simpa using h
  let rowAllocation : ∀ a, StubAllocation (row a) (demand a) := fun a ↦
    ⟨selected a, by
      constructor
      · exact hcard a
      · intro b b' hne
        rw [Finset.disjoint_left]
        intro stub hs hs'
        have hb := hsubset a b hs
        have hb' := hsubset a b' hs'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb hb'
        exact hne (hb.symm.trans hb')⟩
  let columnValue : ∀ a b, ↑(selected a b) → Fin (col b) :=
    fun a b stub ↦
      sigmaSecondCast (matching ⟨a, stub.1⟩) (hlabel a b stub)
  let columnEmbedding : ∀ a b, ↑(selected a b) ↪ Fin (col b) :=
    fun a b ↦
      { toFun := columnValue a b
        inj' := by
          intro x y hxy
          apply Subtype.ext
          have hmatched :
              matching ⟨a, x.1⟩ = matching ⟨a, y.1⟩ := by
            calc
              matching ⟨a, x.1⟩ = ⟨b, columnValue a b x⟩ :=
                sigma_eq_mk_sigmaSecondCast _ (hlabel a b x)
              _ = ⟨b, columnValue a b y⟩ := by rw [hxy]
              _ = matching ⟨a, y.1⟩ :=
                (sigma_eq_mk_sigmaSecondCast _ (hlabel a b y)).symm
          have hglobal := matching.injective hmatched
          exact eq_of_heq (Sigma.mk.inj_iff.mp hglobal).2 }
  let columnCell : ∀ b a, Finset (Fin (col b)) :=
    fun b a ↦ Finset.univ.map (columnEmbedding a b)
  have hcolumnCard : ∀ b a, (columnCell b a).card = demand a b := by
    intro b a
    simp [columnCell, hcard a b]
  have hcolumnDisjoint : ∀ b a a', a ≠ a' →
      Disjoint (columnCell b a) (columnCell b a') := by
    intro b a a' hne
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [columnCell, Finset.mem_map, Finset.mem_univ, true_and] at hc hc'
    obtain ⟨x, hx⟩ := hc
    obtain ⟨y, hy⟩ := hc'
    change columnValue a b x = c at hx
    change columnValue a' b y = c at hy
    have hmatchx : matching ⟨a, x.1⟩ = ⟨b, c⟩ := by
      calc
        matching ⟨a, x.1⟩ = ⟨b, columnValue a b x⟩ :=
          sigma_eq_mk_sigmaSecondCast _ (hlabel a b x)
        _ = ⟨b, c⟩ := by rw [hx]
    have hmatchy : matching ⟨a', y.1⟩ = ⟨b, c⟩ := by
      calc
        matching ⟨a', y.1⟩ = ⟨b, columnValue a' b y⟩ :=
          sigma_eq_mk_sigmaSecondCast _ (hlabel a' b y)
        _ = ⟨b, c⟩ := by rw [hy]
    have hglobal := matching.injective (hmatchx.trans hmatchy.symm)
    exact hne (congrArg Sigma.fst hglobal)
  let colAllocation : ∀ b, StubAllocation (col b) (fun a ↦ demand a b) :=
    fun b ↦ ⟨columnCell b, hcolumnCard b, hcolumnDisjoint b⟩
  let cellEquiv : ∀ a b, ↑(selected a b) ≃ ↑(columnCell b a) :=
    fun a b ↦ Equiv.ofBijective
      (fun stub ↦
        ⟨columnEmbedding a b stub, by
          simp [columnCell]⟩)
      ⟨by
        intro x y hxy
        exact (columnEmbedding a b).injective (congrArg Subtype.val hxy),
       by
        intro y
        have hy := y.2
        simp only [columnCell, Finset.mem_map, Finset.mem_univ, true_and] at hy
        obtain ⟨x, hx⟩ := hy
        refine ⟨x, ?_⟩
        apply Subtype.ext
        exact hx⟩
  let witness : PrescribedDemandWitness demand row col :=
    ⟨rowAllocation, colAllocation, cellEquiv⟩
  refine ⟨witness, ?_⟩
  rw [extendsPrescribedDemandWitness_iff_cellwise]
  intro a b stub
  change matching ⟨a, stub.1⟩ = ⟨b, columnValue a b stub⟩
  exact sigma_eq_mk_sigmaSecondCast _ (hlabel a b stub)

noncomputable instance instFintypePrescribedCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :
    Fintype
      {matching : ConfigurationMatching row col //
        matching ∈ prescribedCellEvent demand row col} :=
  Fintype.ofFinite _

/-- A deterministic classical choice of one extending witness for each
matching in the prescribed-cell event. -/
noncomputable def prescribedCellEventWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching :
      {matching : ConfigurationMatching row col //
        matching ∈ prescribedCellEvent demand row col}) :
    PrescribedDemandWitness demand row col :=
  Classical.choose
    (exists_extendingWitness_of_mem_prescribedCellEvent matching.2)

theorem prescribedCellEventWitness_extends
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching :
      {matching : ConfigurationMatching row col //
        matching ∈ prescribedCellEvent demand row col}) :
    ExtendsPrescribedDemandWitness matching.1
      (prescribedCellEventWitness matching) :=
  Classical.choose_spec
    (exists_extendingWitness_of_mem_prescribedCellEvent matching.2)

/-- Retaining the original matching makes the choice of one covering witness
into an embedding of the cell event into the disjoint union of all witness
extension events. -/
noncomputable def prescribedCellEventEmbedding
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ} :
    {matching : ConfigurationMatching row col //
        matching ∈ prescribedCellEvent demand row col} ↪
      (Σ witness : PrescribedDemandWitness demand row col,
        {matching : ConfigurationMatching row col //
          ExtendsPrescribedDemandWitness matching witness}) where
  toFun matching :=
    ⟨prescribedCellEventWitness matching,
      ⟨matching.1, prescribedCellEventWitness_extends matching⟩⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z ↦ z.2.1) hxy

noncomputable instance instFintypeExtensionsOfPrescribedDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Fintype
      {matching : ConfigurationMatching row col //
        ExtendsPrescribedDemandWitness matching witness} :=
  Fintype.ofFinite _

/-- Exact number of full configuration matchings extending one fixed witness.
No feasibility premise is needed: an infeasible witness type has no element to
which this theorem can be applied. -/
theorem card_extensionsOfPrescribedDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (witness : PrescribedDemandWitness demand row col) :
    Fintype.card
        {matching : ConfigurationMatching row col //
          ExtendsPrescribedDemandWitness matching witness} =
      (Finset.univ.sum row -
        Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a))).factorial := by
  have hcard : Fintype.card (RowStub row) = Fintype.card (ColumnStub col) := by
    rw [card_rowStub, card_columnStub, htotal]
  simpa [ExtendsPrescribedDemandWitness,
    witnessColumnPairingEmbedding, card_witnessRowAtom witness] using
      card_extensions_of_embedding_pairing hcard
        (witnessRowEmbedding witness)
        (witnessColumnPairingEmbedding witness)

/-- Cardinal union bound for the prescribed-cell event.  Every event matching
is assigned one extending witness, and every witness has the same exact number
of full extensions. -/
theorem card_prescribedCellEvent_le_witness_mul_factorial
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    Fintype.card
        {matching : ConfigurationMatching row col //
          matching ∈ prescribedCellEvent demand row col} ≤
      Fintype.card (PrescribedDemandWitness demand row col) *
        (Finset.univ.sum row -
          Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a))).factorial := by
  calc
    Fintype.card
        {matching : ConfigurationMatching row col //
          matching ∈ prescribedCellEvent demand row col} ≤
        Fintype.card
          (Σ witness : PrescribedDemandWitness demand row col,
            {matching : ConfigurationMatching row col //
              ExtendsPrescribedDemandWitness matching witness}) :=
      Fintype.card_le_of_embedding prescribedCellEventEmbedding
    _ = ∑ witness : PrescribedDemandWitness demand row col,
          Fintype.card
            {matching : ConfigurationMatching row col //
              ExtendsPrescribedDemandWitness matching witness} :=
      Fintype.card_sigma
    _ = _ := by
      simp_rw [card_extensionsOfPrescribedDemandWitness htotal]
      simp

end Erdos625
