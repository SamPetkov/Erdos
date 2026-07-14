import Erdos625.PrescribedDemandTools
import Erdos625.MatchingExtensionTools

/-!
# Prescribed cells inside the configuration model

This module supplies the finite types and injective maps needed to interpret a
`PrescribedDemandWitness` as a family of distinct row--column stub pairs.  It
does not yet state event coverage or the probability estimate (6.8).
-/

namespace Erdos625

open scoped BigOperators

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

end Erdos625
