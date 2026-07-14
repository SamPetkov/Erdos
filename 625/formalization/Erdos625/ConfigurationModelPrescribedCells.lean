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

end Erdos625
