import Erdos625.ConfigurationModelPrescribedCells
import Erdos625.OverlapContingencyTools

/-!
# Margins of a configuration-model cell table

This module verifies that the cell counts induced by an actual configuration
matching have exactly the prescribed row and column margins.  It then applies
the deterministic high-cell lemma to that concrete table: under one common
degree cap, cells containing more than half the cap form a matching.
-/

namespace Erdos625

open scoped BigOperators

/-- A subtype of a dependent sum is the dependent sum of its fiberwise
subtypes.  This local equivalence is used to count a column of the
configuration table by first partitioning the row stubs according to their
row class. -/
private def subtypeSigmaPredEquiv
    {A : Type*} {p : A → Type*} (P : (Σ a, p a) → Prop) :
    {x : Σ a, p a // P x} ≃ Σ a, {y : p a // P ⟨a, y⟩} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Summing the cells in row `a` recovers the number of row stubs in class
`a`. -/
theorem sum_configurationCellCount_row
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (a : A) :
    (∑ b, configurationCellCount matching a b) = row a := by
  classical
  simpa [configurationCellCount] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (row a)))
      (Finset.univ : Finset B)
      (fun stub : Fin (row a) => (matching ⟨a, stub⟩).1))

/-- Summing the cells in column `b` recovers the number of column stubs in
class `b`.  The proof first joins the rowwise fibers, then transports the
resulting global fiber through the configuration bijection. -/
theorem sum_configurationCellCount_column
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (b : B) :
    (∑ a, configurationCellCount matching a b) = col b := by
  classical
  let P : RowStub row → Prop := fun x => (matching x).1 = b
  let rowFiberEquiv :
      {x : RowStub row // P x} ≃
        Σ a, {stub : Fin (row a) // P ⟨a, stub⟩} :=
    subtypeSigmaPredEquiv P
  let matchingFiberEquiv :
      {x : RowStub row // P x} ≃
        {y : ColumnStub col // y.1 = b} :=
    Equiv.subtypeEquiv matching (fun _ => Iff.rfl)
  calc
    (∑ a, configurationCellCount matching a b) =
        Fintype.card (Σ a, {stub : Fin (row a) // P ⟨a, stub⟩}) := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro a _
      rw [configurationCellCount, ← Fintype.card_coe
        (Finset.univ.filter
          (fun stub : Fin (row a) => (matching ⟨a, stub⟩).1 = b))]
      apply Fintype.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl _) (fun _ => by
        simp [P])
    _ = Fintype.card {x : RowStub row // P x} :=
      Fintype.card_congr rowFiberEquiv.symm
    _ = Fintype.card {y : ColumnStub col // y.1 = b} :=
      Fintype.card_congr matchingFiberEquiv
    _ = col b := by
      simpa using Fintype.card_congr
        (Equiv.sigmaSubtype (β := fun b : B => Fin (col b)) b)

/-- For the cell table of an actual configuration matching, a common upper
bound `U` on every row and column degree forces the cells of size greater than
`U / 2` to form a matching: there is at most one such cell in every row and in
every column. -/
theorem configurationCellCount_highCells_form_matching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (U : ℕ)
    (hrow : ∀ a, row a ≤ U)
    (hcol : ∀ b, col b ≤ U) :
    (∀ a b₁ b₂,
      U / 2 < configurationCellCount matching a b₁ →
      U / 2 < configurationCellCount matching a b₂ →
      b₁ = b₂) ∧
    (∀ b a₁ a₂,
      U / 2 < configurationCellCount matching a₁ b →
      U / 2 < configurationCellCount matching a₂ b →
      a₁ = a₂) := by
  apply highCells_form_matching (table := configurationCellCount matching) U
  · intro a
    rw [sum_configurationCellCount_row]
    exact hrow a
  · intro b
    rw [sum_configurationCellCount_column]
    exact hcol b

end Erdos625
