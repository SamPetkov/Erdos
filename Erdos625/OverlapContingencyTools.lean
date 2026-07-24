import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite contingency-table feasibility tools

This module isolates the deterministic margin facts used before the
prescribed-cell probability estimate in manuscript Sections 6--9.  In
particular, an infeasible demand event is proved empty rather than silently
fed into a falling-factorial bound outside its valid range.
-/

open scoped BigOperators

namespace Erdos625

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The total obtained by summing the rows of a finite table equals the total
obtained by summing its columns. -/
theorem sum_table_rows_eq_sum_table_columns
    (table : A → B → ℕ) :
    (∑ a, ∑ b, table a b) = ∑ b, ∑ a, table a b := by
  rw [Finset.sum_comm]

/-- Entrywise demands bounded by a table have no more total mass than the
table. -/
theorem sum_demand_le_sum_table
    (demand table : A → B → ℕ)
    (hdemand : ∀ a b, demand a b ≤ table a b) :
    (∑ a, ∑ b, demand a b) ≤ ∑ a, ∑ b, table a b := by
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hdemand a b

/-- No nonnegative integer contingency table can realize infeasible row or
column demands.  The three impossible branches are: a demanded row exceeds
its row margin, a demanded column exceeds its column margin, or the two total
margin masses disagree. -/
theorem no_contingencyTable_of_infeasible_demands
    [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ)
    (row : A → ℕ) (column : B → ℕ)
    (hbad :
      (∃ a, row a < ∑ b, demand a b) ∨
      (∃ b, column b < ∑ a, demand a b) ∨
      (∑ a, row a) ≠ ∑ b, column b) :
    ¬ ∃ table : A → B → ℕ,
      (∀ a, (∑ b, table a b) = row a) ∧
      (∀ b, (∑ a, table a b) = column b) ∧
      ∀ a b, demand a b ≤ table a b := by
  rintro ⟨table, hrow, hcolumn, hdemand⟩
  rcases hbad with hbadRow | hbadColumn | hbadTotal
  · obtain ⟨a, ha⟩ := hbadRow
    have hle : (∑ b, demand a b) ≤ ∑ b, table a b :=
      Finset.sum_le_sum fun b _ => hdemand a b
    have : (∑ b, demand a b) ≤ row a := by
      simpa only [hrow a] using hle
    exact (Nat.not_lt_of_ge this) ha
  · obtain ⟨b, hb⟩ := hbadColumn
    have hle : (∑ a, demand a b) ≤ ∑ a, table a b :=
      Finset.sum_le_sum fun a _ => hdemand a b
    have : (∑ a, demand a b) ≤ column b := by
      simpa only [hcolumn b] using hle
    exact (Nat.not_lt_of_ge this) hb
  · apply hbadTotal
    calc
      (∑ a, row a) = ∑ a, ∑ b, table a b := by
        apply Finset.sum_congr rfl
        intro a _
        exact (hrow a).symm
      _ = ∑ b, ∑ a, table a b := sum_table_rows_eq_sum_table_columns table
      _ = ∑ b, column b := by
        apply Finset.sum_congr rfl
        intro b _
        exact hcolumn b

/-- If every row and column has mass at most `U`, cells with mass strictly
larger than `U / 2` form a matching.  This is the finite combinatorial claim
used to define the canonical high-cell skeleton in Section 8. -/
theorem highCells_form_matching
    [DecidableEq A] [DecidableEq B]
    (table : A → B → ℕ) (U : ℕ)
    (hrow : ∀ a, (∑ b, table a b) ≤ U)
    (hcolumn : ∀ b, (∑ a, table a b) ≤ U) :
    (∀ a b₁ b₂,
      U / 2 < table a b₁ → U / 2 < table a b₂ → b₁ = b₂) ∧
    (∀ b a₁ a₂,
      U / 2 < table a₁ b → U / 2 < table a₂ b → a₁ = a₂) := by
  constructor
  · intro a b₁ b₂ hb₁ hb₂
    by_contra hne
    have hpair :
        (∑ b ∈ ({b₁, b₂} : Finset B), table a b) ≤ ∑ b, table a b :=
      Finset.sum_le_sum_of_subset (by simp)
    have htwo : table a b₁ + table a b₂ ≤ ∑ b, table a b := by
      simpa [hne] using hpair
    have hle : table a b₁ + table a b₂ ≤ U := htwo.trans (hrow a)
    omega
  · intro b a₁ a₂ ha₁ ha₂
    by_contra hne
    have hpair :
        (∑ a ∈ ({a₁, a₂} : Finset A), table a b) ≤ ∑ a, table a b :=
      Finset.sum_le_sum_of_subset (by simp)
    have htwo : table a₁ b + table a₂ b ≤ ∑ a, table a b := by
      simpa [hne] using hpair
    have hle : table a₁ b + table a₂ b ≤ U := htwo.trans (hcolumn b)
    omega

end Erdos625
