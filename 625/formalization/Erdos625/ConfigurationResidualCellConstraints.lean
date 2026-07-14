import Erdos625.ConfigurationResidualCellCounts

/-!
# Residual cell constraints after a fixed exposure

This module translates two cellwise conditions through the exact decomposition
`full = demand + residual`: equality with the exposed demand means zero
residual count, and a cap becomes the corresponding truncated residual cap.
It contains no probability or canonical-skeleton statement.
-/

namespace Erdos625

/-- Adding a natural number changes nothing exactly when the addend is zero. -/
theorem nat_add_eq_left_iff_right_eq_zero (d r : ℕ) :
    d + r = d ↔ r = 0 := by
  constructor
  · intro h
    exact Nat.add_left_cancel (n := d) (m := r) (k := 0)
      (by simpa using h)
  · rintro rfl
    simp

/-- If the exposed demand is at most the cap, the remaining capacity is the
natural subtraction `cap - demand`, with no truncation ambiguity. -/
theorem nat_add_le_iff_le_sub_of_le {d r cap : ℕ} (hcap : d ≤ cap) :
    d + r ≤ cap ↔ r ≤ cap - d := by
  constructor
  · intro h
    exact (Nat.le_sub_iff_add_le hcap).2 (by
      simpa [Nat.add_comm] using h)
  · intro h
    have := (Nat.le_sub_iff_add_le hcap).1 h
    simpa [Nat.add_comm] using this

/-- Arithmetic packaging used by the configuration-model theorem below. -/
theorem exposedCell_constraints_iff_residual
    (full demand residual cap : ℕ)
    (hsplit : full = demand + residual) (hcap : demand ≤ cap) :
    (full = demand ↔ residual = 0) ∧
      (full ≤ cap ↔ residual ≤ cap - demand) := by
  rw [hsplit]
  exact ⟨nat_add_eq_left_iff_right_eq_zero demand residual,
    nat_add_le_iff_le_sub_of_le hcap⟩

/-- For one actual cell of a configuration matching extending a fixed labelled
witness, no additional pair and the cell cap are exactly the corresponding
conditions on the transported residual matching. -/
theorem configurationCell_constraints_iff_residual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (extension : {matching : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness matching witness})
    (a : A) (b : B) (cap : ℕ) (hcap : demand a b ≤ cap) :
    (configurationCellCount extension.1 a b = demand a b ↔
        configurationCellCount
          (extensionsOfWitnessEquivResidualConfiguration witness extension)
          a b = 0) ∧
      (configurationCellCount extension.1 a b ≤ cap ↔
        configurationCellCount
          (extensionsOfWitnessEquivResidualConfiguration witness extension)
          a b ≤ cap - demand a b) := by
  exact exposedCell_constraints_iff_residual
    (configurationCellCount extension.1 a b)
    (demand a b)
    (configurationCellCount
      (extensionsOfWitnessEquivResidualConfiguration witness extension) a b)
    cap
    (configurationCellCount_eq_demand_add_residual witness extension a b)
    hcap

end Erdos625
