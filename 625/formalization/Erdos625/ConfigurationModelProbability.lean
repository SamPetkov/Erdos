import Mathlib.Probability.Distributions.Uniform
import Erdos625.ConfigurationModelPrescribedCells

/-!
# Uniform configuration-model probability and the joint prescribed-cell bound

This module transports the exact finite counts from
`ConfigurationModelPrescribedCells` through the uniform probability mass
function.  Its final theorem is the formal counterpart of manuscript equation
(6.8): it retains one global descending factorial for the total demand.
-/

namespace Erdos625

open scoped BigOperators ENNReal

/-- Total prescribed demand across all cells. -/
def totalDemand
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) : ℕ :=
  Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a))

/-- Product of the factorials of all prescribed cell demands. -/
def demandFactorialProduct
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) : ℕ :=
  Finset.univ.prod
    (fun a ↦ Finset.univ.prod (fun b ↦ (demand a b).factorial))

/-- Product of the row descending-factorial selection counts. -/
def rowDescendingProduct
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) (row : A → ℕ) : ℕ :=
  Finset.univ.prod
    (fun a ↦ (row a).descFactorial (Finset.univ.sum (demand a)))

/-- Product of the column descending-factorial selection counts. -/
def columnDescendingProduct
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) (col : B → ℕ) : ℕ :=
  Finset.univ.prod
    (fun b ↦
      (col b).descFactorial (Finset.univ.sum (fun a ↦ demand a b)))

/-- Equal total row and column degrees provide at least one full matching. -/
noncomputable def configurationMatchingEquiv
    {A B : Type*}
    [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    RowStub row ≃ ColumnStub col :=
  Fintype.equivOfCardEq (by
    rw [card_rowStub, card_columnStub, htotal])

/-- The uniform law on all bipartite configuration matchings. -/
noncomputable def uniformConfigurationMatching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    PMF (ConfigurationMatching row col) := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  exact PMF.uniformOfFintype _

/-- Under the uniform configuration law, an event has probability equal to
its finite cardinality divided by the ambient `m!` cardinality. -/
theorem uniformConfigurationMatching_prescribedCellEvent_apply
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (prescribedCellEvent demand row col) =
      (Fintype.card
          {matching : ConfigurationMatching row col //
            matching ∈ prescribedCellEvent demand row col} : ℝ≥0∞) /
        (Finset.univ.sum row).factorial := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  change (PMF.uniformOfFintype (ConfigurationMatching row col)).toOuterMeasure
      (prescribedCellEvent demand row col) = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    card_configurationMatching row col htotal]

/-- Probability form of the finite witness-union bound, before normalizing the
exact witness cardinality. -/
theorem uniformConfigurationMatching_prescribedCellEvent_le_witness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (prescribedCellEvent demand row col) ≤
      (Fintype.card (PrescribedDemandWitness demand row col) : ℝ≥0∞) *
          ((Finset.univ.sum row - totalDemand demand).factorial : ℝ≥0∞) /
        ((Finset.univ.sum row).factorial : ℝ≥0∞) := by
  rw [uniformConfigurationMatching_prescribedCellEvent_apply
    demand row col htotal]
  gcongr
  exact_mod_cast
    card_prescribedCellEvent_le_witness_mul_factorial demand row col htotal

/-- Joint prescribed-cell bound, the formal counterpart of manuscript (6.8).
Only the total-demand feasibility inequality is needed for the final global
factorial cancellation; individual infeasible rows or columns already force
the corresponding descending-factorial numerator, and the event, to vanish. -/
theorem jointPrescribedCellBound
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hDemand : totalDemand demand ≤ Finset.univ.sum row) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (prescribedCellEvent demand row col) ≤
      ((rowDescendingProduct demand row *
          columnDescendingProduct demand col : ℕ) : ℝ≥0∞) /
        (((Finset.univ.sum row).descFactorial (totalDemand demand) *
          demandFactorialProduct demand : ℕ) : ℝ≥0∞) := by
  let m := Finset.univ.sum row
  let x := totalDemand demand
  let W := Fintype.card (PrescribedDemandWitness demand row col)
  let D := demandFactorialProduct demand
  let N := rowDescendingProduct demand row *
    columnDescendingProduct demand col
  have hraw :=
    uniformConfigurationMatching_prescribedCellEvent_le_witness
      demand row col htotal
  change _ ≤ (W : ℝ≥0∞) * ((m - x).factorial : ℝ≥0∞) /
    (m.factorial : ℝ≥0∞) at hraw
  change _ ≤ (N : ℝ≥0∞) /
    ((m.descFactorial x * D : ℕ) : ℝ≥0∞)
  refine hraw.trans_eq ?_
  have hWitnessNat : W * D = N := by
    simpa [W, D, N, demandFactorialProduct,
      rowDescendingProduct, columnDescendingProduct] using
        card_prescribedDemandWitness_mul_factorials demand row col
  have hCrossNat :
      (m.descFactorial x * D) * (W * (m - x).factorial) =
        m.factorial * N := by
    calc
      (m.descFactorial x * D) * (W * (m - x).factorial) =
          ((m - x).factorial * m.descFactorial x) * (W * D) := by
        ac_rfl
      _ = m.factorial * N := by
        rw [Nat.factorial_mul_descFactorial hDemand, hWitnessNat]
  have hTargetDenPos : 0 < m.descFactorial x * D := by
    apply Nat.mul_pos (Nat.descFactorial_pos.mpr hDemand)
    simp [D, demandFactorialProduct, Nat.factorial_pos]
  have hTargetDenZero :
      ((m.descFactorial x * D : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hTargetDenPos.ne'
  have hTargetDenTop :
      ((m.descFactorial x * D : ℕ) : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.natCast_ne_top _
  have hRawDenZero : ((m.factorial : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast m.factorial_ne_zero
  have hRawDenTop : ((m.factorial : ℕ) : ℝ≥0∞) ≠ ∞ := by
    exact ENNReal.natCast_ne_top _
  apply (ENNReal.div_eq_div_iff hTargetDenZero hTargetDenTop
    hRawDenZero hRawDenTop).2
  exact_mod_cast hCrossNat

end Erdos625
