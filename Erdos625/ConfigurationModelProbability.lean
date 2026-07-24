import Mathlib.Probability.Distributions.Uniform
import Erdos625.ConfigurationModelPrescribedCells
import Erdos625.FallingFactorialBounds

/-!
# Uniform configuration-model probability and the joint prescribed-cell bound

This module transports the exact finite counts from
`ConfigurationModelPrescribedCells` through the uniform probability mass
function.  It proves the exact global descending-factorial estimate (6.8),
the effective falling-factorial simplification (6.10), and the resulting
cellwise estimate (6.9).
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

/-- Product of the crude cellwise degree powers.  It is the numerator that
appears after replacing every row and column descending factorial by a power. -/
def cellDegreePowerProduct
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) : ℕ :=
  Finset.univ.prod (fun a ↦
    Finset.univ.prod (fun b ↦ (row a * col b) ^ demand a b))

/-- The row/column selection numerator is bounded by the product of its
cellwise degree powers. -/
theorem row_column_descendingProduct_le_cellDegreePowerProduct
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) :
    rowDescendingProduct demand row * columnDescendingProduct demand col ≤
      cellDegreePowerProduct demand row col := by
  have hrow : rowDescendingProduct demand row ≤
      Finset.univ.prod
        (fun a ↦ (row a) ^ Finset.univ.sum (demand a)) := by
    apply Finset.prod_le_prod'
    intro a ha
    exact Nat.descFactorial_le_pow _ _
  have hcol : columnDescendingProduct demand col ≤
      Finset.univ.prod
        (fun b ↦ (col b) ^ Finset.univ.sum (fun a ↦ demand a b)) := by
    apply Finset.prod_le_prod'
    intro b hb
    exact Nat.descFactorial_le_pow _ _
  calc
    rowDescendingProduct demand row * columnDescendingProduct demand col ≤
        (Finset.univ.prod
          (fun a ↦ (row a) ^ Finset.univ.sum (demand a))) *
        (Finset.univ.prod
          (fun b ↦ (col b) ^ Finset.univ.sum (fun a ↦ demand a b))) :=
      Nat.mul_le_mul hrow hcol
    _ = (Finset.univ.prod (fun a ↦
          Finset.univ.prod (fun b ↦ (row a) ^ demand a b))) *
        (Finset.univ.prod (fun a ↦
          Finset.univ.prod (fun b ↦ (col b) ^ demand a b))) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro a ha
        simpa using
          (Finset.prod_pow_eq_pow_sum Finset.univ (demand a) (row a)).symm
      · rw [Finset.prod_comm]
        apply Finset.prod_congr rfl
        intro b hb
        simpa using
          (Finset.prod_pow_eq_pow_sum Finset.univ
            (fun a ↦ demand a b) (col b)).symm
    _ = cellDegreePowerProduct demand row col := by
      simp only [cellDegreePowerProduct, ← Finset.prod_mul_distrib,
        ← mul_pow]

/-- The exact cell parameter from manuscript (6.9). -/
noncomputable def configurationCellTheta
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (m : ℕ) (a : A) (b : B) : ℝ≥0∞ :=
  eulerENNReal * (row a : ℝ≥0∞) * (col b : ℝ≥0∞) / (m : ℝ≥0∞)

/-- The product of the powers of the cell parameters separates into the
degree-power numerator and the single global `(e / m)` power. -/
theorem configurationCellTheta_pow_product
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (m : ℕ) :
    Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col m a b ^ demand a b)) =
      (cellDegreePowerProduct demand row col : ℝ≥0∞) *
        (eulerENNReal / (m : ℝ≥0∞)) ^ totalDemand demand := by
  calc
    Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col m a b ^ demand a b)) =
        Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
          ((row a * col b : ℕ) : ℝ≥0∞) ^ demand a b *
            (eulerENNReal / (m : ℝ≥0∞)) ^ demand a b)) := by
      apply Finset.prod_congr rfl
      intro a ha
      apply Finset.prod_congr rfl
      intro b hb
      rw [← mul_pow]
      congr 1
      simp only [configurationCellTheta, Nat.cast_mul]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ac_rfl
    _ = (Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
          ((row a * col b : ℕ) : ℝ≥0∞) ^ demand a b))) *
        Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
          (eulerENNReal / (m : ℝ≥0∞)) ^ demand a b)) := by
      simp only [Finset.prod_mul_distrib]
    _ = (cellDegreePowerProduct demand row col : ℝ≥0∞) *
        (eulerENNReal / (m : ℝ≥0∞)) ^ totalDemand demand := by
      congr 1
      · simp [cellDegreePowerProduct]
      · simp [totalDemand, Finset.prod_pow_eq_pow_sum]

/-- Inversion commutes with a finite product of nonzero natural-number casts. -/
private theorem ennreal_inv_natCast_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (((∏ i ∈ s, f i) : ℕ) : ℝ≥0∞)⁻¹ =
      ∏ i ∈ s, ((f i : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : (f a : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast hf a (Finset.mem_insert_self a s)
      have hfaTop : (f a : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
      have hrest : ∀ i ∈ s, f i ≠ 0 := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Nat.cast_mul,
        ENNReal.mul_inv (Or.inl hfa) (Or.inl hfaTop),
        Finset.prod_insert ha, ih hrest]

/-- Inversion distributes over the factorial product because every factorial
is positive and finite. -/
theorem inv_demandFactorialProduct
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) :
    ((demandFactorialProduct demand : ℕ) : ℝ≥0∞)⁻¹ =
      Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        ((demand a b).factorial : ℝ≥0∞)⁻¹)) := by
  simp only [demandFactorialProduct]
  rw [ennreal_inv_natCast_prod]
  · apply Finset.prod_congr rfl
    intro a ha
    rw [ennreal_inv_natCast_prod]
    intro b hb
    exact Nat.factorial_ne_zero _
  · intro a ha
    exact Finset.prod_ne_zero_iff.mpr (fun b hb ↦ Nat.factorial_ne_zero _)

/-- Exact normalization identity converting the global `(m/e)^x` denominator
into the product of cellwise weights from (6.9). -/
theorem configurationCellWeight_product_eq_global
    {A B : Type*} [Fintype A] [Fintype B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (m : ℕ)
    (hm : 0 < m) :
    Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col m a b ^ demand a b /
          ((demand a b).factorial : ℝ≥0∞))) =
      (cellDegreePowerProduct demand row col : ℝ≥0∞) /
        ((((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand) *
          (demandFactorialProduct demand : ℝ≥0∞)) := by
  have hMzero : (m : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hMtop : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hinv : ((m : ℝ≥0∞) / eulerENNReal)⁻¹ =
      eulerENNReal / (m : ℝ≥0∞) :=
    ENNReal.inv_div (Or.inr hMtop) (Or.inr hMzero)
  have hquotient :
      (cellDegreePowerProduct demand row col : ℝ≥0∞) *
          (eulerENNReal / (m : ℝ≥0∞)) ^ totalDemand demand =
        (cellDegreePowerProduct demand row col : ℝ≥0∞) /
          (((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand) := by
    calc
      (cellDegreePowerProduct demand row col : ℝ≥0∞) *
          (eulerENNReal / (m : ℝ≥0∞)) ^ totalDemand demand =
        (cellDegreePowerProduct demand row col : ℝ≥0∞) *
          (((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)⁻¹ := by
        rw [← hinv, ← ENNReal.inv_pow]
      _ = (((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)⁻¹ *
          (cellDegreePowerProduct demand row col : ℝ≥0∞) := mul_comm _ _
      _ = (cellDegreePowerProduct demand row col : ℝ≥0∞) /
          (((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand) :=
        (ENNReal.div_eq_inv_mul).symm
  calc
    Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col m a b ^ demand a b /
          ((demand a b).factorial : ℝ≥0∞))) =
        (Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
          configurationCellTheta row col m a b ^ demand a b))) /
        (demandFactorialProduct demand : ℝ≥0∞) := by
      rw [ENNReal.div_eq_inv_mul, inv_demandFactorialProduct]
      simp only [ENNReal.div_eq_inv_mul, Finset.prod_mul_distrib]
    _ = ((cellDegreePowerProduct demand row col : ℝ≥0∞) *
          (eulerENNReal / (m : ℝ≥0∞)) ^ totalDemand demand) /
        (demandFactorialProduct demand : ℝ≥0∞) := by
      rw [configurationCellTheta_pow_product]
    _ = ((cellDegreePowerProduct demand row col : ℝ≥0∞) /
          (((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)) /
        (demandFactorialProduct demand : ℝ≥0∞) := by rw [hquotient]
    _ = (cellDegreePowerProduct demand row col : ℝ≥0∞) /
        ((((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand) *
          (demandFactorialProduct demand : ℝ≥0∞)) := by
      have hDzero : (demandFactorialProduct demand : ℝ≥0∞) ≠ 0 := by
        exact_mod_cast (by
          simp only [demandFactorialProduct]
          exact Finset.prod_ne_zero_iff.mpr (fun a ha ↦
            Finset.prod_ne_zero_iff.mpr (fun b hb ↦
              Nat.factorial_ne_zero _)) :
            demandFactorialProduct demand ≠ 0)
      have hDtop : (demandFactorialProduct demand : ℝ≥0∞) ≠ ∞ :=
        ENNReal.natCast_ne_top _
      have hmulInv := ENNReal.mul_inv
        (a := ((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)
        (b := (demandFactorialProduct demand : ℝ≥0∞))
        (Or.inr hDtop) (Or.inr hDzero)
      calc
        ((cellDegreePowerProduct demand row col : ℝ≥0∞) /
            (((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)) /
            (demandFactorialProduct demand : ℝ≥0∞) =
          (demandFactorialProduct demand : ℝ≥0∞)⁻¹ *
            ((((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)⁻¹ *
              (cellDegreePowerProduct demand row col : ℝ≥0∞)) := by
            rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        _ = ((((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand)⁻¹ *
              (demandFactorialProduct demand : ℝ≥0∞)⁻¹) *
            (cellDegreePowerProduct demand row col : ℝ≥0∞) := by ac_rfl
        _ = ((((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand) *
              (demandFactorialProduct demand : ℝ≥0∞))⁻¹ *
            (cellDegreePowerProduct demand row col : ℝ≥0∞) := by rw [hmulInv]
        _ = (cellDegreePowerProduct demand row col : ℝ≥0∞) /
            ((((m : ℝ≥0∞) / eulerENNReal) ^ totalDemand demand) *
              (demandFactorialProduct demand : ℝ≥0∞)) :=
          (ENNReal.div_eq_inv_mul).symm

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

/-- Under the uniform configuration law, any finite event has probability
equal to its finite cardinality divided by the ambient matching cardinality. -/
theorem uniformConfigurationMatching_event_apply
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (event : Set (ConfigurationMatching row col)) [Fintype event] :
    (uniformConfigurationMatching row col htotal).toOuterMeasure event =
      (Fintype.card event : ℝ≥0∞) /
        ((Finset.univ.sum row).factorial : ℝ≥0∞) := by
  letI : Nonempty (ConfigurationMatching row col) :=
    ⟨configurationMatchingEquiv row col htotal⟩
  change (PMF.uniformOfFintype (ConfigurationMatching row col)).toOuterMeasure
      event = _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    card_configurationMatching row col htotal]

#print axioms uniformConfigurationMatching_event_apply

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

/-- Feasible-total branch of the cellwise joint prescribed-cell estimate. -/
theorem jointPrescribedCellBound_cellwise_of_totalDemand_le
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row)
    (hDemand : totalDemand demand ≤ Finset.univ.sum row) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (prescribedCellEvent demand row col) ≤
      Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col (Finset.univ.sum row) a b ^
            demand a b /
          ((demand a b).factorial : ℝ≥0∞))) := by
  let m := Finset.univ.sum row
  let x := totalDemand demand
  let F := m.descFactorial x
  let D := demandFactorialProduct demand
  let N := rowDescendingProduct demand row *
    columnDescendingProduct demand col
  let C := cellDegreePowerProduct demand row col
  have h68 := jointPrescribedCellBound demand row col htotal hDemand
  change _ ≤ (N : ℝ≥0∞) / ((F * D : ℕ) : ℝ≥0∞) at h68
  have hnum : (N : ℝ≥0∞) ≤ (C : ℝ≥0∞) := by
    exact_mod_cast
      row_column_descendingProduct_le_cellDegreePowerProduct demand row col
  have hfall : ((m : ℝ≥0∞) / eulerENNReal) ^ x ≤ (F : ℝ≥0∞) := by
    exact ennreal_div_euler_pow_le_descFactorial hm hDemand
  have hden :
      ((m : ℝ≥0∞) / eulerENNReal) ^ x * (D : ℝ≥0∞) ≤
        ((F * D : ℕ) : ℝ≥0∞) := by
    simpa [Nat.cast_mul] using
      (mul_le_mul_left hfall (D : ℝ≥0∞))
  calc
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (prescribedCellEvent demand row col) ≤
        (N : ℝ≥0∞) / ((F * D : ℕ) : ℝ≥0∞) := h68
    _ ≤ (C : ℝ≥0∞) /
        ((((m : ℝ≥0∞) / eulerENNReal) ^ x) * (D : ℝ≥0∞)) :=
      ENNReal.div_le_div hnum hden
    _ = Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col m a b ^ demand a b /
          ((demand a b).factorial : ℝ≥0∞))) := by
      symm
      exact configurationCellWeight_product_eq_global demand row col m hm

/-- If the total requested cell demand exceeds the number of row stubs, the
prescribed-cell event is empty. -/
theorem not_mem_prescribedCellEvent_of_total_lt
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (h : Finset.univ.sum row < totalDemand demand) :
    ∀ matching : ConfigurationMatching row col,
      matching ∉ prescribedCellEvent demand row col := by
  intro matching hEvent
  let witness := Classical.choose
    (exists_extendingWitness_of_mem_prescribedCellEvent hEvent)
  have hCard := Fintype.card_le_of_embedding (witnessRowEmbedding witness)
  rw [card_witnessRowAtom witness, card_rowStub row] at hCard
  exact (Nat.not_le_of_gt h) hCard

/-- Cellwise joint prescribed-cell estimate, the exact all-cases formal
counterpart of manuscript (6.9).  Total infeasibility is discharged by proving
the event empty; no feasibility hypothesis is exposed in the statement. -/
theorem jointPrescribedCellBound_cellwise
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (hm : 0 < Finset.univ.sum row) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (prescribedCellEvent demand row col) ≤
      Finset.univ.prod (fun a ↦ Finset.univ.prod (fun b ↦
        configurationCellTheta row col (Finset.univ.sum row) a b ^
            demand a b /
          ((demand a b).factorial : ℝ≥0∞))) := by
  by_cases hDemand : totalDemand demand ≤ Finset.univ.sum row
  · exact jointPrescribedCellBound_cellwise_of_totalDemand_le
      demand row col htotal hm hDemand
  · have hempty : prescribedCellEvent demand row col = ∅ :=
      Set.eq_empty_of_forall_notMem
        (not_mem_prescribedCellEvent_of_total_lt demand row col
          (Nat.lt_of_not_ge hDemand))
    rw [hempty, MeasureTheory.measure_empty]
    exact bot_le

end Erdos625
