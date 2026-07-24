import Erdos625.ConfigurationModelResidualMatching
import Erdos625.ResidualFiberCounts
import Erdos625.UniformEquivTransport
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Degree-labelled residual configuration matchings

For a fixed prescribed-demand witness, this module turns the unused global
stub subtypes into ordinary dependent sums indexed by the exact residual row
and column degrees.  It then transports the deterministic extension
equivalence to the standard `ConfigurationMatching` type for those residual
degrees.

No conditioning statement is made here: this module identifies the finite
sample spaces only.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The selected local row-stub indices in class `a`, obtained by pulling back
the witness's global selected-stub set. -/
def witnessSelectedRowIndices
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (a : A) :
    Finset (Fin (row a)) :=
  Finset.univ.filter (fun i =>
    (⟨a, i⟩ : RowStub row) ∈ witnessSelectedRowStubs witness)

/-- The selected local column-stub indices in class `b`. -/
def witnessSelectedColumnIndices
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (b : B) :
    Finset (Fin (col b)) :=
  Finset.univ.filter (fun i =>
    (⟨b, i⟩ : ColumnStub col) ∈ witnessSelectedColumnStubs witness)

/-- Exact residual degree of row class `a`. -/
def residualRowDegree
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (_witness : PrescribedDemandWitness demand row col) (a : A) : ℕ :=
  row a - ∑ b, demand a b

/-- Exact residual degree of column class `b`. -/
def residualColumnDegree
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (_witness : PrescribedDemandWitness demand row col) (b : B) : ℕ :=
  col b - ∑ a, demand a b

theorem card_witnessSelectedRowIndices
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (a : A) :
    (witnessSelectedRowIndices witness a).card = ∑ b, demand a b := by
  classical
  let f : Fin (row a) → RowStub row := fun i => ⟨a, i⟩
  have hf : Function.Injective f := by
    intro i j h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have himage :
      (witnessSelectedRowIndices witness a).image f =
        (witnessSelectedRowStubs witness).filter (fun stub => stub.1 = a) := by
    ext stub
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨by
        simpa [f, witnessSelectedRowIndices] using hi, rfl⟩
    · intro h
      obtain ⟨hselected, hclass⟩ := Finset.mem_filter.mp h
      obtain ⟨a', i⟩ := stub
      simp only at hclass
      subst a'
      exact Finset.mem_image.mpr ⟨i, by
        simp [witnessSelectedRowIndices, hselected], rfl⟩
  calc
    (witnessSelectedRowIndices witness a).card =
        ((witnessSelectedRowIndices witness a).image f).card := by
      rw [Finset.card_image_of_injective _ hf]
    _ = ((witnessSelectedRowStubs witness).filter
          (fun stub => stub.1 = a)).card := by rw [himage]
    _ = ∑ b, demand a b := card_selectedRowStubs_in_class witness a

theorem card_witnessSelectedColumnIndices
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (b : B) :
    (witnessSelectedColumnIndices witness b).card = ∑ a, demand a b := by
  classical
  let f : Fin (col b) → ColumnStub col := fun i => ⟨b, i⟩
  have hf : Function.Injective f := by
    intro i j h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have himage :
      (witnessSelectedColumnIndices witness b).image f =
        (witnessSelectedColumnStubs witness).filter (fun stub => stub.1 = b) := by
    ext stub
    constructor
    · intro h
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨by
        simpa [f, witnessSelectedColumnIndices] using hi, rfl⟩
    · intro h
      obtain ⟨hselected, hclass⟩ := Finset.mem_filter.mp h
      obtain ⟨b', i⟩ := stub
      simp only at hclass
      subst b'
      exact Finset.mem_image.mpr ⟨i, by
        simp [witnessSelectedColumnIndices, hselected], rfl⟩
  calc
    (witnessSelectedColumnIndices witness b).card =
        ((witnessSelectedColumnIndices witness b).image f).card := by
      rw [Finset.card_image_of_injective _ hf]
    _ = ((witnessSelectedColumnStubs witness).filter
          (fun stub => stub.1 = b)).card := by rw [himage]
    _ = ∑ a, demand a b := card_selectedColumnStubs_in_class witness b

/-- The unused local row-stub fibre has the manuscript's residual degree. -/
theorem card_remainingRowFiber
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (a : A) :
    Fintype.card
        {i : Fin (row a) // i ∉ witnessSelectedRowIndices witness a} =
      residualRowDegree witness a := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter
          (fun i : Fin (row a) => i ∉ witnessSelectedRowIndices witness a) =
        (witnessSelectedRowIndices witness a)ᶜ := by
    ext i
    simp
  rw [hfilter, Finset.card_compl, Fintype.card_fin,
    card_witnessSelectedRowIndices witness]
  rfl

/-- The unused local column-stub fibre has the manuscript's residual degree. -/
theorem card_remainingColumnFiber
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (b : B) :
    Fintype.card
        {i : Fin (col b) // i ∉ witnessSelectedColumnIndices witness b} =
      residualColumnDegree witness b := by
  classical
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter
          (fun i : Fin (col b) => i ∉ witnessSelectedColumnIndices witness b) =
        (witnessSelectedColumnIndices witness b)ᶜ := by
    ext i
    simp
  rw [hfilter, Finset.card_compl, Fintype.card_fin,
    card_witnessSelectedColumnIndices witness]
  rfl

private def remainingRowStubEquivFibres
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    RemainingRowStub witness ≃
      Σ a, {i : Fin (row a) // i ∉ witnessSelectedRowIndices witness a} where
  toFun x := ⟨x.1.1, ⟨x.1.2, by
    simpa [witnessSelectedRowIndices] using x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    simpa [witnessSelectedRowIndices] using x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def remainingColumnStubEquivFibres
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    RemainingColumnStub witness ≃
      Σ b, {i : Fin (col b) // i ∉ witnessSelectedColumnIndices witness b} where
  toFun x := ⟨x.1.1, ⟨x.1.2, by
    simpa [witnessSelectedColumnIndices] using x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, by
    simpa [witnessSelectedColumnIndices] using x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Class-preserving identification of unused row stubs with the standard
dependent sum carrying the residual row degrees. -/
def remainingRowStubEquivResidual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    RemainingRowStub witness ≃ RowStub (residualRowDegree witness) :=
  (remainingRowStubEquivFibres witness).trans
    (Equiv.sigmaCongrRight (fun a =>
      Fintype.equivFinOfCardEq (card_remainingRowFiber witness a)))

/-- Class-preserving identification of unused column stubs with the standard
dependent sum carrying the residual column degrees. -/
def remainingColumnStubEquivResidual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    RemainingColumnStub witness ≃ ColumnStub (residualColumnDegree witness) :=
  (remainingColumnStubEquivFibres witness).trans
    (Equiv.sigmaCongrRight (fun b =>
      Fintype.equivFinOfCardEq (card_remainingColumnFiber witness b)))

@[simp] theorem remainingRowStubEquivResidual_class
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (x : RemainingRowStub witness) :
    (remainingRowStubEquivResidual witness x).1 = x.1.1 := rfl

@[simp] theorem remainingColumnStubEquivResidual_class
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (x : RemainingColumnStub witness) :
    (remainingColumnStubEquivResidual witness x).1 = x.1.1 := rfl

/-- Exact finite-space identification: full matchings extending a fixed
exposed witness are equivalent to configuration matchings having the induced
residual row and column degrees. -/
def extensionsOfWitnessEquivResidualConfiguration
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    {matching : ConfigurationMatching row col //
        ExtendsPrescribedDemandWitness matching witness} ≃
      ConfigurationMatching (residualRowDegree witness)
        (residualColumnDegree witness) :=
  (extensionsOfPrescribedDemandWitnessEquivRemaining witness).trans
    ((remainingRowStubEquivResidual witness).equivCongr
      (remainingColumnStubEquivResidual witness))

/-- Uniformity transports across the exact extension/residual equivalence.
This is a law on the extension subtype; conditioning the ambient law is a
separate generic step. -/
theorem uniform_extensionSubtype_map_residual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    [Nonempty {matching : ConfigurationMatching row col //
        ExtendsPrescribedDemandWitness matching witness}]
    [Nonempty (ConfigurationMatching (residualRowDegree witness)
      (residualColumnDegree witness))] :
    (PMF.uniformOfFintype
        {matching : ConfigurationMatching row col //
          ExtendsPrescribedDemandWitness matching witness}).map
        (extensionsOfWitnessEquivResidualConfiguration witness) =
      PMF.uniformOfFintype
        (ConfigurationMatching (residualRowDegree witness)
          (residualColumnDegree witness)) :=
  uniformOfFintype_map_equiv
    (extensionsOfWitnessEquivResidualConfiguration witness)

end

end Erdos625
