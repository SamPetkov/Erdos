import Erdos625.ResidualDegreeMatching
import Mathlib.Tactic

/-!
# Cell-count decomposition after a fixed exposure

This module proves the deterministic classwise split of a configuration cell
after exposing one fixed prescribed-demand witness.  It does not assert a
conditional probability law, a high-cell cap, or canonical-skeleton
uniqueness.
-/

namespace Erdos625

noncomputable section

/-- A finite target fibre splits into its used part and the transported fibre
on the complement. -/
theorem card_targetFiber_eq_usedTarget_add_residual
    {X Y B : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [DecidableEq B]
    (used : Finset X) (fullTarget : X → B) (b : B)
    (residualEquiv : {x : X // x ∉ used} ≃ Y)
    (residualTarget : Y → B)
    (htransport : ∀ x, residualTarget (residualEquiv x) = fullTarget x.1) :
    (Finset.univ.filter (fun x => fullTarget x = b)).card =
      (used.filter (fun x => fullTarget x = b)).card +
        (Finset.univ.filter (fun y => residualTarget y = b)).card := by
  classical
  let complementFiberEquiv :
      {x : X // x ∉ used ∧ fullTarget x = b} ≃
        {y : Y // residualTarget y = b} :=
    { toFun := fun x => ⟨residualEquiv ⟨x.1, x.2.1⟩, by
        rw [htransport]
        exact x.2.2⟩
      invFun := fun y =>
        let x := residualEquiv.symm y.1
        ⟨x.1, x.2, by
          rw [← htransport x, residualEquiv.apply_symm_apply]
          exact y.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  have hresidualCard :
      (Finset.univ.filter (fun y => residualTarget y = b)).card =
        (Finset.univ.filter
          (fun x => x ∉ used ∧ fullTarget x = b)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr complementFiberEquiv.symm
  let fullFiber := Finset.univ.filter (fun x => fullTarget x = b)
  have hused :
      fullFiber.filter (fun x => x ∈ used) =
        used.filter (fun x => fullTarget x = b) := by
    ext x
    simp [fullFiber, and_comm]
  have hunused :
      fullFiber.filter (fun x => ¬ x ∈ used) =
        Finset.univ.filter (fun x => x ∉ used ∧ fullTarget x = b) := by
    ext x
    simp [fullFiber, and_comm]
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := fullFiber)
      (fun x => x ∈ used)
  rw [hused, hunused] at hpartition
  rw [hresidualCard]
  exact hpartition.symm

/-- The classwise component of `remainingRowStubEquivResidual`. -/
def remainingRowIndexEquivResidual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (a : A) :
    {i : Fin (row a) // i ∉ witnessSelectedRowIndices witness a} ≃
      Fin (residualRowDegree witness a) :=
  Fintype.equivFinOfCardEq (card_remainingRowFiber witness a)

theorem remainingRowStubEquivResidual_apply_in_class
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (a : A)
    (i : {i : Fin (row a) //
      i ∉ witnessSelectedRowIndices witness a}) :
    remainingRowStubEquivResidual witness
        ⟨⟨a, i.1⟩, by
          simpa [witnessSelectedRowIndices] using i.2⟩ =
      ⟨a, remainingRowIndexEquivResidual witness a i⟩ := by
  rfl

/-- The transported residual matching preserves the target class of every
unused row stub. -/
theorem residualConfiguration_targetClass
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (extension : {matching : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness matching witness})
    (x : RemainingRowStub witness) :
    ((extensionsOfWitnessEquivResidualConfiguration witness extension)
      (remainingRowStubEquivResidual witness x)).1 =
        (extension.1 x.1).1 := by
  calc
    ((extensionsOfWitnessEquivResidualConfiguration witness extension)
        (remainingRowStubEquivResidual witness x)).1 =
        (remainingColumnStubEquivResidual witness
          ((extensionsOfPrescribedDemandWitnessEquivRemaining witness extension)
            ((remainingRowStubEquivResidual witness).symm
              (remainingRowStubEquivResidual witness x)))).1 := rfl
    _ = (remainingColumnStubEquivResidual witness
          ((extensionsOfPrescribedDemandWitnessEquivRemaining witness extension)
            x)).1 := by rw [Equiv.symm_apply_apply]
    _ = (((extensionsOfPrescribedDemandWitnessEquivRemaining witness extension)
          x).1).1 := remainingColumnStubEquivResidual_class _ _
    _ = (extension.1 x.1).1 := by
      rfl

/-- Among all row stubs selected by the witness, the ones that a full
extension sends to class `b` are exactly the stubs selected in cell `(a,b)`. -/
theorem usedRowTargetIndices_eq_witnessCell
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (extension : {matching : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness matching witness})
    (a : A) (b : B) :
    (witnessSelectedRowIndices witness a).filter
        (fun i => (extension.1 ⟨a, i⟩).1 = b) =
      (witness.1 a).1 b := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨hselected, htarget⟩ := Finset.mem_filter.mp hi
    have hglobal :
        (⟨a, i⟩ : RowStub row) ∈ witnessSelectedRowStubs witness := by
      simpa [witnessSelectedRowIndices] using hselected
    obtain ⟨atom, _, hatom⟩ := Finset.mem_image.mp hglobal
    obtain ⟨a', b', stub⟩ := atom
    have ha : a' = a := (Sigma.mk.inj_iff.mp hatom).1
    subst a'
    have hstub : (stub : Fin (row a)) = i :=
      eq_of_heq (Sigma.mk.inj_iff.mp hatom).2
    have hbtarget := congrArg Sigma.fst (extension.2 ⟨a, b', stub⟩)
    change (extension.1 ⟨a, (stub : Fin (row a))⟩).1 = b' at hbtarget
    have hb : b' = b := by
      rw [hstub] at hbtarget
      exact hbtarget.symm.trans htarget
    subst b'
    simpa [hstub] using stub.2
  · intro hi
    let atom : WitnessRowAtom witness := ⟨a, b, ⟨i, hi⟩⟩
    have hglobal :
        (⟨a, i⟩ : RowStub row) ∈ witnessSelectedRowStubs witness := by
      apply Finset.mem_image.mpr
      exact ⟨atom, Finset.mem_univ atom, rfl⟩
    have hselected : i ∈ witnessSelectedRowIndices witness a := by
      simp [witnessSelectedRowIndices, hglobal]
    have htarget := congrArg Sigma.fst (extension.2 atom)
    change (extension.1 ⟨a, i⟩).1 = b at htarget
    exact Finset.mem_filter.mpr ⟨hselected, htarget⟩

/-- Exact classwise cell-count split after exposing a fixed labelled witness:
the full cell consists of its prescribed pairs plus the corresponding cell of
the transported residual configuration matching. -/
theorem configurationCellCount_eq_demand_add_residual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (extension : {matching : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness matching witness})
    (a : A) (b : B) :
    configurationCellCount extension.1 a b =
      demand a b +
        configurationCellCount
          (extensionsOfWitnessEquivResidualConfiguration witness extension)
          a b := by
  let residual :=
    extensionsOfWitnessEquivResidualConfiguration witness extension
  have htransport : ∀ x :
      {i : Fin (row a) // i ∉ witnessSelectedRowIndices witness a},
      (residual ⟨a, remainingRowIndexEquivResidual witness a x⟩).1 =
        (extension.1 ⟨a, x.1⟩).1 := by
    intro x
    let unused : RemainingRowStub witness :=
      ⟨⟨a, x.1⟩, by
        simpa [witnessSelectedRowIndices] using x.2⟩
    have hclass := residualConfiguration_targetClass witness extension unused
    rw [remainingRowStubEquivResidual_apply_in_class witness a x] at hclass
    exact hclass
  have hsplit := card_targetFiber_eq_usedTarget_add_residual
    (witnessSelectedRowIndices witness a)
    (fun i => (extension.1 ⟨a, i⟩).1) b
    (remainingRowIndexEquivResidual witness a)
    (fun i => (residual ⟨a, i⟩).1) htransport
  rw [usedRowTargetIndices_eq_witnessCell witness extension a b,
    (witness.1 a).2.1 b] at hsplit
  exact hsplit

end

end Erdos625
