import Erdos625.Section8CanonicalEventCharacterization

/-!
# Section 8: canonical-event cardinality

The literal canonical event partitions into one fixed-witness fibre for each
labelled prescribed-demand witness.  Each fibre transports to the same residual
half-cap/no-return event, yielding the exact finite incidence count.
-/

namespace Erdos625

noncomputable section

/-! The event subtypes are finite, but the project deliberately does not make
their `Fintype` instances global.  Keep them local to this counting module. -/
local instance instFintypeCanonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

local instance instFintypeFixedWitnessCanonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (fixedWitnessCanonicalDemandEvent witness U) :=
  Fintype.ofFinite _

local instance instFintypeCanonicalResidualCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

private theorem card_fixedWitnessCanonicalDemandEvent_eq_residual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b) :
    Fintype.card (fixedWitnessCanonicalDemandEvent witness U) =
      Fintype.card (canonicalResidualCellEvent witness U) := by
  classical
  let f :
      ↑(fixedWitnessCanonicalDemandEvent witness U) →
        ↑(canonicalResidualCellEvent witness U) :=
    fun extension =>
      ⟨fixedWitnessExtensionEquivResidual witness extension.1,
        (mem_fixedWitnessCanonicalDemandEvent_iff_residual
          witness U hhigh extension.1).mp extension.2⟩
  apply Fintype.card_congr
  exact
  { toFun := f
    invFun := fun residual =>
      ⟨(fixedWitnessExtensionEquivResidual witness).symm residual.1,
        (mem_fixedWitnessCanonicalDemandEvent_iff_residual
          witness U hhigh
          ((fixedWitnessExtensionEquivResidual witness).symm residual.1)).mpr
          (by
            rw [(fixedWitnessExtensionEquivResidual witness).apply_symm_apply]
            exact residual.2)⟩
    left_inv := by
      intro extension
      apply Subtype.ext
      exact (fixedWitnessExtensionEquivResidual witness).symm_apply_apply extension.1
    right_inv := by
      intro residual
      apply Subtype.ext
      exact (fixedWitnessExtensionEquivResidual witness).apply_symm_apply residual.1 }

private theorem card_canonicalResidualCellEvent_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness witness₀ : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype.card (canonicalResidualCellEvent witness U) =
      Fintype.card (canonicalResidualCellEvent witness₀ U) := by
  apply Fintype.card_congr
  exact Equiv.refl _

private theorem existsUnique_canonicalDemandEventWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (x : ↑(canonicalDemandEvent demand row col U)) :
    ∃! witness : PrescribedDemandWitness demand row col,
      ExtendsPrescribedDemandWitness x.1 witness := by
  have hx : canonicalDemandOfMatching x.1 U = demand := x.2
  have hunique :=
    existsUnique_canonicalHighDemandWitness row col x.1 U
  rw [hx] at hunique
  exact hunique

private noncomputable def canonicalDemandEventWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (x : ↑(canonicalDemandEvent demand row col U)) :
    PrescribedDemandWitness demand row col :=
  Classical.choose
    (existsUnique_canonicalDemandEventWitness demand row col U x).exists

private theorem canonicalDemandEventWitness_extends
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (x : ↑(canonicalDemandEvent demand row col U)) :
    ExtendsPrescribedDemandWitness x.1
      (canonicalDemandEventWitness demand row col U x) := by
  unfold canonicalDemandEventWitness
  exact Classical.choose_spec
    (existsUnique_canonicalDemandEventWitness demand row col U x).exists

private theorem canonicalDemandEventWitness_unique
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (x : ↑(canonicalDemandEvent demand row col U))
    (witness : PrescribedDemandWitness demand row col)
    (hwitness : ExtendsPrescribedDemandWitness x.1 witness) :
    canonicalDemandEventWitness demand row col U x = witness := by
  obtain ⟨witness₀, hwitness₀, hunique⟩ :=
    existsUnique_canonicalDemandEventWitness demand row col U x
  have hchosen : canonicalDemandEventWitness demand row col U x = witness₀ :=
    hunique _ (canonicalDemandEventWitness_extends demand row col U x)
  have hgiven : witness = witness₀ := hunique _ hwitness
  exact hchosen.trans hgiven.symm

private theorem canonicalDemandEventWitness_eq_iff_extends
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (x : ↑(canonicalDemandEvent demand row col U))
    (witness : PrescribedDemandWitness demand row col) :
    canonicalDemandEventWitness demand row col U x = witness ↔
      ExtendsPrescribedDemandWitness x.1 witness := by
  constructor
  · intro h
    exact h ▸ canonicalDemandEventWitness_extends demand row col U x
  · intro h
    exact canonicalDemandEventWitness_unique demand row col U x witness h

private noncomputable def fixedWitnessCanonicalDemandEventEquivFiber
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    fixedWitnessCanonicalDemandEvent witness U ≃
      {x : ↑(canonicalDemandEvent demand row col U) //
        canonicalDemandEventWitness demand row col U x = witness} := by
  let e₁ : fixedWitnessCanonicalDemandEvent witness U ≃
      {m : ConfigurationMatching row col //
        ExtendsPrescribedDemandWitness m witness ∧
          canonicalDemandOfMatching m U = demand} := by
    change {e : {m : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness m witness} //
      canonicalDemandOfMatching e.1 U = demand} ≃ _
    exact Equiv.subtypeSubtypeEquivSubtypeInter
      (fun m : ConfigurationMatching row col =>
        ExtendsPrescribedDemandWitness m witness)
      (fun m => canonicalDemandOfMatching m U = demand)
  let e₂ : {m : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness m witness ∧
        canonicalDemandOfMatching m U = demand} ≃
      {m : ConfigurationMatching row col //
        canonicalDemandOfMatching m U = demand ∧
          ExtendsPrescribedDemandWitness m witness} :=
    Equiv.subtypeEquivRight (fun _ => and_comm)
  let e₃ : {m : ConfigurationMatching row col //
      canonicalDemandOfMatching m U = demand ∧
        ExtendsPrescribedDemandWitness m witness} ≃
      {x : ↑(canonicalDemandEvent demand row col U) //
        ExtendsPrescribedDemandWitness x.1 witness} := by
    change _ ≃ {x : {m : ConfigurationMatching row col //
      canonicalDemandOfMatching m U = demand} //
      ExtendsPrescribedDemandWitness x.1 witness}
    exact (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun m : ConfigurationMatching row col =>
        canonicalDemandOfMatching m U = demand)
      (fun m => ExtendsPrescribedDemandWitness m witness)).symm
  let e₄ : {x : ↑(canonicalDemandEvent demand row col U) //
      ExtendsPrescribedDemandWitness x.1 witness} ≃
      {x : ↑(canonicalDemandEvent demand row col U) //
        canonicalDemandEventWitness demand row col U x = witness} :=
    (Equiv.subtypeEquivRight (fun x =>
      canonicalDemandEventWitness_eq_iff_extends demand row col U x witness)).symm
  exact e₁.trans (e₂.trans (e₃.trans e₄))

private theorem canonicalDemandEvent_equiv_sigma_fixedWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    ↑(canonicalDemandEvent demand row col U) ≃
      Σ witness : PrescribedDemandWitness demand row col,
        ↑(fixedWitnessCanonicalDemandEvent witness U) := by
  exact
    (Equiv.sigmaFiberEquiv
      (canonicalDemandEventWitness demand row col U)).symm.trans
      (Equiv.sigmaCongrRight
      (fun witness =>
        (fixedWitnessCanonicalDemandEventEquivFiber
          (demand := demand) (row := row) (col := col) witness U).symm))

private theorem card_canonicalDemandEvent_eq_sum_fixedWitnessCanonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Fintype.card ↑(canonicalDemandEvent demand row col U) =
      ∑ witness : PrescribedDemandWitness demand row col,
        Fintype.card ↑(fixedWitnessCanonicalDemandEvent witness U) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (canonicalDemandEvent_equiv_sigma_fixedWitness demand row col U)

/-- Exact once-only incidence count: canonical configurations are a labelled
witness choice times one common residual cap/no-return fibre. -/
theorem card_canonicalDemandEvent_eq_witness_mul_residual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (witness₀ : PrescribedDemandWitness demand row col) :
    Fintype.card ↑(canonicalDemandEvent demand row col U) =
      Fintype.card (PrescribedDemandWitness demand row col) *
        Fintype.card ↑(canonicalResidualCellEvent witness₀ U) := by
  classical
  calc
    Fintype.card ↑(canonicalDemandEvent demand row col U) =
        ∑ witness : PrescribedDemandWitness demand row col,
          Fintype.card ↑(fixedWitnessCanonicalDemandEvent witness U) :=
      card_canonicalDemandEvent_eq_sum_fixedWitnessCanonicalDemandEvent
        demand row col U
    _ = ∑ witness : PrescribedDemandWitness demand row col,
          Fintype.card ↑(canonicalResidualCellEvent witness U) := by
      apply Finset.sum_congr rfl
      intro witness _
      exact card_fixedWitnessCanonicalDemandEvent_eq_residual witness U hhigh
    _ = ∑ _witness : PrescribedDemandWitness demand row col,
          Fintype.card ↑(canonicalResidualCellEvent witness₀ U) := by
      apply Finset.sum_congr rfl
      intro witness _
      exact card_canonicalResidualCellEvent_eq witness witness₀ U
    _ = Fintype.card (PrescribedDemandWitness demand row col) *
          Fintype.card ↑(canonicalResidualCellEvent witness₀ U) := by
      simp

#print axioms card_canonicalDemandEvent_eq_witness_mul_residual

end

end Erdos625
