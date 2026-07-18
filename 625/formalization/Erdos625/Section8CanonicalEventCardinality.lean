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

/-- For a fixed labelled witness, transport the canonical full-event fibre to
the corresponding residual half-cap/no-return fibre. -/
noncomputable def fixedWitnessCanonicalDemandEventEquivResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b) :
    fixedWitnessCanonicalDemandEvent witness U ≃
      canonicalResidualCellEvent witness U := by
  exact Equiv.subtypeEquiv (fixedWitnessExtensionEquivResidual witness)
    (mem_fixedWitnessCanonicalDemandEvent_iff_residual witness U hhigh)

private theorem card_fixedWitnessCanonicalDemandEvent_eq_residual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b) :
    Fintype.card (fixedWitnessCanonicalDemandEvent witness U) =
      Fintype.card (canonicalResidualCellEvent witness U) := by
  exact Fintype.card_congr
    (fixedWitnessCanonicalDemandEventEquivResidual witness U hhigh)

private theorem card_canonicalResidualCellEvent_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness witness₀ : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype.card (canonicalResidualCellEvent witness U) =
      Fintype.card (canonicalResidualCellEvent witness₀ U) := by
  rfl

private theorem existsUnique_canonicalDemandEventWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (x : ↑(canonicalDemandEvent demand row col U)) :
    ∃! witness : PrescribedDemandWitness demand row col,
      ExtendsPrescribedDemandWitness x.1 witness := by
  have hunique := existsUnique_canonicalHighDemandWitness row col x.1 U
  rw [x.2] at hunique
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
  exact (existsUnique_canonicalDemandEventWitness demand row col U x).unique
    (canonicalDemandEventWitness_extends demand row col U x) hwitness

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
  exact
  { toFun := fun extension =>
      ⟨⟨extension.1.1, extension.2⟩,
        (canonicalDemandEventWitness_eq_iff_extends
          demand row col U _ witness).mpr extension.1.2⟩
    invFun := fun x =>
      ⟨⟨x.1.1, (canonicalDemandEventWitness_eq_iff_extends
          demand row col U x.1 witness).mp x.2⟩, x.1.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private noncomputable def canonicalDemandEvent_equiv_sigma_fixedWitness
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

/-- Exact partition of a fixed canonical-demand event by its unique labelled
canonical witness.  No high-demand hypothesis is needed for this first
finite decomposition. -/
noncomputable def canonicalDemandEventEquivSigmaFixedWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    ↑(canonicalDemandEvent demand row col U) ≃
      Σ witness : PrescribedDemandWitness demand row col,
        ↑(fixedWitnessCanonicalDemandEvent witness U) :=
  canonicalDemandEvent_equiv_sigma_fixedWitness demand row col U

/-- Under the strict high-demand condition, the canonical-demand event is
exactly the sigma family of residual half-cap/no-return fibres.  This is a
finite equivalence, not a conditional-probability assertion. -/
noncomputable def canonicalDemandEventEquivSigmaResidual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b) :
    ↑(canonicalDemandEvent demand row col U) ≃
      Σ witness : PrescribedDemandWitness demand row col,
        ↑(canonicalResidualCellEvent witness U) :=
  (canonicalDemandEventEquivSigmaFixedWitness demand row col U).trans
    (Equiv.sigmaCongrRight (fun witness =>
      fixedWitnessCanonicalDemandEventEquivResidual witness U hhigh))

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
        Fintype.card (Σ witness : PrescribedDemandWitness demand row col,
          ↑(canonicalResidualCellEvent witness U)) :=
      Fintype.card_congr
        (canonicalDemandEventEquivSigmaResidual demand row col U hhigh)
    _ = ∑ witness : PrescribedDemandWitness demand row col,
          Fintype.card ↑(canonicalResidualCellEvent witness U) :=
      Fintype.card_sigma
    _ = ∑ _witness : PrescribedDemandWitness demand row col,
          Fintype.card ↑(canonicalResidualCellEvent witness₀ U) := by
      apply Finset.sum_congr rfl
      intro witness _
      exact card_canonicalResidualCellEvent_eq witness witness₀ U
    _ = Fintype.card (PrescribedDemandWitness demand row col) *
          Fintype.card ↑(canonicalResidualCellEvent witness₀ U) := by
      calc
        _ = Finset.univ.card *
              Fintype.card ↑(canonicalResidualCellEvent witness₀ U) :=
          Finset.sum_const_nat (fun _ _ => rfl)
        _ = _ := by rw [Finset.card_univ]

#print axioms card_canonicalDemandEvent_eq_witness_mul_residual

end

end Erdos625
