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
  apply Fintype.card_congr
  refine Equiv.ofBijective
    (fun extension =>
      ⟨fixedWitnessExtensionEquivResidual witness extension.1,
        (mem_fixedWitnessCanonicalDemandEvent_iff_residual
          witness U hhigh extension.1).mp extension.2⟩) ?_ ?_
  · intro x y hxy
    apply Subtype.ext
    apply (fixedWitnessExtensionEquivResidual witness).injective
    exact Subtype.ext_iff.mp hxy
  · intro residual
    refine ⟨⟨(fixedWitnessExtensionEquivResidual witness).symm residual.1,
      (mem_fixedWitnessCanonicalDemandEvent_iff_residual
        witness U hhigh
        ((fixedWitnessExtensionEquivResidual witness).symm residual.1)).mpr ?_⟩,
      ?_⟩
    · simpa using residual.2
    · apply Subtype.ext
      exact (fixedWitnessExtensionEquivResidual witness).apply_symm_apply
        residual.1

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

private noncomputable def canonicalDemandEventPartitionMap
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    ↑(canonicalDemandEvent demand row col U) →
      Σ witness : PrescribedDemandWitness demand row col,
        ↑(fixedWitnessCanonicalDemandEvent witness U) := fun x =>
  ⟨canonicalDemandEventWitness demand row col U x,
    ⟨⟨x.1, canonicalDemandEventWitness_extends demand row col U x⟩,
      by
        change canonicalDemandOfMatching x.1 U = demand
        exact x.2⟩⟩

private theorem canonicalDemandEventPartitionMap_injective
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Function.Injective (canonicalDemandEventPartitionMap demand row col U) := by
  intro x y hxy
  apply Subtype.ext
  simpa [canonicalDemandEventPartitionMap] using
    congrArg (fun z => z.2.1.1) hxy

private theorem canonicalDemandEventPartitionMap_surjective
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Function.Surjective (canonicalDemandEventPartitionMap demand row col U) := by
  intro y
  let x : ↑(canonicalDemandEvent demand row col U) :=
    ⟨y.2.1.1, by
      change canonicalDemandOfMatching y.2.1.1 U = demand
      exact y.2.2⟩
  refine ⟨x, ?_⟩
  have hwitness : canonicalDemandEventWitness demand row col U x = y.1 :=
    canonicalDemandEventWitness_unique demand row col U x y.1 y.2.1.2
  unfold canonicalDemandEventPartitionMap
  apply Sigma.ext hwitness
  cases hwitness
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  rfl

private theorem canonicalDemandEvent_equiv_sigma_fixedWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    ↑(canonicalDemandEvent demand row col U) ≃
      Σ witness : PrescribedDemandWitness demand row col,
        ↑(fixedWitnessCanonicalDemandEvent witness U) := by
  exact Equiv.ofBijective
    (canonicalDemandEventPartitionMap demand row col U)
    ⟨canonicalDemandEventPartitionMap_injective demand row col U,
      canonicalDemandEventPartitionMap_surjective demand row col U⟩

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
