import Erdos625.ConfigurationModelPrescribedCells

/-!
# Residual matchings after exposing a prescribed-demand witness

For a fixed `PrescribedDemandWitness`, the selected row and column stubs are
already paired.  This module identifies configuration matchings extending
that witness with arbitrary bijections between the two sets of unused stubs.

This is only a deterministic finite equivalence.  It does not assert a
probability law for the residual matching, nor does it identify residual
degree fibres.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The global row stubs selected by a prescribed-demand witness. -/
def witnessSelectedRowStubs
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Finset (RowStub row) :=
  Finset.univ.image (witnessRowEmbedding witness)

/-- The global column stubs paired with the selected row stubs. -/
def witnessSelectedColumnStubs
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Finset (ColumnStub col) :=
  Finset.univ.image (witnessColumnPairingEmbedding witness)

/-- Row stubs not selected by the fixed witness. -/
abbrev RemainingRowStub
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :=
  {stub : RowStub row // stub ∉ witnessSelectedRowStubs witness}

/-- Column stubs not selected by the fixed witness. -/
abbrev RemainingColumnStub
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :=
  {stub : ColumnStub col // stub ∉ witnessSelectedColumnStubs witness}

/-- An embedding is an equivalence from its domain to its finite image. -/
private def residualEmbeddingRangeEquiv
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X ↪ Y) : X ≃ ↑(Finset.univ.image f) :=
  Equiv.ofBijective
    (fun x ↦ ⟨f x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
    ⟨fun x y hxy ↦ f.injective (Subtype.ext_iff.mp hxy),
      fun y ↦ by
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp y.2
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp] private theorem residualEmbeddingRangeEquiv_val
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X ↪ Y) (x : X) :
    (residualEmbeddingRangeEquiv f x).1 = f x := rfl

/-- The selected images of two embeddings are paired by their common index. -/
private def residualEmbeddingImagePairing
    {X L R : Type*}
    [Fintype X] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (domain : X ↪ L) (codomain : X ↪ R) :
    ↑(Finset.univ.image domain) ≃ ↑(Finset.univ.image codomain) :=
  (residualEmbeddingRangeEquiv domain).symm.trans
    (residualEmbeddingRangeEquiv codomain)

/-- Pair the selected row and column stubs exactly as specified by the
fixed witness. -/
def witnessSelectedStubEquiv
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    ↑(witnessSelectedRowStubs witness) ≃
      ↑(witnessSelectedColumnStubs witness) :=
  residualEmbeddingImagePairing
    (witnessRowEmbedding witness)
    (witnessColumnPairingEmbedding witness)

/-- Rephrase an indexed extension condition as extension of the induced
bijection between the two finite images. -/
private def indexedExtensionsEquivImageExtensions
    {X L R : Type*}
    [Fintype X] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (domain : X ↪ L) (codomain : X ↪ R) :
    {matching : L ≃ R // ∀ x, matching (domain x) = codomain x} ≃
      MatchingExtensions (Finset.univ.image domain)
        (Finset.univ.image codomain)
        (residualEmbeddingImagePairing domain codomain) where
  toFun extension := ⟨extension.1, by
    intro y
    obtain ⟨x, rfl⟩ := (residualEmbeddingRangeEquiv domain).surjective y
    simpa [residualEmbeddingImagePairing] using extension.2 x⟩
  invFun extension := ⟨extension.1, by
    intro x
    simpa [residualEmbeddingImagePairing] using
      extension.2 (residualEmbeddingRangeEquiv domain x)⟩
  left_inv extension := by
    apply Subtype.ext
    rfl
  right_inv extension := by
    apply Subtype.ext
    rfl

/-- Restrict a full matching extending an exposed pairing to the complements
of the exposed finite subsets. -/
private def restrictResidualMatching
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {S : Finset L} {T : Finset R} {exposed : (↑S) ≃ (↑T)}
    (extension : MatchingExtensions S T exposed) :
    {x : L // x ∉ S} ≃ {y : R // y ∉ T} where
  toFun x := ⟨extension.1 x.1, by
    intro hxT
    let y : ↑T := ⟨extension.1 x.1, hxT⟩
    let s : ↑S := exposed.symm y
    have hsmap : extension.1 s.1 = y.1 := by
      calc
        extension.1 s.1 = (exposed s).1 := extension.2 s
        _ = y.1 := congrArg Subtype.val (exposed.apply_symm_apply y)
    have hsx : s.1 = x.1 := extension.1.injective hsmap
    exact x.2 (hsx ▸ s.2)⟩
  invFun y := ⟨extension.1.symm y.1, by
    intro hxS
    let s : ↑S := ⟨extension.1.symm y.1, hxS⟩
    have hsmap := extension.2 s
    apply y.2
    have hvalue : (exposed s).1 = y.1 := by
      calc
        (exposed s).1 = extension.1 s.1 := hsmap.symm
        _ = y.1 := extension.1.apply_symm_apply y.1
    exact hvalue ▸ (exposed s).2⟩
  left_inv x := by
    apply Subtype.ext
    exact extension.1.symm_apply_apply x.1
  right_inv y := by
    apply Subtype.ext
    exact extension.1.apply_symm_apply y.1

/-- Glue an exposed pairing and an arbitrary complement bijection into one
full matching. -/
private def extendResidualMatching
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {S : Finset L} {T : Finset R} (exposed : (↑S) ≃ (↑T))
    (residual : {x : L // x ∉ S} ≃ {y : R // y ∉ T}) :
    MatchingExtensions S T exposed := by
  let matching : L ≃ R :=
    (Equiv.sumCompl (fun x : L ↦ x ∈ S)).symm |>.trans
      ((Equiv.sumCongr exposed residual).trans
        (Equiv.sumCompl (fun y : R ↦ y ∈ T)))
  refine ⟨matching, ?_⟩
  intro x
  simp [matching]

/-- Extending an exposed finite pairing is equivalent to choosing an
arbitrary bijection between the two complements. -/
private def matchingExtensionsEquivResidual
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (S : Finset L) (T : Finset R) (exposed : (↑S) ≃ (↑T)) :
    MatchingExtensions S T exposed ≃
      ({x : L // x ∉ S} ≃ {y : R // y ∉ T}) where
  toFun := restrictResidualMatching
  invFun := extendResidualMatching exposed
  left_inv extension := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ S
    · simpa [extendResidualMatching, hx] using
        (extension.2 ⟨x, hx⟩).symm
    · simp [extendResidualMatching, restrictResidualMatching, hx]
  right_inv residual := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp [extendResidualMatching, restrictResidualMatching]

/-- Configuration matchings extending one fixed witness correspond exactly
to bijections between its unused row and column stubs. -/
def extensionsOfPrescribedDemandWitnessEquivRemaining
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    {matching : ConfigurationMatching row col //
        ExtendsPrescribedDemandWitness matching witness} ≃
      (RemainingRowStub witness ≃ RemainingColumnStub witness) :=
  (indexedExtensionsEquivImageExtensions
      (witnessRowEmbedding witness)
      (witnessColumnPairingEmbedding witness)).trans
    (matchingExtensionsEquivResidual
      (witnessSelectedRowStubs witness)
      (witnessSelectedColumnStubs witness)
      (witnessSelectedStubEquiv witness))

/-- Cardinality of the complement of a finite subset. -/
private theorem card_notMem_finset
    {X : Type*} [Fintype X] [DecidableEq X] (S : Finset X) :
    Fintype.card {x : X // x ∉ S} = Fintype.card X - S.card := by
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun x : X ↦ x ∉ S) = Sᶜ := by
    ext x
    simp
  rw [hfilter, Finset.card_compl]

/-- The selected row-stub set has exactly the total prescribed demand. -/
theorem card_witnessSelectedRowStubs
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    (witnessSelectedRowStubs witness).card =
      Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a)) := by
  unfold witnessSelectedRowStubs
  rw [Finset.card_image_of_injective]
  · simpa using card_witnessRowAtom witness
  · exact (witnessRowEmbedding witness).injective

/-- The selected column-stub set has exactly the total prescribed demand. -/
theorem card_witnessSelectedColumnStubs
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    (witnessSelectedColumnStubs witness).card =
      Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a)) := by
  unfold witnessSelectedColumnStubs
  rw [Finset.card_image_of_injective]
  · simpa using card_witnessRowAtom witness
  · exact (witnessColumnPairingEmbedding witness).injective

/-- Exact number of unused row stubs after exposing the witness. -/
theorem card_remainingRowStub
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Fintype.card (RemainingRowStub witness) =
      Finset.univ.sum row -
        Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a)) := by
  rw [card_notMem_finset, card_rowStub,
    card_witnessSelectedRowStubs witness]

/-- Exact number of unused column stubs after exposing the witness. -/
theorem card_remainingColumnStub
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Fintype.card (RemainingColumnStub witness) =
      Finset.univ.sum col -
        Finset.univ.sum (fun a ↦ Finset.univ.sum (demand a)) := by
  rw [card_notMem_finset, card_columnStub,
    card_witnessSelectedColumnStubs witness]

/-- Equal original row and column totals leave equally many unused stubs. -/
theorem card_remainingStubs_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    Fintype.card (RemainingRowStub witness) =
      Fintype.card (RemainingColumnStub witness) := by
  rw [card_remainingRowStub witness, card_remainingColumnStub witness, htotal]

end

end Erdos625
