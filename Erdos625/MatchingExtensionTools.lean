import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-!
# Exact extension counts for exposed finite matchings

This module supplies the fixed-witness denominator factor needed to turn the
prescribed-demand count into the configuration-model probability bound (6.8).
-/

namespace Erdos625

/-- Full bijections extending a fixed bijection between two selected finite
subsets. -/
def MatchingExtensions
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (S : Finset L) (T : Finset R) (exposed : (↑S) ≃ (↑T)) :=
  {matching : L ≃ R //
    ∀ x : ↑S, matching x.1 = (exposed x).1}

instance instFiniteMatchingExtensions
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (S : Finset L) (T : Finset R) (exposed : (↑S) ≃ (↑T)) :
    Finite (MatchingExtensions S T exposed) := by
  unfold MatchingExtensions
  infer_instance

noncomputable instance instFintypeMatchingExtensions
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (S : Finset L) (T : Finset R) (exposed : (↑S) ≃ (↑T)) :
    Fintype (MatchingExtensions S T exposed) :=
  Fintype.ofFinite _

/-- Restrict an extending full matching to the two complements. -/
private noncomputable def restrictMatchingExtension
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

/-- Glue an exposed bijection and a complement bijection into one full
matching. -/
private def extendComplementMatching
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    {S : Finset L} {T : Finset R} (exposed : (↑S) ≃ (↑T))
    (complement : {x : L // x ∉ S} ≃ {y : R // y ∉ T}) :
    MatchingExtensions S T exposed := by
  let matching : L ≃ R :=
    (Equiv.sumCompl (fun x : L ↦ x ∈ S)).symm |>.trans
      ((Equiv.sumCongr exposed complement).trans
        (Equiv.sumCompl (fun y : R ↦ y ∈ T)))
  refine ⟨matching, ?_⟩
  intro x
  simp [matching]

/-- Extending full matchings correspond exactly to arbitrary bijections of
the two complements. -/
private noncomputable def matchingExtensionsEquivComplement
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (S : Finset L) (T : Finset R) (exposed : (↑S) ≃ (↑T)) :
    MatchingExtensions S T exposed ≃
      ({x : L // x ∉ S} ≃ {y : R // y ∉ T}) where
  toFun := restrictMatchingExtension
  invFun := extendComplementMatching exposed
  left_inv extension := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ S
    · simpa [extendComplementMatching, hx] using
        (extension.2 ⟨x, hx⟩).symm
    · simp [extendComplementMatching, restrictMatchingExtension, hx]
  right_inv complement := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    simp [extendComplementMatching, restrictMatchingExtension]

private lemma card_notMem
    {L : Type*} [Fintype L] [DecidableEq L] (S : Finset L) :
    Fintype.card {x : L // x ∉ S} = Fintype.card L - S.card := by
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun x : L ↦ x ∉ S) = Sᶜ := by
    ext x
    simp
  rw [hfilter, Finset.card_compl]

/-- Once an exposed pairing between equal-sized finite subsets is fixed,
exactly `(card L - card S)!` full bijections extend it. -/
theorem card_extensions_of_exposed_equiv
    {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (hcard : Fintype.card L = Fintype.card R)
    (S : Finset L) (T : Finset R) (exposed : (↑S) ≃ (↑T)) :
    Fintype.card (MatchingExtensions S T exposed) =
      (Fintype.card L - S.card).factorial := by
  have hST : S.card = T.card := by
    have h := Fintype.card_congr exposed
    rwa [Fintype.card_coe, Fintype.card_coe] at h
  have hcompl : Fintype.card {x : L // x ∉ S} =
      Fintype.card {y : R // y ∉ T} := by
    rw [card_notMem, card_notMem, hcard, hST]
  rw [Fintype.card_congr (matchingExtensionsEquivComplement S T exposed),
    Fintype.card_equiv (Fintype.equivOfCardEq hcompl), card_notMem]

/-- An embedding is an equivalence from its domain onto its finite image. -/
private noncomputable def embeddingRangeEquiv
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X ↪ Y) : X ≃ ↑(Finset.univ.image f) :=
  Equiv.ofBijective
    (fun x ↦ ⟨f x, Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩)
    ⟨fun x y hxy ↦ f.injective (Subtype.ext_iff.mp hxy),
      fun y ↦ by
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp y.2
        exact ⟨x, Subtype.ext hx⟩⟩

@[simp] private lemma embeddingRangeEquiv_val
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X ↪ Y) (x : X) :
    (embeddingRangeEquiv f x).1 = f x := rfl

/-- The selected images of two embeddings are paired using their common
indexing type. -/
private noncomputable def embeddingImagePairing
    {X L R : Type*}
    [Fintype X] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (domain : X ↪ L) (codomain : X ↪ R) :
    ↑(Finset.univ.image domain) ≃ ↑(Finset.univ.image codomain) :=
  (embeddingRangeEquiv domain).symm.trans (embeddingRangeEquiv codomain)

/-- Stating extension through the common embedding index or through the
induced exposed image equivalence gives equivalent finite types. -/
private noncomputable def pairingExtensionsEquivImageExtensions
    {X L R : Type*}
    [Fintype X] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (domain : X ↪ L) (codomain : X ↪ R) :
    {matching : L ≃ R // ∀ x, matching (domain x) = codomain x} ≃
      MatchingExtensions (Finset.univ.image domain)
        (Finset.univ.image codomain)
        (embeddingImagePairing domain codomain) where
  toFun extension := ⟨extension.1, by
    intro y
    obtain ⟨x, rfl⟩ := (embeddingRangeEquiv domain).surjective y
    simpa [embeddingImagePairing] using extension.2 x⟩
  invFun extension := ⟨extension.1, by
    intro x
    simpa [embeddingImagePairing] using
      extension.2 (embeddingRangeEquiv domain x)⟩
  left_inv extension := by
    apply Subtype.ext
    rfl
  right_inv extension := by
    apply Subtype.ext
    rfl

/-- Exactly `(card L-card X)!` full bijections extend a prescribed family of
distinct pairs indexed by `X`.  This is the generic fixed-witness count used
before the union bound in (6.8). -/
theorem card_extensions_of_embedding_pairing
    {X L R : Type*}
    [Fintype X] [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    (hcard : Fintype.card L = Fintype.card R)
    (domain : X ↪ L) (codomain : X ↪ R) :
    Fintype.card
        {matching : L ≃ R // ∀ x, matching (domain x) = codomain x} =
      (Fintype.card L - Fintype.card X).factorial := by
  rw [Fintype.card_congr
      (pairingExtensionsEquivImageExtensions domain codomain),
    card_extensions_of_exposed_equiv hcard]
  congr 2
  rw [Finset.card_image_of_injective]
  · simp
  · exact domain.injective

end Erdos625
