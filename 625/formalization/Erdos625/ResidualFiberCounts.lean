import Erdos625.ConfigurationModelResidualMatching

namespace Erdos625

open scoped BigOperators

noncomputable section

/-!
# Degree fibres of the exposed witness

These theorems refine the global selected-stub cardinalities class by class.
They are deterministic counts only; the conditional residual probability law
is not asserted here.
-/

theorem card_selectedRowStubs_in_class
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (a : A) :
    ((witnessSelectedRowStubs witness).filter
      (fun stub => stub.1 = a)).card = ∑ b, demand a b := by
  classical
  let f := witnessRowEmbedding witness
  have himage :
      (Finset.univ.image f).filter (fun stub => stub.1 = a) =
        (Finset.univ.filter
          (fun atom : WitnessRowAtom witness => (f atom).1 = a)).image f := by
    ext stub
    constructor
    · intro h
      obtain ⟨himage, hclass⟩ := Finset.mem_filter.mp h
      obtain ⟨atom, _, rfl⟩ := Finset.mem_image.mp himage
      exact Finset.mem_image.mpr ⟨atom,
        Finset.mem_filter.mpr ⟨Finset.mem_univ atom, hclass⟩, rfl⟩
    · intro h
      obtain ⟨atom, hatom, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨_, hclass⟩ := Finset.mem_filter.mp hatom
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_image_of_mem f (Finset.mem_univ atom), hclass⟩
  have hfilter :
      Finset.univ.filter
          (fun atom : WitnessRowAtom witness => (f atom).1 = a) =
        Finset.univ.filter (fun atom : WitnessRowAtom witness => atom.1 = a) := by
    ext atom
    simp [f, witnessRowEmbedding]
  unfold witnessSelectedRowStubs
  rw [himage, Finset.card_image_of_injective, hfilter]
  · rw [Finset.card_filter, Fintype.sum_sigma]
    have hinner : ∀ x : A,
        (∑ y : (b : B) × ↑((witness.1 x).1 b),
          if (⟨x, y⟩ : WitnessRowAtom witness).1 = a then (1 : ℕ) else 0) =
          if x = a then (∑ b, demand x b) else 0 := by
      intro x
      by_cases hx : x = a
      · subst x
        simp [Fintype.card_sigma, (witness.1 a).2.1]
      · simp [hx]
    rw [Finset.sum_congr rfl (fun x _ => hinner x),
      Finset.sum_ite_eq' Finset.univ a (fun x => ∑ b, demand x b)]
    simp
  · exact f.injective

theorem card_selectedColumnStubs_in_class
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (b : B) :
    ((witnessSelectedColumnStubs witness).filter
      (fun stub => stub.1 = b)).card = ∑ a, demand a b := by
  classical
  let f := witnessColumnPairingEmbedding witness
  have himage :
      (Finset.univ.image f).filter (fun stub => stub.1 = b) =
        (Finset.univ.filter
          (fun atom : WitnessRowAtom witness => (f atom).1 = b)).image f := by
    ext stub
    constructor
    · intro h
      obtain ⟨himage, hclass⟩ := Finset.mem_filter.mp h
      obtain ⟨atom, _, rfl⟩ := Finset.mem_image.mp himage
      exact Finset.mem_image.mpr ⟨atom,
        Finset.mem_filter.mpr ⟨Finset.mem_univ atom, hclass⟩, rfl⟩
    · intro h
      obtain ⟨atom, hatom, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨_, hclass⟩ := Finset.mem_filter.mp hatom
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_image_of_mem f (Finset.mem_univ atom), hclass⟩
  have hfilter :
      Finset.univ.filter
          (fun atom : WitnessRowAtom witness => (f atom).1 = b) =
        Finset.univ.filter
          (fun atom : WitnessRowAtom witness => atom.2.1 = b) := by
    ext atom
    simp [f, witnessColumnPairingEmbedding, witnessAtomEquiv,
      witnessColumnEmbedding]
  unfold witnessSelectedColumnStubs
  rw [himage, Finset.card_image_of_injective, hfilter]
  · rw [Finset.card_filter, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro a _
    rw [Fintype.sum_sigma]
    have hinner : ∀ x : B,
        (∑ _stub : ↑((witness.1 a).1 x),
          if x = b then (1 : ℕ) else 0) =
          if x = b then demand a x else 0 := by
      intro x
      by_cases hx : x = b
      · subst x
        simpa [Fintype.card_coe] using (witness.1 a).2.1 b
      · simp [hx]
    rw [Finset.sum_congr rfl (fun x _ => hinner x),
      Finset.sum_ite_eq' Finset.univ b (fun x => demand a x)]
    simp
  · exact f.injective

end

end Erdos625
