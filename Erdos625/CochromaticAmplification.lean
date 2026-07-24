import Erdos625.InducedCochromaticCapacity

/-!
# Deterministic cochromatic amplification bridge

This file isolates the deterministic part of manuscript Lemma 10.2.  A set
attaining `cochromaticInducedCapacity` exists because the defining feasible
family is a nonempty finite family.  Concatenating its cocolouring with an
ordinary colouring of the complementary induced graph gives the exact
whole-graph bound corresponding to (10.9).

No probabilistic amplification or leftover-colouring estimate is asserted
here.
-/

open Finset Set

namespace Erdos625

noncomputable section

/-- The maximum in `cochromaticInducedCapacity` is attained by an actual
induced vertex set carrying a `k`-cocolouring. -/
theorem exists_cochromaticInducedCapacity_witness {n : ℕ}
    (G : LabeledGraph n) (k : ℕ) :
    ∃ W : Finset (Fin n),
      CoColorable (G.induce (↑W : Set (Fin n))) k ∧
        W.card = cochromaticInducedCapacity G k := by
  classical
  have hmem : cochromaticInducedCapacity G k ∈
      (cochromaticFeasibleSets G k).image Finset.card :=
    Finset.max'_mem _ _
  rw [Finset.mem_image] at hmem
  obtain ⟨W, hWmem, hWcard⟩ := hmem
  rw [cochromaticFeasibleSets, Finset.mem_filter] at hWmem
  exact ⟨W, hWmem.2, hWcard⟩

/-- The subtype of vertices left outside a capacity-attaining set has exactly
`n - cochromaticInducedCapacity G k` elements. -/
theorem capacity_witness_compl_card {n k : ℕ} {G : LabeledGraph n}
    {W : Finset (Fin n)}
    (hWcard : W.card = cochromaticInducedCapacity G k) :
    Fintype.card (↑((↑W : Set (Fin n)))ᶜ : Type) =
      n - cochromaticInducedCapacity G k := by
  classical
  rw [Fintype.card_compl_set]
  simp [hWcard]

/-- A `k`-cocolourable induced core and an ordinary optimal colouring of its
complement concatenate to a cocolouring of the whole graph. -/
theorem coColorable_add_chromaticNumber_compl {n k : ℕ}
    (G : LabeledGraph n) (W : Finset (Fin n))
    (hW : CoColorable (G.induce (↑W : Set (Fin n))) k) :
    CoColorable G
      (k + chromaticNumberNat
        (G.induce ((↑W : Set (Fin n)))ᶜ)) := by
  exact coColorable_of_induce_and_colorable_compl
    (↑W : Set (Fin n)) hW
      (colorable_chromaticNumberNat
        (G.induce ((↑W : Set (Fin n)))ᶜ))

/-- Natural-number form of the deterministic manuscript inequality (10.9)
for any induced core admitting a `k`-cocolouring. -/
theorem cochromaticNumber_le_add_chromaticNumber_compl {n k : ℕ}
    (G : LabeledGraph n) (W : Finset (Fin n))
    (hW : CoColorable (G.induce (↑W : Set (Fin n))) k) :
    cochromaticNumber G ≤
      k + chromaticNumberNat
        (G.induce ((↑W : Set (Fin n)))ᶜ) :=
  cochromaticNumber_le_of_coColorable G
    (coColorable_add_chromaticNumber_compl G W hW)

/-- A maximizing induced core can be chosen so that its exact size, the exact
leftover size, and the deterministic whole-graph cochromatic bound are all
available from one witness. -/
theorem exists_capacity_witness_with_compl_bound {n : ℕ}
    (G : LabeledGraph n) (k : ℕ) :
    ∃ W : Finset (Fin n),
      CoColorable (G.induce (↑W : Set (Fin n))) k ∧
      W.card = cochromaticInducedCapacity G k ∧
      Fintype.card (↑((↑W : Set (Fin n)))ᶜ : Type) =
        n - cochromaticInducedCapacity G k ∧
      cochromaticNumber G ≤
        k + chromaticNumberNat
          (G.induce ((↑W : Set (Fin n)))ᶜ) := by
  obtain ⟨W, hW, hWcard⟩ :=
    exists_cochromaticInducedCapacity_witness G k
  exact ⟨W, hW, hWcard, capacity_witness_compl_card hWcard,
    cochromaticNumber_le_add_chromaticNumber_compl G W hW⟩

end

end Erdos625
