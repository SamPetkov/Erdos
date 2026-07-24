import Erdos625.Section8EndpointFoundation
import Erdos625.Section8TypeTableFeasibility
import Mathlib.Tactic

/-!
# Target D: full-table feasibility from block matching

The block matching is an explicit input. This target must not identify the
full-cell table with a raw stub aggregate or infer matching from stub
uniqueness without the canonical-high bridge.
-/

namespace Erdos625

set_option autoImplicit false

theorem fourEndpoint_fullTable_feasible_of_matching
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k))
    (hMatching : FourEndpointFullPairsAreMatching alpha hAlpha k S) :
    FourEndpointFeasible alpha hAlpha k
      (fourEndpointFullTableOfBlockTypeTable alpha hAlpha k S.typeTable) := by
  classical
  have hslots (i : Fin 4) :
      (fourEndpointBlockSlots alpha hAlpha k i).card =
        fourEndpointMultiplicity alpha hAlpha k i := by
    have hcount := ColoringProfile.count_sizes_at k
      (fourEndpointCoordinate alpha hAlpha i)
    change (fourEndpointBlockSlots alpha hAlpha k i).card =
      k (fourEndpointCoordinate alpha hAlpha i)
    rw [← hcount]
    calc
      _ = Fintype.card {q : ProfileBlockIndex k //
          (q.1 : Nat) = (fourEndpointCoordinate alpha hAlpha i).val + 1} := by
        symm
        apply Fintype.card_ofFinset
      _ = _ := card_shapeBlockIndexOfSize (ColoringProfile.sizes k)
        ((fourEndpointCoordinate alpha hAlpha i).val + 1)
  have hsize_injective : Function.Injective (fourEndpointSize alpha hAlpha) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [fourEndpointSize, fourEndpointCoordinate, fourDeficitCoordinate,
        fourDeficit] at hij ⊢ <;> omega
  constructor
  · intro i
    let C : Fin 4 → Finset (ProfileBlockIndex k × ProfileBlockIndex k) := fun j =>
      ((fourEndpointBlockSlots alpha hAlpha k i).product
        (fourEndpointBlockSlots alpha hAlpha k j)).filter
          (fun ab => S.typeTable ab.1 ab.2 =
            fourEndpointOverlapSize alpha hAlpha i j)
    have hdisj : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint C := by
      intro j₁ _ j₂ _ hj
      change Disjoint (C j₁) (C j₂)
      rw [Finset.disjoint_left]
      intro ab hab₁ hab₂
      dsimp [C] at hab₁ hab₂
      simp only [Finset.mem_filter, Finset.mem_product] at hab₁ hab₂
      have hb₁ : ab.2 ∈ fourEndpointBlockSlots alpha hAlpha k j₁ :=
        hab₁.1.2
      have hb₂ : ab.2 ∈ fourEndpointBlockSlots alpha hAlpha k j₂ :=
        hab₂.1.2
      have hs₁ : profileBlockMargin k ab.2 = fourEndpointSize alpha hAlpha j₁ :=
        (Finset.mem_filter.mp hb₁).2
      have hs₂ : profileBlockMargin k ab.2 = fourEndpointSize alpha hAlpha j₂ :=
        (Finset.mem_filter.mp hb₂).2
      exact hj (hsize_injective (hs₁.symm.trans hs₂))
    have hcard : (Finset.univ.sum fun j => (C j).card) =
        (Finset.univ.biUnion C).card := by
      rw [Finset.card_biUnion hdisj]
    have hle : (Finset.univ.biUnion C).card ≤
        (fourEndpointBlockSlots alpha hAlpha k i).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro ab hab
        have hab' : ab ∈ Finset.univ.biUnion C := hab
        rw [Finset.mem_biUnion] at hab'
        obtain ⟨j, -, hj⟩ := hab'
        dsimp [C] at hj
        simp only [Finset.mem_filter, Finset.mem_product] at hj
        exact hj.1.1
      · intro ab₁ hab₁ ab₂ hab₂ heq
        have hab₁' : ab₁ ∈ Finset.univ.biUnion C := hab₁
        have hab₂' : ab₂ ∈ Finset.univ.biUnion C := hab₂
        rw [Finset.mem_biUnion] at hab₁' hab₂'
        obtain ⟨j₁, -, hj₁⟩ := hab₁'
        obtain ⟨j₂, -, hj₂⟩ := hab₂'
        dsimp [C] at hj₁ hj₂
        simp only [Finset.mem_filter, Finset.mem_product] at hj₁ hj₂
        apply Prod.ext heq
        apply hMatching.1 ab₁.1 ab₁.2 ab₂.2
        · rw [fourEndpointFullPairs, Finset.mem_filter]
          exact ⟨by simp, i, j₁, hj₁.1.1, hj₁.1.2, hj₁.2⟩
        · rw [fourEndpointFullPairs, Finset.mem_filter]
          refine ⟨by simp, i, j₂, ?_⟩
          simpa [heq] using ⟨hj₂.1.1, hj₂.1.2, hj₂.2⟩
    rw [fourEndpointRowMargin, fourEndpointFullTableOfBlockTypeTable]
    change (Finset.univ.sum fun j => (C j).card) ≤ _
    rw [hcard]
    simpa [hslots i] using hle
  · intro j
    let C : Fin 4 → Finset (ProfileBlockIndex k × ProfileBlockIndex k) := fun i =>
      ((fourEndpointBlockSlots alpha hAlpha k i).product
        (fourEndpointBlockSlots alpha hAlpha k j)).filter
          (fun ab => S.typeTable ab.1 ab.2 =
            fourEndpointOverlapSize alpha hAlpha i j)
    have hdisj : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint C := by
      intro i₁ _ i₂ _ hi
      change Disjoint (C i₁) (C i₂)
      rw [Finset.disjoint_left]
      intro ab hab₁ hab₂
      dsimp [C] at hab₁ hab₂
      simp only [Finset.mem_filter, Finset.mem_product] at hab₁ hab₂
      have ha₁ := (Finset.mem_filter.mp hab₁.1.1).2
      have ha₂ := (Finset.mem_filter.mp hab₂.1.1).2
      exact hi (hsize_injective (ha₁.symm.trans ha₂))
    have hcard : (Finset.univ.sum fun i => (C i).card) =
        (Finset.univ.biUnion C).card := by
      rw [Finset.card_biUnion hdisj]
    have hle : (Finset.univ.biUnion C).card ≤
        (fourEndpointBlockSlots alpha hAlpha k j).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro ab hab
        have hab' : ab ∈ Finset.univ.biUnion C := hab
        rw [Finset.mem_biUnion] at hab'
        obtain ⟨i, -, hi⟩ := hab'
        dsimp [C] at hi
        simp only [Finset.mem_filter, Finset.mem_product] at hi
        exact hi.1.2
      · intro ab₁ hab₁ ab₂ hab₂ heq
        have hab₁' : ab₁ ∈ Finset.univ.biUnion C := hab₁
        have hab₂' : ab₂ ∈ Finset.univ.biUnion C := hab₂
        rw [Finset.mem_biUnion] at hab₁' hab₂'
        obtain ⟨i₁, -, hi₁⟩ := hab₁'
        obtain ⟨i₂, -, hi₂⟩ := hab₂'
        dsimp [C] at hi₁ hi₂
        simp only [Finset.mem_filter, Finset.mem_product] at hi₁ hi₂
        apply Prod.ext
        · apply hMatching.2 ab₁.1 ab₂.1 ab₁.2
          · rw [fourEndpointFullPairs, Finset.mem_filter]
            exact ⟨by simp, i₁, j, hi₁.1.1, hi₁.1.2, hi₁.2⟩
          · rw [fourEndpointFullPairs, Finset.mem_filter]
            refine ⟨by simp, i₂, j, ?_⟩
            simpa [heq] using ⟨hi₂.1.1, hi₂.1.2, hi₂.2⟩
        · exact heq
    rw [fourEndpointColumnMargin, fourEndpointFullTableOfBlockTypeTable]
    change (Finset.univ.sum fun i => (C i).card) ≤ _
    rw [hcard]
    simpa [hslots j] using hle

end Erdos625
