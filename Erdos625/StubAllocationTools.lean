import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite disjoint stub allocations

This module begins the trusted local replacement for the quarantined
Aristotle Section 6 counting leaves.  The statements here are purely finite:
they count labelled subsets of `Fin m` disjoint from already allocated cells.
-/

namespace Erdos625

open scoped BigOperators

/-- A family of pairwise disjoint labelled subsets of `Fin m`, with prescribed
cardinality in each cell. -/
def StubAllocation {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :=
  {allocation : C → Finset (Fin m) //
    (∀ c, (allocation c).card = demand c) ∧
    ∀ c₁ c₂, c₁ ≠ c₂ → Disjoint (allocation c₁) (allocation c₂)}

instance instFiniteStubAllocation
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :
    Finite (StubAllocation m demand) := by
  unfold StubAllocation
  infer_instance

noncomputable instance instFintypeStubAllocation
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :
    Fintype (StubAllocation m demand) :=
  Fintype.ofFinite _

/-- The union of a disjoint stub allocation has cardinality equal to the total
demand. -/
theorem card_iUnion_stubAllocation
    {C : Type*} [Fintype C] [DecidableEq C]
    {m : ℕ} {demand : C → ℕ}
    (allocation : StubAllocation m demand) :
    (Finset.univ.biUnion allocation.1).card = Finset.univ.sum demand := by
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl (fun c _ => allocation.2.1 c)
  · intro c₁ _ c₂ _ hne
    exact allocation.2.2 c₁ c₂ hne

/-- After a disjoint family using `sum demand` labelled stubs has been fixed,
the number of new `d`-subsets disjoint from it is the residual binomial
coefficient.  No feasibility hypothesis on `d` is needed: both sides vanish
when `d` exceeds the complement size. -/
theorem card_disjoint_extension
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ)
    (allocation : StubAllocation m demand) (d : ℕ) :
    Fintype.card
        {s : Finset (Fin m) //
          s.card = d ∧ ∀ c, Disjoint s (allocation.1 c)} =
      Nat.choose (m - Finset.univ.sum demand) d := by
  classical
  let U : Finset (Fin m) := Finset.univ.biUnion allocation.1
  have hUcard : U.card = Finset.univ.sum demand := by
    simpa [U] using card_iUnion_stubAllocation allocation
  rw [Fintype.card_subtype]
  have hset :
      Finset.filter
          (fun s : Finset (Fin m) =>
            s.card = d ∧ ∀ c, Disjoint s (allocation.1 c)) Finset.univ =
        Finset.powersetCard d Uᶜ := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard]
    rw [Finset.subset_compl_iff_disjoint_right]
    simp only [U, Finset.disjoint_biUnion_right, Finset.mem_univ, true_implies]
    constructor
    · rintro ⟨hcard, hdisj⟩
      exact ⟨hdisj, hcard⟩
    · rintro ⟨hdisj, hcard⟩
      exact ⟨hcard, hdisj⟩
  rw [hset, Finset.card_powersetCard, Finset.card_compl, hUcard, Fintype.card_fin]

/-- The number of embeddings of the disjoint union of the demanded blocks into
`Fin m` is the corresponding descending factorial. -/
theorem card_stubEmbedding_eq_descFactorial
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :
    Fintype.card ((Σ c, Fin (demand c)) ↪ Fin m) =
      m.descFactorial (Finset.univ.sum demand) := by
  simp +decide [Fintype.card_sigma, Fintype.card_fin]

/-- An embedding of the disjoint union of demanded blocks is the same finite
data as a disjoint allocation together with an ordering of each allocated
cell.  This is the structural bijection behind the allocation count. -/
theorem card_stubEmbedding_eq_labeledAllocation
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :
    Fintype.card ((Σ c, Fin (demand c)) ↪ Fin m) =
      Fintype.card
        (Σ allocation : StubAllocation m demand,
          ∀ c, Fin (demand c) ≃ ↑(allocation.1 c)) := by
  refine Fintype.card_congr (Equiv.symm ?_)
  refine Equiv.ofBijective
    (fun x ↦ ⟨fun p ↦ (x.2 p.1 p.2 : Fin m), ?_⟩) ⟨?_, ?_⟩
  all_goals norm_num [funext_iff, Function.Injective, Sigma.ext_iff] at *
  · intro a₁ a₂ h
    have hdisjoint := x.1.2.2 a₁.1 a₂.1
    simp_all +decide [Finset.disjoint_left]
    by_cases hc : a₁.fst = a₂.fst <;> simp_all +decide
    · have hinjective := (x.2 a₁.1).injective
      aesop
    · exact hdisjoint (x.2 a₁.fst a₁.snd).2
        (h.symm ▸ (x.2 a₂.fst a₂.snd).2)
  · intro x y h
    have hpoint : ∀ c : C, ∀ i : Fin (demand c),
        (x.2 c i : Fin m) = (y.2 c i : Fin m) := by
      exact fun c i ↦ h ⟨c, i⟩
    have hcells : ∀ c : C, x.1.1 c = y.1.1 c := by
      intro c
      ext i
      simp
      constructor <;> intro hi
      · obtain ⟨j, hj⟩ := (x.2 c).surjective ⟨i, hi⟩
        grind
      · obtain ⟨j, hj⟩ := (y.2 c).surjective ⟨i, hi⟩
        grind
    have hallocation : x.1 = y.1 :=
      Subtype.ext (funext hcells)
    aesop
  · intro x
    let cells : C → Finset (Fin m) := fun c ↦
      Finset.image (fun i ↦ x ⟨c, i⟩) Finset.univ
    have hcard : ∀ c, (cells c).card = demand c := by
      intro c
      rw [show cells c = Finset.image (fun i ↦ x ⟨c, i⟩) Finset.univ by rfl]
      rw [Finset.card_image_of_injective]
      · simp
      · intro i j hij
        exact eq_of_heq (Sigma.mk.inj_iff.mp (x.injective hij)).2
    have hdisjoint : ∀ c₁ c₂, c₁ ≠ c₂ → Disjoint (cells c₁) (cells c₂) := by
      intro c₁ c₂ hne
      rw [Finset.disjoint_left]
      intro z hz₁ hz₂
      simp only [cells, Finset.mem_image, Finset.mem_univ, true_and] at hz₁ hz₂
      obtain ⟨i₁, hi₁⟩ := hz₁
      obtain ⟨i₂, hi₂⟩ := hz₂
      exact hne (Sigma.mk.inj_iff.mp (x.injective (hi₁.trans hi₂.symm))).1
    let allocation : StubAllocation m demand := ⟨cells, hcard, hdisjoint⟩
    let order : ∀ c, Fin (demand c) ≃ ↑(allocation.1 c) := fun c ↦
      Equiv.ofBijective
      (fun i ↦ ⟨x ⟨c, i⟩,
        Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
      ⟨fun i j hij ↦ by
          simpa [Fin.ext_iff] using x.injective (Subtype.ext_iff.mp hij),
        fun i ↦ by
          rcases Finset.mem_image.mp i.2 with ⟨j, _, hj⟩
          exact ⟨j, Subtype.ext hj⟩⟩
    refine ⟨⟨allocation, order⟩, ?_⟩
    ext p
    rfl

/-- For each allocation, the internal cell orderings contribute exactly the
product of the cell factorials. -/
theorem card_labeledStubAllocation
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :
    Fintype.card
        (Σ allocation : StubAllocation m demand,
          ∀ c, Fin (demand c) ≃ ↑(allocation.1 c)) =
      Fintype.card (StubAllocation m demand) *
        Finset.univ.prod (fun c ↦ (demand c).factorial) := by
  have hcard : ∀ allocation : StubAllocation m demand,
      Fintype.card (∀ c, Fin (demand c) ≃ ↑(allocation.1 c)) =
        ∏ c, (demand c).factorial := by
    intro allocation
    convert Fintype.card_pi
    rw [Fintype.card_equiv]
    aesop
    exact Fintype.equivOfCardEq (by simp +decide [allocation.2.1])
  rw [Fintype.card_sigma,
    Finset.sum_congr rfl (fun allocation _ ↦ by simpa using hcard allocation)]
  simp +decide

/-- Exact count of pairwise-disjoint labelled stub selections.  Multiplying
by the internal ordering count in every cell gives the descending factorial.
No feasibility premise is required: both sides vanish when the total demand
exceeds `m`. -/
theorem card_stubAllocation_mul_factorials
    {C : Type*} [Fintype C] [DecidableEq C]
    (m : ℕ) (demand : C → ℕ) :
    Fintype.card (StubAllocation m demand) *
        Finset.univ.prod (fun c ↦ (demand c).factorial) =
      m.descFactorial (Finset.univ.sum demand) := by
  rw [← card_labeledStubAllocation,
    ← card_stubEmbedding_eq_labeledAllocation,
    card_stubEmbedding_eq_descFactorial]

end Erdos625
