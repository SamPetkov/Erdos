import Mathlib.Data.Fintype.BigOperators
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

end Erdos625
