import Erdos625.ConfigurationModelPrescribedCells
import Erdos625.Section8CanonicalSkeleton

/-!
# Canonical labelled witness

For a fixed configuration matching, retain the complete cell precisely when
its multiplicity is above the canonical cutoff.  The resulting demand has one
and only one labelled prescribed-demand witness extended by that matching.
This is the missing labelled-witness identification before manuscript (8.3).
-/

namespace Erdos625

/-- Canonical high-cell demand extracted from one literal configuration
matching. -/
def canonicalDemandOfMatching
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (U : ℕ) : A → B → ℕ :=
  canonicalHighDemand (configurationCellCount matching) U

private theorem rowAllocation_subset_cellFiber_of_extends
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (witness : PrescribedDemandWitness demand row col)
    (hextends : ExtendsPrescribedDemandWitness matching witness)
    (a : A) (b : B) :
    (witness.1 a).1 b ⊆
      Finset.univ.filter
        (fun stub : Fin (row a) ↦ (matching ⟨a, stub⟩).1 = b) := by
  intro stub hstub
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hpair :=
    (extendsPrescribedDemandWitness_iff_cellwise matching witness).1
      hextends a b ⟨stub, hstub⟩
  exact congrArg Sigma.fst hpair

private theorem cellPairings_eq_of_extends
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (rowAllocation : ∀ a, StubAllocation (row a) (demand a))
    (colAllocation : ∀ b, StubAllocation (col b) (fun a ↦ demand a b))
    (pairing₁ pairing₂ : ∀ a b,
      (↑((rowAllocation a).1 b)) ≃ (↑((colAllocation b).1 a)))
    (h₁ : ExtendsPrescribedDemandWitness matching
      ⟨rowAllocation, colAllocation, pairing₁⟩)
    (h₂ : ExtendsPrescribedDemandWitness matching
      ⟨rowAllocation, colAllocation, pairing₂⟩) :
    pairing₁ = pairing₂ := by
  funext a b
  apply Equiv.ext
  intro stub
  apply Subtype.ext
  have hpair₁ :=
    (extendsPrescribedDemandWitness_iff_cellwise matching
      ⟨rowAllocation, colAllocation, pairing₁⟩).1 h₁ a b stub
  have hpair₂ :=
    (extendsPrescribedDemandWitness_iff_cellwise matching
      ⟨rowAllocation, colAllocation, pairing₂⟩).1 h₂ a b stub
  exact eq_of_heq (Sigma.mk.inj_iff.mp (hpair₁.symm.trans hpair₂)).2

private theorem extendingWitness_unique_of_full_or_zero
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (hfull : ∀ a b, demand a b = configurationCellCount matching a b ∨
      demand a b = 0)
    (w₁ w₂ : PrescribedDemandWitness demand row col)
    (h₁ : ExtendsPrescribedDemandWitness matching w₁)
    (h₂ : ExtendsPrescribedDemandWitness matching w₂) :
    w₁ = w₂ := by
  obtain ⟨w₁_row, w₁_col, w₁_eq⟩ := w₁
  obtain ⟨w₂_row, w₂_col, w₂_eq⟩ := w₂
  have h_row : w₁_row = w₂_row := by
    funext a
    apply Subtype.ext
    funext b
    by_cases h_demand :
        demand a b = configurationCellCount matching a b
    · have hw₁_full :
          (w₁_row a).1 b =
            Finset.univ.filter
              (fun stub : Fin (row a) ↦ (matching ⟨a, stub⟩).1 = b) := by
        refine Finset.eq_of_subset_of_card_le
          (rowAllocation_subset_cellFiber_of_extends matching
            ⟨w₁_row, w₁_col, w₁_eq⟩ h₁ a b) ?_
        rw [(w₁_row a).2.1 b, h_demand]
        rfl
      have hw₂_full :
          (w₂_row a).1 b =
            Finset.univ.filter
              (fun stub : Fin (row a) ↦ (matching ⟨a, stub⟩).1 = b) := by
        refine Finset.eq_of_subset_of_card_le
          (rowAllocation_subset_cellFiber_of_extends matching
            ⟨w₂_row, w₂_col, w₂_eq⟩ h₂ a b) ?_
        rw [(w₂_row a).2.1 b, h_demand]
        rfl
      exact hw₁_full.trans hw₂_full.symm
    · have hzero : demand a b = 0 :=
        (hfull a b).resolve_left h_demand
      have hw₁_zero : (w₁_row a).1 b = ∅ := by
        apply Finset.card_eq_zero.mp
        exact ((w₁_row a).2.1 b).trans hzero
      have hw₂_zero : (w₂_row a).1 b = ∅ := by
        apply Finset.card_eq_zero.mp
        exact ((w₂_row a).2.1 b).trans hzero
      exact hw₁_zero.trans hw₂_zero.symm
  cases h_row
  have h_col : w₁_col = w₂_col := by
    funext b
    apply Subtype.ext
    funext a
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      let y : ↑((w₁_row a).1 b) :=
        (w₁_eq a b).symm ⟨x, hx⟩
      have hy : (w₁_eq a b y).1 = x :=
        congrArg Subtype.val ((w₁_eq a b).apply_symm_apply ⟨x, hx⟩)
      have hpair₁ :=
        (extendsPrescribedDemandWitness_iff_cellwise matching
          ⟨w₁_row, w₁_col, w₁_eq⟩).1 h₁ a b y
      have hpair₂ :=
        (extendsPrescribedDemandWitness_iff_cellwise matching
          ⟨w₁_row, w₂_col, w₂_eq⟩).1 h₂ a b y
      have hvalue : (w₁_eq a b y).1 = (w₂_eq a b y).1 :=
        eq_of_heq
          (Sigma.mk.inj_iff.mp (hpair₁.symm.trans hpair₂)).2
      have hxvalue : x = (w₂_eq a b y).1 := hy.symm.trans hvalue
      rw [hxvalue]
      exact (w₂_eq a b y).2
    · rw [(w₂_col b).2.1 a, (w₁_col b).2.1 a]
  cases h_col
  have h_eq : w₁_eq = w₂_eq :=
    cellPairings_eq_of_extends matching w₁_row w₁_col
      w₁_eq w₂_eq h₁ h₂
  cases h_eq
  rfl

private theorem canonicalDemandOfMatching_le_cellCount
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (U : ℕ) :
    ∀ a b,
      canonicalDemandOfMatching matching U a b ≤
        configurationCellCount matching a b := by
  intro a b
  by_cases hhigh : U / 2 < configurationCellCount matching a b
  · rw [canonicalDemandOfMatching, canonicalHighDemand, if_pos hhigh]
  · rw [canonicalDemandOfMatching, canonicalHighDemand, if_neg hhigh]
    exact Nat.zero_le _

private theorem canonicalDemandOfMatching_full_or_zero
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) (U : ℕ) :
    ∀ a b,
      canonicalDemandOfMatching matching U a b =
          configurationCellCount matching a b ∨
        canonicalDemandOfMatching matching U a b = 0 := by
  intro a b
  by_cases hhigh : U / 2 < configurationCellCount matching a b
  · left
    rw [canonicalDemandOfMatching, canonicalHighDemand, if_pos hhigh]
  · right
    rw [canonicalDemandOfMatching, canonicalHighDemand, if_neg hhigh]

/-- The canonical full-cell demand determines a unique labelled exposure of
the supplied matching.  No witness-existence or uniqueness premise is assumed. -/
theorem existsUnique_canonicalHighDemandWitness
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ)
    (matching : ConfigurationMatching row col) (U : ℕ) :
    ∃! witness : PrescribedDemandWitness
        (canonicalDemandOfMatching matching U) row col,
      ExtendsPrescribedDemandWitness matching witness := by
  obtain ⟨w₁, hw₁⟩ :=
    exists_extendingWitness_of_mem_prescribedCellEvent
      (matching := matching)
      (canonicalDemandOfMatching_le_cellCount matching U)
  refine ⟨w₁, hw₁, ?_⟩
  intro w₂ hw₂
  exact extendingWitness_unique_of_full_or_zero matching
    (canonicalDemandOfMatching_full_or_zero matching U)
    w₂ w₁ hw₂ hw₁

#print axioms existsUnique_canonicalHighDemandWitness

end Erdos625
