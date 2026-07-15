import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Distinguishable near-skeleton expansion for Section VIII

This module proves the exact finite product expansion over optional deficit
choices attached to distinguishable cells.  It does not identify these choices
with unlabelled typed near-skeletons, prove that forgetting identical typed
cells introduces no multiplicity, or establish the ratio estimates required
for manuscript (8.25a).  Those application bridges remain separate proof
obligations.
-/

namespace Erdos625

open scoped BigOperators ENNReal

/-- For each distinguishable cell, choose no deficit or one allowed deficit. -/
def NearSkeletonChoice
    (Cell Deficit : Type*) [Fintype Cell] [Fintype Deficit]
    [DecidableEq Deficit] (allowed : Cell → Finset Deficit) :=
  (c : Cell) → Option {e : Deficit // e ∈ allowed c}

noncomputable instance instFintypeNearSkeletonChoice
    (Cell Deficit : Type*) [Fintype Cell] [Fintype Deficit]
    [DecidableEq Deficit] (allowed : Cell → Finset Deficit) :
    Fintype (NearSkeletonChoice Cell Deficit allowed) := by
  classical
  unfold NearSkeletonChoice
  infer_instance

/-- Product weight of one distinguishable near-skeleton choice. -/
noncomputable def nearSkeletonChoiceWeight
    {Cell Deficit : Type*} [Fintype Cell] [Fintype Deficit]
    [DecidableEq Deficit] (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ℝ≥0∞)
    (choice : NearSkeletonChoice Cell Deficit allowed) : ℝ≥0∞ :=
  ∏ c, match choice c with
    | none => 1
    | some e => weight c e.1

private lemma direct_finset_prod_sum
    {ι R : Type*} [CommSemiring R] [DecidableEq ι]
    {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i))
    (f : ∀ i, κ i → R) :
    ∏ a ∈ s, ∑ b ∈ t a, f a b =
      ∑ p ∈ s.pi t, ∏ x ∈ s.attach, f x.1 (p x.1 x.2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h₁ : ∀ x ∈ t a, ∀ y ∈ t a, x ≠ y →
        Disjoint (Finset.image (Finset.Pi.cons s a x) (s.pi t))
          (Finset.image (Finset.Pi.cons s a y) (s.pi t)) := by
      intro x _ y _ h
      simp only [Finset.disjoint_iff_ne, Finset.mem_image]
      rintro _ ⟨p₂, _, eq₂⟩ _ ⟨p₃, _, eq₃⟩ eq
      have hx : Finset.Pi.cons s a x p₂ a (Finset.mem_insert_self _ _) =
          Finset.Pi.cons s a y p₃ a (Finset.mem_insert_self _ _) := by
        rw [eq₂, eq₃, eq]
      rw [Finset.Pi.cons_same, Finset.Pi.cons_same] at hx
      exact h hx
    rw [Finset.prod_insert ha, Finset.pi_insert ha, ih, Finset.sum_mul,
      Finset.sum_biUnion h₁]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h₂ : ∀ p₁ ∈ s.pi t, ∀ p₂ ∈ s.pi t,
        Finset.Pi.cons s a b p₁ = Finset.Pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ _ p₂ _ eq => Finset.Pi.cons_injective ha eq
    rw [Finset.sum_image h₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
    · simp only [Finset.Pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact (Finset.Pi.cons_ne (by rintro rfl; exact ha hv)).symm
    · exact fun _ _ _ _ => Subtype.ext ∘ Subtype.mk.inj
    · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq,
        true_and, Subtype.exists, exists_prop, exists_eq_right] using ha

/-- Exact finite expansion over all distinguishable near-skeleton choices. -/
theorem sum_nearSkeletonChoiceWeight_eq_product
    {Cell Deficit : Type*} [Fintype Cell] [Fintype Deficit]
    [DecidableEq Deficit] (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ℝ≥0∞) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) =
      ∏ c, (1 + ∑ e ∈ allowed c, weight c e) := by
  classical
  let f : (c : Cell) → Option {e : Deficit // e ∈ allowed c} → ℝ≥0∞ :=
    fun c x => match x with
      | none => 1
      | some e => weight c e.1
  have expand := direct_finset_prod_sum (Finset.univ : Finset Cell)
    (fun c => (Finset.univ : Finset (Option {e : Deficit // e ∈ allowed c}))) f
  simp only [Finset.prod_attach_univ, Finset.sum_univ_pi] at expand
  rw [show (∏ c, (1 + ∑ e ∈ allowed c, weight c e)) =
      ∏ c, ∑ x, f c x by
        apply Fintype.prod_congr
        intro c
        simp [f, Finset.sum_attach]]
  exact expand.symm

#print axioms sum_nearSkeletonChoiceWeight_eq_product

end Erdos625
