import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

/-!
# Even matrices supported on a matching

An even bipartite edge set supported on a row matching is empty.  This is the
kernel statement needed before restriction to residual edges can be shown
injective in the small-residual branch of Section IX.
-/

def BipartiteEvenMatrix {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ZMod 2) : Prop :=
  (∀ a, ∑ b, x a b = 0) ∧ (∀ b, ∑ a, x a b = 0)

theorem evenMatrix_eq_zero_of_support_rowMatching
    {A B : Type*} [Fintype A] [Fintype B]
    (x : A → B → ZMod 2) (M : A → B → Prop)
    (heven : BipartiteEvenMatrix x)
    (hmatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hsupport : ∀ a b, x a b ≠ 0 → M a b) :
    x = 0 := by
  funext a b
  simp only [Pi.zero_apply]
  by_contra hb
  have hrow : ∑ b', x a b' = x a b := by
    refine Finset.sum_eq_single b ?_ ?_
    · intro b' _ hne
      by_contra hb'
      exact hne (hmatching a b' b (hsupport a b' hb') (hsupport a b hb))
    · intro hmem
      exact absurd (Finset.mem_univ b) hmem
  have hzero := heven.1 a
  rw [hrow] at hzero
  exact hb hzero

end Erdos625
