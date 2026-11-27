import Erdos625.Section6PairSignCompatibility
import Mathlib.Tactic

/-!
# Heckel's marking bound for two partitions with common classes

Two marked partitions are compatible when their marks agree on every overlap
cell with at least two vertices.  If some column classes are *common*, i.e.
each of them meets some row class in at least two vertices, then the mark of
such a column is determined by the row marks.  Hence the number of compatible
pairs of markings is at most `2 ^ (|A| + |B| - ℓ)`, where `ℓ` is the number
of common columns.

With `|A| = |B| = k` this is the bound `2 ^ (2k - ℓ)` of Heckel, *The
difference between the chromatic and the cochromatic number of a random
graph*, Proposition 6.  It is used in the Heckel–Panagiotou route to the
second moment (`erdos625suggestion/note`).
-/

namespace Erdos625

/-- Compatible pairs of markings are determined by the row marks and the
marks of the columns that are not common. -/
theorem natCard_compatiblePairSignAssignments_le_two_pow_of_common
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) (c : B → Prop) [DecidablePred c]
    (g : {b // c b} → A) (hg : ∀ b : {b // c b}, 2 ≤ r (g b) b.1) :
    Nat.card (CompatiblePairSignAssignments r) ≤
      2 ^ (Fintype.card A + Fintype.card {b // ¬ c b}) := by
  classical
  let f : CompatiblePairSignAssignments r →
      (A → Bool) × ({b // ¬ c b} → Bool) :=
    fun sigma ↦ (sigma.1.1, fun b ↦ sigma.1.2 b.1)
  have hf : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    have h1 : s.1.1 = t.1.1 := (Prod.ext_iff.mp hst).1
    have h2 : (fun b : {b // ¬ c b} ↦ s.1.2 b.1) = fun b ↦ t.1.2 b.1 :=
      (Prod.ext_iff.mp hst).2
    apply Prod.ext h1
    funext b
    by_cases hb : c b
    · have hs := s.2 (g ⟨b, hb⟩) b (hg ⟨b, hb⟩)
      have ht := t.2 (g ⟨b, hb⟩) b (hg ⟨b, hb⟩)
      rw [← hs, ← ht, h1]
    · exact congrFun h2 ⟨b, hb⟩
  calc
    Nat.card (CompatiblePairSignAssignments r)
        ≤ Nat.card ((A → Bool) × ({b // ¬ c b} → Bool)) :=
      Nat.card_le_card_of_injective f hf
    _ = 2 ^ (Fintype.card A + Fintype.card {b // ¬ c b}) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fun, Fintype.card_bool, pow_add]

/-- Heckel's bound: with `ℓ` common columns, at most `2 ^ (|A| + |B| - ℓ)`
pairs of markings are compatible. -/
theorem natCard_compatiblePairSignAssignments_le_two_pow_sub_common
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) (c : B → Prop) [DecidablePred c]
    (g : {b // c b} → A) (hg : ∀ b : {b // c b}, 2 ≤ r (g b) b.1) :
    Nat.card (CompatiblePairSignAssignments r) ≤
      2 ^ (Fintype.card A + Fintype.card B - Fintype.card {b // c b}) := by
  have h := natCard_compatiblePairSignAssignments_le_two_pow_of_common r c g hg
  have hc : Fintype.card {b // ¬ c b} =
      Fintype.card B - Fintype.card {b // c b} :=
    Fintype.card_subtype_compl c
  have hle : Fintype.card {b // c b} ≤ Fintype.card B :=
    Fintype.card_subtype_le c
  rw [hc] at h
  rwa [Nat.add_sub_assoc hle]

#print axioms natCard_compatiblePairSignAssignments_le_two_pow_of_common
#print axioms natCard_compatiblePairSignAssignments_le_two_pow_sub_common

end Erdos625
