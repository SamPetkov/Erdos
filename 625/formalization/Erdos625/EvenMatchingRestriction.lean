import Erdos625.EvenMatchingKernel

/-!
# Restricting even bipartite matrices away from a matching

This module isolates the deterministic injection used in the small-residual
branch of Section IX.  If two even `ZMod 2` matrices are supported on the union
of a row matching `M` and an arbitrary residual relation `R`, then their values
on `R` determine the whole matrix.  Consequently the finite family of such
matrices has cardinality at most `2 ^ |R|`.

No probability, asymptotic estimate, cycle decomposition, or attachment bound
is asserted here.
-/

namespace Erdos625

noncomputable section

/-- Two even matrices supported on `M ∪ R` are equal once they agree on `R`,
provided `M` is a row matching. -/
theorem evenMatrix_eq_of_eq_on_residual
    {A B : Type*} [Fintype A] [Fintype B]
    (x y : A → B → ZMod 2) (M R : A → B → Prop)
    (hxEven : BipartiteEvenMatrix x)
    (hyEven : BipartiteEvenMatrix y)
    (hmatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂)
    (hxSupport : ∀ a b, x a b ≠ 0 → M a b ∨ R a b)
    (hySupport : ∀ a b, y a b ≠ 0 → M a b ∨ R a b)
    (hresidual : ∀ a b, R a b → x a b = y a b) :
    x = y := by
  let z : A → B → ZMod 2 := fun a b ↦ x a b - y a b
  have hzEven : BipartiteEvenMatrix z := by
    constructor
    · intro a
      simp only [z, Finset.sum_sub_distrib, hxEven.1 a, hyEven.1 a, sub_self]
    · intro b
      simp only [z, Finset.sum_sub_distrib, hxEven.2 b, hyEven.2 b, sub_self]
  have hzSupport : ∀ a b, z a b ≠ 0 → M a b := by
    intro a b hz
    have hxy : x a b ≠ y a b := sub_ne_zero.mp hz
    by_contra hM
    have hR : R a b := by
      by_cases hx0 : x a b = 0
      · have hy0 : y a b ≠ 0 := by
          intro hy0
          exact hxy (hx0.trans hy0.symm)
        exact (hySupport a b hy0).resolve_left hM
      · exact (hxSupport a b hx0).resolve_left hM
    exact hxy (hresidual a b hR)
  have hzZero : z = 0 :=
    evenMatrix_eq_zero_of_support_rowMatching z M hzEven hmatching hzSupport
  funext a b
  have hab : z a b = 0 := by rw [hzZero]; rfl
  exact sub_eq_zero.mp hab

/-- Even matrices supported on `M ∪ R`. -/
def EvenMatrixSupportedOn
    {A B : Type*} [Fintype A] [Fintype B]
    (M R : A → B → Prop) :=
  {x : A → B → ZMod 2 //
    BipartiteEvenMatrix x ∧ ∀ a b, x a b ≠ 0 → M a b ∨ R a b}

/-- A residual cell, represented by a row-column pair satisfying `R`. -/
def ResidualCell
    {A B : Type*} (R : A → B → Prop) :=
  {e : A × B // R e.1 e.2}

/-- Restrict a supported even matrix to the residual cells. -/
def residualRestriction
    {A B : Type*} [Fintype A] [Fintype B]
    (M R : A → B → Prop) :
    EvenMatrixSupportedOn M R → ResidualCell R → ZMod 2 :=
  fun x e ↦ x.1 e.1.1 e.1.2

/-- Restriction to residual cells is injective when the complementary support
relation is a row matching. -/
theorem residualRestriction_injective
    {A B : Type*} [Fintype A] [Fintype B]
    (M R : A → B → Prop)
    (hmatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂) :
    Function.Injective (residualRestriction M R) := by
  intro x y hxy
  apply Subtype.ext
  apply evenMatrix_eq_of_eq_on_residual x.1 y.1 M R
    x.2.1 y.2.1 hmatching x.2.2 y.2.2
  intro a b hR
  exact congrFun hxy ⟨(a, b), hR⟩

/-- There are at most `2 ^ |R|` even matrices supported on a row matching
together with the residual relation `R`. -/
theorem card_evenMatrixSupportedOn_le_pow_card_residualCell
    {A B : Type*} [Fintype A] [Fintype B]
    (M R : A → B → Prop)
    (hmatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂) :
    Nat.card (EvenMatrixSupportedOn M R) ≤
      2 ^ Nat.card (ResidualCell R) := by
  letI : Finite (EvenMatrixSupportedOn M R) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (ResidualCell R) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (EvenMatrixSupportedOn M R) := Fintype.ofFinite _
  letI : Fintype (ResidualCell R) := Fintype.ofFinite _
  letI : DecidableEq (ResidualCell R) := Classical.decEq _
  calc
    Nat.card (EvenMatrixSupportedOn M R) =
        Fintype.card (EvenMatrixSupportedOn M R) := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (ResidualCell R → ZMod 2) :=
      Fintype.card_le_of_injective (residualRestriction M R)
        (residualRestriction_injective M R hmatching)
    _ = 2 ^ Nat.card (ResidualCell R) := by
      rw [Fintype.card_fun, Nat.card_eq_fintype_card]
      norm_num

end

end Erdos625
