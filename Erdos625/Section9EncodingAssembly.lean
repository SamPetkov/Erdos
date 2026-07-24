import Erdos625.ConfigurationResidualSupport
import Erdos625.EvenMatchingRestriction

/-!
# Section IX encoding and restriction assembly

This module gives the deterministic seam needed by the small-residual branch
of Section IX.  Any finite family that admits an injective encoding by even
`ZMod 2` matrices supported on a row matching plus an explicit residual
relation inherits the verified `2 ^ |R|` bound.  For the actual configuration
residual-support relation, the accepted mass estimate then bounds the exponent
by half the total row-stub mass.

The existence, injectivity, evenness, and support properties of the concrete
manuscript encoding remain explicit hypotheses.  No cycle-space identity or
large-residual estimate is asserted here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- An explicit injective even-matrix encoding supported on `M ∪ R` turns the
accepted restriction injection into a cardinality bound for the source
family. -/
theorem card_family_le_pow_residualCells_of_even_encoding
    {X A B : Type*} [Finite X] [Fintype A] [Fintype B]
    (encode : X → A → B → ZMod 2) (M R : A → B → Prop)
    (hencode : Function.Injective encode)
    (heven : ∀ x, BipartiteEvenMatrix (encode x))
    (hsupport : ∀ x a b, encode x a b ≠ 0 → M a b ∨ R a b)
    (hmatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂) :
    Nat.card X ≤ 2 ^ Nat.card (ResidualCell R) := by
  let toSupported : X → EvenMatrixSupportedOn M R :=
    fun x ↦ ⟨encode x, heven x, hsupport x⟩
  have hSupported : Function.Injective toSupported := by
    intro x y hxy
    apply hencode
    exact congrArg Subtype.val hxy
  letI : Finite (EvenMatrixSupportedOn M R) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (EvenMatrixSupportedOn M R) := Fintype.ofFinite _
  calc
    Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
    _ ≤ Fintype.card (EvenMatrixSupportedOn M R) :=
      Fintype.card_le_of_injective toSupported hSupported
    _ = Nat.card (EvenMatrixSupportedOn M R) :=
      Nat.card_eq_fintype_card.symm
    _ ≤ 2 ^ Nat.card (ResidualCell R) :=
      card_evenMatrixSupportedOn_le_pow_card_residualCell M R hmatching

/-- Residual cells for an actual configuration matching are equivalent to the
subtype of its finite residual-support finset. -/
def configurationResidualCellEquivSupportSubtype
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) :
    ResidualCell (configurationResidualSupportRelation matching) ≃
      ↥(configurationResidualSupportFinset matching) where
  toFun e := ⟨e.1,
    (mem_configurationResidualSupportFinset matching e.1).mpr e.2⟩
  invFun p := ⟨p.1,
    (mem_configurationResidualSupportFinset matching p.1).mp p.2⟩
  left_inv e := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- Exact identification of the abstract residual-cell exponent with the
cardinality of the concrete residual-support finset. -/
theorem natCard_configurationResidualCell_eq_supportFinset_card
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col) :
    Nat.card (ResidualCell (configurationResidualSupportRelation matching)) =
      (configurationResidualSupportFinset matching).card := by
  calc
    Nat.card
        (ResidualCell (configurationResidualSupportRelation matching)) =
        Nat.card ↥(configurationResidualSupportFinset matching) :=
      Nat.card_congr (configurationResidualCellEquivSupportSubtype matching)
    _ = Fintype.card ↥(configurationResidualSupportFinset matching) :=
      Nat.card_eq_fintype_card
    _ = (configurationResidualSupportFinset matching).card :=
      Fintype.card_coe _

/-- Actual small-residual seam.  Once a finite family has the explicit
injective even encoding and support decomposition stated in the hypotheses,
its cardinality is at most `2` to half the total row-stub mass. -/
theorem card_family_le_two_pow_half_stubMass
    {X A B : Type*} [Finite X]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ}
    (matching : ConfigurationMatching row col)
    (encode : X → A → B → ZMod 2) (M : A → B → Prop)
    (hencode : Function.Injective encode)
    (heven : ∀ x, BipartiteEvenMatrix (encode x))
    (hsupport : ∀ x a b, encode x a b ≠ 0 →
      M a b ∨ configurationResidualSupportRelation matching a b)
    (hmatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂) :
    Nat.card X ≤ 2 ^ ((∑ a, row a) / 2) := by
  have hRestriction : Nat.card X ≤
      2 ^ Nat.card
        (ResidualCell (configurationResidualSupportRelation matching)) :=
    card_family_le_pow_residualCells_of_even_encoding
      encode M (configurationResidualSupportRelation matching)
      hencode heven hsupport hmatching
  have hResidualCard :
      Nat.card
          (ResidualCell (configurationResidualSupportRelation matching)) ≤
        (∑ a, row a) / 2 := by
    rw [natCard_configurationResidualCell_eq_supportFinset_card matching]
    exact card_configurationResidualSupportFinset_le_half_stubMass matching
  exact hRestriction.trans
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hResidualCard)

end

end Erdos625
