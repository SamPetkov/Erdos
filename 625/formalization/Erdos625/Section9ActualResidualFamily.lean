import Erdos625.BipartiteEdgeMatrix
import Erdos625.Section9EncodingAssembly

/-!
# The actual residual even-edge family in Section IX

The residual relation here is not an abstract placeholder: it is literally the
set of cells whose supplied multiplicity is at least two.  Finite even edge
sets supported on that relation together with a row matching are encoded by
their zero-one matrices.  The previously verified matching-restriction theorem
then gives the exact `2 ^ |H_res|` bound.

This finite bridge does not prove the cycle decomposition, traversal estimates,
or the uniform attachment bound of Lemma 9.1.
-/

namespace Erdos625

/-- Actual even edge sets supported on a high-skeleton relation `M` together
with the multiplicity-at-least-two residual cells. -/
def ActualResidualEvenEdgeFamily
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : A → B → Prop) :=
  {F : Finset (A × B) //
    BipartiteEvenEdgeSet F ∧
      ∀ e ∈ F, M e.1 e.2 ∨ 2 ≤ cellCount e.1 e.2}

/-- The actual residual family is bounded by the number of zero-one choices on
the actual multiplicity-at-least-two support. -/
theorem card_actualResidualEvenEdgeFamily_le_pow_support
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (cellCount : A → B → ℕ) (M : A → B → Prop)
    (hRowMatching : ∀ a b₁ b₂, M a b₁ → M a b₂ → b₁ = b₂) :
    Nat.card (ActualResidualEvenEdgeFamily cellCount M) ≤
      2 ^ Nat.card (ResidualCell (fun a b => 2 ≤ cellCount a b)) := by
  letI : Finite (ActualResidualEvenEdgeFamily cellCount M) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  refine card_family_le_pow_residualCells_of_even_encoding
    (X := ActualResidualEvenEdgeFamily cellCount M)
    (fun F => bipartiteEdgeMatrix F.1) M
    (fun a b => 2 ≤ cellCount a b) ?_ ?_ ?_ hRowMatching
  · intro F G hFG
    apply Subtype.ext
    exact bipartiteEdgeMatrix_injective hFG
  · intro F
    exact (bipartiteEdgeMatrix_even_iff F.1).2 F.2.1
  · intro F a b hab
    have hmem :=
      (bipartiteEdgeMatrix_apply_ne_zero_iff F.1 a b).mp hab
    exact F.2.2 (a, b) hmem

#print axioms card_actualResidualEvenEdgeFamily_le_pow_support

end Erdos625
