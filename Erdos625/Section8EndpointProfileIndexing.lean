import Erdos625.Section8EndpointFoundation
import Mathlib.Tactic

/-!
# Target A: four-endpoint profile indexing

This is the exact finite bridge from `fourDeficitCoordinate` to the endpoint
labels used by the Section VIII table. It contains no canonical-demand or
probability assertion.
-/

namespace Erdos625

set_option autoImplicit false

def FourEndpointProfileIndexingFacts (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) : Prop :=
  (forall i, fourEndpointSize alpha hAlpha i = alpha - 2 - i.val) /\
    (forall i,
      (fourEndpointBlockSlots alpha hAlpha k i).card =
        fourEndpointMultiplicity alpha hAlpha k i) /\
      (forall i j, i != j ->
        Disjoint (fourEndpointBlockSlots alpha hAlpha k i)
          (fourEndpointBlockSlots alpha hAlpha k j))

theorem fourEndpoint_profile_indexing_facts
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) :
    FourEndpointProfileIndexingFacts alpha hAlpha k := by
  have hsize : ∀ i, fourEndpointSize alpha hAlpha i = alpha - 2 - i.val := by
    intro i
    unfold fourEndpointSize fourEndpointCoordinate fourDeficitCoordinate
    simp [fourDeficit]
    omega
  refine ⟨hsize, ?_, ?_⟩
  · intro i
    rw [show (fourEndpointBlockSlots alpha hAlpha k i).card =
        Fintype.card {q : ProfileBlockIndex k //
          profileBlockMargin k q = fourEndpointSize alpha hAlpha i} by
      rw [Fintype.card_subtype]
      rfl]
    change Fintype.card {q : ShapeBlockIndex (ColoringProfile.sizes k) //
      (q.1 : Nat) = fourEndpointSize alpha hAlpha i} = _
    rw [card_shapeBlockIndexOfSize]
    rw [show fourEndpointSize alpha hAlpha i =
        (fourEndpointCoordinate alpha hAlpha i).val + 1 by rfl]
    rw [ColoringProfile.count_sizes_at]
    rfl
  · intro i j hij
    rw [Finset.disjoint_left]
    intro q hqi hqj
    simp only [fourEndpointBlockSlots, Finset.mem_filter, Finset.mem_univ,
      true_and] at hqi hqj
    have hs : fourEndpointSize alpha hAlpha i = fourEndpointSize alpha hAlpha j :=
      hqi.symm.trans hqj
    have heq : i = j := by
      apply Fin.ext
      rw [hsize i, hsize j] at hs
      omega
    subst j
    simp at hij

end Erdos625
