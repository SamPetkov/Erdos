import Erdos625.Section8AttainedDemandBlockSupport
import Erdos625.MidpointProfileCoordinates
import Mathlib.Tactic

/-!
# Section VIII: the four-deficit profile gives an endpoint block cover

The attained-demand support/deficit construction is phrased for a profile whose
actual blocks are covered by the four endpoint size classes.  The midpoint
profile is already known to be supported on the four distinguished deficit
coordinates.  This module supplies the finite adapter between those two
statements.
-/

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- A profile supported on the four distinguished deficit coordinates has every
actual block in one of the four endpoint-size slot families. -/
theorem isFourEndpointProfileCover_of_isFourDeficitSupported
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hsupport : IsFourDeficitSupported alpha k) :
    IsFourEndpointProfileCover alpha hAlpha k := by
  intro a
  have haMem : (a.1 : Nat) ∈ ColoringProfile.sizes k :=
    Multiset.mem_toFinset.mp a.1.2
  simp only [ColoringProfile.sizes, Multiset.mem_sum] at haMem
  obtain ⟨coord, _hcoord, hrep⟩ := haMem
  simp only [Multiset.mem_replicate] at hrep
  obtain ⟨hkpos, hsize⟩ := hrep
  rcases hsupport coord (by omega) with h0 | hrest
  · subst coord
    refine ⟨0, ?_⟩
    simp only [fourEndpointBlockSlots, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (a.1 : Nat) = fourEndpointSize alpha hAlpha 0
    simpa [fourEndpointSize, fourEndpointCoordinate] using hsize
  · rcases hrest with h1 | hrest
    · subst coord
      refine ⟨1, ?_⟩
      simp only [fourEndpointBlockSlots, Finset.mem_filter,
        Finset.mem_univ, true_and]
      change (a.1 : Nat) = fourEndpointSize alpha hAlpha 1
      simpa [fourEndpointSize, fourEndpointCoordinate] using hsize
    · rcases hrest with h2 | h3
      · subst coord
        refine ⟨2, ?_⟩
        simp only [fourEndpointBlockSlots, Finset.mem_filter,
          Finset.mem_univ, true_and]
        change (a.1 : Nat) = fourEndpointSize alpha hAlpha 2
        simpa [fourEndpointSize, fourEndpointCoordinate] using hsize
      · subst coord
        refine ⟨3, ?_⟩
        simp only [fourEndpointBlockSlots, Finset.mem_filter,
          Finset.mem_univ, true_and]
        change (a.1 : Nat) = fourEndpointSize alpha hAlpha 3
        simpa [fourEndpointSize, fourEndpointCoordinate] using hsize

/-- The concrete four-deficit embedding used by the midpoint construction
satisfies the endpoint-cover hypothesis needed by the Section VIII block
support and deficit reconstruction. -/
theorem fourDeficitEmbedding_isFourEndpointProfileCover
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    IsFourEndpointProfileCover alpha hAlpha
      (fourDeficitEmbedding alpha hAlpha m) := by
  apply isFourEndpointProfileCover_of_isFourDeficitSupported
  exact (fourDeficitEmbedding_profile_invariants alpha hAlpha m).2.2

#print axioms isFourEndpointProfileCover_of_isFourDeficitSupported
#print axioms fourDeficitEmbedding_isFourEndpointProfileCover

end

end Erdos625
