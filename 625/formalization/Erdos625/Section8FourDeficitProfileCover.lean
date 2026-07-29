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

/-- Equality of deficit values determines the finite size coordinate. -/
theorem profileDeficit_eq_fourDeficit_imp_coordinate_eq
    (alpha : Nat) (hAlpha : 5 < alpha)
    (coord : Fin (alpha + 1)) (i : Fin 4)
    (hdeficit : profileDeficit alpha coord = (fourDeficit i : Real)) :
    coord = fourDeficitCoordinate alpha hAlpha i := by
  let target := fourDeficitCoordinate alpha hAlpha i
  have htarget : profileDeficit alpha target = (fourDeficit i : Real) :=
    profileDeficit_fourDeficitCoordinate alpha hAlpha i
  have hsumCoord := profileClassSize_add_profileDeficit alpha coord
  have hsumTarget := profileClassSize_add_profileDeficit alpha target
  have hclass : profileClassSize coord = profileClassSize target := by
    rw [hdeficit] at hsumCoord
    rw [htarget] at hsumTarget
    linarith
  apply Fin.ext
  unfold profileClassSize at hclass
  norm_num at hclass
  omega

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
  obtain ⟨i, hdeficit⟩ := hsupport coord hkpos
  have hcoord : coord = fourDeficitCoordinate alpha hAlpha i :=
    profileDeficit_eq_fourDeficit_imp_coordinate_eq
      alpha hAlpha coord i hdeficit
  subst coord
  refine ⟨i, ?_⟩
  simp only [fourEndpointBlockSlots, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change (a.1 : Nat) = fourEndpointSize alpha hAlpha i
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

#print axioms profileDeficit_eq_fourDeficit_imp_coordinate_eq
#print axioms isFourEndpointProfileCover_of_isFourDeficitSupported
#print axioms fourDeficitEmbedding_isFourEndpointProfileCover

end

end Erdos625
