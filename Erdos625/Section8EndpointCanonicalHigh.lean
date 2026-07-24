import Erdos625.Section8EndpointFoundation
import Mathlib.Tactic

/-!
# Section VIII: endpoint canonical-high bridge

For an endpoint-only physical skeleton, every literal full endpoint cell is
strictly above the endpoint high threshold.  The separate block-matching
conclusion is intentionally not included here.
-/

namespace Erdos625

set_option autoImplicit false

theorem fourEndpoint_endpointOnly_isCanonicalHigh
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (k : ColoringProfile (alpha + 1))
    (S : UnlabelledTypedSkeleton (profileBlockMargin k) (profileBlockMargin k))
    (hOnly : IsFourEndpointOnlyPhysicalSkeleton alpha hAlpha k S) :
    IsCanonicalHighFourEndpointSkeleton alpha hAlpha k S := by
  refine ⟨hOnly, ?_⟩
  intro ab hab
  simp only [fourEndpointFullPairs, Finset.mem_filter] at hab
  rcases hab with ⟨_, i, j, _, _, hij⟩
  rw [hij]
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointHighCutoff, fourEndpointOverlapSize, fourEndpointSize,
      fourEndpointCoordinate, fourDeficitCoordinate, fourDeficit] <;> omega

end Erdos625
