import Erdos625.MidpointProfileRoundingCast
import Erdos625.MidpointProfileRoundingIntDisplacement

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The actual natural midpoint multiplicities remain uniformly within five
of their real optimizer coordinates. -/
theorem midpointMultiplicity_uniform_displacement
    (n alpha K : Nat)
    (h : MidpointRoundingAdmissible n alpha K) :
    ∀ i : Fin 4,
      |((midpointMultiplicity n alpha K i : Nat) : Real) -
          (K : Real) * midpointOptimizer n alpha K i| ≤ (5 : Real) := by
  intro i
  rw [midpointMultiplicity_cast_eq_correctedInt n alpha K h i]
  exact (midpointMultiplicity_count_deficit_intDisplacement n alpha K h).2.2 i

end

end Erdos625
