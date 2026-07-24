import Erdos625.TangentNatConservationDisplacement
import Erdos625.TangentCorrectedCountNonnegativity
import Erdos625.MidpointProfileCoordinates
import Erdos625.ProfileOptimizerUniformS4
import Erdos625.MidpointProfileRounding
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Exact natural count and deficit conservation, together with the uniform
displacement estimate at the corrected-integer level.  The final conjunct is
intentionally stated before any `Int.toNat` cast, so the later nonnegativity
and cast transport remain explicit proof obligations. -/
theorem midpointMultiplicity_count_deficit_intDisplacement
    (n alpha K : Nat)
    (h : MidpointRoundingAdmissible n alpha K) :
    (∑ i : Fin 4, midpointMultiplicity n alpha K i) = K ∧
    (∑ i : Fin 4,
        tangentDeficitNat i * midpointMultiplicity n alpha K i) =
          midpointDeficit n alpha K ∧
    (∀ i : Fin 4,
      |((tangentCorrectedInt K (midpointDeficit n alpha K)
            (midpointOptimizer n alpha K) i : Int) : Real) -
          (K : Real) * midpointOptimizer n alpha K i| ≤
        (5 : Real)) := by
  rcases h with ⟨_hAlpha, hK, hn, hTarget, hLower⟩
  have hCount :
      ∑ i : Fin 4, (K : Real) * midpointOptimizer n alpha K i =
        (K : Real) := by
    rw [← Finset.mul_sum, midpointOptimizer,
      ProfileEntropyS4.sum_optimizer, mul_one]
  have hMoment :
      ∑ i : Fin 4, (tangentDeficit i : Real) *
          ((K : Real) * midpointOptimizer n alpha K i) =
        ((midpointDeficit n alpha K : Nat) : Real) := by
    calc
      _ = (K : Real) * ∑ i : Fin 4,
          midpointOptimizer n alpha K i * ProfileEntropyS4.support i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        have hDeficit : (tangentDeficit i : Real) =
            ProfileEntropyS4.support i := by
          simp [tangentDeficit, ProfileEntropyS4.support]
        rw [hDeficit]
        ring
      _ = (K : Real) * fourSizeTarget n alpha (K : Real) := by
        rw [midpointOptimizer,
          ProfileEntropyS4.sum_optimizer_mul_support
            (fourDeficitScore alpha) hTarget]
      _ = ((midpointDeficit n alpha K : Nat) : Real) := by
        rw [midpointDeficit,
          deficit_cast_eq_parts_mul_fourSizeTarget n alpha K hK hn]
  exact tangent_rounding_nat_conservation_and_uniform_displacement
    K (midpointDeficit n alpha K) (midpointOptimizer n alpha K)
      hCount hMoment hLower

end

end Erdos625
