import Erdos625.MidpointProfileRounding

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Safe transport from the corrected integer count to its natural-number
representation.  The proof deliberately establishes nonnegativity before
using `Int.toNat_of_nonneg`, so no negative count can be silently truncated. -/
theorem midpointMultiplicity_cast_eq_correctedInt
    (n alpha K : Nat)
    (h : MidpointRoundingAdmissible n alpha K)
    (i : Fin 4) :
    ((midpointMultiplicity n alpha K i : Nat) : Real) =
      ((tangentCorrectedInt K (midpointDeficit n alpha K)
          (midpointOptimizer n alpha K) i : Int) : Real) := by
  rcases h with ⟨hAlpha, hK, hn, hTarget, hLower⟩
  have hCountMoment :
      (∑ j : Fin 4,
          (K : Real) * midpointOptimizer n alpha K j) =
            (K : Real) ∧
      (∑ j : Fin 4,
          (tangentDeficit j : Real) *
            ((K : Real) * midpointOptimizer n alpha K j)) =
            (midpointDeficit n alpha K : Real) := by
    constructor
    · calc
        (∑ j : Fin 4,
            (K : Real) * midpointOptimizer n alpha K j) =
            (K : Real) *
              (∑ j : Fin 4, midpointOptimizer n alpha K j) := by
                rw [Finset.mul_sum]
        _ = (K : Real) := by
          rw [midpointOptimizer, ProfileEntropyS4.sum_optimizer]
          ring
    · calc
        (∑ j : Fin 4,
            (tangentDeficit j : Real) *
              ((K : Real) * midpointOptimizer n alpha K j)) =
            (K : Real) *
              (∑ j : Fin 4,
                midpointOptimizer n alpha K j *
                  ProfileEntropyS4.support j) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [← fourDeficit_cast_eq_support]
                    simp only [tangentDeficit, fourDeficit]
                    push_cast
                    ring
        _ = (K : Real) * fourSizeTarget n alpha (K : Real) := by
          rw [midpointOptimizer,
            ProfileEntropyS4.sum_optimizer_mul_support
              (fourDeficitScore alpha) hTarget]
        _ = (midpointDeficit n alpha K : Real) := by
          rw [midpointDeficit,
            deficit_cast_eq_parts_mul_fourSizeTarget n alpha K hK hn]
  have hNonneg :
      (0 : Int) ≤
        tangentCorrectedInt K (midpointDeficit n alpha K)
          (midpointOptimizer n alpha K) i :=
    tangent_corrected_counts_nonnegative_of_fourteen
      K (midpointDeficit n alpha K) (midpointOptimizer n alpha K)
      hCountMoment.1 hCountMoment.2 hLower i
  unfold midpointMultiplicity tangentCorrectedNat
  norm_cast
  exact Int.toNat_of_nonneg hNonneg

end

end Erdos625
