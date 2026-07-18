import Erdos625.RootSeparationSlope
import Erdos625.RootSeparationRoundingNatAdapter
import Erdos625.RootSeparationRoundingBudget
import Erdos625.Section11AsymptoticAssembly

/-!
# Concrete root-corridor adapter for Section XI

This module composes the signed mean-value root separation, the concrete
negligible rounding budget, and transport of the rounded integer locations to
natural numbers.  Its conclusion is the exact constant and root scale used by
the final Section XI assembly.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

/-- The analytic signed-objective corridor data, with advantage-to-slope ratio
at least the manuscript root gap, yields the exact eventual natural-number
threshold separation after the manuscript floor/ceiling choices. -/
theorem eventually_concrete_root_corridor_gap
    (F : ℕ → ℝ → ℝ)
    (rCo rPlus advantage slope : ℕ → ℝ)
    (hCorridor : ∀ᶠ n : ℕ in atTop,
      rCo n ≤ rPlus n ∧
      ContinuousOn (F n) (Icc (rCo n) (rPlus n)) ∧
      DifferentiableOn ℝ (F n) (Ioo (rCo n) (rPlus n)) ∧
      0 < slope n ∧
      (∀ x ∈ Ioo (rCo n) (rPlus n), deriv (F n) x ≤ slope n) ∧
      F n (rCo n) = 0 ∧
      advantage n ≤ F n (rPlus n) ∧
      (Real.log 2) ^ 2 / 8 * Real.log (200 / 153 : ℝ) * baseScale n ≤
        advantage n / slope n ∧
      0 ≤ rootChromaticIndex (rPlus n) (Real.log (n : ℝ)) ∧
      0 ≤ rootCochromaticIndex (rCo n) (rPlus n)) :
    ∀ᶠ n : ℕ in atTop,
      (((Real.log 2) ^ 2 / 16 * Real.log (200 / 153 : ℝ)) -
          rootRoundingBudget n) * baseScale n ≤
        (((rootChromaticIndex (rPlus n) (Real.log (n : ℝ))).toNat : ℕ) : ℝ) -
          (((rootCochromaticIndex (rCo n) (rPlus n)).toNat : ℕ) : ℝ) := by
  filter_upwards [hCorridor, root_rounding_budget_spec.2] with n hn hround
  rcases hn with
    ⟨hOrder, hCont, hDiff, hSlopePos, hSlope, hRootCo, hAdvantage,
      hConcrete, hChromaticNonneg, hCochromaticNonneg⟩
  have hSeparation : advantage n / slope n ≤ rPlus n - rCo n :=
    signed_root_separation_of_advantage_and_slope
      hOrder hCont hDiff hSlopePos hSlope hRootCo hAdvantage
  have hGap :
      (Real.log 2) ^ 2 / 8 * Real.log (200 / 153 : ℝ) * baseScale n ≤
        rPlus n - rCo n :=
    hConcrete.trans hSeparation
  have hRounding :
      Real.log (n : ℝ) + 3 ≤ rootRoundingBudget n * baseScale n := by
    simpa only [baseScale] using hround
  have h := root_midpoint_rounding_gap_toNat
    (rPlus n) (rCo n) (Real.log (n : ℝ))
    ((Real.log 2) ^ 2 / 8 * Real.log (200 / 153 : ℝ))
    (baseScale n) (rootRoundingBudget n)
    hGap hRounding hChromaticNonneg hCochromaticNonneg
  calc
    (((Real.log 2) ^ 2 / 16 * Real.log (200 / 153 : ℝ)) -
          rootRoundingBudget n) * baseScale n =
        (((Real.log 2) ^ 2 / 8 * Real.log (200 / 153 : ℝ)) / 2 -
          rootRoundingBudget n) * baseScale n := by ring
    _ ≤ _ := h

#print axioms eventually_concrete_root_corridor_gap

end

end Erdos625
