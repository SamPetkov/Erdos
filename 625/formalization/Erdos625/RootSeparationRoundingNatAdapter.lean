import Erdos625.RootSeparationRounding

/-!
# Natural-number transport for the exact root-rounding gap

This is only an `Int.toNat` transport adapter for the already proved
real-valued rounding gap. The two nonnegativity hypotheses are explicit and
are the only new hypotheses.
-/

namespace Erdos625

theorem root_midpoint_rounding_gap_toNat
    (rPlus rCo N c base rho : ℝ)
    (hGap : c * base ≤ rPlus - rCo)
    (hRounding : N + 3 ≤ rho * base)
    (hChromaticNonneg : 0 ≤ rootChromaticIndex rPlus N)
    (hCochromaticNonneg : 0 ≤ rootCochromaticIndex rCo rPlus) :
    (c / 2 - rho) * base ≤
      (((rootChromaticIndex rPlus N).toNat : Nat) : ℝ) -
        (((rootCochromaticIndex rCo rPlus).toNat : Nat) : ℝ) := by
  have h := root_midpoint_rounding_gap rPlus rCo N c base rho hGap hRounding
  rw [← Int.toNat_of_nonneg hChromaticNonneg,
    ← Int.toNat_of_nonneg hCochromaticNonneg] at h
  exact h

end Erdos625
