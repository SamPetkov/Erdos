import Mathlib

/-!
# Root separation from a signed value and a slope ceiling

This is the noncircular mean-value step used after the two real roots have
already been bracketed in the same corridor. It does not posit a gap between
the roots: the gap is derived from the value of the signed objective at the
unrestricted root and an upper derivative bound on the intervening interval.
-/

namespace Erdos625

open Set
open scoped Topology

noncomputable section

/-- If a signed objective vanishes at its signed root, has a positive value at
the unrestricted root, and has derivative at most `slope` throughout the
already-established interval, then the two roots are separated by at least
the value divided by that slope. No root-gap hypothesis is assumed. -/
theorem signed_root_separation_of_advantage_and_slope
    {F : ℝ → ℝ} {rCo rPlus advantage slope : ℝ}
    (hOrder : rCo ≤ rPlus)
    (hCont : ContinuousOn F (Icc rCo rPlus))
    (hDiff : DifferentiableOn ℝ F (Ioo rCo rPlus))
    (hSlopePos : 0 < slope)
    (hSlope : ∀ x ∈ Ioo rCo rPlus, deriv F x ≤ slope)
    (hRootCo : F rCo = 0)
    (hAdvantage : advantage ≤ F rPlus) :
    advantage / slope ≤ rPlus - rCo := by
  rcases hOrder.eq_or_lt with hEq | hLt
  · subst rPlus
    have hAdvantageNonpos : advantage ≤ 0 := by
      simpa [hRootCo] using hAdvantage
    simpa using div_nonpos_of_nonpos_of_nonneg hAdvantageNonpos hSlopePos.le
  · obtain ⟨c, hc, hDeriv⟩ := exists_deriv_eq_slope F hLt hCont hDiff
    have hGapPos : 0 < rPlus - rCo := sub_pos.mpr hLt
    have hQuotient : (F rPlus - F rCo) / (rPlus - rCo) ≤ slope := by
      rw [← hDeriv]
      exact hSlope c hc
    apply (div_le_iff₀ hSlopePos).2
    calc
      advantage ≤ F rPlus - F rCo := by simpa [hRootCo] using hAdvantage
      _ = ((F rPlus - F rCo) / (rPlus - rCo)) * (rPlus - rCo) := by
        exact (div_mul_cancel₀ _ hGapPos.ne').symm
      _ ≤ slope * (rPlus - rCo) :=
        mul_le_mul_of_nonneg_right hQuotient hGapPos.le
      _ = (rPlus - rCo) * slope := mul_comm _ _

end

end Erdos625
