import Erdos625.Target

/-!
# Section 11: deterministic event assembly

This module isolates the pointwise implication used in the final event
intersection.  It contains no asymptotic or probabilistic hypothesis: once a
chromatic lower threshold and a cochromatic upper threshold are separated by
the exact manuscript scale, every graph in their intersection belongs to the
target gap event.

The strict chromatic event is handled without a rounding shortcut: for
natural-valued chromatic number, `kChi < chi` gives `kChi + 1 <= chi`.
-/

namespace Erdos625

open Set

/-- The strict chromatic lower event appearing in manuscript Section 11. -/
def chromaticLowerEvent (n kChi : ℕ) : Set (LabeledGraph n) :=
  {G | kChi < chromaticNumberNat G}

/-- The real-valued cochromatic upper event, allowing the deterministic
amplification error `a`. -/
def cochromaticUpperEvent (n kCo : ℕ) (a : ℝ) : Set (LabeledGraph n) :=
  {G | (cochromaticNumber G : ℝ) ≤ (kCo : ℝ) + a}

/-- Pointwise Section 11 assembly.  The `+1` is the exact integer consequence
of the strict chromatic lower event. -/
theorem thresholdIntersection_subset_gapEvent
    {n kChi kCo : ℕ} {a : ℝ}
    (hsep : gapScale n ≤
      ((kChi + 1 : ℕ) : ℝ) - ((kCo : ℝ) + a)) :
    chromaticLowerEvent n kChi ∩ cochromaticUpperEvent n kCo a ⊆
      gapEvent n := by
  intro G hG
  rcases hG with ⟨hChi, hCo⟩
  have hChiNat : kChi + 1 ≤ chromaticNumberNat G := by
    exact Nat.succ_le_iff.mpr hChi
  have hChiReal : ((kChi + 1 : ℕ) : ℝ) ≤
      (chromaticNumberNat G : ℝ) := by
    exact_mod_cast hChiNat
  change gapScale n ≤
    (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
  change (cochromaticNumber G : ℝ) ≤ (kCo : ℝ) + a at hCo
  linarith

/-- Fully expanded spelling of the same inclusion, displaying the constant
from (11.2) rather than hiding it behind `gapScale`. -/
theorem explicitThresholdIntersection_subset_gapEvent
    {n kChi kCo : ℕ} {a : ℝ}
    (hsep :
      ((Real.log 2) ^ 2 / 32 * Real.log (200 / 153 : ℝ)) * (n : ℝ) /
          (Real.log (n : ℝ)) ^ 3 ≤
        ((kChi + 1 : ℕ) : ℝ) - ((kCo : ℝ) + a)) :
    chromaticLowerEvent n kChi ∩ cochromaticUpperEvent n kCo a ⊆
      gapEvent n := by
  apply thresholdIntersection_subset_gapEvent
  simpa [gapScale, gapConstant] using hsep

end Erdos625
