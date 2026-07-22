import Erdos625.FourDeficitGaussianBound
import Erdos625.ProfileValueMonotonicityS4
import Erdos625.SPlusEntropySupremumDualInterior
import Mathlib.Tactic

namespace Erdos625

noncomputable section

set_option autoImplicit false

/-- The mixed comparison between the exact finite four-size entropy value and
the limiting unrestricted extended entropy value.  This is not a finite-cutoff
`S₊` entropy loss. -/
noncomputable def finiteFourVsExtendedEntropyLoss
    (alpha : ℕ) (target : ℝ) : ℝ :=
  extendedGaussianEntropyValue target -
    ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) target

/-- The mixed finite-four versus limiting-extended entropy loss is
nonnegative on the interior target interval. -/
theorem finiteFourVsExtendedEntropyLoss_nonneg
    (alpha : ℕ) (hAlpha : 5 < alpha) {target : ℝ}
    (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    0 ≤ finiteFourVsExtendedEntropyLoss alpha target := by
  unfold finiteFourVsExtendedEntropyLoss
  have hFiniteGaussian :
      ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) target ≤
        ProfileEntropyS4.optimizedValue fourGaussianScore target :=
    ProfileEntropyS4.optimizedValue_mono_scores
      (fourDeficitScore alpha) fourGaussianScore hT
      (fourDeficitScore_le_fourGaussianScore alpha hAlpha)
  have hGaussianExtended :
      ProfileEntropyS4.optimizedValue fourGaussianScore target ≤
        extendedGaussianEntropyValue target :=
    fourGaussian_optimizedValue_le_extendedGaussianEntropyValue hT
  linarith

end

end Erdos625
