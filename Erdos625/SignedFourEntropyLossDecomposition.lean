import Erdos625.SignedFourSizeObjective
import Erdos625.SPlusEntropySupremumDualInterior
import Mathlib.Tactic

namespace Erdos625

noncomputable section

/-- The finite four-size loss is the limiting four-size loss plus the exact
finite-score approximation error. -/
theorem finite_four_entropy_loss_eq_limiting_add_error
    (alpha : ℕ) (T : ℝ) :
    extendedGaussianEntropyValue T - fourSizeFiniteEntropy alpha T =
      fourEntropyLoss T +
        (ProfileEntropyS4.optimizedValue fourGaussianScore T -
          ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T) := by
  unfold fourSizeFiniteEntropy fourEntropyLoss
  ring

end

end Erdos625
