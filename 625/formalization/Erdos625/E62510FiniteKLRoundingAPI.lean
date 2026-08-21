import Erdos625.MidpointRoundedFourSizeEntropyLoss

/-!
# Explicit finite KL rounding API for E625-10

This module gives stable names to the finite Gibbs-gap quantity already proved
in `MidpointRoundedFourSizeEntropyLoss`.  It deliberately does not introduce a
second optimizer, a limiting Gaussian substitution, a phase-root hypothesis,
or any asymptotic conclusion.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The exact finite entropy-score loss of the tangent-rounded midpoint
profile. -/
noncomputable def midpointRoundedFourSizeEntropyLoss
    (n alpha K : Nat) : Real :=
  (K : Real) *
    (fourSizeFiniteEntropy alpha
        (fourSizeTarget n alpha (K : Real)) -
      (-(∑ i : Fin 4,
          midpointRoundedProportion n alpha K i *
            Real.log (midpointRoundedProportion n alpha K i)) +
        ∑ i : Fin 4,
          midpointRoundedProportion n alpha K i *
            fourDeficitScore alpha i))

/-- Manuscript-facing finite bound: the exact tangent-rounding entropy loss is
nonnegative and at most `50 / 7`. -/
theorem midpointRoundedFourSizeEntropyLoss_nonneg_and_le
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    0 ≤ midpointRoundedFourSizeEntropyLoss n alpha K ∧
      midpointRoundedFourSizeEntropyLoss n alpha K ≤ (50 / 7 : Real) := by
  simpa only [midpointRoundedFourSizeEntropyLoss] using
    midpointRoundedFourSizeEntropy_loss_le n alpha K h

/-- Absolute-value form used by downstream finite error assembly. -/
theorem abs_midpointRoundedFourSizeEntropyLoss_le
    (n alpha K : Nat) (h : MidpointRoundingAdmissible n alpha K) :
    |midpointRoundedFourSizeEntropyLoss n alpha K| ≤ (50 / 7 : Real) := by
  have hLoss :=
    midpointRoundedFourSizeEntropyLoss_nonneg_and_le n alpha K h
  rw [abs_of_nonneg hLoss.1]
  exact hLoss.2

#print axioms midpointRoundedFourSizeEntropyLoss_nonneg_and_le
#print axioms abs_midpointRoundedFourSizeEntropyLoss_le

end

end Erdos625
