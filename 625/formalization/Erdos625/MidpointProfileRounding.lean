import Erdos625.TangentNatConservationDisplacement
import Erdos625.TangentCorrectedCountNonnegativity
import Erdos625.MidpointProfileCoordinates
import Erdos625.ProfileOptimizerUniformS4
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

def midpointDeficit (n alpha K : Nat) : Nat :=
  alpha * K - n

noncomputable def midpointOptimizer
    (n alpha K : Nat) : Fin 4 → Real :=
  ProfileEntropyS4.optimizer (fourDeficitScore alpha)
    (fourSizeTarget n alpha (K : Real))

noncomputable def midpointMultiplicity
    (n alpha K : Nat) : Fin 4 → Nat :=
  tangentCorrectedNat K (midpointDeficit n alpha K)
    (midpointOptimizer n alpha K)

def MidpointRoundingAdmissible
    (n alpha K : Nat) : Prop :=
  5 < alpha ∧
  0 < K ∧
  n ≤ alpha * K ∧
  fourSizeTarget n alpha (K : Real) ∈ Set.Ioo (2 : Real) 5 ∧
  ∀ i : Fin 4,
    (14 : Real) ≤
      (K : Real) * midpointOptimizer n alpha K i

theorem midpointOptimizer_count_and_moment
    (n alpha K : Nat)
    (hK : 0 < K)
    (hn : n ≤ alpha * K)
    (hTarget :
      fourSizeTarget n alpha (K : Real) ∈ Set.Ioo (2 : Real) 5) :
    (∑ i : Fin 4,
        (K : Real) * midpointOptimizer n alpha K i) =
          (K : Real) ∧
    (∑ i : Fin 4,
        (tangentDeficit i : Real) *
          ((K : Real) * midpointOptimizer n alpha K i)) =
          (midpointDeficit n alpha K : Real) := by
  constructor
  · unfold midpointOptimizer
    rw [← Finset.mul_sum, ProfileEntropyS4.sum_optimizer]
    ring
  · have hMean :=
      ProfileEntropyS4.sum_optimizer_mul_support
        (fourDeficitScore alpha) hTarget
    have hDeficit := deficit_cast_eq_parts_mul_fourSizeTarget n alpha K hK hn
    unfold midpointOptimizer
    change (∑ i : Fin 4,
        (tangentDeficit i : Real) *
          ((K : Real) * ProfileEntropyS4.optimizer (fourDeficitScore alpha)
            (fourSizeTarget n alpha (K : Real)) i)) =
      (alpha * K - n : Nat)
    calc
      _ = (K : Real) *
          (∑ i : Fin 4,
            ProfileEntropyS4.optimizer (fourDeficitScore alpha)
              (fourSizeTarget n alpha (K : Real)) i *
                ProfileEntropyS4.support i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [tangentDeficit, ProfileEntropyS4.support]
        push_cast
        ring
      _ = (K : Real) * fourSizeTarget n alpha (K : Real) := by rw [hMean]
      _ = (alpha * K - n : Nat) := hDeficit.symm

end

end Erdos625
