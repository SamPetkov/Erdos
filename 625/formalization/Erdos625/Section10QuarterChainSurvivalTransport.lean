import Erdos625.Section10QuarterChainSurvival
import Mathlib.Tactic

/-!
# Section X: shifted-potential survival transport

The chosen-start survival estimate is monotone in the initial residual
cardinality.  This file records that deterministic transport separately so a
later chain construction can be initialized on any vertex set whose size is
at least `quarterChainStart n`.  It contains no density event, graph-chain,
independent-set, colouring, or probability assertion.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The shifted-potential survival estimate at `quarterChainStart n` transports
to every finite vertex set whose cardinality is at least that starting scale. -/
theorem quarterChain_shifted_survival_of_start_le_card
    (n : ℕ) (U : Finset (Fin n))
    (hU : quarterChainStart n ≤ U.card)
    (hStart : ∀ j : ℕ, j < quarterChainSteps n →
      (quarterDensityCutoff n : ℝ) ≤
        (4 : ℝ)⁻¹ ^ j * ((quarterChainStart n : ℝ) + 1 / 3) - 1 / 3) :
    ∀ j : ℕ, j < quarterChainSteps n →
      (quarterDensityCutoff n : ℝ) ≤
        (4 : ℝ)⁻¹ ^ j * ((U.card : ℝ) + 1 / 3) - 1 / 3 := by
  intro j hj
  have hUreal : (quarterChainStart n : ℝ) ≤ (U.card : ℝ) := by
    exact_mod_cast hU
  have hShift :
      (quarterChainStart n : ℝ) + 1 / 3 ≤ (U.card : ℝ) + 1 / 3 := by
    linarith
  have hMultiplier : 0 ≤ (4 : ℝ)⁻¹ ^ j := by
    positivity
  have hPotential :
      (4 : ℝ)⁻¹ ^ j * ((quarterChainStart n : ℝ) + 1 / 3) - 1 / 3 ≤
        (4 : ℝ)⁻¹ ^ j * ((U.card : ℝ) + 1 / 3) - 1 / 3 := by
    simpa using sub_le_sub_right
      (mul_le_mul_of_nonneg_left hShift hMultiplier) (1 / 3 : ℝ)
  exact (hStart j hj).trans hPotential

/-- Along the full natural sequence, the chosen-start survival estimate holds
uniformly for every finite residual set at least as large as the starting
scale. -/
theorem quarterChain_shifted_survival_all_larger_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ U : Finset (Fin n),
      quarterChainStart n ≤ U.card →
      ∀ j : ℕ, j < quarterChainSteps n →
        (quarterDensityCutoff n : ℝ) ≤
          (4 : ℝ)⁻¹ ^ j * ((U.card : ℝ) + 1 / 3) - 1 / 3 := by
  filter_upwards [quarterChain_shifted_survival_eventually] with n hStart
  intro U hU
  exact quarterChain_shifted_survival_of_start_le_card n U hU hStart

#print axioms quarterChain_shifted_survival_of_start_le_card
#print axioms quarterChain_shifted_survival_all_larger_eventually

end

end Erdos625
