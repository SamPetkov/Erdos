import Erdos625.Section9MixedCycleWeightedEnumeration
import Erdos625.Section9ResidualQDegreeAssembly

/-!
# Section IX: literal residual-q mixed-cycle enumeration

The abstract weighted mixed-cycle theorem is specialized here to the literal
`residualQ` kernel.  The already established absolute degree-cap estimate
supplies both row and column norms at
`tau = κ * U^3 / m`; whenever this parameter is below `1/3`, the physical
mixed-cycle weight is bounded by the explicit marked-walk geometric series.

This remains a deterministic finite theorem.  It does not identify a random
conditioned residual table with these parameters, prove that `tau < 1/3`
holds with high probability, or establish the Section IX attachment
expectation.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- One absolute finite positive constant gives the literal residual-q
weighted mixed-cycle estimate under the exact degree-cap hypotheses. -/
theorem existsAbsoluteResidualQMixedCycleWeightedEnumeration :
    ∃ κ : ℝ≥0∞, 0 < κ ∧ κ ≠ ∞ ∧
      ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U R m : ℕ)
          (row : A → ℕ) (col : B → ℕ),
        IsBipartiteMatching M →
        0 < m →
        (∑ a, row a) = m →
        (∑ b, col b) = m →
        (∀ a, row a ≤ U) →
        (∀ b, col b ≤ U) →
        R = U / 2 →
        2 ^ U ≤ m ^ 3 →
        let tau : ℝ≥0∞ :=
          κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)
        tau < (1 / 3 : ℝ≥0∞) →
        let b : ℝ≥0∞ := tau * (1 - tau)⁻¹
        b < 1 ∧
          (∑ C : MixedSimpleCycle A B M,
              edgeWeightOutsideENN (residualQ M R row col) M C.1) ≤
            (((2 * M.card : ℕ) : ℝ≥0∞) *
              (b * (1 - b)⁻¹)) := by
  obtain ⟨κ, hκpos, hκtop, hκ⟩ :=
    existsAbsoluteResidualQRowColumnBound_of_degreeCaps
  refine ⟨κ, hκpos, hκtop, ?_⟩
  intro A B _ _ _ _ M U R m row col hM hm hrowTotal hcolTotal
    hrowCap hcolCap hR hpow
  dsimp only
  intro htau
  have hNorm :=
    hκ M U R m row col hm hrowTotal hcolTotal hrowCap hcolCap hR hpow
  exact
    mixedSimpleCycle_weighted_walk_enumeration
      (residualQ M R row col) M hM
      (κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞))
      htau hNorm.1 hNorm.2

#print axioms existsAbsoluteResidualQMixedCycleWeightedEnumeration

end

end Erdos625
