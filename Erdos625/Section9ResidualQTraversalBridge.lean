import Erdos625.Section9ResidualQDegreeAssembly
import Erdos625.Section9TraversalKernel

/-!
# Section IX: residual `q` as a bipartite traversal kernel

This module composes the accepted degree-cap residual-q row/column estimate
with the accepted generic bipartite-kernel interface.  It is a deterministic
finite kernel-norm bridge only: it neither identifies a conditioned residual
law, encodes cycles as walks, nor proves an attachment estimate.
-/

universe u v

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Under the same finite degree-cap hypotheses as the residual-q norm
theorem, the literal symmetric bipartite kernel has the corresponding uniform
row norm. -/
theorem existsAbsoluteResidualQBipartiteKernelRowBound_of_degreeCaps :
    ∃ κ : ℝ≥0∞, 0 < κ ∧ κ ≠ ∞ ∧
      ∀ {A : Type u} {B : Type v} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (M : Finset (A × B)) (U R m : ℕ)
          (row : A → ℕ) (col : B → ℕ),
        0 < m →
        (∑ a, row a) = m →
        (∑ b, col b) = m →
        (∀ a, row a ≤ U) →
        (∀ b, col b ≤ U) →
        R = U / 2 →
        2 ^ U ≤ m ^ 3 →
        ∀ v : A ⊕ B,
          ∑ w, bipartiteCellKernel (residualQ M R row col) v w ≤
            κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞) := by
  obtain ⟨κ, hκpos, hκtop, hκ⟩ :=
    existsAbsoluteResidualQRowColumnBound_of_degreeCaps
  refine ⟨κ, hκpos, hκtop, ?_⟩
  intro A B _ _ _ _ M U R m row col hm hrowTotal hcolTotal hrowCap hcolCap
    hR hpow
  obtain ⟨hRow, hColumn⟩ :=
    hκ M U R m row col hm hrowTotal hcolTotal hrowCap hcolCap hR hpow
  exact bipartiteCellKernel_rowSum_le (residualQ M R row col)
    (κ * (U : ℝ≥0∞) ^ 3 / (m : ℝ≥0∞)) hRow hColumn

#print axioms existsAbsoluteResidualQBipartiteKernelRowBound_of_degreeCaps

end

end Erdos625
