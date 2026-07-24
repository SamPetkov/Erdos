import Erdos625.Section8CanonicalDemandGlobalResidual
import Erdos625.Section8ResidualEventToSection9
import Erdos625.ConfigurationModelCellMarginals
import Erdos625.Section9CyclePolymerBound

/-!
# Section VIII--IX: matchingness of canonical positive support

An attained canonical demand records precisely the cells whose original
configuration counts exceed the half-cap threshold.  Under the ambient row
and column degree caps, those high cells form a bipartite matching.  Therefore
the positive support of every attained canonical demand is a matching as
required by the deterministic Section IX traversal theorems.

This statement is pointwise in an attained demand.  It asserts no law on
demands, residual matching, conditional distribution, or attachment bound.
-/

namespace Erdos625

/-- The positive support of every attained canonical demand is a bipartite
matching under the ambient degree caps. -/
theorem positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ} (U : ℕ)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (demand : canonicalDemandImage row col U) :
    IsBipartiteMatching (positiveDemandSupport demand.1) := by
  classical
  obtain ⟨matching, -, hmatching⟩ := Finset.mem_image.mp demand.2
  have hhigh := configurationCellCount_highCells_form_matching
    matching U hrowCap hcolCap
  have high_of_mem : ∀ a b,
      (a, b) ∈ positiveDemandSupport demand.1 →
        U / 2 < configurationCellCount matching a b := by
    intro a b hab
    have hn : canonicalDemandOfMatching matching U a b ≠ 0 := by
      rw [hmatching]
      simpa only [positiveDemandSupport, Finset.mem_filter,
        Finset.mem_univ, true_and] using hab
    by_contra hnot
    exact hn (by simp [canonicalDemandOfMatching,
      canonicalHighDemand, hnot])
  constructor
  · intro a b₁ b₂ hb₁ hb₂
    exact hhigh.1 a b₁ b₂ (high_of_mem a b₁ hb₁) (high_of_mem a b₂ hb₂)
  · intro b a₁ a₂ ha₁ ha₂
    exact hhigh.2 b a₁ a₂ (high_of_mem a₁ b ha₁) (high_of_mem a₂ b ha₂)

#print axioms positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage

end Erdos625
