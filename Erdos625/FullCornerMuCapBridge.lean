import Erdos625.FullCornerLocalRatioBound
import Erdos625.PartialDiagonalMidpointActivityBridge
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A finite full-corner cap certificate implies the full-corner weight bound.

The `mu` certificate is deliberately stated at the largest residual vertex
count relevant to the final profile.  The proof must reduce it to the exact
prefix-local quotient hypothesis of `fullCornerWeight_le_one_of_local_ratio`;
it must not add a global ratio hypothesis. -/
theorem fullCornerWeight_le_one_of_mu_cap
    (u k h : I → Nat) (massCap : Nat)
    (hprofile : IsPartialSubprofile k h)
    (hmass : residualVertexMass u h ≤ massCap)
    (hmuCap : ∀ i,
      2 * (k i : Real) * mu (massCap + u i) (u i) ≤ 1) :
    fullCornerWeight u k h ≤ 1 := by
  apply fullCornerWeight_le_one_of_local_ratio u k h hprofile
  intro g i hg hgi
  rw [fullCornerWeight_increment_div u k g i
    (fun j ↦ le_trans (hg j) (hprofile j))]
  have hmass_g : residualVertexMass u g ≤ residualVertexMass u h := by
    unfold residualVertexMass selectedVertexMass
    exact Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_left (u j) (hg j)
  have hvertex : residualVertexMass u g + u i ≤ massCap + u i := by
    omega
  have hmu : mu (residualVertexMass u g + u i) (u i) ≤
      mu (massCap + u i) (u i) :=
    mu_le_of_le_vertex_count (Nat.le_add_left _ _) hvertex
  have hk : ((k i - g i : Nat) : Real) ≤ k i := by
    exact_mod_cast Nat.sub_le (k i) (g i)
  have hmu_nonneg :
      0 ≤ mu (residualVertexMass u g + u i) (u i) :=
    mu_nonneg _ _
  have hnum :
      2 * ((k i - g i : Nat) : Real) *
          mu (residualVertexMass u g + u i) (u i) ≤
        2 * (k i : Real) * mu (massCap + u i) (u i) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hmu
      hmu_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hden : (1 : Real) ≤ (g i + 1 : Real) ^ 2 := by
    nlinarith [show (0 : Real) ≤ g i by positivity]
  have hnum_nonneg :
      0 ≤ 2 * ((k i - g i : Nat) : Real) *
          mu (residualVertexMass u g + u i) (u i) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hmu_nonneg
  calc
    (2 * ((k i - g i : Nat) : Real) *
          mu (residualVertexMass u g + u i) (u i)) /
        (g i + 1 : Real) ^ 2 ≤
      2 * ((k i - g i : Nat) : Real) *
          mu (residualVertexMass u g + u i) (u i) := by
            exact div_le_self hnum_nonneg hden
    _ ≤ 2 * (k i : Real) * mu (massCap + u i) (u i) := hnum
    _ ≤ 1 := hmuCap i

end

end Erdos625
