import Erdos625.FullCornerFilteredReindexing
import Erdos625.FullCornerMuCapBridge
import Erdos625.PartialDiagonalDecayReindexing
import Mathlib.Tactic

/-!
# Finite full-corner aggregate bound

This is the finite analytic successor to the exact filtered full-corner
reindexing.  A coordinatewise `mu` cap is converted into a factorial majorant
for residual full-corner weights and summed by the existing truncated
exponential machinery.

The theorem contains no phase estimate, signed first-moment lower bound,
limit, empty-corner estimate, or central-range estimate.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- A coordinatewise full-corner `mu` cap controls the complete-moment-scaled
filtered partial-diagonal mass by the exponential of the total activity.

This is a finite, division-free statement.  The canonical phase estimate
instantiates the activities, while the lower bound on
`completeSignedFirstMoment` controls the unscaled sum. -/
theorem sum_partialDiagonalWeight_fullCorner_filter_mul_complete_le_exp_sum_of_mu_cap
    {I : Type*} [Fintype I] [DecidableEq I]
    (n massCap : Nat) (u k : I → Nat) (xi : I → Real)
    (hfullMass : selectedVertexMass u k = n)
    (hmuCap : ∀ i : I,
      2 * (k i : Real) * mu (massCap + u i) (u i) ≤ xi i) :
    (∑ ell ∈ (partialSubprofileBox k).filter
        (fun ell => n - selectedVertexMass u ell ≤ massCap),
      partialDiagonalWeight n u k ell) *
        completeSignedFirstMoment u k ≤
      Real.exp (∑ i : I, xi i) := by
  -- Nonnegativity of the supplied activities, from the `mu` cap.
  have hxi : ∀ i : I, 0 ≤ xi i := by
    intro i
    refine le_trans ?_ (hmuCap i)
    exact mul_nonneg (by positivity) (mu_nonneg _ _)
  -- The residual-mass region is down-closed under coordinate increments.
  have hdown : ∀ (g : I → Nat) (i : I),
      residualVertexMass u (incrementProfile g i) ≤ massCap →
      residualVertexMass u g ≤ massCap := by
    intro g i hg
    have hstepMass : residualVertexMass u (incrementProfile g i) =
        residualVertexMass u g + u i := by
      unfold residualVertexMass
      exact selectedVertexMass_increment u g i
    omega
  -- The empty residual profile has full-corner weight exactly one.
  have hzero : fullCornerWeight u k (fun _ => 0) ≤ 1 := by
    simp +decide [fullCornerWeight, residualMarkingCount,
      completeSignedFirstMoment, residualVertexMass, partialSignedFirstMoment,
      selectedVertexMass, selectedBlockCount, selectedInternalEdgeCount,
      partialProfileFactorialProduct]
  -- One-step factorial decay of the full-corner weight inside the region.
  have hstep : ∀ (g : I → Nat) (i : I), IsPartialSubprofile k g → g i < k i →
      residualVertexMass u (incrementProfile g i) ≤ massCap →
      fullCornerWeight u k (incrementProfile g i) ≤
        fullCornerWeight u k g * (xi i / (g i + 1 : Real)) := by
    intro g i hg hgi hregion
    have hstepMass : residualVertexMass u (incrementProfile g i) =
        residualVertexMass u g + u i := by
      unfold residualVertexMass
      exact selectedVertexMass_increment u g i
    have hvertex : residualVertexMass u g + u i ≤ massCap + u i := by omega
    have hmu : mu (residualVertexMass u g + u i) (u i) ≤
        mu (massCap + u i) (u i) :=
      mu_le_of_le_vertex_count (Nat.le_add_left _ _) hvertex
    have hk : ((k i - g i : Nat) : Real) ≤ (k i : Real) := by
      exact_mod_cast Nat.sub_le (k i) (g i)
    have hnum :
        2 * ((k i - g i : Nat) : Real) *
            mu (residualVertexMass u g + u i) (u i) ≤ xi i := by
      refine le_trans ?_ (hmuCap i)
      refine mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hmu
        (mu_nonneg _ _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    have hpos : 0 < fullCornerWeight u k g := fullCornerWeight_pos u k g hg
    have hposIncrement : 0 < fullCornerWeight u k (incrementProfile g i) :=
      fullCornerWeight_pos u k _ (isPartialSubprofile_increment hg hgi)
    have hc : (0 : Real) < (g i + 1 : Real) := by positivity
    have hc1 : (1 : Real) ≤ (g i + 1 : Real) := by
      have : (0 : Real) ≤ (g i : Real) := Nat.cast_nonneg _
      linarith
    have hkey := fullCornerWeight_increment_mul u k g i
    rw [← mul_div_assoc, le_div_iff₀ hc]
    have hsquare :
        fullCornerWeight u k (incrementProfile g i) * (g i + 1 : Real) ≤
          fullCornerWeight u k (incrementProfile g i) * (g i + 1 : Real) ^ 2 := by
      have hmono : (g i + 1 : Real) ≤ (g i + 1 : Real) ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left hmono hposIncrement.le
    have hcap :
        fullCornerWeight u k g *
            (2 * ((k i - g i : Nat) : Real) *
              mu (residualVertexMass u g + u i) (u i)) ≤
          fullCornerWeight u k g * xi i :=
      mul_le_mul_of_nonneg_left hnum hpos.le
    linarith [hkey]
  -- Restricted factorial majorant for the full-corner weights.
  have hmajorant : ∀ h : I → Nat, h ∈ partialSubprofileBox k →
      residualVertexMass u h ≤ massCap →
      fullCornerWeight u k h ≤ partialDiagonalFactorialMajorant xi h := by
    intro h hbox hcap
    exact pointwise_le_factorialMajorant_of_increment_decay_on k xi
      (fullCornerWeight u k) (fun g => residualVertexMass u g ≤ massCap)
      hdown hxi hzero hstep h hcap (mem_partialSubprofileBox.mp hbox)
  -- Exact filtered full-corner reindexing, then the truncated-exponential sum.
  rw [sum_partialDiagonalWeight_fullCorner_filter_mul_complete_eq
    n massCap u k hfullMass]
  calc
    (∑ h ∈ (partialSubprofileBox k).filter
        (fun h => residualVertexMass u h ≤ massCap),
      fullCornerWeight u k h) ≤
        ∏ i, ∑ r ∈ Finset.range (k i + 1),
          xi i ^ r / (r.factorial : Real) :=
      sum_le_product_truncatedExp_of_partialDiagonal_majorant_on k xi
        (fullCornerWeight u k) (fun h => residualVertexMass u h ≤ massCap)
        hxi hmajorant
    _ ≤ Real.exp (∑ i : I, xi i) := product_truncatedExp_le_exp_sum k xi hxi

end

end Erdos625
