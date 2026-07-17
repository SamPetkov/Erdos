import Erdos625.ColoringProfileDeficitConvergence
import Erdos625.ProfileValueUniformS4
import Mathlib.Tactic

/-!
# E1: exact four-deficit scores and uniform convergence

The four coordinates are the manuscript deficits `2,3,4,5`.  This file
bridges their exact finite descending-factorial scores to the accepted
four-point optimized-value stability theorem.
-/

open Filter
open scoped Topology

namespace Erdos625

noncomputable section

/-- Manuscript deficits `2,3,4,5`, indexed by `Fin 4`. -/
def fourDeficit (i : Fin 4) : Nat := i.1 + 2

/-- Exact finite score after removal of the affine profile terms. -/
def fourDeficitScore (alpha : Nat) (i : Fin 4) : Real :=
  Real.log (alpha.descFactorial (fourDeficit i) : Real) -
    (fourDeficit i : Real) * Real.log (alpha : Real) -
      q / 2 * (fourDeficit i : Real) ^ 2

/-- Limiting Gaussian score on the support `2,3,4,5`. -/
def fourGaussianScore (i : Fin 4) : Real :=
  -(q / 2) * ProfileEntropyS4.support i ^ 2

@[simp] theorem fourDeficit_zero : fourDeficit 0 = 2 := by
  rfl

@[simp] theorem fourDeficit_one : fourDeficit 1 = 3 := by
  rfl

@[simp] theorem fourDeficit_two : fourDeficit 2 = 4 := by
  rfl

@[simp] theorem fourDeficit_three : fourDeficit 3 = 5 := by
  rfl

@[simp] theorem fourDeficit_cast_eq_support (i : Fin 4) :
    (fourDeficit i : Real) = ProfileEntropyS4.support i := by
  simp [fourDeficit, ProfileEntropyS4.support]

/-- The closed formula is the literal growing-profile residual score at the
coordinate whose deficit is `fourDeficit i`. -/
theorem profileDeficitResidualScore_rev_succ_eq_fourDeficitScore
    (alpha : Nat) (i : Fin 4) (h : fourDeficit i < alpha) :
    profileDeficitResidualScore alpha
        (Fin.rev ((⟨fourDeficit i, h⟩ : Fin alpha).succ)) =
      fourDeficitScore alpha i := by
  have hsize :
      (Fin.rev ((⟨fourDeficit i, h⟩ : Fin alpha).succ)).1 + 1 ≤ alpha := by
    rw [Fin.val_rev, Fin.val_succ]
    omega
  have hsub :
      alpha -
          ((Fin.rev ((⟨fourDeficit i, h⟩ : Fin alpha).succ)).1 + 1) =
        fourDeficit i := by
    rw [Fin.val_rev, Fin.val_succ]
    change
      alpha - (alpha + 1 - (fourDeficit i + 1 + 1) + 1) =
        fourDeficit i
    omega
  rw [profileDeficitResidualScore_eq_descFactorial alpha _ hsize, hsub]
  rfl

/-- Pointwise convergence of each one of the four exact scores. -/
theorem tendsto_fourDeficitScore (i : Fin 4) :
    Tendsto
      (fun alpha : Nat => fourDeficitScore alpha i)
      atTop
      (nhds (fourGaussianScore i)) := by
  have hcorr := tendsto_log_descFactorial_sub_mul_log (fourDeficit i)
  have hscore := hcorr.sub_const
    (q / 2 * (fourDeficit i : Real) ^ 2)
  simpa [fourDeficitScore, fourGaussianScore,
    fourDeficit_cast_eq_support] using hscore

/-- One threshold works simultaneously for all four deficit coordinates. -/
theorem eventually_uniform_fourDeficitScore :
    ∀ epsilon > 0, ∃ N : Nat, ∀ alpha ≥ N, ∀ i : Fin 4,
      |fourDeficitScore alpha i - fourGaussianScore i| < epsilon := by
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_fourDeficitScore (0 : Fin 4)))
      epsilon hepsilon
  obtain ⟨N1, hN1⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_fourDeficitScore (1 : Fin 4)))
      epsilon hepsilon
  obtain ⟨N2, hN2⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_fourDeficitScore (2 : Fin 4)))
      epsilon hepsilon
  obtain ⟨N3, hN3⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_fourDeficitScore (3 : Fin 4)))
      epsilon hepsilon
  refine ⟨max (max N0 N1) (max N2 N3), fun alpha halpha i ↦ ?_⟩
  fin_cases i
  · simpa [Real.dist_eq] using hN0 alpha (by omega)
  · simpa [Real.dist_eq] using hN1 alpha (by omega)
  · simpa [Real.dist_eq] using hN2 alpha (by omega)
  · simpa [Real.dist_eq] using hN3 alpha (by omega)

/-- Uniform score convergence transfers directly to optimized values for one
common threshold and every interior target `T in (2,5)`. -/
theorem eventually_uniform_fourDeficitOptimizedValue :
    ∀ epsilon > 0, ∃ N : Nat, ∀ alpha ≥ N,
      ∀ T ∈ Set.Ioo (2 : Real) 5,
        |ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) T -
          ProfileEntropyS4.optimizedValue fourGaussianScore T| < epsilon := by
  exact
    ProfileEntropyS4.eventually_uniform_optimizedValue_on_Ioo_of_uniform_scores
      fourDeficitScore fourGaussianScore eventually_uniform_fourDeficitScore

end

#print axioms fourDeficit_zero
#print axioms fourDeficit_one
#print axioms fourDeficit_two
#print axioms fourDeficit_three
#print axioms fourDeficit_cast_eq_support
#print axioms profileDeficitResidualScore_rev_succ_eq_fourDeficitScore
#print axioms tendsto_fourDeficitScore
#print axioms eventually_uniform_fourDeficitScore
#print axioms eventually_uniform_fourDeficitOptimizedValue

end Erdos625
