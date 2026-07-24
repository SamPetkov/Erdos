import Erdos625.ColoringProfileDiscreteObjective
import Erdos625.ColoringProfileFirstMomentBound

/-!
# Abstract variational envelope for bounded coloring profiles

This module closes the finite aggregation step without assuming a particular
solution of the remaining variational problem.  A real number `L` is required
only to dominate the discrete objective on every admissible finite profile.
The resulting first-moment estimate has the coordinate-box multiplicity and
the single numerator-factorial error from the preceding exact bounds.

The statements impose no positivity hypotheses on `n`, `b`, or the number of
parts, and therefore include the empty profile and empty graph.
-/

namespace Erdos625

noncomputable section

/-- `L` uniformly dominates the discrete objective on the finite family of
mass-`n`, exactly-`parts` profiles with class sizes at most `b`. -/
def IsUniformProfileDiscreteObjectiveUpperBound
    (n b parts : ℕ) (L : ℝ) : Prop :=
  ∀ p ∈ boundedColoringProfiles n b parts,
    profileDiscreteObjective n p ≤ L

/-- The natural coordinate-box multiplicity and its real `ofReal` spelling
are exactly equal, including when `n = 0` or `b = 0`. -/
theorem ennreal_boxMultiplicity_eq_ofReal (n b : ℕ) :
    (((n + 1) ^ b : ℕ) : ENNReal) =
      ENNReal.ofReal (((n : ℝ) + 1) ^ b) := by
  rw [← ENNReal.ofReal_natCast ((n + 1) ^ b)]
  congr 1
  norm_num

/-- A uniform variational upper envelope for the discrete objective gives the
finite bounded-profile first-moment bound. -/
theorem boundedProfileColoringExpectation_le_variationalEnvelope
    (n b parts : ℕ) (L : ℝ)
    (hL : IsUniformProfileDiscreteObjectiveUpperBound n b parts L) :
    boundedProfileColoringExpectation n b parts ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
        ENNReal.ofReal
          (Real.exp (L + factorialLogErrorBound n)) := by
  have hFinite :=
    boundedProfileColoringExpectation_le_box_mul_exp
      n b parts (L + factorialLogErrorBound n) (by
        intro p hp
        rw [profileStirlingUpperMain_eq_profileDiscreteObjective]
        exact add_le_add (hL p hp) (le_refl _))
  rw [ennreal_boxMultiplicity_eq_ofReal] at hFinite
  exact hFinite

/-! ## Packaging a continuous relaxation -/

/-- Data asserting that a continuous objective on an abstract feasible space
majorizes every embedded discrete profile and is itself bounded above by `L`.
The feasible space can be a subtype encoding all continuous constraints. -/
def IsContinuousProfileRelaxationUpperBound
    {X : Type*} [TopologicalSpace X]
    (n b parts : ℕ) (embed : ColoringProfile b → X)
    (objective : X → ℝ) (L : ℝ) : Prop :=
  Continuous objective ∧
    (∀ p ∈ boundedColoringProfiles n b parts,
      profileDiscreteObjective n p ≤ objective (embed p)) ∧
    ∀ x, objective x ≤ L

/-- Any supplied continuous relaxation satisfying the comparison and global
upper-bound obligations yields the same finite variational envelope. -/
theorem boundedProfileColoringExpectation_le_of_continuousRelaxation
    {X : Type*} [TopologicalSpace X]
    (n b parts : ℕ) (embed : ColoringProfile b → X)
    (objective : X → ℝ) (L : ℝ)
    (hL : IsContinuousProfileRelaxationUpperBound
      n b parts embed objective L) :
    boundedProfileColoringExpectation n b parts ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
        ENNReal.ofReal
          (Real.exp (L + factorialLogErrorBound n)) := by
  apply boundedProfileColoringExpectation_le_variationalEnvelope n b parts L
  intro p hp
  exact (hL.2.1 p hp).trans (hL.2.2 (embed p))

end

end Erdos625
