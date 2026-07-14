import Erdos625.ColoringProfileDualDifferentiation

/-!
# Attainment of the finite coloring-profile dual

This module identifies the positive Gibbs reference profile as an exact
optimizer whenever its mean satisfies the vertex-mass constraint.  It is a
finite-dimensional equality statement: existence of a target-matching tilt
and all phase-uniform asymptotics remain separate obligations.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- The Gibbs real profile with total part mass `parts`. -/
def profileDualOptimizer {b : ℕ} (parts t : ℝ) : RealColoringProfile b :=
  fun i ↦ profileDualReferenceMass parts t i

@[simp] theorem profileDualOptimizer_apply {b : ℕ}
    (parts t : ℝ) (i : Fin b) :
    profileDualOptimizer parts t i = profileDualReferenceMass parts t i :=
  rfl

theorem profileDualOptimizer_nonnegative {b : ℕ} (hb : 0 < b)
    {parts : ℝ} (hparts : 0 ≤ parts) (t : ℝ) :
    RealColoringProfile.IsNonnegative
      (profileDualOptimizer (b := b) parts t) := by
  intro i
  exact mul_nonneg hparts (profileDualWeight_pos hb t i).le

theorem profileDualOptimizer_pos {b : ℕ} (hb : 0 < b)
    {parts : ℝ} (hparts : 0 < parts) (t : ℝ) (i : Fin b) :
    0 < profileDualOptimizer parts t i :=
  profileDualReferenceMass_pos hb hparts t i

theorem profileDualOptimizer_partCount {b : ℕ} (hb : 0 < b)
    (parts t : ℝ) :
    RealColoringProfile.partCount
        (profileDualOptimizer (b := b) parts t) = parts := by
  exact sum_profileDualReferenceMass hb parts t

theorem profileDualOptimizer_vertexMass {b : ℕ} (parts t : ℝ) :
    RealColoringProfile.vertexMass
        (profileDualOptimizer (b := b) parts t) =
      parts * profileDualMean b t := by
  calc
    RealColoringProfile.vertexMass
        (profileDualOptimizer (b := b) parts t) =
        ∑ i : Fin b,
          profileClassSize i * (parts * profileDualWeight t i) := by
      rfl
    _ = parts *
        (∑ i : Fin b, profileDualWeight t i * profileClassSize i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = parts * profileDualMean b t := by
      rw [← profileDualMean_eq_sum_weight_size]

/-- A target-matching tilt makes the Gibbs profile feasible for the exact
part-count and vertex-mass constraints. -/
theorem profileDualOptimizer_isFeasible {b : ℕ} (hb : 0 < b)
    {n parts t : ℝ} (hparts : 0 < parts)
    (hmass : parts * profileDualMean b t = n) :
    RealColoringProfile.IsFeasible
      (profileDualOptimizer (b := b) parts t) n parts := by
  refine ⟨profileDualOptimizer_nonnegative hb hparts.le t,
    profileDualOptimizer_partCount hb parts t, ?_⟩
  rw [profileDualOptimizer_vertexMass]
  exact hmass

/-- The coordinate cost of the target-matching Gibbs profile has the affine
log-partition form used by duality. -/
theorem realProfileCoordinateCost_profileDualOptimizer {b : ℕ} (hb : 0 < b)
    {parts : ℝ} (hparts : 0 < parts) (t : ℝ) (i : Fin b) :
    realProfileCoordinateCost (i.1 + 1)
        (profileDualOptimizer parts t i) =
      profileDualOptimizer parts t i *
        (Real.log parts + t * profileClassSize i -
          Real.log (profileDualPartition b t)) := by
  rw [realProfileCoordinateCost, profileDualOptimizer_apply,
    log_profileDualReferenceMass hb hparts]
  simp only [profileDualScore]
  ring

/-- The Gibbs optimizer attains the finite dual value whenever its weighted
mean gives the required vertex mass. -/
theorem profileRealObjective_profileDualOptimizer_eq_profileDualUpper
    {b : ℕ} (hb : 0 < b) {n parts t : ℝ} (hparts : 0 < parts)
    (hmass : parts * profileDualMean b t = n) :
    profileRealObjective n (profileDualOptimizer (b := b) parts t) =
      profileDualUpper b n parts t := by
  have hCost :
      (∑ i : Fin b,
        realProfileCoordinateCost (i.1 + 1)
          (profileDualOptimizer parts t i)) =
        Real.log parts *
            RealColoringProfile.partCount
              (profileDualOptimizer (b := b) parts t) +
          t * RealColoringProfile.vertexMass
              (profileDualOptimizer (b := b) parts t) -
          Real.log (profileDualPartition b t) *
            RealColoringProfile.partCount
              (profileDualOptimizer (b := b) parts t) := by
    calc
      _ = ∑ i : Fin b,
          profileDualOptimizer parts t i *
            (Real.log parts + t * profileClassSize i -
              Real.log (profileDualPartition b t)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact realProfileCoordinateCost_profileDualOptimizer hb hparts t i
      _ = _ := by
        calc
          _ = ∑ i : Fin b,
              (Real.log parts * profileDualOptimizer parts t i +
                t * (profileClassSize i * profileDualOptimizer parts t i) -
                Real.log (profileDualPartition b t) *
                  profileDualOptimizer parts t i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (∑ i : Fin b,
                Real.log parts * profileDualOptimizer parts t i) +
              (∑ i : Fin b,
                t * (profileClassSize i * profileDualOptimizer parts t i)) -
              ∑ i : Fin b,
                Real.log (profileDualPartition b t) *
                  profileDualOptimizer parts t i := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
          _ = _ := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
            rfl
  rw [profileRealObjective, profileDualUpper, hCost,
    profileDualOptimizer_partCount hb,
    profileDualOptimizer_vertexMass, hmass]
  ring

/-- Consequently the finite Gibbs upper bound is sharp at every
target-matching tilt. -/
theorem profileDualUpper_eq_profileRealObjective_of_mean_eq
    {b : ℕ} (hb : 0 < b) {n parts t : ℝ} (hparts : 0 < parts)
    (hmean : profileDualMean b t = n / parts) :
    profileDualUpper b n parts t =
      profileRealObjective n (profileDualOptimizer (b := b) parts t) := by
  symm
  apply profileRealObjective_profileDualOptimizer_eq_profileDualUpper
    hb hparts
  rw [hmean]
  field_simp [hparts.ne']

/-- At a target-matching tilt, the Gibbs profile maximizes the real profile
objective over the entire feasible set. -/
theorem profileRealObjective_le_profileDualOptimizer
    {b : ℕ} (hb : 0 < b) {n parts t : ℝ} (hparts : 0 < parts)
    (hmass : parts * profileDualMean b t = n)
    (x : RealColoringProfile b)
    (hx : RealColoringProfile.IsFeasible x n parts) :
    profileRealObjective n x ≤
      profileRealObjective n (profileDualOptimizer (b := b) parts t) := by
  rw [profileRealObjective_profileDualOptimizer_eq_profileDualUpper
    hb hparts hmass]
  exact profileRealObjective_le_profileDualUpper hb hparts x hx t

/-- The dual value is an attained greatest value of the finite-dimensional
real relaxation. -/
theorem profileDualUpper_isGreatest_profileRealObjective
    {b : ℕ} (hb : 0 < b) {n parts t : ℝ} (hparts : 0 < parts)
    (hmass : parts * profileDualMean b t = n) :
    IsGreatest
      (profileRealObjective n ''
        {x : RealColoringProfile b |
          RealColoringProfile.IsFeasible x n parts})
      (profileDualUpper b n parts t) := by
  refine ⟨?_, ?_⟩
  · refine ⟨profileDualOptimizer (b := b) parts t,
      profileDualOptimizer_isFeasible hb hparts hmass, ?_⟩
    exact profileRealObjective_profileDualOptimizer_eq_profileDualUpper
      hb hparts hmass
  · rintro y ⟨x, hx, rfl⟩
    exact profileRealObjective_le_profileDualUpper hb hparts x hx t

end

end Erdos625
