import Erdos625.ColoringProfileRealObjective
import Erdos625.ColoringProfileVariationalEnvelope

/-!
# A finite Gibbs-dual upper bound for coloring profiles

This module supplies the first concrete continuous upper relaxation for the
finite profile objective.  For positive support size `b` and positive real
part count `K`, every feasible nonnegative real profile is bounded above by a
one-parameter log-partition dual expression.  The proof is a zero-safe finite
relative-entropy inequality, so competitor coordinates may vanish.

No minimizing tilt, maximum, root, or asymptotic estimate is asserted here.
Those are subsequent analytic obligations.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Positive class size represented by coordinate `i`. -/
def profileClassSize {b : ℕ} (i : Fin b) : ℝ :=
  ((i.1 + 1 : ℕ) : ℝ)

/-- Logarithmic score `-log(s! 2^(choose(s,2)))` of a class of size `s`. -/
def profileDualScore {b : ℕ} (i : Fin b) : ℝ :=
  -coloringClassLogCost (i.1 + 1)

/-- Unnormalized exponential-family mass at coordinate `i`. -/
def profileDualUnnormalized {b : ℕ} (t : ℝ) (i : Fin b) : ℝ :=
  Real.exp (profileDualScore i + t * profileClassSize i)

/-- Finite log-partition sum for the positive class sizes `1, …, b`. -/
def profileDualPartition (b : ℕ) (t : ℝ) : ℝ :=
  ∑ i : Fin b, profileDualUnnormalized t i

theorem profileDualUnnormalized_pos {b : ℕ} (t : ℝ) (i : Fin b) :
    0 < profileDualUnnormalized t i :=
  Real.exp_pos _

theorem profileDualPartition_pos {b : ℕ} (hb : 0 < b) (t : ℝ) :
    0 < profileDualPartition b t := by
  let i0 : Fin b := ⟨0, hb⟩
  exact Finset.sum_pos'
    (fun i _ ↦ (profileDualUnnormalized_pos t i).le)
    ⟨i0, Finset.mem_univ i0, profileDualUnnormalized_pos t i0⟩

/-- Normalized exponential-family weight on class sizes `1, …, b`. -/
def profileDualWeight {b : ℕ} (t : ℝ) (i : Fin b) : ℝ :=
  profileDualUnnormalized t i / profileDualPartition b t

theorem profileDualWeight_pos {b : ℕ} (hb : 0 < b)
    (t : ℝ) (i : Fin b) :
    0 < profileDualWeight t i :=
  div_pos (profileDualUnnormalized_pos t i) (profileDualPartition_pos hb t)

theorem sum_profileDualWeight {b : ℕ} (hb : 0 < b) (t : ℝ) :
    ∑ i : Fin b, profileDualWeight t i = 1 := by
  simp only [profileDualWeight]
  rw [← Finset.sum_div, profileDualPartition]
  exact div_self (profileDualPartition_pos hb t).ne'

theorem log_profileDualWeight {b : ℕ} (hb : 0 < b)
    (t : ℝ) (i : Fin b) :
    Real.log (profileDualWeight t i) =
      profileDualScore i + t * profileClassSize i -
        Real.log (profileDualPartition b t) := by
  rw [profileDualWeight,
    Real.log_div (profileDualUnnormalized_pos t i).ne'
      (profileDualPartition_pos hb t).ne',
    profileDualUnnormalized, Real.log_exp]

/-! ## A zero-safe relative-entropy inequality -/

/-- Scalar relative-entropy inequality, including the boundary `x = 0`. -/
theorem profile_neg_mul_log_add_mul_log_le_sub {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 < y) :
    -x * Real.log x + x * Real.log y ≤ y - x := by
  rcases eq_or_lt_of_le hx with rfl | hxPos
  · simpa using hy.le
  · have hLog := Real.log_le_sub_one_of_pos (div_pos hy hxPos)
    have hScaled := mul_le_mul_of_nonneg_left hLog hx
    rw [Real.log_div hy.ne' hxPos.ne'] at hScaled
    field_simp [hxPos.ne'] at hScaled
    linarith

/-- Reference vector of total mass `parts` obtained by scaling the normalized
dual weight. -/
def profileDualReferenceMass {b : ℕ}
    (parts t : ℝ) (i : Fin b) : ℝ :=
  parts * profileDualWeight t i

theorem profileDualReferenceMass_pos {b : ℕ} (hb : 0 < b)
    {parts : ℝ} (hparts : 0 < parts) (t : ℝ) (i : Fin b) :
    0 < profileDualReferenceMass parts t i :=
  mul_pos hparts (profileDualWeight_pos hb t i)

theorem sum_profileDualReferenceMass {b : ℕ} (hb : 0 < b)
    (parts t : ℝ) :
    ∑ i : Fin b, profileDualReferenceMass parts t i = parts := by
  change (∑ i : Fin b, parts * profileDualWeight t i) = parts
  rw [← Finset.mul_sum,
    sum_profileDualWeight hb, mul_one]

theorem log_profileDualReferenceMass {b : ℕ} (hb : 0 < b)
    {parts : ℝ} (hparts : 0 < parts) (t : ℝ) (i : Fin b) :
    Real.log (profileDualReferenceMass parts t i) =
      Real.log parts + profileDualScore i + t * profileClassSize i -
        Real.log (profileDualPartition b t) := by
  rw [profileDualReferenceMass,
    Real.log_mul hparts.ne' (profileDualWeight_pos hb t i).ne',
    log_profileDualWeight hb]
  ring

/-- Relative entropy against the positive reference vector is nonpositive in
the sign convention used by the profile objective. -/
theorem sum_profile_relativeEntropy_le_zero {b : ℕ} (hb : 0 < b)
    {parts : ℝ} (hparts : 0 < parts)
    (x : RealColoringProfile b)
    (hx : RealColoringProfile.IsNonnegative x)
    (hcount : RealColoringProfile.partCount x = parts)
    (t : ℝ) :
    ∑ i : Fin b,
        (-x i * Real.log (x i) +
          x i * Real.log (profileDualReferenceMass parts t i)) ≤ 0 := by
  calc
    ∑ i : Fin b,
        (-x i * Real.log (x i) +
          x i * Real.log (profileDualReferenceMass parts t i)) ≤
        ∑ i : Fin b, (profileDualReferenceMass parts t i - x i) := by
      apply Finset.sum_le_sum
      intro i _
      exact profile_neg_mul_log_add_mul_log_le_sub
        (hx i) (profileDualReferenceMass_pos hb hparts t i)
    _ = 0 := by
      rw [Finset.sum_sub_distrib, sum_profileDualReferenceMass hb,
        ← RealColoringProfile.partCount, hcount, sub_self]

/-- The explicit one-parameter dual upper expression. -/
def profileDualUpper (b : ℕ) (n parts t : ℝ) : ℝ :=
  n * Real.log n - n + parts - parts * Real.log parts +
    parts * Real.log (profileDualPartition b t) - t * n

/-- Every feasible real profile lies below every finite Gibbs dual value.
Competitor coordinates may be zero. -/
theorem profileRealObjective_le_profileDualUpper {b : ℕ} (hb : 0 < b)
    {n parts : ℝ} (hparts : 0 < parts)
    (x : RealColoringProfile b)
    (hx : RealColoringProfile.IsFeasible x n parts)
    (t : ℝ) :
    profileRealObjective n x ≤ profileDualUpper b n parts t := by
  have hRelative := sum_profile_relativeEntropy_le_zero hb hparts x
    hx.nonnegative hx.partCount_eq t
  have hExpanded :
      (∑ i : Fin b,
        (-x i * Real.log (x i) +
          x i * Real.log (profileDualReferenceMass parts t i))) =
        -(∑ i : Fin b, x i * Real.log (x i)) +
          Real.log parts * RealColoringProfile.partCount x +
          (∑ i : Fin b, x i * profileDualScore i) +
          t * RealColoringProfile.vertexMass x -
          Real.log (profileDualPartition b t) *
            RealColoringProfile.partCount x := by
    calc
      _ = ∑ i : Fin b,
          (-(x i * Real.log (x i)) +
            (Real.log parts * x i + x i * profileDualScore i +
              t * (profileClassSize i * x i) -
                Real.log (profileDualPartition b t) * x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [log_profileDualReferenceMass hb hparts]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_neg_distrib, Finset.mul_sum,
          RealColoringProfile.partCount,
          RealColoringProfile.vertexMass,
          profileClassSize]
        ring
  rw [hExpanded, hx.partCount_eq, hx.vertexMass_eq] at hRelative
  simp only [profileDualScore, mul_neg, Finset.sum_neg_distrib] at hRelative
  rw [profileRealObjective, profileDualUpper, hx.partCount_eq]
  simp only [realProfileCoordinateCost]
  have hCost :
      (∑ i : Fin b,
        x i * (Real.log (x i) + coloringClassLogCost (i.1 + 1))) =
        (∑ i : Fin b, x i * Real.log (x i)) +
          ∑ i : Fin b, x i * coloringClassLogCost (i.1 + 1) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [hCost]
  linarith

/-! ## Exact transfer back to natural profiles -/

/-- Every admissible natural profile is bounded by every Gibbs dual value. -/
theorem profileDiscreteObjective_le_profileDualUpper
    {n b parts : ℕ} (hb : 0 < b) (hparts : 0 < parts)
    (p : ColoringProfile b) (hp : p ∈ boundedColoringProfiles n b parts)
    (t : ℝ) :
    profileDiscreteObjective n p ≤
      profileDualUpper b (n : ℝ) (parts : ℝ) t := by
  have hConstraints := (mem_boundedColoringProfiles p).1 hp
  have hFeasible := RealColoringProfile.isFeasible_ofNat p
    hConstraints.2 hConstraints.1
  rw [← profileRealObjective_ofNat n p]
  exact profileRealObjective_le_profileDualUpper hb
    (by exact_mod_cast hparts) _ hFeasible t

theorem profileDualUpper_isUniformProfileDiscreteObjectiveUpperBound
    {n b parts : ℕ} (hb : 0 < b) (hparts : 0 < parts) (t : ℝ) :
    IsUniformProfileDiscreteObjectiveUpperBound n b parts
      (profileDualUpper b (n : ℝ) (parts : ℝ) t) := by
  intro p hp
  exact profileDiscreteObjective_le_profileDualUpper hb hparts p hp t

/-- Concrete aggregate first-moment bound at an arbitrary dual parameter. -/
theorem boundedProfileColoringExpectation_le_profileDualUpper
    {n b parts : ℕ} (hb : 0 < b) (hparts : 0 < parts) (t : ℝ) :
    boundedProfileColoringExpectation n b parts ≤
      ENNReal.ofReal (((n : ℝ) + 1) ^ b) *
        ENNReal.ofReal
          (Real.exp
            (profileDualUpper b (n : ℝ) (parts : ℝ) t +
              factorialLogErrorBound n)) :=
  boundedProfileColoringExpectation_le_variationalEnvelope n b parts
    (profileDualUpper b (n : ℝ) (parts : ℝ) t)
    (profileDualUpper_isUniformProfileDiscreteObjectiveUpperBound
      hb hparts t)

end

end Erdos625
