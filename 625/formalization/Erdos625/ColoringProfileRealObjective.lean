import Erdos625.ColoringProfileDiscreteObjective

/-!
# Real coloring profiles and their finite objective

This module supplies the finite-dimensional real relaxation of a bounded
coloring profile.  Feasibility records coordinatewise nonnegativity and the
two exact affine constraints: number of parts and vertex mass.  No optimizer
or maximum is introduced here.

The real objective uses `x * log x` at every coordinate.  Since Lean's real
logarithm is total and `0 * log 0 = 0`, the definition includes zero
coordinates and the empty profile without a positivity side condition.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A bounded real coloring profile.  Coordinate `i : Fin b` represents the
real number of classes of positive size `i + 1`. -/
abbrev RealColoringProfile (b : ℕ) := Fin b → ℝ

namespace RealColoringProfile

/-- Every coordinate of a real profile is nonnegative. -/
def IsNonnegative {b : ℕ} (x : RealColoringProfile b) : Prop :=
  ∀ i, 0 ≤ x i

/-- Total (real) number of parts represented by a profile. -/
def partCount {b : ℕ} (x : RealColoringProfile b) : ℝ :=
  ∑ i : Fin b, x i

/-- Total (real) vertex mass represented by a profile. -/
def vertexMass {b : ℕ} (x : RealColoringProfile b) : ℝ :=
  ∑ i : Fin b, ((i.1 + 1 : ℕ) : ℝ) * x i

/-- Feasibility for ambient vertex mass `n` and part count `parts`. -/
def IsFeasible {b : ℕ} (x : RealColoringProfile b)
    (n parts : ℝ) : Prop :=
  IsNonnegative x ∧ partCount x = parts ∧ vertexMass x = n

theorem IsFeasible.nonnegative {b : ℕ} {x : RealColoringProfile b}
    {n parts : ℝ} (h : IsFeasible x n parts) : IsNonnegative x :=
  h.1

theorem IsFeasible.partCount_eq {b : ℕ} {x : RealColoringProfile b}
    {n parts : ℝ} (h : IsFeasible x n parts) : partCount x = parts :=
  h.2.1

theorem IsFeasible.vertexMass_eq {b : ℕ} {x : RealColoringProfile b}
    {n parts : ℝ} (h : IsFeasible x n parts) : vertexMass x = n :=
  h.2.2

/-- Coordinatewise embedding of a natural coloring profile into the real
profile space. -/
def ofNat {b : ℕ} (k : ColoringProfile b) : RealColoringProfile b :=
  fun i ↦ (k i : ℝ)

@[simp] theorem ofNat_apply {b : ℕ} (k : ColoringProfile b) (i : Fin b) :
    ofNat k i = (k i : ℝ) :=
  rfl

theorem isNonnegative_ofNat {b : ℕ} (k : ColoringProfile b) :
    IsNonnegative (ofNat k) := by
  intro i
  change (0 : ℝ) ≤ (k i : ℝ)
  exact_mod_cast Nat.zero_le (k i)

@[simp] theorem partCount_ofNat {b : ℕ} (k : ColoringProfile b) :
    partCount (ofNat k) = (ColoringProfile.partCount k : ℝ) := by
  rw [ColoringProfile.partCount_eq_sum, Nat.cast_sum]
  rfl

@[simp] theorem vertexMass_ofNat {b : ℕ} (k : ColoringProfile b) :
    vertexMass (ofNat k) = (ColoringProfile.vertexMass k : ℝ) := by
  rw [ColoringProfile.vertexMass_eq_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ofNat_apply, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]

/-- Exact natural profiles embed as feasible real profiles.  No positivity or
nonemptiness hypothesis is needed, so this includes `b = n = parts = 0` and
profiles with zero coordinates. -/
theorem isFeasible_ofNat {b n parts : ℕ} (k : ColoringProfile b)
    (hparts : ColoringProfile.partCount k = parts)
    (hmass : ColoringProfile.vertexMass k = n) :
    IsFeasible (ofNat k) (n : ℝ) (parts : ℝ) := by
  refine ⟨isNonnegative_ofNat k, ?_, ?_⟩
  · simpa only [partCount_ofNat] using congrArg Nat.cast hparts
  · simpa only [vertexMass_ofNat] using congrArg Nat.cast hmass

@[simp] theorem partCount_empty (x : RealColoringProfile 0) :
    partCount x = 0 := by
  simp [partCount]

@[simp] theorem vertexMass_empty (x : RealColoringProfile 0) :
    vertexMass x = 0 := by
  simp [vertexMass]

/-- The unique-dimensional empty profile is feasible for zero mass and zero
parts. -/
theorem isFeasible_empty (x : RealColoringProfile 0) :
    IsFeasible x 0 0 := by
  refine ⟨?_, partCount_empty x, vertexMass_empty x⟩
  intro i
  exact Fin.elim0 i

end RealColoringProfile

/-! ## The real finite-profile objective -/

/-- Zero-safe contribution of one real class-count coordinate. -/
def realProfileCoordinateCost (s : ℕ) (x : ℝ) : ℝ :=
  x * (Real.log x + coloringClassLogCost s)

@[simp] theorem realProfileCoordinateCost_zero (s : ℕ) :
    realProfileCoordinateCost s 0 = 0 := by
  simp [realProfileCoordinateCost]

/-- The finite real profile objective corresponding to manuscript (3.2).
The ambient mass is real because this is the analytic relaxation used by the
later dual and maximum arguments. -/
def profileRealObjective {b : ℕ}
    (n : ℝ) (x : RealColoringProfile b) : ℝ :=
  n * Real.log n - n + RealColoringProfile.partCount x -
    ∑ i : Fin b, realProfileCoordinateCost (i.1 + 1) (x i)

/-- Casting an exact natural profile preserves the finite objective exactly.
This identity is valid at zero coordinates and for the empty `b = n = 0`
profile. -/
theorem profileRealObjective_ofNat {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    profileRealObjective (n : ℝ) (RealColoringProfile.ofNat k) =
      profileDiscreteObjective n k := by
  calc
    profileRealObjective (n : ℝ) (RealColoringProfile.ofNat k) =
        profileManuscriptObjective n k := by
      simp only [profileRealObjective, profileManuscriptObjective,
        RealColoringProfile.partCount_ofNat,
        RealColoringProfile.ofNat_apply, realProfileCoordinateCost]
    _ = profileDiscreteObjective n k :=
      (profileDiscreteObjective_eq_profileManuscriptObjective n k).symm

@[simp] theorem profileRealObjective_empty (n : ℝ)
    (x : RealColoringProfile 0) :
    profileRealObjective n x = n * Real.log n - n := by
  simp [profileRealObjective]

@[simp] theorem profileRealObjective_empty_zero
    (x : RealColoringProfile 0) :
    profileRealObjective 0 x = 0 := by
  simp

end

end Erdos625
