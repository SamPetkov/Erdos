import Erdos625.PartialDiagonalWeights

/-!
# Exact full-corner weights

This module formalizes the finite algebra in manuscript (7.5)--(7.6).
For a residual profile h inside a full profile k, it defines the
complementary common profile k - h, the exact complete signed first moment
on the residual vertex mass, and the full-corner weight B(h).

The coordinate recurrence is first proved without division. Its ratio form
then follows from the explicit subprofile hypothesis, which makes the old
weight positive.
-/

namespace Erdos625

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- The common profile complementary to a residual profile h. -/
def complementaryProfile (k h : I → ℕ) : I → ℕ :=
  fun i ↦ k i - h i

/-- The residual vertex mass v = sum_i u_i h_i. -/
def residualVertexMass (u h : I → ℕ) : ℕ :=
  selectedVertexMass u h

/-- The single (not squared) product of residual marking choices. -/
def residualMarkingCount (k h : I → ℕ) : ℕ :=
  ∏ i, (k i).choose (h i)

/-- The exact signed first moment of a complete profile h on its own
vertex mass v = sum_i u_i h_i. -/
noncomputable def completeSignedFirstMoment (u h : I → ℕ) : ℝ :=
  partialSignedFirstMoment (residualVertexMass u h) u h

/-- The full-corner weight B(h) from (7.5). -/
noncomputable def fullCornerWeight (u k h : I → ℕ) : ℝ :=
  (residualMarkingCount k h : ℝ) * completeSignedFirstMoment u h

theorem completeSignedFirstMoment_pos (u h : I → ℕ) :
    0 < completeSignedFirstMoment u h :=
  partialSignedFirstMoment_pos _ _ _

theorem residualMarkingCount_pos (k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h) :
    0 < residualMarkingCount k h := by
  unfold residualMarkingCount
  exact Finset.prod_pos fun i _ ↦ Nat.choose_pos (hprofile i)

theorem fullCornerWeight_pos (u k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h) :
    0 < fullCornerWeight u k h := by
  unfold fullCornerWeight
  exact mul_pos
    (by exact_mod_cast residualMarkingCount_pos k h hprofile)
    (completeSignedFirstMoment_pos u h)

section ComplementAlgebra

omit [Fintype I] in
theorem complementaryProfile_add
    (k h : I → ℕ) (hprofile : IsPartialSubprofile k h) (i : I) :
    complementaryProfile k h i + h i = k i := by
  exact Nat.sub_add_cancel (hprofile i)

theorem selectedBlockCount_complement_add
    (k h : I → ℕ) (hprofile : IsPartialSubprofile k h) :
    selectedBlockCount (complementaryProfile k h) +
        selectedBlockCount h =
      selectedBlockCount k := by
  rw [selectedBlockCount, selectedBlockCount, selectedBlockCount,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact complementaryProfile_add k h hprofile i

theorem selectedVertexMass_complement_add
    (u k h : I → ℕ) (hprofile : IsPartialSubprofile k h) :
    selectedVertexMass u (complementaryProfile k h) +
        selectedVertexMass u h =
      selectedVertexMass u k := by
  rw [selectedVertexMass, selectedVertexMass, selectedVertexMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.mul_add, complementaryProfile_add k h hprofile i]

/-- Under a genuine full-profile mass identity, the complementary profile is
feasible in the ambient vertex set. This is the domain fact that turns the
total algebraic definition of partialSignedFirstMoment into the counting
moment used in manuscript (7.5). -/
theorem selectedVertexMass_complement_le_of_fullMass
    (n : ℕ) (u k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h)
    (hfullMass : selectedVertexMass u k = n) :
    selectedVertexMass u (complementaryProfile k h) ≤ n := by
  have hsplit := selectedVertexMass_complement_add u k h hprofile
  omega

/-- A residual subprofile also occupies at most the full-profile mass. -/
theorem selectedVertexMass_le_of_fullMass
    (n : ℕ) (u k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h)
    (hfullMass : selectedVertexMass u k = n) :
    selectedVertexMass u h ≤ n := by
  have hsplit := selectedVertexMass_complement_add u k h hprofile
  omega

theorem selectedInternalEdgeCount_complement_add
    (u k h : I → ℕ) (hprofile : IsPartialSubprofile k h) :
    selectedInternalEdgeCount u (complementaryProfile k h) +
        selectedInternalEdgeCount u h =
      selectedInternalEdgeCount u k := by
  rw [selectedInternalEdgeCount, selectedInternalEdgeCount,
    selectedInternalEdgeCount, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.mul_add, complementaryProfile_add k h hprofile i]

theorem partialMarkingCount_complement
    (k h : I → ℕ) (hprofile : IsPartialSubprofile k h) :
    partialMarkingCount k (complementaryProfile k h) =
      residualMarkingCount k h ^ 2 := by
  rw [partialMarkingCount, residualMarkingCount]
  calc
    (∏ i, (k i).choose (complementaryProfile k h i) ^ 2) =
        ∏ i, (k i).choose (h i) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [complementaryProfile, Nat.choose_symm (hprofile i)]
    _ = (∏ i, (k i).choose (h i)) ^ 2 :=
      Finset.prod_pow Finset.univ 2 (fun i ↦ (k i).choose (h i))

/-- Exact coordinatewise factorial cancellation behind (7.5). -/
theorem residualMarking_mul_profileFactorials
    (u k h : I → ℕ) (hprofile : IsPartialSubprofile k h) :
    residualMarkingCount k h *
        partialProfileFactorialProduct u h *
        partialProfileFactorialProduct u (complementaryProfile k h) =
      partialProfileFactorialProduct u k := by
  rw [residualMarkingCount, partialProfileFactorialProduct,
    partialProfileFactorialProduct, partialProfileFactorialProduct,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hfactorial :=
    Nat.choose_mul_factorial_mul_factorial (hprofile i)
  have hpower :=
    Nat.pow_sub_mul_pow (u i).factorial (hprofile i)
  change
    (k i).choose (h i) *
          ((u i).factorial ^ h i * (h i).factorial) *
          ((u i).factorial ^ (k i - h i) * (k i - h i).factorial) =
      (u i).factorial ^ k i * (k i).factorial
  calc
    (k i).choose (h i) *
          ((u i).factorial ^ h i * (h i).factorial) *
          ((u i).factorial ^ (k i - h i) * (k i - h i).factorial) =
        ((u i).factorial ^ (k i - h i) *
          (u i).factorial ^ h i) *
        ((k i).choose (h i) * (h i).factorial *
          (k i - h i).factorial) := by ring
    _ = (u i).factorial ^ k i * (k i).factorial := by
      rw [hpower, hfactorial]

/-- Denominator-free factorization underlying manuscript (7.5).

The subprofile and full-mass hypotheses are explicit. In particular they imply
that the complementary partial profile has vertex mass at most n, so the
partial signed first moment on the left is a genuine counting moment rather
than merely its total algebraic extension.
-/
theorem partialDiagonalWeight_complement_mul_complete
    (n : ℕ) (u k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h)
    (hfullMass : selectedVertexMass u k = n) :
    partialDiagonalWeight n u k (complementaryProfile k h) *
        completeSignedFirstMoment u k =
      fullCornerWeight u k h := by
  have hmassSplit :=
    selectedVertexMass_complement_add u k h hprofile
  have hrem :
      n - selectedVertexMass u (complementaryProfile k h) =
        selectedVertexMass u h := by
    omega
  have hblocks :=
    selectedBlockCount_complement_add k h hprofile
  have hedges :=
    selectedInternalEdgeCount_complement_add u k h hprofile
  have hmark :=
    partialMarkingCount_complement k h hprofile
  have hfactorials :=
    residualMarking_mul_profileFactorials u k h hprofile
  rw [partialDiagonalWeight, completeSignedFirstMoment, fullCornerWeight,
    completeSignedFirstMoment, partialSignedFirstMoment,
    partialSignedFirstMoment, partialSignedFirstMoment, residualVertexMass,
    hmark, hrem,
    hfullMass]
  simp only [residualVertexMass, Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, one_mul]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hnFactorial : (n.factorial : ℝ) ≠ 0 := by positivity
  have hvFactorial :
      ((selectedVertexMass u h).factorial : ℝ) ≠ 0 := by positivity
  have hpartialFactorial :
      (partialProfileFactorialProduct u (complementaryProfile k h) : ℝ) ≠ 0 := by
    have hp : 0 <
        partialProfileFactorialProduct u (complementaryProfile k h) := by
      unfold partialProfileFactorialProduct
      positivity
    exact_mod_cast hp.ne'
  have hcompleteFactorial :
      (partialProfileFactorialProduct u h : ℝ) ≠ 0 := by
    have hp : 0 < partialProfileFactorialProduct u h := by
      unfold partialProfileFactorialProduct
      positivity
    exact_mod_cast hp.ne'
  have hfullFactorial :
      (partialProfileFactorialProduct u k : ℝ) ≠ 0 := by
    have hp : 0 < partialProfileFactorialProduct u k := by
      unfold partialProfileFactorialProduct
      positivity
    exact_mod_cast hp.ne'
  field_simp
  have hfactorialsReal :
      (residualMarkingCount k h : ℝ) *
          (partialProfileFactorialProduct u h : ℝ) *
          (partialProfileFactorialProduct u (complementaryProfile k h) : ℝ) =
        (partialProfileFactorialProduct u k : ℝ) := by
    exact_mod_cast hfactorials
  norm_num only [Nat.cast_pow]
  rw [← hblocks, ← hedges, pow_add, pow_add, ← hfactorialsReal]
  ring

/-- Quotient form of the exact endpoint factorization (7.5). -/
theorem partialDiagonalWeight_complement_eq_fullCorner_div
    (n : ℕ) (u k h : I → ℕ)
    (hprofile : IsPartialSubprofile k h)
    (hfullMass : selectedVertexMass u k = n) :
    partialDiagonalWeight n u k (complementaryProfile k h) =
      fullCornerWeight u k h / completeSignedFirstMoment u k := by
  have hmomentNe : completeSignedFirstMoment u k ≠ 0 :=
    ne_of_gt (completeSignedFirstMoment_pos u k)
  apply (eq_div_iff hmomentNe).2
  exact partialDiagonalWeight_complement_mul_complete
    n u k h hprofile hfullMass

end ComplementAlgebra

section CoordinateRecurrence

variable [DecidableEq I]

/-- Denominator-free update of the single binomial marking product. -/
theorem residualMarkingCount_increment_mul
    (k h : I → ℕ) (i : I) :
    residualMarkingCount k (incrementProfile h i) * (h i + 1) =
      residualMarkingCount k h * (k i - h i) := by
  let f : I → ℕ := fun j ↦ (k j).choose (h j)
  let b : ℕ := (k i).choose (h i + 1)
  have hnew :
      residualMarkingCount k (incrementProfile h i) =
        b * ∏ j ∈ Finset.univ \ {i}, f j := by
    rw [residualMarkingCount]
    have hfun :
        (fun j ↦ (k j).choose (incrementProfile h i j)) =
          Function.update f i b := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [incrementProfile, f, b]
      · simp [incrementProfile, f, b, hji]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hold :
      residualMarkingCount k h =
        f i * ∏ j ∈ Finset.univ \ {i}, f j := by
    rw [residualMarkingCount]
    exact Finset.prod_eq_mul_prod_sdiff_singleton i f (by simp)
  rw [hnew, hold]
  dsimp [b, f]
  calc
    ((k i).choose (h i + 1) *
          ∏ j ∈ Finset.univ \ {i}, (k j).choose (h j)) * (h i + 1) =
        (∏ j ∈ Finset.univ \ {i}, (k j).choose (h j)) *
          ((k i).choose (h i + 1) * (h i + 1)) := by ring
    _ = (∏ j ∈ Finset.univ \ {i}, (k j).choose (h j)) *
          ((k i).choose (h i) * (k i - h i)) := by
      rw [Nat.choose_succ_right_eq]
    _ = ((k i).choose (h i) *
          ∏ j ∈ Finset.univ \ {i}, (k j).choose (h j)) *
        (k i - h i) := by ring

/-- Adding one residual block changes the exact complete signed first moment
by the factor 2 * mu(v+u_i,u_i) / (h_i+1), written without division. -/
theorem completeSignedFirstMoment_increment_mul
    (u h : I → ℕ) (i : I) :
    completeSignedFirstMoment u (incrementProfile h i) *
        (h i + 1 : ℝ) =
      completeSignedFirstMoment u h *
        (2 * mu (residualVertexMass u h + u i) (u i)) := by
  have hu : u i ≤ selectedVertexMass u h + u i := Nat.le_add_left _ _
  have hsub :
      selectedVertexMass u h + u i - u i = selectedVertexMass u h := by
    omega
  have hfactorialNat := Nat.choose_mul_factorial_mul_factorial hu
  have hfactorial :
      ((selectedVertexMass u h + u i).choose (u i) : ℝ) *
          (u i).factorial *
          (selectedVertexMass u h).factorial =
        (selectedVertexMass u h + u i).factorial := by
    simpa [hsub] using congrArg (fun x : ℕ ↦ (x : ℝ)) hfactorialNat
  rw [completeSignedFirstMoment, completeSignedFirstMoment,
    residualVertexMass,
    partialSignedFirstMoment, partialSignedFirstMoment,
    selectedVertexMass_increment, selectedBlockCount_increment,
    selectedInternalEdgeCount_increment,
    partialProfileFactorialProduct_increment, mu]
  simp only [residualVertexMass, Nat.sub_self, Nat.factorial_zero,
    Nat.cast_one, Nat.cast_mul, Nat.cast_add]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hvertexFactorial :
      ((selectedVertexMass u h).factorial : ℝ) ≠ 0 := by positivity
  have hsumFactorial :
      ((selectedVertexMass u h + u i).factorial : ℝ) ≠ 0 := by positivity
  have huFactorial : ((u i).factorial : ℝ) ≠ 0 := by positivity
  have hhSucc : ((h i : ℝ) + 1) ≠ 0 := by positivity
  have hprofileFactorial :
      (partialProfileFactorialProduct u h : ℝ) ≠ 0 := by
    have hpositive : 0 < partialProfileFactorialProduct u h := by
      unfold partialProfileFactorialProduct
      positivity
    exact_mod_cast Nat.ne_of_gt hpositive
  field_simp
  simp only [pow_succ, pow_add]
  rw [← hfactorial]
  ring

/-- Denominator-free form of the full-corner recurrence (7.6). -/
theorem fullCornerWeight_increment_mul
    (u k h : I → ℕ) (i : I) :
    fullCornerWeight u k (incrementProfile h i) * (h i + 1 : ℝ) ^ 2 =
      fullCornerWeight u k h *
        (2 * ((k i - h i : ℕ) : ℝ) *
          mu (residualVertexMass u h + u i) (u i)) := by
  have hmarkNat := residualMarkingCount_increment_mul k h i
  have hmark :
      (residualMarkingCount k (incrementProfile h i) : ℝ) *
          (h i + 1 : ℝ) =
        (residualMarkingCount k h : ℝ) *
          ((k i - h i : ℕ) : ℝ) := by
    exact_mod_cast hmarkNat
  have hmoment := completeSignedFirstMoment_increment_mul u h i
  unfold fullCornerWeight
  calc
    ((residualMarkingCount k (incrementProfile h i) : ℝ) *
          completeSignedFirstMoment u (incrementProfile h i)) *
        (h i + 1 : ℝ) ^ 2 =
      ((residualMarkingCount k (incrementProfile h i) : ℝ) *
          (h i + 1 : ℝ)) *
        (completeSignedFirstMoment u (incrementProfile h i) *
          (h i + 1 : ℝ)) := by ring
    _ = ((residualMarkingCount k h : ℝ) *
          ((k i - h i : ℕ) : ℝ)) *
        (completeSignedFirstMoment u h *
          (2 * mu (residualVertexMass u h + u i) (u i))) := by
      rw [hmark, hmoment]
    _ = (residualMarkingCount k h : ℝ) *
        completeSignedFirstMoment u h *
          (2 * ((k i - h i : ℕ) : ℝ) *
            mu (residualVertexMass u h + u i) (u i)) := by ring

/-- The manuscript ratio (7.6). Componentwise containment ensures that
B(h) is positive, so division by the old weight is legitimate. -/
theorem fullCornerWeight_increment_div
    (u k h : I → ℕ) (i : I)
    (hprofile : IsPartialSubprofile k h) :
    fullCornerWeight u k (incrementProfile h i) /
        fullCornerWeight u k h =
      (2 * ((k i - h i : ℕ) : ℝ) *
          mu (residualVertexMass u h + u i) (u i)) /
        (h i + 1 : ℝ) ^ 2 := by
  have hweightNe : fullCornerWeight u k h ≠ 0 :=
    ne_of_gt (fullCornerWeight_pos u k h hprofile)
  have hdenominatorNe : (h i + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  apply (div_eq_div_iff hweightNe hdenominatorNe).2
  simpa [mul_comm] using fullCornerWeight_increment_mul u k h i

end CoordinateRecurrence

end Erdos625
