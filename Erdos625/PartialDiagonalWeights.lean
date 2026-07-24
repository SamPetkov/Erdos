import Erdos625.Phase

/-!
# Exact partial-diagonal weights

This module formalizes the finite algebra in (7.1)--(7.4).  The coordinate
type is an arbitrary finite type.  For block sizes `u`, full multiplicities
`k`, and a selected common subprofile `ell`, it defines

* the three exact statistics `L`, `m`, and `M` from (7.1);
* the signed first moment `Y_ell^sgn` from (7.2);
* the marked common-subprofile weight `D(ell)` from (7.3).

Natural-number subtraction makes the definitions total even when the selected
mass is larger than `n`.  Every recurrence below carries the exact feasibility
hypothesis needed to recover the manuscript interpretation.

The main algebraic theorem is first stated without division by either marked
weight.  The ratio form (7.4) is then derived under the componentwise
subprofile condition, which proves that `D(ell)` is nonzero.
-/

namespace Erdos625

open scoped BigOperators

variable {I : Type*} [Fintype I]

/-- Increase coordinate `i` of a selected subprofile by one. -/
def incrementProfile [DecidableEq I] (ell : I → ℕ) (i : I) : I → ℕ :=
  Function.update ell i (ell i + 1)

/-- The number `L = sum_i ell_i` of selected common blocks. -/
def selectedBlockCount (ell : I → ℕ) : ℕ :=
  ∑ i, ell i

/-- The selected vertex mass `m = sum_i u_i ell_i`. -/
def selectedVertexMass (u ell : I → ℕ) : ℕ :=
  ∑ i, u i * ell i

/-- The selected internal-edge count `M = sum_i choose(u_i,2) ell_i`. -/
def selectedInternalEdgeCount (u ell : I → ℕ) : ℕ :=
  ∑ i, (u i).choose 2 * ell i

/-- The product `prod_i (u_i!)^(ell_i) ell_i!` in (7.2). -/
def partialProfileFactorialProduct (u ell : I → ℕ) : ℕ :=
  ∏ i, (u i).factorial ^ ell i * (ell i).factorial

/-- The number `prod_i choose(k_i,ell_i)^2` of marked row/column choices. -/
def partialMarkingCount (k ell : I → ℕ) : ℕ :=
  ∏ i, (k i).choose (ell i) ^ 2

/-- `ell` is a genuine common subprofile of the full multiplicity vector `k`. -/
def IsPartialSubprofile (k ell : I → ℕ) : Prop :=
  ∀ i, ell i ≤ k i

section UpdateAlgebra

variable [DecidableEq I]

private theorem sum_update_add (f : I → ℕ) (i : I) (b : ℕ) :
    (∑ j, Function.update f i (f i + b) j) = (∑ j, f j) + b := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hold := Finset.sum_update_of_mem (Finset.mem_univ i) f (f i)
  have hself : Function.update f i (f i) = f := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hself] at hold
  rw [hold]
  omega

private theorem prod_update_mul {M : Type*} [CommMonoid M]
    (f : I → M) (i : I) (b : M) :
    (∏ j, Function.update f i (f i * b) j) = (∏ j, f j) * b := by
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hold := Finset.prod_update_of_mem (Finset.mem_univ i) f (f i)
  have hself : Function.update f i (f i) = f := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hself] at hold
  rw [hold]
  ac_rfl

@[simp] theorem selectedBlockCount_increment (ell : I → ℕ) (i : I) :
    selectedBlockCount (incrementProfile ell i) = selectedBlockCount ell + 1 := by
  exact sum_update_add ell i 1

@[simp] theorem selectedVertexMass_increment (u ell : I → ℕ) (i : I) :
    selectedVertexMass u (incrementProfile ell i) =
      selectedVertexMass u ell + u i := by
  let f : I → ℕ := fun j ↦ u j * ell j
  have hfun : (fun j ↦ u j * incrementProfile ell i j) =
      Function.update f i (f i + u i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [incrementProfile, f, Nat.mul_add]
    · simp [incrementProfile, f, hji]
  rw [selectedVertexMass, selectedVertexMass, hfun]
  exact sum_update_add f i (u i)

@[simp] theorem selectedInternalEdgeCount_increment
    (u ell : I → ℕ) (i : I) :
    selectedInternalEdgeCount u (incrementProfile ell i) =
      selectedInternalEdgeCount u ell + (u i).choose 2 := by
  let f : I → ℕ := fun j ↦ (u j).choose 2 * ell j
  have hfun : (fun j ↦ (u j).choose 2 * incrementProfile ell i j) =
      Function.update f i (f i + (u i).choose 2) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [incrementProfile, f, Nat.mul_add]
    · simp [incrementProfile, f, hji]
  rw [selectedInternalEdgeCount, selectedInternalEdgeCount, hfun]
  exact sum_update_add f i ((u i).choose 2)

@[simp] theorem partialProfileFactorialProduct_increment
    (u ell : I → ℕ) (i : I) :
    partialProfileFactorialProduct u (incrementProfile ell i) =
      partialProfileFactorialProduct u ell * (u i).factorial * (ell i + 1) := by
  let f : I → ℕ :=
    fun j ↦ (u j).factorial ^ ell j * (ell j).factorial
  have hlocal :
      (u i).factorial ^ (ell i + 1) * (ell i + 1).factorial =
        f i * ((u i).factorial * (ell i + 1)) := by
    simp [f, pow_succ, Nat.factorial_succ]
    ring
  have hfun :
      (fun j ↦
        (u j).factorial ^ incrementProfile ell i j *
          (incrementProfile ell i j).factorial) =
        Function.update f i (f i * ((u i).factorial * (ell i + 1))) := by
    funext j
    by_cases hji : j = i
    · subst j
      simpa [incrementProfile] using hlocal
    · simp [incrementProfile, f, hji]
  rw [partialProfileFactorialProduct, partialProfileFactorialProduct,
    hfun, prod_update_mul]
  simp [f, mul_assoc]

/-- Denominator-free form of the binomial-marking update. -/
theorem partialMarkingCount_increment_mul (k ell : I → ℕ) (i : I) :
    partialMarkingCount k (incrementProfile ell i) * (ell i + 1) ^ 2 =
      partialMarkingCount k ell * (k i - ell i) ^ 2 := by
  let f : I → ℕ := fun j ↦ (k j).choose (ell j) ^ 2
  let b : ℕ := (k i).choose (ell i + 1) ^ 2
  have hnew :
      partialMarkingCount k (incrementProfile ell i) =
        b * ∏ j ∈ Finset.univ \ {i}, f j := by
    rw [partialMarkingCount]
    have hfun :
        (fun j ↦ (k j).choose (incrementProfile ell i j) ^ 2) =
          Function.update f i b := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [incrementProfile, f, b]
      · simp [incrementProfile, f, b, hji]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  have hold :
      partialMarkingCount k ell = f i * ∏ j ∈ Finset.univ \ {i}, f j := by
    rw [partialMarkingCount]
    exact Finset.prod_eq_mul_prod_sdiff_singleton i f (by simp)
  rw [hnew, hold]
  dsimp [b, f]
  have hchoose := Nat.choose_succ_right_eq (k i) (ell i)
  calc
    ((k i).choose (ell i + 1) ^ 2 *
          ∏ j ∈ Finset.univ \ {i}, (k j).choose (ell j) ^ 2) *
        (ell i + 1) ^ 2 =
        (∏ j ∈ Finset.univ \ {i}, (k j).choose (ell j) ^ 2) *
          ((k i).choose (ell i + 1) * (ell i + 1)) ^ 2 := by ring
    _ = (∏ j ∈ Finset.univ \ {i}, (k j).choose (ell j) ^ 2) *
          ((k i).choose (ell i) * (k i - ell i)) ^ 2 := by rw [hchoose]
    _ = ((k i).choose (ell i) ^ 2 *
          ∏ j ∈ Finset.univ \ {i}, (k j).choose (ell j) ^ 2) *
        (k i - ell i) ^ 2 := by ring

omit [Fintype I] in
theorem isPartialSubprofile_increment {k ell : I → ℕ} {i : I}
    (hprofile : IsPartialSubprofile k ell) (hi : ell i < k i) :
    IsPartialSubprofile k (incrementProfile ell i) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa [incrementProfile] using hi
  · simpa [incrementProfile, hji] using hprofile j

end UpdateAlgebra

/-- The total algebraic expression in (7.2).  When
`selectedVertexMass u ell ≤ n` it is the exact signed first moment
`Y_ell^sgn`; outside that feasible counting domain it is only the chosen
natural-subtraction extension.  The factor `2^(-M)` is represented by
placing `2^M` in the denominator.
-/
noncomputable def partialSignedFirstMoment
    (n : ℕ) (u ell : I → ℕ) : ℝ :=
  ((2 : ℝ) ^ selectedBlockCount ell * (n.factorial : ℝ)) /
    (((n - selectedVertexMass u ell).factorial : ℝ) *
      (partialProfileFactorialProduct u ell : ℝ) *
      (2 : ℝ) ^ selectedInternalEdgeCount u ell)

/-- The total algebraic marked weight in (7.3).  It has the manuscript's
counting interpretation on the feasible selected-mass domain. -/
noncomputable def partialDiagonalWeight
    (n : ℕ) (u k ell : I → ℕ) : ℝ :=
  (partialMarkingCount k ell : ℝ) / partialSignedFirstMoment n u ell

theorem partialSignedFirstMoment_pos (n : ℕ) (u ell : I → ℕ) :
    0 < partialSignedFirstMoment n u ell := by
  have hfactorialProduct : 0 < partialProfileFactorialProduct u ell := by
    unfold partialProfileFactorialProduct
    positivity
  unfold partialSignedFirstMoment
  positivity

theorem partialMarkingCount_pos (k ell : I → ℕ)
    (hprofile : IsPartialSubprofile k ell) :
    0 < partialMarkingCount k ell := by
  unfold partialMarkingCount
  exact Finset.prod_pos fun i _ ↦ pow_pos (Nat.choose_pos (hprofile i)) 2

theorem partialDiagonalWeight_pos (n : ℕ) (u k ell : I → ℕ)
    (hprofile : IsPartialSubprofile k ell) :
    0 < partialDiagonalWeight n u k ell := by
  unfold partialDiagonalWeight
  exact div_pos
    (by exact_mod_cast partialMarkingCount_pos k ell hprofile)
    (partialSignedFirstMoment_pos n u ell)

@[simp] theorem partialDiagonalWeight_zero (n : ℕ) (u k : I → ℕ) :
    partialDiagonalWeight n u k (fun _ ↦ 0) = 1 := by
  simp [partialDiagonalWeight, partialSignedFirstMoment, partialMarkingCount,
    partialProfileFactorialProduct, selectedBlockCount, selectedVertexMass,
    selectedInternalEdgeCount, Nat.factorial_ne_zero]

section Recurrence

variable [DecidableEq I]

/-- Adding one common block changes the signed first moment by the exact
factor `2 * mu(rem,u_i) / (ell_i+1)`, written without division by either
first moment. -/
theorem partialSignedFirstMoment_increment_mul
    (n : ℕ) (u ell : I → ℕ) (i : I)
    (hmass : selectedVertexMass u ell + u i ≤ n) :
    partialSignedFirstMoment n u (incrementProfile ell i) *
        (ell i + 1 : ℝ) =
      partialSignedFirstMoment n u ell *
        (2 * mu (n - selectedVertexMass u ell) (u i)) := by
  have hu : u i ≤ n - selectedVertexMass u ell :=
    Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hmass)
  have hsub :
      n - (selectedVertexMass u ell + u i) =
        n - selectedVertexMass u ell - u i := by
    omega
  have hfactorialNat := Nat.choose_mul_factorial_mul_factorial hu
  have hfactorial :
      ((n - selectedVertexMass u ell).choose (u i) : ℝ) *
          (u i).factorial *
          (n - selectedVertexMass u ell - u i).factorial =
        (n - selectedVertexMass u ell).factorial := by
    exact_mod_cast hfactorialNat
  rw [partialSignedFirstMoment, partialSignedFirstMoment,
    selectedBlockCount_increment, selectedVertexMass_increment,
    selectedInternalEdgeCount_increment,
    partialProfileFactorialProduct_increment, hsub, mu]
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hnFactorial : (n.factorial : ℝ) ≠ 0 := by positivity
  have hremFactorial :
      ((n - selectedVertexMass u ell).factorial : ℝ) ≠ 0 := by
    positivity
  have hsubFactorial :
      ((n - selectedVertexMass u ell - u i).factorial : ℝ) ≠ 0 := by
    positivity
  have huFactorial : ((u i).factorial : ℝ) ≠ 0 := by positivity
  have hellSucc : ((ell i : ℝ) + 1) ≠ 0 := by positivity
  have hprofileFactorial :
      (partialProfileFactorialProduct u ell : ℝ) ≠ 0 := by
    have hpositive : 0 < partialProfileFactorialProduct u ell := by
      unfold partialProfileFactorialProduct
      positivity
    exact_mod_cast Nat.ne_of_gt hpositive
  field_simp
  simp only [pow_succ, pow_add]
  rw [← hfactorial]
  ring

/-- Denominator-free exact partial-diagonal recurrence underlying (7.4).

This form remains valid even when the marking count is zero; only the vertex
mass feasibility needed by factorial cancellation is assumed.
-/
theorem partialDiagonalWeight_increment_mul
    (n : ℕ) (u k ell : I → ℕ) (i : I)
    (hmass : selectedVertexMass u ell + u i ≤ n) :
    partialDiagonalWeight n u k (incrementProfile ell i) *
        (2 * (ell i + 1 : ℝ) *
          mu (n - selectedVertexMass u ell) (u i)) =
      partialDiagonalWeight n u k ell *
        ((k i - ell i : ℕ) : ℝ) ^ 2 := by
  have hmoment := partialSignedFirstMoment_increment_mul n u ell i hmass
  have hmomentNe : partialSignedFirstMoment n u ell ≠ 0 :=
    ne_of_gt (partialSignedFirstMoment_pos n u ell)
  have hmomentIncrementNe :
      partialSignedFirstMoment n u (incrementProfile ell i) ≠ 0 :=
    ne_of_gt (partialSignedFirstMoment_pos n u (incrementProfile ell i))
  have hmarkNat := partialMarkingCount_increment_mul k ell i
  have hmark :
      (partialMarkingCount k (incrementProfile ell i) : ℝ) *
          (ell i + 1 : ℝ) ^ 2 =
        (partialMarkingCount k ell : ℝ) *
          ((k i - ell i : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hmarkNat
  have hmu :
      2 * mu (n - selectedVertexMass u ell) (u i) =
        partialSignedFirstMoment n u (incrementProfile ell i) *
            (ell i + 1 : ℝ) /
          partialSignedFirstMoment n u ell := by
    apply (eq_div_iff hmomentNe).2
    nlinarith [hmoment]
  rw [partialDiagonalWeight, partialDiagonalWeight,
    show 2 * (ell i + 1 : ℝ) *
        mu (n - selectedVertexMass u ell) (u i) =
      (ell i + 1 : ℝ) *
        (2 * mu (n - selectedVertexMass u ell) (u i)) by ring,
    hmu]
  field_simp
  nlinarith [hmark]

/-- The manuscript ratio (7.4).  Componentwise containment ensures that the
old marked weight is positive, so division by `D(ell)` is legitimate. -/
theorem partialDiagonalWeight_increment_div
    (n : ℕ) (u k ell : I → ℕ) (i : I)
    (hprofile : IsPartialSubprofile k ell)
    (hmass : selectedVertexMass u ell + u i ≤ n) :
    partialDiagonalWeight n u k (incrementProfile ell i) /
        partialDiagonalWeight n u k ell =
      ((k i - ell i : ℕ) : ℝ) ^ 2 /
        (2 * (ell i + 1 : ℝ) *
          mu (n - selectedVertexMass u ell) (u i)) := by
  have hweightNe : partialDiagonalWeight n u k ell ≠ 0 :=
    ne_of_gt (partialDiagonalWeight_pos n u k ell hprofile)
  have hu : u i ≤ n - selectedVertexMass u ell :=
    Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hmass)
  have hdenominatorNe :
      2 * (ell i + 1 : ℝ) *
          mu (n - selectedVertexMass u ell) (u i) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by positivity))
      (ne_of_gt (mu_pos hu))
  apply (div_eq_div_iff hweightNe hdenominatorNe).2
  simpa [mul_comm] using
    partialDiagonalWeight_increment_mul n u k ell i hmass

end Recurrence

end Erdos625
