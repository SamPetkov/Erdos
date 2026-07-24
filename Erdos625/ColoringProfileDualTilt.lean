import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Erdos625.ColoringProfileDualDifferentiation

/-!
# Endpoint limits and inversion of the coloring-profile dual mean

This module completes the elementary one-dimensional exponential-family
analysis needed to select a finite Gibbs tilt.  For support sizes `1, …, b`,
the mean is continuous and, when `2 ≤ b`, strictly increasing.  After scaling
the finite partition sum by its first or last term, its endpoint limits are
respectively `1` and `b`.  Consequently every target in `(1, b)` is attained
at a unique finite tilt.

No asymptotic estimate for that tilt is asserted here.
-/

namespace Erdos625

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-! ## Continuity and strict monotonicity -/

theorem differentiable_profileDualMean {b : ℕ} (hb : 0 < b) :
    Differentiable ℝ (profileDualMean b) :=
  fun t ↦ (hasDerivAt_profileDualMean hb t).differentiableAt

theorem continuous_profileDualMean {b : ℕ} (hb : 0 < b) :
    Continuous (profileDualMean b) :=
  (differentiable_profileDualMean hb).continuous

theorem strictMono_profileDualMean {b : ℕ} (hb : 2 ≤ b) :
    StrictMono (profileDualMean b) := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  apply strictMono_of_deriv_pos
  intro t
  rw [deriv_profileDualMean hbPos]
  exact profileDualVariance_pos hb t

/-! ## A common scaled representation -/

/-- The first support coordinate. -/
def profileDualFirstIndex (b : ℕ) (hb : 0 < b) : Fin b :=
  ⟨0, hb⟩

/-- The last support coordinate. -/
def profileDualLastIndex (b : ℕ) (hb : 0 < b) : Fin b :=
  ⟨b - 1, by omega⟩

@[simp] theorem profileClassSize_firstIndex (b : ℕ) (hb : 0 < b) :
    profileClassSize (profileDualFirstIndex b hb) = 1 := by
  simp [profileClassSize, profileDualFirstIndex]

@[simp] theorem profileClassSize_lastIndex (b : ℕ) (hb : 0 < b) :
    profileClassSize (profileDualLastIndex b hb) = (b : ℝ) := by
  simp only [profileClassSize, profileDualLastIndex]
  norm_cast
  omega

/-- A partition term divided by the term at a chosen base coordinate. -/
def profileDualScaledTerm {b : ℕ} (base : Fin b) (t : ℝ) (i : Fin b) : ℝ :=
  Real.exp
    ((profileDualScore i - profileDualScore base) +
      t * (profileClassSize i - profileClassSize base))

/-- The partition function divided by the term at `base`. -/
def profileDualScaledDenominator {b : ℕ} (base : Fin b) (t : ℝ) : ℝ :=
  ∑ i : Fin b, profileDualScaledTerm base t i

/-- The first-moment numerator divided by the term at `base`. -/
def profileDualScaledNumerator {b : ℕ} (base : Fin b) (t : ℝ) : ℝ :=
  ∑ i : Fin b, profileClassSize i * profileDualScaledTerm base t i

theorem profileDualUnnormalized_eq_base_mul_scaledTerm {b : ℕ}
    (base i : Fin b) (t : ℝ) :
    profileDualUnnormalized t i =
      profileDualUnnormalized t base * profileDualScaledTerm base t i := by
  rw [profileDualUnnormalized, profileDualUnnormalized,
    profileDualScaledTerm, ← Real.exp_add]
  congr 1
  ring

/-- Scaling by any support term leaves the mean unchanged. -/
theorem profileDualMean_eq_scaled {b : ℕ} (base : Fin b) (t : ℝ) :
    profileDualMean b t =
      profileDualScaledNumerator base t / profileDualScaledDenominator base t := by
  rw [profileDualMean, profileDualFirstNumerator, profileDualPartition]
  have hNumerator :
      (∑ i : Fin b, profileClassSize i * profileDualUnnormalized t i) =
        profileDualUnnormalized t base * profileDualScaledNumerator base t := by
    rw [profileDualScaledNumerator, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [profileDualUnnormalized_eq_base_mul_scaledTerm]
    ring
  have hDenominator :
      (∑ i : Fin b, profileDualUnnormalized t i) =
        profileDualUnnormalized t base * profileDualScaledDenominator base t := by
    rw [profileDualScaledDenominator, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact profileDualUnnormalized_eq_base_mul_scaledTerm base i t
  rw [hNumerator, hDenominator]
  field_simp [ne_of_gt (profileDualUnnormalized_pos t base)]

/-! ## Scalar exponential limits -/

private theorem tendsto_exp_affine_atTop_of_neg {a c : ℝ} (hc : c < 0) :
    Tendsto (fun t : ℝ ↦ Real.exp (a + t * c)) atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hlin : Tendsto (fun t : ℝ ↦ c * t + a) atTop atBot :=
    tendsto_atBot_add_const_right atTop a
      (tendsto_id.const_mul_atTop_of_neg hc)
  simpa only [mul_comm, add_comm] using hlin

private theorem tendsto_exp_affine_atBot_of_pos {a c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ ↦ Real.exp (a + t * c)) atBot (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hlin : Tendsto (fun t : ℝ ↦ c * t + a) atBot atBot :=
    tendsto_atBot_add_const_right atBot a (tendsto_id.const_mul_atBot hc)
  simpa only [mul_comm, add_comm] using hlin

/-! ## The upper endpoint -/

private theorem profileClassSize_lt_last_of_ne {b : ℕ} (hb : 0 < b)
    {i : Fin b} (hi : i ≠ profileDualLastIndex b hb) :
    profileClassSize i < (b : ℝ) := by
  have hlt : i.1 + 1 < b := by
    have hle : i.1 + 1 ≤ b := by omega
    by_contra hnot
    have heq : i.1 + 1 = b := by omega
    apply hi
    apply Fin.ext
    simp only [profileDualLastIndex]
    omega
  change (((i.1 + 1 : ℕ) : ℝ)) < (b : ℝ)
  exact_mod_cast hlt

theorem tendsto_profileDualScaledTerm_last_atTop {b : ℕ} (hb : 0 < b)
    (i : Fin b) :
    Tendsto
      (fun t ↦ profileDualScaledTerm (profileDualLastIndex b hb) t i)
      atTop (nhds (if i = profileDualLastIndex b hb then 1 else 0)) := by
  by_cases hi : i = profileDualLastIndex b hb
  · subst i
    simp [profileDualScaledTerm]
  · rw [if_neg hi]
    apply tendsto_exp_affine_atTop_of_neg
    rw [profileClassSize_lastIndex]
    exact sub_neg.mpr (profileClassSize_lt_last_of_ne hb hi)

theorem tendsto_profileDualScaledDenominator_last_atTop {b : ℕ}
    (hb : 0 < b) :
    Tendsto
      (profileDualScaledDenominator (profileDualLastIndex b hb))
      atTop (nhds 1) := by
  have hsum := tendsto_finsetSum (f := fun i t ↦
      profileDualScaledTerm (profileDualLastIndex b hb) t i)
    (a := fun i ↦ if i = profileDualLastIndex b hb then 1 else 0)
    Finset.univ (fun i _ ↦ tendsto_profileDualScaledTerm_last_atTop hb i)
  change Tendsto
    (fun t ↦ ∑ i : Fin b,
      profileDualScaledTerm (profileDualLastIndex b hb) t i)
    atTop (nhds 1)
  simpa using hsum

theorem tendsto_profileDualScaledNumerator_last_atTop {b : ℕ}
    (hb : 0 < b) :
    Tendsto
      (profileDualScaledNumerator (profileDualLastIndex b hb))
      atTop (nhds (b : ℝ)) := by
  have hterm : ∀ i : Fin b,
      Tendsto
        (fun t ↦ profileClassSize i *
          profileDualScaledTerm (profileDualLastIndex b hb) t i)
        atTop
        (nhds (if i = profileDualLastIndex b hb then (b : ℝ) else 0)) := by
    intro i
    by_cases hi : i = profileDualLastIndex b hb
    · subst i
      simpa using
        (tendsto_profileDualScaledTerm_last_atTop hb
          (profileDualLastIndex b hb)).const_mul
          (profileClassSize (profileDualLastIndex b hb))
    · simpa [hi] using
        (tendsto_profileDualScaledTerm_last_atTop hb i).const_mul
          (profileClassSize i)
  have hsum := tendsto_finsetSum (f := fun i t ↦ profileClassSize i *
      profileDualScaledTerm (profileDualLastIndex b hb) t i)
    (a := fun i ↦ if i = profileDualLastIndex b hb then (b : ℝ) else 0)
    Finset.univ (fun i _ ↦ hterm i)
  change Tendsto
    (fun t ↦ ∑ i : Fin b, profileClassSize i *
      profileDualScaledTerm (profileDualLastIndex b hb) t i)
    atTop (nhds (b : ℝ))
  simpa using hsum

/-- At large positive tilt, the Gibbs mean concentrates at support size `b`. -/
theorem tendsto_profileDualMean_atTop {b : ℕ} (hb : 0 < b) :
    Tendsto (profileDualMean b) atTop (nhds (b : ℝ)) := by
  rw [show profileDualMean b =
      fun t ↦ profileDualScaledNumerator (profileDualLastIndex b hb) t /
        profileDualScaledDenominator (profileDualLastIndex b hb) t from by
    funext t
    exact profileDualMean_eq_scaled (profileDualLastIndex b hb) t]
  have h : Tendsto
      (profileDualScaledNumerator (profileDualLastIndex b hb) /
        profileDualScaledDenominator (profileDualLastIndex b hb))
      atTop (nhds (b : ℝ)) := by
    simpa only [div_one] using
      (tendsto_profileDualScaledNumerator_last_atTop hb).div
        (tendsto_profileDualScaledDenominator_last_atTop hb)
        (by norm_num : (1 : ℝ) ≠ 0)
  convert h using 1
  ext t
  rfl

/-! ## The lower endpoint -/

private theorem first_lt_profileClassSize_of_ne {b : ℕ} (hb : 0 < b)
    {i : Fin b} (hi : i ≠ profileDualFirstIndex b hb) :
    (1 : ℝ) < profileClassSize i := by
  have hpos : 0 < i.1 := by
    by_contra hnot
    have hzero : i.1 = 0 := by omega
    apply hi
    apply Fin.ext
    simp [profileDualFirstIndex, hzero]
  simp only [profileClassSize]
  exact_mod_cast (Nat.lt_add_one_iff.mpr hpos)

theorem tendsto_profileDualScaledTerm_first_atBot {b : ℕ} (hb : 0 < b)
    (i : Fin b) :
    Tendsto
      (fun t ↦ profileDualScaledTerm (profileDualFirstIndex b hb) t i)
      atBot (nhds (if i = profileDualFirstIndex b hb then 1 else 0)) := by
  by_cases hi : i = profileDualFirstIndex b hb
  · subst i
    simp [profileDualScaledTerm]
  · rw [if_neg hi]
    apply tendsto_exp_affine_atBot_of_pos
    rw [profileClassSize_firstIndex]
    exact sub_pos.mpr (first_lt_profileClassSize_of_ne hb hi)

theorem tendsto_profileDualScaledDenominator_first_atBot {b : ℕ}
    (hb : 0 < b) :
    Tendsto
      (profileDualScaledDenominator (profileDualFirstIndex b hb))
      atBot (nhds 1) := by
  have hsum := tendsto_finsetSum (f := fun i t ↦
      profileDualScaledTerm (profileDualFirstIndex b hb) t i)
    (a := fun i ↦ if i = profileDualFirstIndex b hb then 1 else 0)
    Finset.univ (fun i _ ↦ tendsto_profileDualScaledTerm_first_atBot hb i)
  change Tendsto
    (fun t ↦ ∑ i : Fin b,
      profileDualScaledTerm (profileDualFirstIndex b hb) t i)
    atBot (nhds 1)
  simpa using hsum

theorem tendsto_profileDualScaledNumerator_first_atBot {b : ℕ}
    (hb : 0 < b) :
    Tendsto
      (profileDualScaledNumerator (profileDualFirstIndex b hb))
      atBot (nhds 1) := by
  have hterm : ∀ i : Fin b,
      Tendsto
        (fun t ↦ profileClassSize i *
          profileDualScaledTerm (profileDualFirstIndex b hb) t i)
        atBot
        (nhds (if i = profileDualFirstIndex b hb then 1 else 0)) := by
    intro i
    by_cases hi : i = profileDualFirstIndex b hb
    · subst i
      simpa using
        (tendsto_profileDualScaledTerm_first_atBot hb
          (profileDualFirstIndex b hb)).const_mul
          (profileClassSize (profileDualFirstIndex b hb))
    · simpa [hi] using
        (tendsto_profileDualScaledTerm_first_atBot hb i).const_mul
          (profileClassSize i)
  have hsum := tendsto_finsetSum (f := fun i t ↦ profileClassSize i *
      profileDualScaledTerm (profileDualFirstIndex b hb) t i)
    (a := fun i ↦ if i = profileDualFirstIndex b hb then 1 else 0)
    Finset.univ (fun i _ ↦ hterm i)
  change Tendsto
    (fun t ↦ ∑ i : Fin b, profileClassSize i *
      profileDualScaledTerm (profileDualFirstIndex b hb) t i)
    atBot (nhds 1)
  simpa using hsum

/-- At large negative tilt, the Gibbs mean concentrates at support size `1`. -/
theorem tendsto_profileDualMean_atBot {b : ℕ} (hb : 0 < b) :
    Tendsto (profileDualMean b) atBot (nhds 1) := by
  rw [show profileDualMean b =
      fun t ↦ profileDualScaledNumerator (profileDualFirstIndex b hb) t /
        profileDualScaledDenominator (profileDualFirstIndex b hb) t from by
    funext t
    exact profileDualMean_eq_scaled (profileDualFirstIndex b hb) t]
  have h : Tendsto
      (profileDualScaledNumerator (profileDualFirstIndex b hb) /
        profileDualScaledDenominator (profileDualFirstIndex b hb))
      atBot (nhds 1) := by
    simpa only [div_one] using
      (tendsto_profileDualScaledNumerator_first_atBot hb).div
        (tendsto_profileDualScaledDenominator_first_atBot hb)
        (by norm_num : (1 : ℝ) ≠ 0)
  convert h using 1
  ext t
  rfl

/-! ## Exact inversion on the open support interval -/

theorem exists_profileDualMean_eq_of_mem_Ioo {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo 1 (b : ℝ)) :
    ∃ t : ℝ, profileDualMean b t = target := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hlow : ∀ᶠ t : ℝ in atBot, profileDualMean b t < target :=
    (tendsto_profileDualMean_atBot hbPos).eventually
      (Iio_mem_nhds htarget.1)
  have hhigh : ∀ᶠ t : ℝ in atTop, target < profileDualMean b t :=
    (tendsto_profileDualMean_atTop hbPos).eventually
      (Ioi_mem_nhds htarget.2)
  obtain ⟨a, ha⟩ := hlow.exists
  obtain ⟨c, hc⟩ := hhigh.exists
  exact Set.mem_range.mp <|
    mem_range_of_exists_le_of_exists_ge
      (continuous_profileDualMean hbPos) ⟨a, ha.le⟩ ⟨c, hc.le⟩

theorem profileDualMean_injective {b : ℕ} (hb : 2 ≤ b) :
    Function.Injective (profileDualMean b) :=
  (strictMono_profileDualMean hb).injective

/-- Every target strictly between the smallest and largest support sizes has
a unique finite Gibbs tilt. -/
theorem existsUnique_profileDualMean_eq_of_mem_Ioo {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo 1 (b : ℝ)) :
    ∃! t : ℝ, profileDualMean b t = target := by
  obtain ⟨t, ht⟩ := exists_profileDualMean_eq_of_mem_Ioo hb htarget
  refine ⟨t, ht, ?_⟩
  intro u hu
  exact profileDualMean_injective hb (hu.trans ht.symm)

end

end Erdos625
