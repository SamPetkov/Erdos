import Erdos625.FullCornerMuCapBridge
import Mathlib.Tactic

/-!
# Pointwise decay of the full-corner weight

`fullCornerWeight_le_one_of_local_ratio` shows `B(h) ≤ 1` when every
one-class step of the reverse recurrence has ratio at most one.  The same
induction gives `B(h) ≤ q ^ (∑ i, h i)` when every step has ratio at most
`q`.  With `q = 2 n^{-3/2}` this is the bound used for nearly identical
pairs in the Heckel–Panagiotou route to the second moment
(`erdos625suggestion/note`, Lemma 1.1).
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- If each one-class step multiplies the full-corner weight by at most `q`,
then the weight of `h` is at most `q` to the number of classes of `h`. -/
theorem fullCornerWeight_le_pow_of_local_ratio
    (u k h : I → ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hprofile : IsPartialSubprofile k h)
    (hlocal : ∀ g i, IsPartialSubprofile h g → g i < h i →
      fullCornerWeight u k (incrementProfile g i) /
          fullCornerWeight u k g ≤ q) :
    fullCornerWeight u k h ≤ q ^ (∑ i, h i) := by
  induction' m : ∑ i, h i using Nat.strong_induction_on with m ih generalizing h
  by_cases h_zero : ∀ i, h i = 0
  · rw [← m, Finset.sum_eq_zero fun i _ ↦ h_zero i, pow_zero]
    apply fullCornerWeight_le_one_of_local_ratio u k h hprofile
    intro g i _ hgi
    rw [h_zero i] at hgi
    exact absurd hgi (Nat.not_lt_zero _)
  · obtain ⟨i, hi⟩ : ∃ i, 0 < h i := by
      by_contra hcon
      exact h_zero fun i ↦ Nat.eq_zero_of_not_pos fun hpos ↦ hcon ⟨i, hpos⟩
    let g : I → ℕ := Function.update h i (h i - 1)
    have hgi : g i = h i - 1 := Function.update_self i _ h
    have hgj : ∀ j, j ≠ i → g j = h j := fun j hj ↦
      Function.update_of_ne hj _ h
    have hgle : IsPartialSubprofile h g := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hgi]
        exact Nat.sub_le _ _
      · rw [hgj j hj]
    have hglt : g i < h i := by
      rw [hgi]
      exact Nat.sub_lt hi Nat.one_pos
    have hinc : incrementProfile g i = h := by
      funext j
      unfold incrementProfile
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, hgi]
        exact Nat.sub_add_cancel hi
      · rw [Function.update_of_ne hj, hgj j hj]
    have hsum : ∑ j, h j = ∑ j, g j + 1 := by
      have h1 := Finset.add_sum_erase Finset.univ h (Finset.mem_univ i)
      have h2 := Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)
      have h3 : ∑ j ∈ Finset.univ.erase i, g j =
          ∑ j ∈ Finset.univ.erase i, h j :=
        Finset.sum_congr rfl fun j hj ↦ hgj j (Finset.ne_of_mem_erase hj)
      rw [h3, hgi] at h2
      omega
    have hgk : IsPartialSubprofile k g := fun j ↦ le_trans (hgle j) (hprofile j)
    have h_ind : fullCornerWeight u k g ≤ q ^ (∑ j, g j) := by
      apply ih (∑ j, g j)
      · rw [← m, hsum]
        exact Nat.lt_succ_self _
      · exact hgk
      · exact fun g' j hg' hg'' ↦
          hlocal g' j (fun l ↦ le_trans (hg' l) (hgle l))
            (lt_of_lt_of_le hg'' (hgle j))
      · rfl
    have h_pos : 0 < fullCornerWeight u k g := fullCornerWeight_pos u k g hgk
    have hstep := hlocal g i hgle hglt
    rw [hinc, div_le_iff₀ h_pos] at hstep
    rw [← m, hsum]
    calc
      fullCornerWeight u k h ≤ q * fullCornerWeight u k g := hstep
      _ ≤ q * q ^ (∑ j, g j) := mul_le_mul_of_nonneg_left h_ind hq
      _ = q ^ (∑ j, g j + 1) := by
        rw [pow_succ]
        ring

/-- A cap on `2 k_i μ(massCap + u_i, u_i)` gives pointwise decay of the
full-corner weight in the number of residual classes. -/
theorem fullCornerWeight_le_pow_of_mu_cap
    (u k h : I → Nat) (massCap : Nat) (q : ℝ) (hq : 0 ≤ q)
    (hprofile : IsPartialSubprofile k h)
    (hmass : residualVertexMass u h ≤ massCap)
    (hmuCap : ∀ i,
      2 * (k i : Real) * mu (massCap + u i) (u i) ≤ q) :
    fullCornerWeight u k h ≤ q ^ (∑ i, h i) := by
  apply fullCornerWeight_le_pow_of_local_ratio u k h q hq hprofile
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
    _ ≤ q := hmuCap i

#print axioms fullCornerWeight_le_pow_of_local_ratio
#print axioms fullCornerWeight_le_pow_of_mu_cap

end

end Erdos625
