import Erdos625.HPRouteFullCornerDecay

/-!
# Finite full-corner recurrence and conditional decay (finite core of Lemma 6.1(ii) and (iv))

`Erdos625.fullCornerWeight_le_pow_of_mu_cap` assumed a cap at `mu (massCap + u i) (u i)`.
When `IsPartialSubprofile h g` and `g i < h i`, the incremented profile
`incrementProfile g i` is still a subprofile of `h`, so its residual vertex mass
`residualVertexMass u g + u i` already satisfies
`residualVertexMass u g + u i ≤ residualVertexMass u h ≤ massCap`.

This module proves the finite conditional recurrence bounds (the asymptotic
instantiations `q = 2 n^{-3/2}` and `q = n^{-3/2}` and part (iii) remain in the
manuscript):
1. `fullCornerWeight_le_pow_of_sharp_mu_cap` and
   `partialDiagonalWeight_complement_le_pow_div_of_sharp_mu_cap`:
   under the exact manuscript cap `∀ i, 2 * k_i * mu massCap (u i) ≤ q`,
   `B(h) ≤ q^(∑ h_i)` and `W(k - h) ≤ q^(∑ h_i) / E[Z_k^mk]`.
2. `unmarkedFullCornerWeight_increment_div`,
   `unmarkedFullCornerWeight_le_pow_of_sharp_mu_cap`, and
   `unmarkedDiagonalWeight_complement_le_pow_div_of_sharp_mu_cap`:
   for the unmarked colouring counterpart `B^ch(h) = 2^(-∑ h_i) B(h)` of
   Lemma 6.1(iv), the factor `2` drops from the recurrence and
   `∀ i, k_i * mu massCap (u i) ≤ q` implies `B^ch(h) ≤ q^(∑ h_i)` and
   `F_1^ch(k - h) ≤ q^(∑ h_i) / E[X̄_k]`.
-/

namespace Erdos625HP

open Erdos625
open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- If `g ≤ h` coordinatewise and `g i < h i`, then `incrementProfile g i ≤ h`,
so `residualVertexMass u g + u i ≤ residualVertexMass u h`. -/
theorem residualVertexMass_add_le_of_lt
    (u h g : I → ℕ) (i : I)
    (hg : IsPartialSubprofile h g) (hgi : g i < h i) :
    residualVertexMass u g + u i ≤ residualVertexMass u h := by
  have hinc_le : IsPartialSubprofile h (incrementProfile g i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [incrementProfile] using Nat.succ_le_of_lt hgi
    · simpa [incrementProfile, hji] using hg j
  have hmass_inc :
      residualVertexMass u (incrementProfile g i) ≤ residualVertexMass u h := by
    unfold residualVertexMass selectedVertexMass
    exact Finset.sum_le_sum fun j _ ↦ Nat.mul_le_mul_left (u j) (hinc_le j)
  rwa [residualVertexMass, selectedVertexMass_increment, ← residualVertexMass]
    at hmass_inc

/-- **Sharp Lemma 6.1(ii) recurrence bound:** a cap on `2 k_i μ(massCap, u_i)`
(without `+ u_i`) implies `B(h) ≤ q ^ (∑ i, h_i)` whenever
`residualVertexMass u h ≤ massCap`. -/
theorem fullCornerWeight_le_pow_of_sharp_mu_cap
    (u k h : I → ℕ) (massCap : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hprofile : IsPartialSubprofile k h)
    (hmass : residualVertexMass u h ≤ massCap)
    (hmuCap : ∀ i, 2 * (k i : ℝ) * mu massCap (u i) ≤ q) :
    fullCornerWeight u k h ≤ q ^ (∑ i, h i) := by
  apply fullCornerWeight_le_pow_of_local_ratio u k h q hq hprofile
  intro g i hg hgi
  rw [fullCornerWeight_increment_div u k g i
    (fun j ↦ le_trans (hg j) (hprofile j))]
  have hvertex : residualVertexMass u g + u i ≤ massCap :=
    le_trans (residualVertexMass_add_le_of_lt u h g i hg hgi) hmass
  have hmu : mu (residualVertexMass u g + u i) (u i) ≤ mu massCap (u i) :=
    mu_le_of_le_vertex_count (Nat.le_add_left _ _) hvertex
  have hk : ((k i - g i : ℕ) : ℝ) ≤ k i := by
    exact_mod_cast Nat.sub_le (k i) (g i)
  have hmu_nonneg : 0 ≤ mu (residualVertexMass u g + u i) (u i) :=
    mu_nonneg _ _
  have hnum :
      2 * ((k i - g i : ℕ) : ℝ) *
          mu (residualVertexMass u g + u i) (u i) ≤
        2 * (k i : ℝ) * mu massCap (u i) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hmu
      hmu_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hden : (1 : ℝ) ≤ (g i + 1 : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ g i by positivity]
  have hnum_nonneg :
      0 ≤ 2 * ((k i - g i : ℕ) : ℝ) *
          mu (residualVertexMass u g + u i) (u i) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hmu_nonneg
  calc
    (2 * ((k i - g i : ℕ) : ℝ) *
          mu (residualVertexMass u g + u i) (u i)) /
        (g i + 1 : ℝ) ^ 2 ≤
      2 * ((k i - g i : ℕ) : ℝ) *
          mu (residualVertexMass u g + u i) (u i) :=
      div_le_self hnum_nonneg hden
    _ ≤ 2 * (k i : ℝ) * mu massCap (u i) := hnum
    _ ≤ q := hmuCap i

/-- **Normalized marked full-corner bound (`W(k - h) ≤ q^(∑ h_i) / E[Z_k^mk]`):**
combining exact endpoint factorization with `fullCornerWeight_le_pow_of_sharp_mu_cap`. -/
theorem partialDiagonalWeight_complement_le_pow_div_of_sharp_mu_cap
    (n : ℕ) (u k h : I → ℕ) (massCap : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hprofile : IsPartialSubprofile k h)
    (hfullMass : selectedVertexMass u k = n)
    (hmass : residualVertexMass u h ≤ massCap)
    (hmuCap : ∀ i, 2 * (k i : ℝ) * mu massCap (u i) ≤ q) :
    partialDiagonalWeight n u k (complementaryProfile k h) ≤
      q ^ (∑ i, h i) / completeSignedFirstMoment u k := by
  rw [partialDiagonalWeight_complement_eq_fullCorner_div n u k h hprofile hfullMass]
  exact div_le_div_of_nonneg_right
    (fullCornerWeight_le_pow_of_sharp_mu_cap u k h massCap q hq hprofile hmass hmuCap)
    (completeSignedFirstMoment_pos u k).le

/-! ## Unmarked colouring full-corner weights (`B^ch` and `F_1^ch`, Lemma 6.1(iv)) -/

/-- Exact unmarked complete first moment `E[X̄_h] = 2^(-∑ h_i) E[Z_h^mk]` on `v(h)`. -/
def completeUnmarkedFirstMoment (u h : I → ℕ) : ℝ :=
  ((2 : ℝ) ^ (∑ i, h i))⁻¹ * completeSignedFirstMoment u h

/-- Exact unmarked full-corner weight `B^ch(h) = (∏ binom(k_i, h_i)) E[X̄_h] = 2^(-∑ h_i) B(h)`. -/
def unmarkedFullCornerWeight (u k h : I → ℕ) : ℝ :=
  ((2 : ℝ) ^ (∑ i, h i))⁻¹ * fullCornerWeight u k h

/-- Exact unmarked common-class weight `F_1^ch(ν) = 2^(∑ ν_i) W(ν) = ∏ binom(k_i, ν_i)² / E[X̄_ν]`. -/
def unmarkedDiagonalWeight (n : ℕ) (u k nu : I → ℕ) : ℝ :=
  (2 : ℝ) ^ (∑ i, nu i) * partialDiagonalWeight n u k nu

/-- One-step ratio for `B^ch`: the factor `2` from the markings drops out. -/
theorem unmarkedFullCornerWeight_increment_div
    (u k g : I → ℕ) (i : I) (hg : IsPartialSubprofile k g) :
    unmarkedFullCornerWeight u k (incrementProfile g i) /
        unmarkedFullCornerWeight u k g =
      (((k i - g i : ℕ) : ℝ) *
          mu (residualVertexMass u g + u i) (u i)) /
        (g i + 1 : ℝ) ^ 2 := by
  have hsum : ∑ j, incrementProfile g i j = ∑ j, g j + 1 := by
    simpa [selectedBlockCount] using selectedBlockCount_increment g i
  have hBpos : 0 < fullCornerWeight u k g := fullCornerWeight_pos u k g hg
  have h2pos : 0 < (2 : ℝ) ^ (∑ j, g j) := by positivity
  unfold unmarkedFullCornerWeight
  rw [hsum, pow_succ, mul_inv_rev]
  have hdiv :
      (((2 : ℝ)⁻¹ * ((2 : ℝ) ^ (∑ j, g j))⁻¹) *
          fullCornerWeight u k (incrementProfile g i)) /
        (((2 : ℝ) ^ (∑ j, g j))⁻¹ * fullCornerWeight u k g) =
      (2 : ℝ)⁻¹ * (fullCornerWeight u k (incrementProfile g i) /
        fullCornerWeight u k g) := by
    field_simp [hBpos.ne', h2pos.ne']
  rw [hdiv, fullCornerWeight_increment_div u k g i hg]
  ring

/-- **Sharp Lemma 6.1(iv) unmarked full-corner decay:** a cap on `k_i μ(massCap, u_i)`
(without the factor `2` and without `+ u_i`) implies `B^ch(h) ≤ q ^ (∑ i, h_i)`. -/
theorem unmarkedFullCornerWeight_le_pow_of_sharp_mu_cap
    (u k h : I → ℕ) (massCap : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hprofile : IsPartialSubprofile k h)
    (hmass : residualVertexMass u h ≤ massCap)
    (hmuCap : ∀ i, (k i : ℝ) * mu massCap (u i) ≤ q) :
    unmarkedFullCornerWeight u k h ≤ q ^ (∑ i, h i) := by
  have h2q : 0 ≤ 2 * q := by linarith
  have hmarked := fullCornerWeight_le_pow_of_sharp_mu_cap u k h massCap (2 * q) h2q
    hprofile hmass (fun i ↦ by linarith [hmuCap i])
  unfold unmarkedFullCornerWeight
  have hinv_nonneg : 0 ≤ ((2 : ℝ) ^ (∑ i, h i))⁻¹ := by positivity
  calc
    ((2 : ℝ) ^ (∑ i, h i))⁻¹ * fullCornerWeight u k h ≤
        ((2 : ℝ) ^ (∑ i, h i))⁻¹ * (2 * q) ^ (∑ i, h i) :=
      mul_le_mul_of_nonneg_left hmarked hinv_nonneg
    _ = q ^ (∑ i, h i) := by
      rw [mul_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- **Normalized unmarked full-corner bound (`F_1^ch(k - h) ≤ q^(∑ h_i) / E[X̄_k]`):**
exact complementary factorization and decay for the unmarked colouring profile. -/
theorem unmarkedDiagonalWeight_complement_le_pow_div_of_sharp_mu_cap
    (n : ℕ) (u k h : I → ℕ) (massCap : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hprofile : IsPartialSubprofile k h)
    (hfullMass : selectedVertexMass u k = n)
    (hmass : residualVertexMass u h ≤ massCap)
    (hmuCap : ∀ i, (k i : ℝ) * mu massCap (u i) ≤ q) :
    unmarkedDiagonalWeight n u k (complementaryProfile k h) ≤
      q ^ (∑ i, h i) / completeUnmarkedFirstMoment u k := by
  have hblocks :
      (∑ i, complementaryProfile k h i) + (∑ i, h i) = ∑ i, k i := by
    simpa [selectedBlockCount] using selectedBlockCount_complement_add k h hprofile
  have hMpos : 0 < completeSignedFirstMoment u k := completeSignedFirstMoment_pos u k
  have h2h : (2 : ℝ) ^ (∑ i, h i) ≠ 0 := by positivity
  have h2k : (2 : ℝ) ^ (∑ i, k i) ≠ 0 := by positivity
  have heq :
      unmarkedDiagonalWeight n u k (complementaryProfile k h) =
        unmarkedFullCornerWeight u k h / completeUnmarkedFirstMoment u k := by
    unfold unmarkedDiagonalWeight unmarkedFullCornerWeight completeUnmarkedFirstMoment
    rw [partialDiagonalWeight_complement_eq_fullCorner_div n u k h hprofile hfullMass,
      ← hblocks, pow_add]
    field_simp [hMpos.ne', h2h, h2k]
  rw [heq]
  have hUpos : 0 < completeUnmarkedFirstMoment u k := by
    unfold completeUnmarkedFirstMoment
    positivity
  exact div_le_div_of_nonneg_right
    (unmarkedFullCornerWeight_le_pow_of_sharp_mu_cap u k h massCap q hq
      hprofile hmass hmuCap)
    hUpos.le

end

end Erdos625HP
