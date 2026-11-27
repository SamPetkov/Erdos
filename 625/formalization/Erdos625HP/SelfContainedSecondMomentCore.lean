import Erdos625HP.CappedAndGeneralRateCertificate

/-!
# Self-contained `G(n, 1/2)` second-moment, stub-pairing, and profile-free entropy core

This module kernel-checks the core combinatorial, algebraic, and analytic
lemmas underlying the self-contained `G(n, 1/2)` second-moment proof (Section 7)
and common-class analysis (Lemma 5.2(i) & Appendix C) of the 15-page manuscript:

1. **Sharp bi-Lipschitz bounds on the realizability cap `θ(δ)` (`Lemma 5.2(i)`):**
   * `capThresholdTheta_biLipschitz_bounds`: for every `δ ∈ [0, x₀]`,
     `(40 / 41) * log 2 * δ ≤ θ(δ) ≤ log 2 * δ`.

2. **Profile-free common-class entropy bound (`Appendix C`, `Lemma 6.1(i)`):**
   * `profileFree_commonClass_entropy_term_le`: for all `0 < y ≤ p ≤ 1`,
     `2 p log p - 2 (p - y) log (p - y) - y log y - y ≤ y log (e / y)`
     with constant `1` and zero lower-bound hypothesis on `p`.

3. **First-moment regularity & cross-edge bounds (`Lemma 7.1`):**
   * `two_rpow_neg_half_alphaZero_sub_one`: exact Bollobás–Erdős center identity
     `2 ^ (-(α₀(n) - 1) / 2) = (2 * log₂ n) / (e * n)` for `1 < n`.
   * `crossEdge_sum_sq_le` and `two_mul_crossEdge_sum_ge`: for `z ≥ 1`, `z ≤ u`,
     and `∑ j : Fin z, x j = u - z`,
     `∑ j, (1 + x j)^2 ≤ (u - z + 1)^2 + (z - 1)` and
     `2 * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (1 + x i) * (1 + x j) ≥ (z - 1) * (2 * u - z)`.

4. **Stub-pairing & overlap-matrix combinatorics (`Lemma 7.2`):**
   * `card_zeroOneMatrices_mul_factorials_le`: the number of `0`–`1` subsets of
     `I × J` with row sums `σ` and column sums `τ` (`∑ σ = ∑ τ = r₁`) times
     `(∏ i, (σ i)!) * (∏ j, (τ j)!)` is at most `r₁!`.
   * `factorial_le_residual_mul_prod_choose`: peeling bound
     `u! ≤ (u - ∑ s, x s)! * ∏ s, ((x s)! * u.choose (x s))` when `∑ s, x s ≤ u`.
   * `transmuted_factorial_ratio_le`: for `1 ≤ n_tr` and `2 * s₂ ≤ n_tr`,
     `((n_tr - s₂)! : ℝ) / (n_tr ! : ℝ) ≤ (n_tr : ℝ) ^ (-(s₂ : ℤ)) * exp (s₂^2 / n_tr)`
     and, for `s₂ = ∑ x ∈ B, x * r x` with `x ≤ n_tr` whenever `r x ≠ 0`, is at
     most `∏ x ∈ B, (exp x / ((x ! : ℝ) * (n_tr.choose x : ℝ))) ^ (r x)`.

5. **Scrambled and similar overlap-range bounds (`Proposition 7.3`):**
   * `scrambledRange_commonClass_sum_le`: summing `∏_{u ∈ U} (2 k_u^2 / μ_a)^{ν_u} / ν_u!`
     over `0 ≤ ν_u ≤ k_u` gives at most `exp (2 * (∑_{u ∈ U} k_u)^2 / μ_a)`.
   * `disjoint_scrambled_extra_pairs_ge`: if `s` pairwise disjoint parts each
     meet at least `z` members of a pairwise disjoint family `P'`, they contain
     at least `s * z.choose 2` unordered pairs not contained in any member of `P'`.
-/

namespace Erdos625HP

open Erdos625 Filter MeasureTheory Set
open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

/-! ## 1. Auxiliary logarithmic inequalities, bi-Lipschitz `θ(δ)`, and profile-free entropy -/

private theorem one_sub_mul_log_one_sub_add_nonneg {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    0 ≤ (1 - y) * Real.log (1 - y) + y - y ^ 2 / 2 := by
  let h₁ : ℝ → ℝ := fun t ↦ (1 - t) * Real.log (1 - t) + t - t ^ 2 / 2
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt h₁ (-Real.log (1 - t) - t) t := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2]
    have hd_sub : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by ring)
    have hd_mlog : HasDerivAt (fun s : ℝ ↦ (1 - s) * Real.log (1 - s))
        (-Real.log (1 - t) - 1) t := by
      have hmul := hd_sub.mul (hd_sub.log h1t)
      exact hmul.congr_deriv (by field_simp [h1t]; ring)
    have hd_sq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
    exact ((hd_mlog.add (hasDerivAt_id t)).sub hd_sq).congr_deriv (by ring)
  have hcont : ContinuousOn h₁ (Set.Icc 0 y) := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2, hy1]
    exact ((((continuousAt_const.sub continuousAt_id).mul
      ((continuousAt_const.sub continuousAt_id).log h1t)).add continuousAt_id).sub
      ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
  have hmono : MonotoneOn h₁ (Set.Icc 0 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ⟨ht.1, lt_trans ht.2 hy1⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 hy1⟩
      rw [(hderiv t ht01).deriv]
      have hlog : Real.log (1 - t) ≤ -t := by
        have := Real.log_le_sub_one_of_pos (sub_pos.mpr ht01.2)
        linarith
      linarith
  have hh0 : h₁ 0 = 0 := by simp [h₁]
  rw [← hh0]
  exact hmono ⟨le_rfl, hy0⟩ ⟨hy0, le_rfl⟩ hy0

private theorem log_one_sub_add_add_sq_div_two_nonpos {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Real.log (1 - p) + p + p ^ 2 / 2 ≤ 0 := by
  let k : ℝ → ℝ := fun t ↦ Real.log (1 - t) + t + t ^ 2 / 2
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt k (-t ^ 2 / (1 - t)) t := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2]
    have hd_sub : HasDerivAt (fun s : ℝ ↦ 1 - s) (-1) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).congr_deriv (by ring)
    have hd_sq : HasDerivAt (fun s : ℝ ↦ s ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by ring)
    exact (((hd_sub.log h1t).add (hasDerivAt_id t)).add hd_sq).congr_deriv
      (by field_simp [h1t]; ring)
  have hcont : ContinuousOn k (Set.Icc 0 p) := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2, hp1]
    exact ((((continuousAt_const.sub continuousAt_id).log h1t).add continuousAt_id).add
      ((continuousAt_id.pow 2).div_const 2)).continuousWithinAt
  have hanti : AntitoneOn k (Set.Icc 0 p) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 p) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ⟨ht.1, lt_trans ht.2 hp1⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht01 : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht.1, lt_trans ht.2 hp1⟩
      rw [(hderiv t ht01).deriv]
      have hpos : 0 ≤ t ^ 2 / (1 - t) :=
        div_nonneg (sq_nonneg t) (sub_pos.mpr ht01.2).le
      rw [neg_div]
      linarith
  have hk0 : k 0 = 0 := by simp [k]
  rw [← hk0]
  exact hanti ⟨le_rfl, hp0⟩ ⟨hp0, le_rfl⟩ hp0

/-- **Bi-Lipschitz linear bounds on the realizability cap `θ(δ)` (`Lemma 5.2(i)`):**
for every `δ ∈ [0, x₀]`, `(40 / 41) * log 2 * δ ≤ θ(δ) ≤ log 2 * δ`. -/
theorem capThresholdTheta_biLipschitz_bounds {d : ℝ}
    (hd : d ∈ Set.Icc (0 : ℝ) criticalPhaseX0) :
    (40 / 41 : ℝ) * Real.log 2 * d ≤ capThresholdTheta d ∧
      capThresholdTheta d ≤ Real.log 2 * d := by
  rcases eq_or_lt_of_le hd.1 with rfl | hd_pos
  · simp [capThresholdTheta]
  · have hd_ioc : d ∈ Set.Ioc (0 : ℝ) criticalPhaseX0 := ⟨hd_pos, hd.2⟩
    have htheta_pos : 0 < capThresholdTheta d := by
      unfold capThresholdTheta
      rw [dif_pos hd_ioc]
      exact (existsUnique_capThresholdTheta_pos hd_ioc).choose_spec.1.1.1
    have htheta_lt40 : capThresholdTheta d < 1 / 40 :=
      (capThresholdTheta_lt_one_div_40 hd).2
    have htheta_lt1 : capThresholdTheta d < 1 := lt_trans htheta_lt40 (by norm_num)
    have h_eq : phiInfAux (capThresholdTheta d) = -1 + Real.log 2 / 2 * d := by
      have hshift := phiInfAux_capThresholdTheta_add_target hd_ioc (0 : ℝ)
      have hT0 : FiveSizeEntropyGap.phaseTarget 0 - 1 = 2 / Real.log 2 := by
        unfold FiveSizeEntropyGap.phaseTarget; ring
      rw [hT0] at hshift
      have hcancel : Real.log 2 / 2 * (2 / Real.log 2) = 1 := by
        field_simp [q_pos.ne']
      linarith
    set p := capThresholdTheta d
    have hp1_pos : 0 < 1 - p := sub_pos.mpr htheta_lt1
    have h_lo_g : -1 + p / 2 ≤ phiInfAux p := by
      have hh := one_sub_mul_log_one_sub_add_nonneg htheta_pos.le htheta_lt1
      have hdiv : (-p + p ^ 2 / 2) / p ≤ ((1 - p) * Real.log (1 - p)) / p :=
        div_le_div_of_nonneg_right (by linarith) htheta_pos.le
      unfold phiInfAux
      calc -1 + p / 2 = (-p + p ^ 2 / 2) / p := by field_simp [htheta_pos.ne']
        _ ≤ ((1 - p) * Real.log (1 - p)) / p := hdiv
    have h_hi_g : phiInfAux p ≤ -1 + (41 / 80 : ℝ) * p := by
      have hk := log_one_sub_add_add_sq_div_two_nonpos htheta_pos.le htheta_lt1
      have hlog_le : Real.log (1 - p) ≤ -p - p ^ 2 / 2 := by linarith
      have hfac : 0 < (1 - p) / p := div_pos hp1_pos htheta_pos
      unfold phiInfAux
      rw [mul_div_right_comm]
      calc (1 - p) / p * Real.log (1 - p)
          ≤ (1 - p) / p * (-p - p ^ 2 / 2) := mul_le_mul_of_nonneg_left hlog_le hfac.le
        _ = -1 + p / 2 + p ^ 2 / 2 := by field_simp [htheta_pos.ne']; ring
        _ ≤ -1 + (41 / 80 : ℝ) * p := by
            have hp_sq : p ^ 2 ≤ (1 / 40 : ℝ) * p := by
              nlinarith [htheta_pos, htheta_lt40]
            linarith
    constructor <;> linarith

/-- **Profile-free common-class entropy inequality (`Appendix C`, `Lemma 6.1(i)`):**
for all `0 < y ≤ p ≤ 1`,
`2 p log p - 2 (p - y) log (p - y) - y log y - y ≤ y log (e / y)`. -/
theorem profileFree_commonClass_entropy_term_le {y p : ℝ}
    (hy0 : 0 < y) (hyp : y ≤ p) (hp1 : p ≤ 1) :
    2 * p * Real.log p - 2 * (p - y) * Real.log (p - y) - y * Real.log y - y ≤
      y * Real.log (Real.exp 1 / y) := by
  let ψ : ℝ → ℝ := fun t ↦ 2 * (t * Real.log t) - 2 * ((t - y) * Real.log (t - y))
  have hcont : ContinuousOn ψ (Set.Icc y 1) := by
    have hc1 : Continuous (fun t : ℝ ↦ 2 * (t * Real.log t)) :=
      continuous_const.mul Real.continuous_mul_log
    have hc2 : Continuous (fun t : ℝ ↦ 2 * ((t - y) * Real.log (t - y))) :=
      continuous_const.mul (Real.continuous_mul_log.comp (continuous_id.sub continuous_const))
    exact (hc1.sub hc2).continuousOn
  have hderiv : ∀ t ∈ Set.Ioo y 1,
      HasDerivAt ψ (2 * (Real.log t - Real.log (t - y))) t := by
    intro t ht
    have ht0 : t ≠ 0 := (lt_trans hy0 ht.1).ne'
    have hty0 : t - y ≠ 0 := (sub_pos.mpr ht.1).ne'
    have hd1 : HasDerivAt (fun s : ℝ ↦ s * Real.log s) (Real.log t + 1) t :=
      Real.hasDerivAt_mul_log ht0
    have hd_sub : HasDerivAt (fun s : ℝ ↦ s - y) 1 t :=
      ((hasDerivAt_id t).sub (hasDerivAt_const t y)).congr_deriv (by ring)
    have hd2 : HasDerivAt (fun s : ℝ ↦ (s - y) * Real.log (s - y))
        (Real.log (t - y) + 1) t := by
      have hmul := hd_sub.mul (hd_sub.log hty0)
      exact hmul.congr_deriv (by field_simp [hty0])
    exact ((hd1.const_mul 2).sub (hd2.const_mul 2)).congr_deriv (by ring)
  have hmono : MonotoneOn ψ (Set.Icc y 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y 1) hcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t ht).deriv]
      have hle : Real.log (t - y) ≤ Real.log t :=
        Real.log_le_log (sub_pos.mpr ht.1) (by linarith)
      linarith
  have hψ_le : ψ p ≤ ψ 1 := hmono ⟨hyp, hp1⟩ ⟨hyp.trans hp1, le_rfl⟩ hp1
  have hψ1 : ψ 1 = -2 * ((1 - y) * Real.log (1 - y)) := by simp [ψ]
  have hrhs : y * Real.log (Real.exp 1 / y) = y - y * Real.log y := by
    rw [Real.log_div (Real.exp_pos 1).ne' hy0.ne', Real.log_exp]
    ring
  rw [hrhs]
  have hlhs : 2 * p * Real.log p - 2 * (p - y) * Real.log (p - y) - y * Real.log y - y =
      ψ p - y * Real.log y - y := by
    dsimp [ψ]; ring
  rw [hlhs]
  rcases eq_or_lt_of_le (hyp.trans hp1) with rfl | hy_lt1
  · simp [ψ] at hψ_le ⊢
    rcases le_antisymm hp1 hyp with rfl
    simp
  · have hh1 := one_sub_mul_log_one_sub_add_nonneg hy0.le hy_lt1
    have hsq : 0 ≤ y ^ 2 / 2 := div_nonneg (sq_nonneg y) (by norm_num)
    linarith [hψ_le, hψ1, hh1, hsq]

/-! ## 2. First-moment regularity & cross-edge bounds (`Lemma 7.1`) -/

/-- **Exact Bollobás–Erdős center identity (`Lemma 7.1`, from `(2.1)`):**
for every natural number `n` with `1 < n`,
`(2 : ℝ) ^ (-(alphaZero n - 1) / 2) = (2 * logBaseTwo n) / (exp 1 * n)`. -/
theorem two_rpow_neg_half_alphaZero_sub_one {n : ℕ} (hn : 1 < n) :
    (2 : ℝ) ^ (-(alphaZero n - 1) / 2) =
      (2 * logBaseTwo (n : ℝ)) / (Real.exp 1 * (n : ℝ)) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one hn1
  have hlb_pos : 0 < logBaseTwo (n : ℝ) := by
    unfold logBaseTwo
    exact div_pos (Real.log_pos hn1) q_pos
  have hexp_pos : 0 < Real.exp 1 / 2 := div_pos (Real.exp_pos 1) two_pos
  have h_exp_arg :
      Real.log 2 * (-(alphaZero n - 1) / 2) =
        Real.log (logBaseTwo (n : ℝ)) - Real.log (n : ℝ) - Real.log (Real.exp 1 / 2) := by
    unfold alphaZero logBaseTwo q
    field_simp [q_pos.ne']
    ring
  rw [Real.rpow_def_of_pos two_pos, h_exp_arg]
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hlb_pos, Real.exp_log hn_pos,
    Real.exp_log hexp_pos]
  field_simp [hn_pos.ne', (Real.exp_pos 1).ne']

private theorem finset_sum_sq_le_sq_sum {α : Type*} (s : Finset α) (f : α → ℕ) :
    ∑ a ∈ s, (f a) ^ 2 ≤ (∑ a ∈ s, f a) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
    rw [Finset.sum_insert hxs, Finset.sum_insert hxs]
    have hmul : 0 ≤ 2 * f x * ∑ a ∈ s, f a := Nat.zero_le _
    nlinarith

/-- **Sum-of-squares upper bound for `z`-composed `u`-sets (`Lemma 7.1`):**
if `1 ≤ z ≤ u` and `∑ j : Fin z, x j = u - z`, then
`∑ j : Fin z, (1 + x j)^2 ≤ (u - z + 1)^2 + (z - 1)`. -/
theorem crossEdge_sum_sq_le {z u : ℕ} (hz1 : 1 ≤ z) (hzu : z ≤ u)
    (x : Fin z → ℕ) (hx : ∑ j : Fin z, x j = u - z) :
    ∑ j : Fin z, (1 + x j) ^ 2 ≤ (u - z + 1) ^ 2 + (z - 1) := by
  have hexp : ∑ j : Fin z, (1 + x j) ^ 2 =
      z + 2 * (∑ j : Fin z, x j) + ∑ j : Fin z, (x j) ^ 2 := by
    have hpt : ∀ j : Fin z, (1 + x j) ^ 2 = 1 + 2 * x j + (x j) ^ 2 := fun j ↦ by ring
    simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hsq : ∑ j : Fin z, (x j) ^ 2 ≤ (u - z) ^ 2 := by
    rw [← hx]
    exact finset_sum_sq_le_sq_sum Finset.univ x
  rw [hexp, hx]
  zify [hz1, hzu] at hsq ⊢
  nlinarith

/-- **Cross-class edge lower bound for `z`-composed `u`-sets (`Lemma 7.1`):**
if `1 ≤ z ≤ u` and `∑ j : Fin z, x j = u - z`, then twice the number of
cross-class pairs satisfies
`2 * ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (1 + x i) * (1 + x j) ≥ (z - 1) * (2 * u - z)`. -/
theorem two_mul_crossEdge_sum_ge {z u : ℕ} (hz1 : 1 ≤ z) (hzu : z ≤ u)
    (x : Fin z → ℕ) (hx : ∑ j : Fin z, x j = u - z) :
    (z - 1) * (2 * u - z) ≤
      2 * ∑ i : Fin z, ∑ j ∈ Finset.univ.filter (fun j : Fin z ↦ i < j),
        (1 + x i) * (1 + x j) := by
  let y : Fin z → ℕ := fun j ↦ 1 + x j
  have hy_sum : ∑ j : Fin z, y j = u := by
    dsimp [y]
    rw [Finset.sum_add_distrib, hx]
    simp [Nat.add_sub_of_le hzu]
  have h_all : (∑ j : Fin z, y j) ^ 2 =
      (∑ j : Fin z, (y j) ^ 2) +
        2 * ∑ i : Fin z, ∑ j ∈ Finset.univ.filter (fun j : Fin z ↦ i < j), y i * y j := by
    rw [sq, Finset.sum_mul_sum]
    have hsplit : ∀ i : Fin z,
        ∑ j : Fin z, y i * y j =
          y i * y i +
            (∑ j ∈ Finset.univ.filter (fun j : Fin z ↦ i < j), y i * y j) +
            (∑ j ∈ Finset.univ.filter (fun j : Fin z ↦ j < i), y i * y j) := by
      intro i
      have h1 : (Finset.univ : Finset (Fin z)) =
          insert i ((Finset.univ.filter (fun j : Fin z ↦ i < j)) ∪
            (Finset.univ.filter (fun j : Fin z ↦ j < i))) := by
        ext j; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_union,
          Finset.mem_filter, true_and, true_iff]
        rcases lt_trichotomy i j with hij | rfl | hji
        · exact Or.inr (Or.inl hij)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hji)
      have hdisj1 : i ∉ (Finset.univ.filter (fun j : Fin z ↦ i < j)) ∪
          (Finset.univ.filter (fun j : Fin z ↦ j < i)) := by simp
      have hdisj2 : Disjoint (Finset.univ.filter (fun j : Fin z ↦ i < j))
          (Finset.univ.filter (fun j : Fin z ↦ j < i)) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
        exact lt_asymm hj1 hj2
      conv_lhs => rw [h1]
      rw [Finset.sum_insert hdisj1, Finset.sum_union hdisj2, add_assoc]
    simp_rw [hsplit, Finset.sum_add_distrib]
    have hsymm :
        (∑ i : Fin z, ∑ j ∈ Finset.univ.filter (fun j : Fin z ↦ j < i), y i * y j) =
          ∑ i : Fin z, ∑ j ∈ Finset.univ.filter (fun j : Fin z ↦ i < j), y i * y j := by
      trans ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin z × Fin z ↦ p.2 < p.1),
          y p.1 * y p.2
      · rw [Finset.sum_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_filter]
      · trans ∑ p ∈ (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin z × Fin z ↦ p.1 < p.2),
            y p.1 * y p.2
        · refine Finset.sum_equiv (Equiv.prodComm (Fin z) (Fin z)) ?_ ?_
          · intro p; simp [Equiv.prodComm]
          · intro p _; simp [Equiv.prodComm, mul_comm]
        · rw [Finset.sum_filter, Finset.sum_product]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_filter]
    have hdiag : ∑ i : Fin z, y i * y i = ∑ i : Fin z, (y i) ^ 2 :=
      Finset.sum_congr rfl fun i _ ↦ (sq (y i)).symm
    rw [hdiag, hsymm]
    ring
  have hsq_le := crossEdge_sum_sq_le hz1 hzu x hx
  have h2u : z ≤ 2 * u := le_trans hzu (Nat.le_mul_of_pos_left u two_pos)
  zify [hz1, hzu, h2u] at h_all hsq_le hy_sum ⊢
  rw [hy_sum] at h_all
  dsimp [y] at h_all
  linarith

/-! ## 3. Stub-pairing & overlap-matrix combinatorics (`Lemma 7.2`) -/

/-- `0`–`1` matrices (represented as subsets `A ⊆ I × J`) with prescribed row
sums `σ` and column sums `τ`. -/
def zeroOneMatricesWithMargins {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (σ : I → ℕ) (τ : J → ℕ) : Finset (Finset (I × J)) :=
  Finset.univ.filter fun A ↦
    (∀ i : I, (A.filter fun p ↦ p.1 = i).card = σ i) ∧
    (∀ j : J, (A.filter fun p ↦ p.2 = j).card = τ j)

/-- **Stub-pairing upper bound for `0`–`1` matrices (`Lemma 7.2`):**
when `∑ i, σ i = r₁` and `∑ j, τ j = r₁`, the number of `0`–`1` subsets of `I × J`
with row sums `σ` and column sums `τ`, multiplied by `(∏ i, (σ i)!) * (∏ j, (τ j)!)`,
is at most `r₁!`. -/
theorem card_zeroOneMatrices_mul_factorials_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (σ : I → ℕ) (τ : J → ℕ) (r₁ : ℕ)
    (hσ : ∑ i : I, σ i = r₁) (hτ : ∑ j : J, τ j = r₁) :
    (zeroOneMatricesWithMargins σ τ).card *
      (∏ i : I, (σ i).factorial) * (∏ j : J, (τ j).factorial) ≤ r₁.factorial := by
  let RowStub := Σ i : I, Fin (σ i)
  let ColStub := Σ j : J, Fin (τ j)
  let Witness :=
    Σ M : zeroOneMatricesWithMargins σ τ,
      (∀ i : I, Fin (σ i) ≃ ↥(M.1.filter fun p ↦ p.1 = i)) ×
      (∀ j : J, Fin (τ j) ≃ ↥(M.1.filter fun p ↦ p.2 = j))
  have hRowCard : Fintype.card RowStub = r₁ := by
    simp [RowStub, Fintype.card_sigma, hσ]
  have hColCard : Fintype.card ColStub = r₁ := by
    simp [ColStub, Fintype.card_sigma, hτ]
  have hEquivCard : Fintype.card (RowStub ≃ ColStub) = r₁.factorial := by
    have eR : RowStub ≃ Fin r₁ := Fintype.equivFinOfCardEq hRowCard
    have eC : ColStub ≃ Fin r₁ := Fintype.equivFinOfCardEq hColCard
    have ePerm : (RowStub ≃ ColStub) ≃ Equiv.Perm (Fin r₁) :=
      Equiv.equivCongr eR eC
    rw [Fintype.card_congr ePerm, Fintype.card_perm, Fintype.card_fin]
  have hWitCard :
      Fintype.card Witness =
        (zeroOneMatricesWithMargins σ τ).card *
          (∏ i : I, (σ i).factorial) * (∏ j : J, (τ j).factorial) := by
    have hFib : ∀ M : zeroOneMatricesWithMargins σ τ,
        Fintype.card
          ((∀ i : I, Fin (σ i) ≃ ↥(M.1.filter fun p ↦ p.1 = i)) ×
            (∀ j : J, Fin (τ j) ≃ ↥(M.1.filter fun p ↦ p.2 = j))) =
          (∏ i : I, (σ i).factorial) * (∏ j : J, (τ j).factorial) := by
      intro M
      have hM := (Finset.mem_filter.mp M.2).2
      rw [Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
      congr 1
      · refine Finset.prod_congr rfl fun i _ ↦ ?_
        have hc : Fintype.card ↥(M.1.filter fun p ↦ p.1 = i) = σ i := by
          rw [Fintype.card_coe, hM.1 i]
        have e : ↥(M.1.filter fun p ↦ p.1 = i) ≃ Fin (σ i) :=
          Fintype.equivFinOfCardEq hc
        rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) e),
          Fintype.card_perm, Fintype.card_fin]
      · refine Finset.prod_congr rfl fun j _ ↦ ?_
        have hc : Fintype.card ↥(M.1.filter fun p ↦ p.2 = j) = τ j := by
          rw [Fintype.card_coe, hM.2 j]
        have e : ↥(M.1.filter fun p ↦ p.2 = j) ≃ Fin (τ j) :=
          Fintype.equivFinOfCardEq hc
        rw [Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) e),
          Fintype.card_perm, Fintype.card_fin]
    dsimp [Witness]
    rw [Fintype.card_sigma]
    simp_rw [hFib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, mul_assoc]
  let rowEquiv : ∀ (M : zeroOneMatricesWithMargins σ τ)
      (_α : ∀ i : I, Fin (σ i) ≃ ↥(M.1.filter fun p ↦ p.1 = i)),
      RowStub ≃ ↥M.1 := fun M α ↦
    { toFun := fun x ↦ ⟨(α x.1 x.2).1, (Finset.mem_filter.mp (α x.1 x.2).2).1⟩
      invFun := fun p ↦ ⟨p.1.1, (α p.1.1).symm ⟨p.1, Finset.mem_filter.mpr ⟨p.2, rfl⟩⟩⟩
      left_inv := fun ⟨i, k⟩ ↦ by
        have hi : (α i k).1.1 = i := (Finset.mem_filter.mp (α i k).2).2
        have haux : ∀ (i' : I) (_h : i' = i)
            (hq : (α i k).1 ∈ M.1.filter fun p ↦ p.1 = i'),
            (⟨i', (α i').symm ⟨(α i k).1, hq⟩⟩ : RowStub) = ⟨i, k⟩ := by
          rintro _ rfl hq
          simp
        exact haux (α i k).1.1 hi _
      right_inv := fun p ↦ by
        apply Subtype.ext
        change ((α p.1.1) ((α p.1.1).symm ⟨p.1, Finset.mem_filter.mpr ⟨p.2, rfl⟩⟩)).1 = p.1
        exact congrArg Subtype.val
          ((α p.1.1).apply_symm_apply ⟨p.1, Finset.mem_filter.mpr ⟨p.2, rfl⟩⟩) }
  let colEquiv : ∀ (M : zeroOneMatricesWithMargins σ τ)
      (_β : ∀ j : J, Fin (τ j) ≃ ↥(M.1.filter fun p ↦ p.2 = j)),
      ColStub ≃ ↥M.1 := fun M β ↦
    { toFun := fun y ↦ ⟨(β y.1 y.2).1, (Finset.mem_filter.mp (β y.1 y.2).2).1⟩
      invFun := fun p ↦ ⟨p.1.2, (β p.1.2).symm ⟨p.1, Finset.mem_filter.mpr ⟨p.2, rfl⟩⟩⟩
      left_inv := fun ⟨j, l⟩ ↦ by
        have hj : (β j l).1.2 = j := (Finset.mem_filter.mp (β j l).2).2
        have haux : ∀ (j' : J) (_h : j' = j)
            (hq : (β j l).1 ∈ M.1.filter fun p ↦ p.2 = j'),
            (⟨j', (β j').symm ⟨(β j l).1, hq⟩⟩ : ColStub) = ⟨j, l⟩ := by
          rintro _ rfl hq
          simp
        exact haux (β j l).1.2 hj _
      right_inv := fun p ↦ by
        apply Subtype.ext
        change ((β p.1.2) ((β p.1.2).symm ⟨p.1, Finset.mem_filter.mpr ⟨p.2, rfl⟩⟩)).1 = p.1
        exact congrArg Subtype.val
          ((β p.1.2).apply_symm_apply ⟨p.1, Finset.mem_filter.mpr ⟨p.2, rfl⟩⟩) }
  let Φ : Witness → (RowStub ≃ ColStub) := fun w ↦
    (rowEquiv w.1 w.2.1).trans (colEquiv w.1 w.2.2).symm
  have hΦ_alpha : ∀ (w : Witness) (i : I) (k : Fin (σ i)),
      (w.2.1 i k).1 = (i, (Φ w ⟨i, k⟩).1) := by
    intro w i k
    have hi : (w.2.1 i k).1.1 = i := (Finset.mem_filter.mp (w.2.1 i k).2).2
    have hϕ : (Φ w ⟨i, k⟩).1 = (w.2.1 i k).1.2 := rfl
    exact Prod.ext hi hϕ.symm
  have hΦ_beta : ∀ (w : Witness) (j : J) (l : Fin (τ j)),
      (w.2.2 j l).1 = (((Φ w).symm ⟨j, l⟩).1, j) := by
    intro w j l
    have hj : (w.2.2 j l).1.2 = j := (Finset.mem_filter.mp (w.2.2 j l).2).2
    have hϕ : ((Φ w).symm ⟨j, l⟩).1 = (w.2.2 j l).1.1 := rfl
    exact Prod.ext hϕ.symm hj
  have hΦ_inj : Function.Injective Φ := by
    intro ⟨M₁, α₁, β₁⟩ ⟨M₂, α₂, β₂⟩ hEq
    have hM_val : M₁.1 = M₂.1 := by
      ext p
      constructor
      · intro hp
        let x := (rowEquiv M₁ α₁).symm ⟨p, hp⟩
        have hx : (rowEquiv M₁ α₁ x).1 = p :=
          congrArg Subtype.val ((rowEquiv M₁ α₁).apply_symm_apply ⟨p, hp⟩)
        have h1 := hΦ_alpha ⟨M₁, α₁, β₁⟩ x.1 x.2
        have h2 := hΦ_alpha ⟨M₂, α₂, β₂⟩ x.1 x.2
        rw [hEq] at h1
        have hp_eq : p = (α₂ x.1 x.2).1 := by
          calc p = (α₁ x.1 x.2).1 := hx.symm
            _ = (x.1, (Φ ⟨M₂, α₂, β₂⟩ ⟨x.1, x.2⟩).1) := h1
            _ = (α₂ x.1 x.2).1 := h2.symm
        rw [hp_eq]
        exact (Finset.mem_filter.mp (α₂ x.1 x.2).2).1
      · intro hp
        let x := (rowEquiv M₂ α₂).symm ⟨p, hp⟩
        have hx : (rowEquiv M₂ α₂ x).1 = p :=
          congrArg Subtype.val ((rowEquiv M₂ α₂).apply_symm_apply ⟨p, hp⟩)
        have h1 := hΦ_alpha ⟨M₁, α₁, β₁⟩ x.1 x.2
        have h2 := hΦ_alpha ⟨M₂, α₂, β₂⟩ x.1 x.2
        rw [hEq] at h1
        have hp_eq : p = (α₁ x.1 x.2).1 := by
          calc p = (α₂ x.1 x.2).1 := hx.symm
            _ = (x.1, (Φ ⟨M₂, α₂, β₂⟩ ⟨x.1, x.2⟩).1) := h2
            _ = (α₁ x.1 x.2).1 := h1.symm
        rw [hp_eq]
        exact (Finset.mem_filter.mp (α₁ x.1 x.2).2).1
    have hM : M₁ = M₂ := Subtype.ext hM_val
    subst hM
    congr 1
    refine Prod.ext ?_ ?_
    · funext i; apply Equiv.ext; intro k; apply Subtype.ext
      have h1 := hΦ_alpha ⟨M₁, α₁, β₁⟩ i k
      have h2 := hΦ_alpha ⟨M₁, α₂, β₂⟩ i k
      rw [hEq] at h1
      exact h1.trans h2.symm
    · funext j; apply Equiv.ext; intro l; apply Subtype.ext
      have h1 := hΦ_beta ⟨M₁, α₁, β₁⟩ j l
      have h2 := hΦ_beta ⟨M₁, α₂, β₂⟩ j l
      rw [hEq] at h1
      exact h1.trans h2.symm
  rw [← hWitCard, ← hEquivCard]
  exact Fintype.card_le_of_injective Φ hΦ_inj

/-- **Peeling factorial inequality (`Lemma 7.2`):**
for `∑ s : Fin m, x s ≤ u`,
`u! ≤ (u - ∑ s, x s)! * ∏ s, ((x s)! * u.choose (x s))`. -/
theorem factorial_le_residual_mul_prod_choose :
    ∀ {m : ℕ} (u : ℕ) (x : Fin m → ℕ), (∑ s : Fin m, x s) ≤ u →
      u.factorial ≤
        (u - ∑ s : Fin m, x s).factorial *
          ∏ s : Fin m, ((x s).factorial * u.choose (x s))
  | 0, u, _, _ => by simp
  | m + 1, u, x, hsum => by
    rw [Fin.sum_univ_succ] at hsum
    have hx0 : x 0 ≤ u := le_trans (Nat.le_add_right _ _) hsum
    have htail : (∑ i : Fin m, x i.succ) ≤ u - x 0 :=
      Nat.le_sub_of_add_le' hsum
    have ih := factorial_le_residual_mul_prod_choose (u - x 0) (fun i ↦ x i.succ) htail
    have hstep : u.factorial = (u - x 0).factorial * ((x 0).factorial * u.choose (x 0)) := by
      have h := Nat.choose_mul_factorial_mul_factorial hx0
      linarith [show u.choose (x 0) * (x 0).factorial * (u - x 0).factorial =
        (u - x 0).factorial * ((x 0).factorial * u.choose (x 0)) by ring]
    have hmono :
        ∏ i : Fin m, ((x i.succ).factorial * (u - x 0).choose (x i.succ)) ≤
          ∏ i : Fin m, ((x i.succ).factorial * u.choose (x i.succ)) :=
      Finset.prod_le_prod' fun i _ ↦
        Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (Nat.sub_le u (x 0)))
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, ← Nat.sub_sub]
    calc u.factorial
        = (u - x 0).factorial * ((x 0).factorial * u.choose (x 0)) := hstep
      _ ≤ ((u - x 0 - ∑ i : Fin m, x i.succ).factorial *
            ∏ i : Fin m, ((x i.succ).factorial * (u - x 0).choose (x i.succ))) *
            ((x 0).factorial * u.choose (x 0)) := Nat.mul_le_mul_right _ ih
      _ ≤ ((u - x 0 - ∑ i : Fin m, x i.succ).factorial *
            ∏ i : Fin m, ((x i.succ).factorial * u.choose (x i.succ))) *
            ((x 0).factorial * u.choose (x 0)) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hmono)
      _ = (u - x 0 - ∑ i : Fin m, x i.succ).factorial *
            (((x 0).factorial * u.choose (x 0)) *
              ∏ i : Fin m, ((x i.succ).factorial * u.choose (x i.succ))) := by ring

private theorem factorial_eq_residual_mul_descProd :
    ∀ (n k : ℕ), k ≤ n →
      (n.factorial : ℝ) = ((n - k).factorial : ℝ) * ∏ j ∈ Finset.range k, (n - j : ℝ)
  | n, 0, _ => by simp
  | n, k + 1, hk => by
    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have ih := factorial_eq_residual_mul_descProd n k hk'
    have hsub : n - k = (n - (k + 1)) + 1 := by omega
    have hfac : ((n - k).factorial : ℝ) =
        ((n - (k + 1)).factorial : ℝ) * (n - k : ℝ) := by
      rw [hsub, Nat.factorial_succ]
      push_cast
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := Nat.cast_sub hk'
      have hsub_cast : (((n - (k + 1) : ℕ) : ℝ) + 1) = (n : ℝ) - (k : ℝ) := by
        have := congrArg (Nat.cast (R := ℝ)) hsub
        push_cast at this
        linarith
      rw [hsub_cast]
      ring
    rw [ih, hfac, Finset.prod_range_succ]
    ring

/-- **Singleton-to-transmuted factorial ratio bound (`Lemma 7.2`):**
for `1 ≤ n_tr`, `2 * s₂ ≤ n_tr`, and `s₂ = ∑ x ∈ B, x * r x` with `x ≤ n_tr`
whenever `r x ≠ 0`,
`((n_tr - s₂)! : ℝ) / (n_tr ! : ℝ) ≤ (n_tr : ℝ) ^ (-(s₂ : ℤ)) * exp (s₂^2 / n_tr)
  ≤ ∏ x ∈ B, (exp x / ((x ! : ℝ) * (n_tr.choose x : ℝ))) ^ (r x)`. -/
theorem transmuted_factorial_ratio_le {n_tr s₂ : ℕ} (hn_pos : 1 ≤ n_tr)
    (hs₂ : 2 * s₂ ≤ n_tr) (B : Finset ℕ) (r : ℕ → ℕ)
    (hs₂_eq : s₂ = ∑ x ∈ B, x * r x)
    (hx_le : ∀ x ∈ B, r x ≠ 0 → x ≤ n_tr) :
    (((n_tr - s₂).factorial : ℝ) / (n_tr.factorial : ℝ) ≤
      ((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ))) ∧
    (((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ)) ≤
      ∏ x ∈ B, (Real.exp (x : ℝ) / ((x.factorial : ℝ) * (n_tr.choose x : ℝ))) ^ (r x)) := by
  have hn_real : (0 : ℝ) < (n_tr : ℝ) := by exact_mod_cast hn_pos
  have hs₂_le : s₂ ≤ n_tr := by omega
  constructor
  · have hdecomp := factorial_eq_residual_mul_descProd n_tr s₂ hs₂_le
    have hprod_pos : 0 < ∏ j ∈ Finset.range s₂, (n_tr - j : ℝ) := by
      refine Finset.prod_pos fun j hj ↦ ?_
      rw [Finset.mem_range] at hj
      have hj_le : (j : ℝ) < (n_tr : ℝ) := by exact_mod_cast (lt_of_lt_of_le hj hs₂_le)
      linarith
    have hstep : ∀ j ∈ Finset.range s₂,
        (n_tr : ℝ) * Real.exp (-2 * (j : ℝ) / (n_tr : ℝ)) ≤ (n_tr - j : ℝ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      let y : ℝ := (j : ℝ) / (n_tr : ℝ)
      have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg j) hn_real.le
      have hy_half : y ≤ 1 / 2 := by
        dsimp [y]
        rw [div_le_iff₀ hn_real]
        have : 2 * j < n_tr := by omega
        have hcast : (2 : ℝ) * (j : ℝ) ≤ (n_tr : ℝ) := by exact_mod_cast this.le
        linarith
      have hexp_ge : 1 + 2 * y ≤ Real.exp (2 * y) := by
        linarith [Real.add_one_le_exp (2 * y)]
      have hprod_ge1 : 1 ≤ (1 - y) * Real.exp (2 * y) := by
        have hquad : 1 ≤ (1 - y) * (1 + 2 * y) := by nlinarith
        exact le_trans hquad (mul_le_mul_of_nonneg_left hexp_ge (by linarith))
      have hinv : Real.exp (-2 * y) ≤ 1 - y := by
        rw [show (-2 : ℝ) * y = -(2 * y) by ring, Real.exp_neg]
        calc (Real.exp (2 * y))⁻¹
            = 1 * (Real.exp (2 * y))⁻¹ := (one_mul _).symm
          _ ≤ ((1 - y) * Real.exp (2 * y)) * (Real.exp (2 * y))⁻¹ :=
              mul_le_mul_of_nonneg_right hprod_ge1 (inv_nonneg.mpr (Real.exp_pos _).le)
          _ = 1 - y := by rw [mul_assoc, mul_inv_cancel₀ (Real.exp_pos _).ne', mul_one]
      have hmul := mul_le_mul_of_nonneg_left hinv hn_real.le
      have hrhs : (n_tr : ℝ) * (1 - y) = (n_tr - j : ℝ) := by
        dsimp [y]; field_simp [hn_real.ne']
      have hlhs : -2 * y = -2 * (j : ℝ) / (n_tr : ℝ) := by dsimp [y]; ring
      rwa [hrhs, hlhs] at hmul
    have hprod_ge :
        ((n_tr : ℝ) ^ s₂) *
          Real.exp (∑ j ∈ Finset.range s₂, (-2 * (j : ℝ) / (n_tr : ℝ))) ≤
          ∏ j ∈ Finset.range s₂, (n_tr - j : ℝ) := by
      rw [Real.exp_sum]
      calc ((n_tr : ℝ) ^ s₂) * ∏ j ∈ Finset.range s₂, Real.exp (-2 * (j : ℝ) / (n_tr : ℝ))
          = ∏ j ∈ Finset.range s₂, ((n_tr : ℝ) * Real.exp (-2 * (j : ℝ) / (n_tr : ℝ))) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        _ ≤ ∏ j ∈ Finset.range s₂, (n_tr - j : ℝ) :=
            Finset.prod_le_prod (fun j _ ↦ mul_nonneg hn_real.le (Real.exp_pos _).le) hstep
    have hsum_neg :
        -(s₂ : ℝ) ^ 2 / (n_tr : ℝ) ≤
          ∑ j ∈ Finset.range s₂, (-2 * (j : ℝ) / (n_tr : ℝ)) := by
      have hsum2 : 2 * ∑ j ∈ Finset.range s₂, (j : ℝ) ≤ (s₂ : ℝ) ^ 2 := by
        have hnat : 2 * ∑ j ∈ Finset.range s₂, j = s₂ * (s₂ - 1) := by
          rw [mul_comm]; exact Finset.sum_range_id_mul_two s₂
        have hle_nat : 2 * ∑ j ∈ Finset.range s₂, j ≤ s₂ * s₂ := by
          rw [hnat]; exact Nat.mul_le_mul_left s₂ (Nat.sub_le s₂ 1)
        have hcast : (2 : ℝ) * ∑ j ∈ Finset.range s₂, (j : ℝ) ≤ (s₂ : ℝ) ^ 2 := by
          have := (Nat.cast_le (α := ℝ)).mpr hle_nat
          push_cast at this
          linarith
        linarith
      have hrew : ∑ j ∈ Finset.range s₂, (-2 * (j : ℝ) / (n_tr : ℝ)) =
          (-2 / (n_tr : ℝ)) * ∑ j ∈ Finset.range s₂, (j : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ by ring
      rw [hrew]
      have hdiv : (2 * ∑ j ∈ Finset.range s₂, (j : ℝ)) / (n_tr : ℝ) ≤
          (s₂ : ℝ) ^ 2 / (n_tr : ℝ) :=
        div_le_div_of_nonneg_right hsum2 hn_real.le
      calc -(s₂ : ℝ) ^ 2 / (n_tr : ℝ)
          = -((s₂ : ℝ) ^ 2 / (n_tr : ℝ)) := neg_div _ _
        _ ≤ -((2 * ∑ j ∈ Finset.range s₂, (j : ℝ)) / (n_tr : ℝ)) := neg_le_neg hdiv
        _ = (-2 / (n_tr : ℝ)) * ∑ j ∈ Finset.range s₂, (j : ℝ) := by ring
    have hprod_ge2 :
        ((n_tr : ℝ) ^ s₂) * Real.exp (-(s₂ : ℝ) ^ 2 / (n_tr : ℝ)) ≤
          ∏ j ∈ Finset.range s₂, (n_tr - j : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsum_neg)
        (pow_nonneg hn_real.le s₂)) hprod_ge
    have hn_fac_pos : (0 : ℝ) < (n_tr.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos n_tr
    rw [div_le_iff₀ hn_fac_pos, hdecomp]
    calc ((n_tr - s₂).factorial : ℝ)
        = ((n_tr - s₂).factorial : ℝ) *
            ((((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ))) *
              (((n_tr : ℝ) ^ s₂) * Real.exp (-(s₂ : ℝ) ^ 2 / (n_tr : ℝ)))) := by
            have hpow_ne : (n_tr : ℝ) ^ s₂ ≠ 0 := pow_ne_zero s₂ hn_real.ne'
            have hexp_mul : Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ)) *
                Real.exp (-(s₂ : ℝ) ^ 2 / (n_tr : ℝ)) = 1 := by
              rw [← Real.exp_add]; simp [neg_div]
            calc ((n_tr - s₂).factorial : ℝ)
                = ((n_tr - s₂).factorial : ℝ) *
                    ((((n_tr : ℝ) ^ s₂)⁻¹ * (n_tr : ℝ) ^ s₂) *
                      (Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ)) *
                        Real.exp (-(s₂ : ℝ) ^ 2 / (n_tr : ℝ)))) := by
                    rw [inv_mul_cancel₀ hpow_ne, hexp_mul, mul_one, mul_one]
              _ = _ := by ring
      _ ≤ ((n_tr - s₂).factorial : ℝ) *
            ((((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ))) *
              ∏ j ∈ Finset.range s₂, (n_tr - j : ℝ)) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hprod_ge2
                (mul_nonneg (inv_nonneg.mpr (pow_nonneg hn_real.le s₂)) (Real.exp_pos _).le))
              (Nat.cast_nonneg _)
      _ = (((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ))) *
            (((n_tr - s₂).factorial : ℝ) * ∏ j ∈ Finset.range s₂, (n_tr - j : ℝ)) := by ring
  · have hs₂_sq_le : (s₂ : ℝ) ^ 2 / (n_tr : ℝ) ≤ (s₂ : ℝ) := by
      rw [div_le_iff₀ hn_real]
      have hcast : (2 : ℝ) * (s₂ : ℝ) ≤ (n_tr : ℝ) := by exact_mod_cast hs₂
      nlinarith [Nat.cast_nonneg (α := ℝ) s₂]
    have hexp_le : Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ)) ≤ Real.exp (s₂ : ℝ) :=
      Real.exp_le_exp.mpr hs₂_sq_le
    have hlhs_eq :
        ((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp (s₂ : ℝ) =
          ∏ x ∈ B, (Real.exp (x : ℝ) / ((n_tr : ℝ) ^ x)) ^ (r x) := by
      have hpow_sum : ∀ (S : Finset ℕ),
          (n_tr : ℝ) ^ (∑ x ∈ S, x * r x) = ∏ x ∈ S, (n_tr : ℝ) ^ (x * r x) := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | @insert a S ha ih => rw [Finset.sum_insert ha, pow_add, Finset.prod_insert ha, ih]
      rw [hs₂_eq, hpow_sum B, ← Finset.prod_inv_distrib]
      have hcast_sum : ((∑ x ∈ B, x * r x : ℕ) : ℝ) = ∑ x ∈ B, (r x : ℝ) * (x : ℝ) := by
        push_cast
        refine Finset.sum_congr rfl fun x _ ↦ mul_comm _ _
      rw [hcast_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      rw [pow_mul, ← inv_pow, Real.exp_nat_mul, div_eq_mul_inv, mul_pow, mul_comm]
    calc ((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp ((s₂ : ℝ) ^ 2 / (n_tr : ℝ))
        ≤ ((n_tr : ℝ) ^ s₂)⁻¹ * Real.exp (s₂ : ℝ) :=
          mul_le_mul_of_nonneg_left hexp_le (inv_nonneg.mpr (pow_nonneg hn_real.le s₂))
      _ = ∏ x ∈ B, (Real.exp (x : ℝ) / ((n_tr : ℝ) ^ x)) ^ (r x) := hlhs_eq
      _ ≤ ∏ x ∈ B,
            (Real.exp (x : ℝ) / ((x.factorial : ℝ) * (n_tr.choose x : ℝ))) ^ (r x) := by
          refine Finset.prod_le_prod
            (fun x _ ↦ pow_nonneg (div_nonneg (Real.exp_pos _).le (pow_nonneg hn_real.le x)) _)
            fun x hxB ↦ ?_
          by_cases hrx : r x = 0
          · simp [hrx]
          · refine pow_le_pow_left₀
              (div_nonneg (Real.exp_pos _).le (pow_nonneg hn_real.le x)) ?_ (r x)
            have hx_n : x ≤ n_tr := hx_le x hxB hrx
            have hdesc_le : x.factorial * n_tr.choose x ≤ n_tr ^ x := by
              rw [← Nat.descFactorial_eq_factorial_mul_choose]
              exact Nat.descFactorial_le_pow n_tr x
            have hdesc_pos : 0 < (x.factorial : ℝ) * (n_tr.choose x : ℝ) := by
              exact_mod_cast Nat.mul_pos (Nat.factorial_pos x) (Nat.choose_pos hx_n)
            exact div_le_div_of_nonneg_left (Real.exp_pos _).le hdesc_pos
              (by exact_mod_cast hdesc_le)

/-! ## 4. Scrambled and similar overlap-range bounds (`Proposition 7.3`) -/

/-- **Scrambled-range common-class box sum bound (`Proposition 7.3`):**
for any finite set `U` of active class sizes, multiplicities `k : ℕ → ℕ`, and `μ_a > 0`,
summing `∏_{u ∈ U} (2 k_u^2 / μ_a)^{ν_u} / ν_u!` over the box `0 ≤ ν_u ≤ k_u`
is bounded by `exp (2 * (∑_{u ∈ U} k_u)^2 / μ_a)`. -/
theorem scrambledRange_commonClass_sum_le (U : Finset ℕ) (k : ℕ → ℕ)
    {μ_a : ℝ} (hμ : 0 < μ_a) :
    (∑ ν : (u : U) → Fin (k u.1 + 1),
      ∏ u : U, ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (ν u : ℕ)) / ((ν u : ℕ).factorial : ℝ)) ≤
      Real.exp (2 * (∑ u ∈ U, (k u : ℝ)) ^ 2 / μ_a) := by
  classical
  have hfact :
      (∑ ν : (u : U) → Fin (k u.1 + 1),
        ∏ u : U, ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (ν u : ℕ)) / ((ν u : ℕ).factorial : ℝ)) =
        ∏ u : U, ∑ m : Fin (k u.1 + 1),
          ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ) :=
    (Fintype.prod_sum fun (u : U) (m : Fin (k u.1 + 1)) ↦
      ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)).symm
  rw [hfact]
  have hterm : ∀ u : U,
      (∑ m : Fin (k u.1 + 1),
        ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)) ≤
        Real.exp (2 * (k u.1 : ℝ) ^ 2 / μ_a) := by
    intro u
    have ha_nn : 0 ≤ 2 * (k u.1 : ℝ) ^ 2 / μ_a :=
      div_nonneg (mul_nonneg two_pos.le (sq_nonneg _)) hμ.le
    have hfin :
        (∑ m : Fin (k u.1 + 1),
          ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)) =
          ∑ m ∈ Finset.range (k u.1 + 1),
            ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ m) / (m.factorial : ℝ) :=
      Fin.sum_univ_eq_sum_range
        (fun m : ℕ ↦ ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ m) / (m.factorial : ℝ)) (k u.1 + 1)
    rw [hfin]
    exact Real.sum_le_exp_of_nonneg ha_nn (k u.1 + 1)
  have hprod_le :
      (∏ u : U, ∑ m : Fin (k u.1 + 1),
        ((2 * (k u.1 : ℝ) ^ 2 / μ_a) ^ (m : ℕ)) / ((m : ℕ).factorial : ℝ)) ≤
        ∏ u : U, Real.exp (2 * (k u.1 : ℝ) ^ 2 / μ_a) := by
    refine Finset.prod_le_prod (fun u _ ↦ ?_) fun u _ ↦ hterm u
    refine Finset.sum_nonneg fun m _ ↦ div_nonneg ?_ (Nat.cast_nonneg _)
    exact pow_nonneg (div_nonneg (mul_nonneg two_pos.le (sq_nonneg _)) hμ.le) _
  rw [← Real.exp_sum] at hprod_le
  refine le_trans hprod_le (Real.exp_le_exp.mpr ?_)
  have hattach :
      (∑ u : U, 2 * (k u.1 : ℝ) ^ 2 / μ_a) =
        (2 / μ_a) * ∑ u ∈ U, (k u : ℝ) ^ 2 := by
    rw [Finset.sum_coe_sort U (fun u ↦ 2 * (k u : ℝ) ^ 2 / μ_a), Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ by ring
  rw [hattach]
  have hsq_nat : ∑ u ∈ U, (k u) ^ 2 ≤ (∑ u ∈ U, k u) ^ 2 :=
    finset_sum_sq_le_sq_sum U k
  have hsq_real : ∑ u ∈ U, (k u : ℝ) ^ 2 ≤ (∑ u ∈ U, (k u : ℝ)) ^ 2 := by
    exact_mod_cast hsq_nat
  have hmul := mul_le_mul_of_nonneg_left hsq_real (div_nonneg two_pos.le hμ.le)
  linarith [show (2 / μ_a) * (∑ u ∈ U, (k u : ℝ)) ^ 2 =
    2 * (∑ u ∈ U, (k u : ℝ)) ^ 2 / μ_a by ring]

/-- **Similar-range disjoint extra-edge lower bound (`Proposition 7.3`):**
if `s` pairwise disjoint vertex subsets `parts i` each meet at least `z` members
of a pairwise disjoint family `P'`, they contribute at least `s * z.choose 2`
unordered vertex pairs that do not lie inside any single member of `P'`. -/
theorem disjoint_scrambled_extra_pairs_ge {V : Type*} [DecidableEq V]
    {s z : ℕ} (parts : Fin s → Finset V)
    (hdisj : Pairwise fun i j ↦ Disjoint (parts i) (parts j))
    (P' : Finset (Finset V))
    (hP' : (P' : Set (Finset V)).PairwiseDisjoint id)
    (hz : ∀ i : Fin s, z ≤ (P'.filter fun W ↦ (parts i ∩ W).Nonempty).card) :
    s * z.choose 2 ≤
      ((Finset.univ.biUnion fun i : Fin s ↦ (parts i).powersetCard 2).filter
        fun e ↦ ∀ W ∈ P', ¬ e ⊆ W).card := by
  have hpair_disj :
      ((Finset.univ : Finset (Fin s)) : Set (Fin s)).PairwiseDisjoint
        fun i ↦ ((parts i).powersetCard 2).filter fun e ↦ ∀ W ∈ P', ¬ e ⊆ W := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro e hei hej
    have hei' := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hei).1
    have hej' := Finset.mem_powersetCard.mp (Finset.mem_filter.mp hej).1
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
    exact Finset.disjoint_left.mp (hdisj hij) (hei'.1 hv) (hej'.1 hv)
  rw [Finset.filter_biUnion, Finset.card_biUnion hpair_disj]
  have h_each : ∀ i : Fin s,
      z.choose 2 ≤
        (((parts i).powersetCard 2).filter fun e ↦ ∀ W ∈ P', ¬ e ⊆ W).card := by
    intro i
    let Q := P'.filter fun W ↦ (parts i ∩ W).Nonempty
    let w : {W // W ∈ Q} → V := fun W ↦ (Finset.mem_filter.mp W.2).2.choose
    have hw_spec : ∀ W : {W // W ∈ Q}, w W ∈ parts i ∩ W.1 :=
      fun W ↦ (Finset.mem_filter.mp W.2).2.choose_spec
    have hw_inj : Function.Injective w := by
      intro W₁ W₂ hEq
      have h1 := (Finset.mem_inter.mp (hw_spec W₁)).2
      have h2 := (Finset.mem_inter.mp (hw_spec W₂)).2
      rw [hEq] at h1
      have hW1P : W₁.1 ∈ P' := (Finset.mem_filter.mp W₁.2).1
      have hW2P : W₂.1 ∈ P' := (Finset.mem_filter.mp W₂.2).1
      by_contra hne
      have hne_val : W₁.1 ≠ W₂.1 := fun h ↦ hne (Subtype.ext h)
      exact Finset.disjoint_left.mp (hP' hW1P hW2P hne_val) h1 h2
    let S : Finset V := Finset.univ.image w
    have hS_sub : S ⊆ parts i := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨W, _, rfl⟩
      exact (Finset.mem_inter.mp (hw_spec W)).1
    have hS_card : z ≤ S.card := by
      have hc : S.card = Q.card := by
        rw [Finset.card_image_of_injective _ hw_inj, Finset.card_univ, Fintype.card_coe]
      rw [hc]
      exact hz i
    have hsub_edges :
        S.powersetCard 2 ⊆
          ((parts i).powersetCard 2).filter fun e ↦ ∀ W ∈ P', ¬ e ⊆ W := by
      intro e he
      rw [Finset.mem_powersetCard] at he
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨he.1.trans hS_sub, he.2⟩, ?_⟩
      intro W hWP heW
      rcases Finset.card_eq_two.mp he.2 with ⟨u₁, u₂, hu_ne, rfl⟩
      have hu₁S : u₁ ∈ S := he.1 (by simp)
      have hu₂S : u₂ ∈ S := he.1 (by simp)
      rcases Finset.mem_image.mp hu₁S with ⟨W₁, _, rfl⟩
      rcases Finset.mem_image.mp hu₂S with ⟨W₂, _, rfl⟩
      have hW₁_ne_W₂ : W₁.1 ≠ W₂.1 := fun h ↦ hu_ne (congrArg w (Subtype.ext h))
      have hw₁W : w W₁ ∈ W := heW (by simp)
      have hw₂W : w W₂ ∈ W := heW (by simp)
      have hw₁W₁ : w W₁ ∈ W₁.1 := (Finset.mem_inter.mp (hw_spec W₁)).2
      have hw₂W₂ : w W₂ ∈ W₂.1 := (Finset.mem_inter.mp (hw_spec W₂)).2
      have hW_eq₁ : W = W₁.1 := by
        by_contra hne₁
        exact Finset.disjoint_left.mp
          (hP' hWP (Finset.mem_filter.mp W₁.2).1 hne₁) hw₁W hw₁W₁
      have hW_eq₂ : W = W₂.1 := by
        by_contra hne₂
        exact Finset.disjoint_left.mp
          (hP' hWP (Finset.mem_filter.mp W₂.2).1 hne₂) hw₂W hw₂W₂
      exact hW₁_ne_W₂ (hW_eq₁.symm.trans hW_eq₂)
    calc z.choose 2
        ≤ S.card.choose 2 := Nat.choose_le_choose 2 hS_card
      _ = (S.powersetCard 2).card := (Finset.card_powersetCard 2 S).symm
      _ ≤ (((parts i).powersetCard 2).filter fun e ↦ ∀ W ∈ P', ¬ e ⊆ W).card :=
          Finset.card_le_card hsub_edges
  calc s * z.choose 2
      = ∑ _i : Fin s, z.choose 2 := by simp
    _ ≤ ∑ i : Fin s,
          (((parts i).powersetCard 2).filter fun e ↦ ∀ W ∈ P', ¬ e ⊆ W).card :=
        Finset.sum_le_sum fun i _ ↦ h_each i

end

end Erdos625HP
