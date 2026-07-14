import Erdos625.ColoringProfileDeficitMomentConvergence
import Erdos625.UniformSeriesConvergenceTools

/-!
# Uniform convergence of the finite deficit moments

This module upgrades the fixed-tilt limits to uniform convergence on every
bounded closed tilt interval.  It treats the natural series and exceptional
atom separately and records uniform limits for the partition and first two
unnormalized moments.  No optimizer-tilt bound is asserted.
-/

namespace Erdos625

open Filter Set
open scoped BigOperators Topology

noncomputable section

/-! ## Uniform convergence on bounded tilt intervals -/

/-- The fixed-coordinate convergence is uniform in the tilt on every bounded
closed interval. -/
theorem tendstoUniformlyOn_profileDeficitNaturalTerm
    (M : ℝ) (d : ℕ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitNaturalTerm alpha lambda d)
      (fun lambda ↦
        extendedGaussianNaturalTerm (Real.log 2) lambda d)
      atTop (Icc (-M) M) := by
  have hr :
      Tendsto
        (fun alpha : ℕ ↦
          (Real.log (alpha.descFactorial d : ℝ) -
              (d : ℝ) * Real.log (alpha : ℝ)) -
            q / 2 * (d : ℝ) ^ 2)
        atTop
        (𝓝 (-(q / 2 * (d : ℝ) ^ 2))) := by
    simpa using
      (tendsto_log_descFactorial_sub_mul_log d).sub_const
        (q / 2 * (d : ℝ) ^ 2)
  have h := tendstoUniformlyOn_exp_affine_add_of_tendsto
    (M := M) hr d
  refine (h.congr ?_).congr_right ?_
  · filter_upwards [eventually_gt_atTop d] with alpha halpha
    intro lambda _
    change
      Real.exp
          (lambda * (d : ℝ) +
            (Real.log (alpha.descFactorial d : ℝ) -
                (d : ℝ) * Real.log (alpha : ℝ) -
              q / 2 * (d : ℝ) ^ 2)) =
        profileDeficitNaturalTerm alpha lambda d
    rw [profileDeficitNaturalTerm_eq_of_lt alpha lambda d halpha]
    congr 1
    ring
  · intro lambda _
    change
      Real.exp (lambda * (d : ℝ) + -(q / 2 * (d : ℝ) ^ 2)) =
        Real.exp
          (lambda * (d : ℝ) - Real.log 2 / 2 * (d : ℝ) ^ 2)
    unfold q
    congr 1

/-- Multiplication by a fixed real scalar preserves uniform convergence. -/
theorem tendstoUniformlyOn_const_mul_real
    {X : Type*} {K : Set X} {F : ℕ → X → ℝ} {f : X → ℝ}
    (h : TendstoUniformlyOn F f atTop K) (c : ℝ) :
    TendstoUniformlyOn
      (fun n x ↦ c * F n x) (fun x ↦ c * f x) atTop K := by
  by_cases hc : c = 0
  · subst c
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).tendstoUniformlyOn_const K
  · rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro eps heps
    have habs : 0 < |c| := abs_pos.mpr hc
    have hE := h (eps / |c|) (div_pos heps habs)
    filter_upwards [hE] with n hn
    intro x hx
    have hnx := hn x hx
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    rw [Real.dist_eq] at hnx
    calc
      |c| * |f x - F n x| < |c| * (eps / |c|) :=
        mul_lt_mul_of_pos_left hnx habs
      _ = eps := by field_simp

/-- Multiplication by the first-moment coordinate preserves the uniform
fixed-coordinate convergence. -/
theorem tendstoUniformlyOn_profileDeficitNaturalFirstMomentTerm
    (M : ℝ) (d : ℕ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦
        (d : ℝ) * profileDeficitNaturalTerm alpha lambda d)
      (fun lambda ↦
        (d : ℝ) *
          extendedGaussianNaturalTerm (Real.log 2) lambda d)
      atTop (Icc (-M) M) := by
  exact tendstoUniformlyOn_const_mul_real
    (tendstoUniformlyOn_profileDeficitNaturalTerm M d) (d : ℝ)

/-- Multiplication by the second-moment coordinate preserves the uniform
fixed-coordinate convergence. -/
theorem tendstoUniformlyOn_profileDeficitNaturalSecondMomentTerm
    (M : ℝ) (d : ℕ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦
        (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d)
      (fun lambda ↦
        (d : ℝ) ^ 2 *
          extendedGaussianNaturalTerm (Real.log 2) lambda d)
      atTop (Icc (-M) M) := by
  exact tendstoUniformlyOn_const_mul_real
    (tendstoUniformlyOn_profileDeficitNaturalTerm M d) ((d : ℝ) ^ 2)

/-- On `[-M,M]`, every finite natural term is dominated by the limiting term
at the endpoint tilt `M`. -/
theorem norm_profileDeficitNaturalTerm_le_at_upper_tilt
    (alpha d : ℕ) {lambda M : ℝ} (hlambda : lambda ∈ Icc (-M) M) :
    ‖profileDeficitNaturalTerm alpha lambda d‖ ≤
      extendedGaussianNaturalTerm (Real.log 2) M d := by
  refine (norm_profileDeficitNaturalTerm_le_extendedGaussianNaturalTerm
    alpha lambda d).trans ?_
  rw [extendedGaussianNaturalTerm, extendedGaussianNaturalTerm]
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_right hlambda.2 (Nat.cast_nonneg d)) _

/-- The same endpoint term dominates every limiting natural term on the
bounded interval. -/
theorem norm_extendedGaussianNaturalTerm_le_at_upper_tilt
    (d : ℕ) {lambda M : ℝ} (hlambda : lambda ∈ Icc (-M) M) :
    ‖extendedGaussianNaturalTerm (Real.log 2) lambda d‖ ≤
      extendedGaussianNaturalTerm (Real.log 2) M d := by
  rw [Real.norm_eq_abs,
    abs_of_pos (extendedGaussianNaturalTerm_pos (Real.log 2) lambda d)]
  rw [extendedGaussianNaturalTerm, extendedGaussianNaturalTerm]
  apply Real.exp_le_exp.mpr
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_right hlambda.2 (Nat.cast_nonneg d)) _

/-- Uniform convergence of the totalized natural mass series. -/
theorem tendstoUniformlyOn_tsum_profileDeficitNaturalTerm (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦
        ∑' d : ℕ, profileDeficitNaturalTerm alpha lambda d)
      (fun lambda ↦
        ∑' d : ℕ,
          extendedGaussianNaturalTerm (Real.log 2) lambda d)
      atTop (Icc (-M) M) := by
  apply tendstoUniformlyOn_tsum_of_uniform_coordinate_limits
    (g := fun d : ℕ ↦
      extendedGaussianNaturalTerm (Real.log 2) M d)
  · exact summable_extendedGaussianNaturalTerm
      (show 0 < Real.log 2 by positivity)
  · exact fun d ↦
      (extendedGaussianNaturalTerm_pos (Real.log 2) M d).le
  · exact fun alpha d lambda hlambda ↦
      norm_profileDeficitNaturalTerm_le_at_upper_tilt
        alpha d hlambda
  · exact fun d lambda hlambda ↦
      norm_extendedGaussianNaturalTerm_le_at_upper_tilt d hlambda
  · exact tendstoUniformlyOn_profileDeficitNaturalTerm M

/-- Uniform convergence of the totalized natural first-moment series. -/
theorem tendstoUniformlyOn_tsum_profileDeficitNaturalFirstMomentTerm
    (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦
        ∑' d : ℕ,
          (d : ℝ) * profileDeficitNaturalTerm alpha lambda d)
      (fun lambda ↦
        ∑' d : ℕ,
          (d : ℝ) *
            extendedGaussianNaturalTerm (Real.log 2) lambda d)
      atTop (Icc (-M) M) := by
  apply tendstoUniformlyOn_tsum_of_uniform_coordinate_limits
    (g := fun d : ℕ ↦
      (d : ℝ) * extendedGaussianNaturalTerm (Real.log 2) M d)
  · exact summable_extendedGaussianFirstMoment
      (show 0 < Real.log 2 by positivity)
  · exact fun d ↦ mul_nonneg (Nat.cast_nonneg d)
      (extendedGaussianNaturalTerm_pos (Real.log 2) M d).le
  · intro alpha d lambda hlambda
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg d)]
    exact mul_le_mul_of_nonneg_left
      (norm_profileDeficitNaturalTerm_le_at_upper_tilt
        alpha d hlambda)
      (Nat.cast_nonneg d)
  · intro d lambda hlambda
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg d)]
    exact mul_le_mul_of_nonneg_left
      (norm_extendedGaussianNaturalTerm_le_at_upper_tilt d hlambda)
      (Nat.cast_nonneg d)
  · exact tendstoUniformlyOn_profileDeficitNaturalFirstMomentTerm M

/-- Uniform convergence of the totalized natural second-moment series. -/
theorem tendstoUniformlyOn_tsum_profileDeficitNaturalSecondMomentTerm
    (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦
        ∑' d : ℕ,
          (d : ℝ) ^ 2 * profileDeficitNaturalTerm alpha lambda d)
      (fun lambda ↦
        ∑' d : ℕ,
          (d : ℝ) ^ 2 *
            extendedGaussianNaturalTerm (Real.log 2) lambda d)
      atTop (Icc (-M) M) := by
  apply tendstoUniformlyOn_tsum_of_uniform_coordinate_limits
    (g := fun d : ℕ ↦
      (d : ℝ) ^ 2 * extendedGaussianNaturalTerm (Real.log 2) M d)
  · exact summable_extendedGaussianSecondMoment
      (show 0 < Real.log 2 by positivity)
  · exact fun d ↦ mul_nonneg (sq_nonneg (d : ℝ))
      (extendedGaussianNaturalTerm_pos (Real.log 2) M d).le
  · intro alpha d lambda hlambda
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (d : ℝ))]
    exact mul_le_mul_of_nonneg_left
      (norm_profileDeficitNaturalTerm_le_at_upper_tilt
        alpha d hlambda)
      (sq_nonneg (d : ℝ))
  · intro d lambda hlambda
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (d : ℝ))]
    exact mul_le_mul_of_nonneg_left
      (norm_extendedGaussianNaturalTerm_le_at_upper_tilt d hlambda)
      (sq_nonneg (d : ℝ))
  · exact tendstoUniformlyOn_profileDeficitNaturalSecondMomentTerm M

/-- The exceptional `-1` atom also converges uniformly on every bounded tilt
interval. -/
theorem tendstoUniformlyOn_profileDeficitExceptionalTerm (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitExceptionalTerm alpha lambda)
      (fun lambda ↦
        extendedGaussianExceptionalAtom (Real.log 2) lambda)
      atTop (Icc (-M) M) := by
  have hscalar :
      Tendsto
        (fun alpha : ℕ ↦
          Real.exp (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1))))
        atTop (𝓝 1) := by
    simpa using tendsto_log_nat_div_nat_add_one.rexp
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let C : ℝ := Real.exp M
  have hC : 0 < C := Real.exp_pos M
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hscalar
    (eps / C) (div_pos heps hC)
  filter_upwards [eventually_ge_atTop N, eventually_gt_atTop 0] with
      alpha halphaN halpha
  intro lambda hlambda
  have herr :
      |1 - Real.exp
        (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)))| < eps / C := by
    simpa only [Real.dist_eq, abs_sub_comm] using hN alpha halphaN
  have hbase : Real.exp (-lambda - q / 2) ≤ C := by
    dsimp [C]
    apply Real.exp_le_exp.mpr
    have hq : 0 < q := q_pos
    nlinarith [hlambda.1]
  rw [profileDeficitExceptionalTerm_eq alpha halpha lambda]
  change
    dist (Real.exp (-lambda - q / 2))
      (Real.exp
        (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)) +
          (-lambda - q / 2))) < eps
  rw [Real.dist_eq, Real.exp_add]
  calc
    |Real.exp (-lambda - q / 2) -
        Real.exp (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1))) *
          Real.exp (-lambda - q / 2)| =
        Real.exp (-lambda - q / 2) *
          |1 - Real.exp
            (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)))| := by
      have hfactor :
          Real.exp (-lambda - q / 2) -
              Real.exp (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1))) *
                Real.exp (-lambda - q / 2) =
            Real.exp (-lambda - q / 2) *
              (1 - Real.exp
                (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)))) := by
        ring
      rw [hfactor, abs_mul,
        abs_of_pos (Real.exp_pos (-lambda - q / 2))]
    _ ≤ C *
          |1 - Real.exp
            (Real.log ((alpha : ℝ) / ((alpha : ℝ) + 1)))| :=
      mul_le_mul_of_nonneg_right hbase (abs_nonneg _)
    _ < C * (eps / C) := mul_lt_mul_of_pos_left herr hC
    _ = eps := by field_simp

/-- The finite partition converges uniformly to the extended Gaussian
partition on every bounded tilt interval. -/
theorem tendstoUniformlyOn_profileDeficitPartition (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitPartition alpha lambda)
      (fun lambda ↦ extendedGaussianPartition (Real.log 2) lambda)
      atTop (Icc (-M) M) := by
  have h := (tendstoUniformlyOn_profileDeficitExceptionalTerm M).add
    (tendstoUniformlyOn_tsum_profileDeficitNaturalTerm M)
  refine (h.congr ?_).congr_right ?_
  · exact Filter.Eventually.of_forall fun alpha lambda _ ↦
      (profileDeficitPartition_eq_exceptional_add_tsum alpha lambda).symm
  · exact fun lambda _ ↦ rfl

/-- The finite first numerator converges uniformly on every bounded tilt
interval. -/
theorem tendstoUniformlyOn_profileDeficitFirstNumerator (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitFirstNumerator alpha lambda)
      (fun lambda ↦ extendedGaussianFirstNumerator (Real.log 2) lambda)
      atTop (Icc (-M) M) := by
  have h := (tendstoUniformlyOn_profileDeficitExceptionalTerm M).neg.add
    (tendstoUniformlyOn_tsum_profileDeficitNaturalFirstMomentTerm M)
  refine (h.congr ?_).congr_right ?_
  · exact Filter.Eventually.of_forall fun alpha lambda _ ↦
      (profileDeficitFirstNumerator_eq_neg_exceptional_add_tsum
        alpha lambda).symm
  · exact fun lambda _ ↦ rfl

/-- The finite second numerator converges uniformly on every bounded tilt
interval. -/
theorem tendstoUniformlyOn_profileDeficitSecondNumerator (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitSecondNumerator alpha lambda)
      (fun lambda ↦ extendedGaussianSecondNumerator (Real.log 2) lambda)
      atTop (Icc (-M) M) := by
  have h := (tendstoUniformlyOn_profileDeficitExceptionalTerm M).add
    (tendstoUniformlyOn_tsum_profileDeficitNaturalSecondMomentTerm M)
  refine (h.congr ?_).congr_right ?_
  · exact Filter.Eventually.of_forall fun alpha lambda _ ↦
      (profileDeficitSecondNumerator_eq_exceptional_add_tsum
        alpha lambda).symm
  · exact fun lambda _ ↦ rfl

/-- An explicit finite bound for the limiting first numerator on `[-M,M]`.
The same endpoint comparison used for the uniform series supplies the bound;
no compactness theorem is hidden here. -/
theorem abs_extendedGaussianFirstNumerator_le_upper_tilt
    {lambda M : ℝ} (hlambda : lambda ∈ Icc (-M) M) :
    |extendedGaussianFirstNumerator (Real.log 2) lambda| ≤
      Real.exp M +
        ∑' d : ℕ,
          (d : ℝ) *
            extendedGaussianNaturalTerm (Real.log 2) M d := by
  have hq : 0 < Real.log 2 := by positivity
  have hatom :
      extendedGaussianExceptionalAtom (Real.log 2) lambda ≤
        Real.exp M := by
    rw [extendedGaussianExceptionalAtom]
    apply Real.exp_le_exp.mpr
    nlinarith [hlambda.1, hq]
  have hsumNonneg :
      0 ≤ ∑' d : ℕ,
        (d : ℝ) *
          extendedGaussianNaturalTerm (Real.log 2) lambda d :=
    tsum_nonneg fun d ↦ mul_nonneg (Nat.cast_nonneg d)
      (extendedGaussianNaturalTerm_pos (Real.log 2) lambda d).le
  have hsumLe :
      (∑' d : ℕ,
          (d : ℝ) *
            extendedGaussianNaturalTerm (Real.log 2) lambda d) ≤
        ∑' d : ℕ,
          (d : ℝ) *
            extendedGaussianNaturalTerm (Real.log 2) M d := by
    exact (summable_extendedGaussianFirstMoment hq).tsum_le_tsum
      (fun d ↦ mul_le_mul_of_nonneg_left
        (by
          rw [extendedGaussianNaturalTerm,
            extendedGaussianNaturalTerm]
          exact Real.exp_le_exp.mpr
            (sub_le_sub_right
              (mul_le_mul_of_nonneg_right hlambda.2
                (Nat.cast_nonneg d)) _))
        (Nat.cast_nonneg d))
      (summable_extendedGaussianFirstMoment hq)
  rw [extendedGaussianFirstNumerator]
  calc
    |-extendedGaussianExceptionalAtom (Real.log 2) lambda +
          ∑' d : ℕ,
            (d : ℝ) *
              extendedGaussianNaturalTerm (Real.log 2) lambda d| ≤
        |-extendedGaussianExceptionalAtom (Real.log 2) lambda| +
          |∑' d : ℕ,
            (d : ℝ) *
              extendedGaussianNaturalTerm (Real.log 2) lambda d| :=
      abs_add_le _ _
    _ = extendedGaussianExceptionalAtom (Real.log 2) lambda +
          ∑' d : ℕ,
            (d : ℝ) *
              extendedGaussianNaturalTerm (Real.log 2) lambda d := by
      rw [abs_neg,
        abs_of_pos
          (extendedGaussianExceptionalAtom_pos (Real.log 2) lambda),
        abs_of_nonneg hsumNonneg]
    _ ≤ Real.exp M +
          ∑' d : ℕ,
            (d : ℝ) *
              extendedGaussianNaturalTerm (Real.log 2) M d :=
      add_le_add hatom hsumLe

end

end Erdos625
