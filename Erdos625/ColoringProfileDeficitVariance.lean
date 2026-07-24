import Mathlib.Analysis.Calculus.Deriv.Shift
import Erdos625.ColoringProfileDeficitUniformMeanConvergence
import Erdos625.ColoringProfileDualDifferentiation

/-!
# Variance of the finite deficit profile

This module records the centered second moment of the finite deficit family.
It identifies that variance both with the usual raw-moment expression and
with the variance of the reflected finite size profile.  The latter identity
transfers the already proved finite dual calculus to the deficit mean.

All finite identities are total at `alpha = 0`.  In particular, this file
does not assume that a selected tilt is bounded or even that a target lies in
the interior of the finite support.
-/

namespace Erdos625

open Filter Set
open scoped BigOperators Topology

noncomputable section

/-- The weighted centered second moment of the finite deficit profile. -/
def profileDeficitVariance (alpha : ℕ) (lambda : ℝ) : ℝ :=
  ∑ i : Fin (alpha + 1),
    profileDeficitWeight alpha lambda i *
      (profileDeficit alpha i - profileDeficitMean alpha lambda) ^ 2

/-- The finite deficit variance is its normalized raw second moment minus the
square of its normalized mean.  This identity also covers `alpha = 0`. -/
theorem profileDeficitVariance_eq_raw (alpha : ℕ) (lambda : ℝ) :
    profileDeficitVariance alpha lambda =
      profileDeficitSecondMoment alpha lambda -
        profileDeficitMean alpha lambda ^ 2 := by
  have hexpand : ∀ i : Fin (alpha + 1),
      profileDeficitWeight alpha lambda i *
          (profileDeficit alpha i - profileDeficitMean alpha lambda) ^ 2 =
        profileDeficitWeight alpha lambda i * profileDeficit alpha i ^ 2 -
          2 * profileDeficitMean alpha lambda *
            (profileDeficitWeight alpha lambda i * profileDeficit alpha i) +
          profileDeficitMean alpha lambda ^ 2 *
            profileDeficitWeight alpha lambda i := by
    intro i
    ring
  unfold profileDeficitVariance
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (∑ i : Fin (alpha + 1),
          profileDeficitWeight alpha lambda i * profileDeficit alpha i ^ 2) =
        profileDeficitSecondMoment alpha lambda by rfl]
  rw [show (∑ i : Fin (alpha + 1),
          profileDeficitWeight alpha lambda i * profileDeficit alpha i) =
        profileDeficitMean alpha lambda by rfl]
  rw [sum_profileDeficitWeight]
  ring

/-- Reflection from support size to centered deficit preserves variance. -/
theorem profileDeficitVariance_eq_profileDualVariance
    (alpha : ℕ) (lambda : ℝ) :
    profileDeficitVariance alpha lambda =
      profileDualVariance (alpha + 1)
        (profileDeficitAffineB alpha - lambda) := by
  unfold profileDeficitVariance profileDualVariance
  apply Finset.sum_congr rfl
  intro i _
  rw [profileDualWeight_eq_profileDeficitWeight,
    profileDualMean_eq_alpha_sub_profileDeficitMean]
  unfold profileDeficit
  ring

/-- Differentiating the finite deficit mean with respect to its normalized
tilt gives the finite deficit variance.  Both signs introduced by reflecting
the dual tilt and centering the dual mean cancel. -/
theorem hasDerivAt_profileDeficitMean (alpha : ℕ) (lambda : ℝ) :
    HasDerivAt (profileDeficitMean alpha)
      (profileDeficitVariance alpha lambda) lambda := by
  rw [profileDeficitVariance_eq_profileDualVariance]
  have hmean := hasDerivAt_profileDualMean
    (show 0 < alpha + 1 by omega)
    (profileDeficitAffineB alpha - lambda)
  have hidentity : ∀ u : ℝ,
      profileDualMean (alpha + 1)
          (profileDeficitAffineB alpha - u) =
        (alpha : ℝ) - profileDeficitMean alpha u :=
    profileDualMean_eq_alpha_sub_profileDeficitMean alpha
  have hfun : profileDeficitMean alpha = fun u : ℝ ↦
      (alpha : ℝ) -
        profileDualMean (alpha + 1) (profileDeficitAffineB alpha - u) := by
    funext u
    have hu := hidentity u
    linarith
  rw [hfun]
  have hcomp : HasDerivAt
      (fun u : ℝ ↦
        profileDualMean (alpha + 1) (profileDeficitAffineB alpha - u))
      (-profileDualVariance (alpha + 1)
          (profileDeficitAffineB alpha - lambda)) lambda :=
    hmean.comp_const_sub (profileDeficitAffineB alpha) lambda
  simpa only [neg_neg] using hcomp.const_sub (alpha : ℝ)

/-! ## Uniform convergence of the finite variance -/

/-- The finite deficit variance converges uniformly to the variance of the
extended Gaussian profile on every bounded tilt interval.  The proof first
replaces the single value `alpha = 0` by the value at `alpha = 1`, so that all
finite partition functions have the common lower bound one.  Eventual
equality restores the original totalized family at the end. -/
theorem tendstoUniformlyOn_profileDeficitVariance (M : ℝ) :
    TendstoUniformlyOn
      (fun alpha lambda ↦ profileDeficitVariance alpha lambda)
      (extendedGaussianRawVariance (Real.log 2))
      atTop (Icc (-M) M) := by
  let Z : ℕ → ℝ → ℝ := fun alpha lambda ↦
    if alpha = 0 then profileDeficitPartition 1 lambda
    else profileDeficitPartition alpha lambda
  let A : ℕ → ℝ → ℝ := fun alpha lambda ↦
    if alpha = 0 then profileDeficitFirstNumerator 1 lambda
    else profileDeficitFirstNumerator alpha lambda
  let B : ℕ → ℝ → ℝ := fun alpha lambda ↦
    if alpha = 0 then profileDeficitSecondNumerator 1 lambda
    else profileDeficitSecondNumerator alpha lambda
  have hZconv :
      TendstoUniformlyOn Z
        (fun lambda ↦ extendedGaussianPartition (Real.log 2) lambda)
        atTop (Icc (-M) M) := by
    apply (tendstoUniformlyOn_profileDeficitPartition M).congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [Z, Nat.ne_of_gt halpha]
  have hAconv :
      TendstoUniformlyOn A
        (fun lambda ↦ extendedGaussianFirstNumerator (Real.log 2) lambda)
        atTop (Icc (-M) M) := by
    apply (tendstoUniformlyOn_profileDeficitFirstNumerator M).congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [A, Nat.ne_of_gt halpha]
  have hBconv :
      TendstoUniformlyOn B
        (fun lambda ↦ extendedGaussianSecondNumerator (Real.log 2) lambda)
        atTop (Icc (-M) M) := by
    apply (tendstoUniformlyOn_profileDeficitSecondNumerator M).congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [B, Nat.ne_of_gt halpha]
  have hZlower : ∀ alpha lambda, lambda ∈ Icc (-M) M →
      1 ≤ Z alpha lambda := by
    intro alpha lambda _
    by_cases halpha : alpha = 0
    · simp [Z, halpha,
        one_le_profileDeficitPartition 1 (by omega) lambda]
    · simp [Z, halpha,
        one_le_profileDeficitPartition alpha
          (Nat.pos_of_ne_zero halpha) lambda]
  have hzlower : ∀ lambda, lambda ∈ Icc (-M) M →
      1 ≤ extendedGaussianPartition (Real.log 2) lambda := by
    intro lambda _
    exact one_le_extendedGaussianPartition
      (show 0 < Real.log 2 by positivity)
  let C₁ : ℝ :=
    Real.exp M +
      ∑' d : ℕ,
        (d : ℝ) * extendedGaussianNaturalTerm (Real.log 2) M d
  let C₂ : ℝ :=
    Real.exp M +
      ∑' d : ℕ,
        (d : ℝ) ^ 2 * extendedGaussianNaturalTerm (Real.log 2) M d
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    exact add_nonneg (Real.exp_pos M).le
      (tsum_nonneg fun d ↦ mul_nonneg (Nat.cast_nonneg d)
        (extendedGaussianNaturalTerm_pos (Real.log 2) M d).le)
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂]
    exact add_nonneg (Real.exp_pos M).le
      (tsum_nonneg fun d ↦ mul_nonneg (sq_nonneg (d : ℝ))
        (extendedGaussianNaturalTerm_pos (Real.log 2) M d).le)
  have hfirstLimit : ∀ lambda, lambda ∈ Icc (-M) M →
      |extendedGaussianFirstNumerator (Real.log 2) lambda| ≤ C₁ := by
    intro lambda hlambda
    exact abs_extendedGaussianFirstNumerator_le_upper_tilt hlambda
  have hsecondLimit : ∀ lambda, lambda ∈ Icc (-M) M →
      |extendedGaussianSecondNumerator (Real.log 2) lambda| ≤ C₂ := by
    intro lambda hlambda
    have hq : 0 < Real.log 2 := by positivity
    have hatom :
        extendedGaussianExceptionalAtom (Real.log 2) lambda ≤
          Real.exp M := by
      rw [extendedGaussianExceptionalAtom]
      apply Real.exp_le_exp.mpr
      nlinarith [hlambda.1, hq]
    have hsumNonneg :
        0 ≤ ∑' d : ℕ,
          (d : ℝ) ^ 2 *
            extendedGaussianNaturalTerm (Real.log 2) lambda d :=
      tsum_nonneg fun d ↦ mul_nonneg (sq_nonneg (d : ℝ))
        (extendedGaussianNaturalTerm_pos (Real.log 2) lambda d).le
    have hsumLe :
        (∑' d : ℕ,
            (d : ℝ) ^ 2 *
              extendedGaussianNaturalTerm (Real.log 2) lambda d) ≤
          ∑' d : ℕ,
            (d : ℝ) ^ 2 *
              extendedGaussianNaturalTerm (Real.log 2) M d := by
      exact (summable_extendedGaussianSecondMoment hq).tsum_le_tsum
        (fun d ↦ mul_le_mul_of_nonneg_left
          (by
            rw [extendedGaussianNaturalTerm,
              extendedGaussianNaturalTerm]
            exact Real.exp_le_exp.mpr
              (sub_le_sub_right
                (mul_le_mul_of_nonneg_right hlambda.2
                  (Nat.cast_nonneg d)) _))
          (sq_nonneg (d : ℝ)))
        (summable_extendedGaussianSecondMoment hq)
    rw [extendedGaussianSecondNumerator,
      abs_of_nonneg
        (add_nonneg
          (extendedGaussianExceptionalAtom_pos
            (Real.log 2) lambda).le hsumNonneg)]
    exact add_le_add hatom hsumLe
  let K : ℝ := C₁ + C₂ + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith
  have hraw :
      TendstoUniformlyOn
        (fun alpha lambda ↦
          B alpha lambda / Z alpha lambda -
            (A alpha lambda / Z alpha lambda) ^ 2)
        (fun lambda ↦
          extendedGaussianSecondNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda -
            (extendedGaussianFirstNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda) ^ 2)
        atTop (Icc (-M) M) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro eps heps
    let scale : ℝ := (1 + K) * (1 + 2 * K)
    have hscale : 0 < scale := by
      dsimp [scale]
      positivity
    let delta : ℝ := min 1 (eps / (2 * scale))
    have hdelta : 0 < delta := by
      dsimp [delta]
      exact lt_min zero_lt_one
        (div_pos heps (mul_pos (by norm_num) hscale))
    have hdeltaOne : delta ≤ 1 := min_le_left _ _
    have hdeltaScale : delta ≤ eps / (2 * scale) := min_le_right _ _
    have hZE := (Metric.tendstoUniformlyOn_iff.mp hZconv) delta hdelta
    have hAE := (Metric.tendstoUniformlyOn_iff.mp hAconv) delta hdelta
    have hBE := (Metric.tendstoUniformlyOn_iff.mp hBconv) delta hdelta
    filter_upwards [hZE, hAE, hBE] with alpha hZalpha hAalpha hBalpha
    intro lambda hlambda
    have hZerr :
        |Z alpha lambda -
            extendedGaussianPartition (Real.log 2) lambda| ≤ delta := by
      have h := hZalpha lambda hlambda
      rw [Real.dist_eq, abs_sub_comm] at h
      exact h.le
    have hAerr :
        |A alpha lambda -
            extendedGaussianFirstNumerator (Real.log 2) lambda| ≤ delta := by
      have h := hAalpha lambda hlambda
      rw [Real.dist_eq, abs_sub_comm] at h
      exact h.le
    have hBerr :
        |B alpha lambda -
            extendedGaussianSecondNumerator (Real.log 2) lambda| ≤ delta := by
      have h := hBalpha lambda hlambda
      rw [Real.dist_eq, abs_sub_comm] at h
      exact h.le
    have ha₀ := hfirstLimit lambda hlambda
    have hb₀ := hsecondLimit lambda hlambda
    have hC₁K : C₁ ≤ K := by
      dsimp [K]
      linarith
    have hC₂K : C₂ ≤ K := by
      dsimp [K]
      linarith
    have haK :
        |extendedGaussianFirstNumerator (Real.log 2) lambda| ≤ K :=
      ha₀.trans hC₁K
    have hbK :
        |extendedGaussianSecondNumerator (Real.log 2) lambda| ≤ K :=
      hb₀.trans hC₂K
    have hATriangle :
        |A alpha lambda| ≤
          |A alpha lambda -
              extendedGaussianFirstNumerator (Real.log 2) lambda| +
            |extendedGaussianFirstNumerator (Real.log 2) lambda| := by
      calc
        |A alpha lambda| =
            |(A alpha lambda -
                extendedGaussianFirstNumerator (Real.log 2) lambda) +
              extendedGaussianFirstNumerator (Real.log 2) lambda| := by
                congr 1
                ring
        _ ≤ |A alpha lambda -
                extendedGaussianFirstNumerator (Real.log 2) lambda| +
              |extendedGaussianFirstNumerator (Real.log 2) lambda| :=
          abs_add_le _ _
    have hAK : |A alpha lambda| ≤ K := by
      calc
        |A alpha lambda| ≤
            |A alpha lambda -
                extendedGaussianFirstNumerator (Real.log 2) lambda| +
              |extendedGaussianFirstNumerator (Real.log 2) lambda| :=
          hATriangle
        _ ≤ delta + C₁ := add_le_add hAerr ha₀
        _ ≤ 1 + C₁ := by linarith
        _ ≤ K := by
          dsimp [K]
          linarith
    have hfirst :
        |A alpha lambda / Z alpha lambda -
            extendedGaussianFirstNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda| ≤
          delta + K * delta := by
      have h := abs_div_sub_div_le_of_denominator_ge
        (z := 1) (epsA := delta) (epsB := delta) (M := K)
        zero_lt_one hdelta.le hdelta.le hK
        (hZlower alpha lambda hlambda) (hzlower lambda hlambda)
        hAerr hZerr haK
      simpa using h
    have hsecond :
        |B alpha lambda / Z alpha lambda -
            extendedGaussianSecondNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda| ≤
          delta + K * delta := by
      have h := abs_div_sub_div_le_of_denominator_ge
        (z := 1) (epsA := delta) (epsB := delta) (M := K)
        zero_lt_one hdelta.le hdelta.le hK
        (hZlower alpha lambda hlambda) (hzlower lambda hlambda)
        hBerr hZerr hbK
      simpa using h
    have hANorm : |A alpha lambda / Z alpha lambda| ≤ K := by
      rw [abs_div,
        abs_of_nonneg (by
          linarith [hZlower alpha lambda hlambda] : 0 ≤ Z alpha lambda)]
      exact
        (div_le_self (abs_nonneg (A alpha lambda))
          (hZlower alpha lambda hlambda)).trans hAK
    have haNorm :
        |extendedGaussianFirstNumerator (Real.log 2) lambda /
            extendedGaussianPartition (Real.log 2) lambda| ≤ K := by
      rw [abs_div,
        abs_of_nonneg (by
          linarith [hzlower lambda hlambda] :
            0 ≤ extendedGaussianPartition (Real.log 2) lambda)]
      exact
        (div_le_self
          (abs_nonneg
            (extendedGaussianFirstNumerator (Real.log 2) lambda))
          (hzlower lambda hlambda)).trans haK
    have hsquare :
        |(A alpha lambda / Z alpha lambda) ^ 2 -
            (extendedGaussianFirstNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda) ^ 2| ≤
          (delta + K * delta) * (2 * K) := by
      rw [show (A alpha lambda / Z alpha lambda) ^ 2 -
          (extendedGaussianFirstNumerator (Real.log 2) lambda /
            extendedGaussianPartition (Real.log 2) lambda) ^ 2 =
        (A alpha lambda / Z alpha lambda -
          extendedGaussianFirstNumerator (Real.log 2) lambda /
            extendedGaussianPartition (Real.log 2) lambda) *
        (A alpha lambda / Z alpha lambda +
          extendedGaussianFirstNumerator (Real.log 2) lambda /
            extendedGaussianPartition (Real.log 2) lambda) by ring,
        abs_mul]
      have hsum :
          |A alpha lambda / Z alpha lambda +
              extendedGaussianFirstNumerator (Real.log 2) lambda /
                extendedGaussianPartition (Real.log 2) lambda| ≤
            2 * K := by
        calc
          |A alpha lambda / Z alpha lambda +
              extendedGaussianFirstNumerator (Real.log 2) lambda /
                extendedGaussianPartition (Real.log 2) lambda| ≤
              |A alpha lambda / Z alpha lambda| +
                |extendedGaussianFirstNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda| :=
            abs_add_le _ _
          _ ≤ 2 * K := by linarith
      exact mul_le_mul hfirst hsum (abs_nonneg _) (by positivity)
    have hstable :
        |(B alpha lambda / Z alpha lambda -
              (A alpha lambda / Z alpha lambda) ^ 2) -
            (extendedGaussianSecondNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda -
              (extendedGaussianFirstNumerator (Real.log 2) lambda /
                extendedGaussianPartition (Real.log 2) lambda) ^ 2)| ≤
          (1 + K) * (1 + 2 * K) * delta := by
      calc
        |(B alpha lambda / Z alpha lambda -
              (A alpha lambda / Z alpha lambda) ^ 2) -
            (extendedGaussianSecondNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda -
              (extendedGaussianFirstNumerator (Real.log 2) lambda /
                extendedGaussianPartition (Real.log 2) lambda) ^ 2)| =
            |(B alpha lambda / Z alpha lambda -
                extendedGaussianSecondNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda) -
              ((A alpha lambda / Z alpha lambda) ^ 2 -
                (extendedGaussianFirstNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda) ^ 2)| := by
              congr 1
              ring
        _ ≤ |B alpha lambda / Z alpha lambda -
                extendedGaussianSecondNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda| +
              |(A alpha lambda / Z alpha lambda) ^ 2 -
                (extendedGaussianFirstNumerator (Real.log 2) lambda /
                  extendedGaussianPartition (Real.log 2) lambda) ^ 2| :=
          abs_sub _ _
        _ ≤ (delta + K * delta) +
              (delta + K * delta) * (2 * K) :=
          add_le_add hsecond hsquare
        _ = (1 + K) * (1 + 2 * K) * delta := by ring
    rw [Real.dist_eq, abs_sub_comm]
    calc
      |(B alpha lambda / Z alpha lambda -
            (A alpha lambda / Z alpha lambda) ^ 2) -
          (extendedGaussianSecondNumerator (Real.log 2) lambda /
                extendedGaussianPartition (Real.log 2) lambda -
            (extendedGaussianFirstNumerator (Real.log 2) lambda /
                extendedGaussianPartition (Real.log 2) lambda) ^ 2)| ≤
          (1 + K) * (1 + 2 * K) * delta := hstable
      _ = scale * delta := by rfl
      _ ≤ scale * (eps / (2 * scale)) :=
        mul_le_mul_of_nonneg_left hdeltaScale hscale.le
      _ = eps / 2 := by
        field_simp [hscale.ne']
      _ < eps := by linarith
  have hrawActual :
      TendstoUniformlyOn
        (fun alpha lambda ↦
          profileDeficitSecondNumerator alpha lambda /
              profileDeficitPartition alpha lambda -
            (profileDeficitFirstNumerator alpha lambda /
              profileDeficitPartition alpha lambda) ^ 2)
        (fun lambda ↦
          extendedGaussianSecondNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda -
            (extendedGaussianFirstNumerator (Real.log 2) lambda /
              extendedGaussianPartition (Real.log 2) lambda) ^ 2)
        atTop (Icc (-M) M) := by
    apply hraw.congr
    filter_upwards [eventually_gt_atTop 0] with alpha halpha
    intro lambda _
    simp [A, B, Z, Nat.ne_of_gt halpha]
  refine (hrawActual.congr ?_).congr_right ?_
  · exact Filter.Eventually.of_forall fun alpha lambda _ ↦ by
      change
        profileDeficitSecondNumerator alpha lambda /
              profileDeficitPartition alpha lambda -
            (profileDeficitFirstNumerator alpha lambda /
              profileDeficitPartition alpha lambda) ^ 2 =
          profileDeficitVariance alpha lambda
      rw [profileDeficitVariance_eq_raw,
        profileDeficitSecondMoment_eq_secondNumerator_div,
        profileDeficitMean_eq_firstNumerator_div]
  · exact fun lambda _ ↦ rfl

end

end Erdos625
