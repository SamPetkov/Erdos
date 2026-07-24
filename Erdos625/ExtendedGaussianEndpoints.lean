import Erdos625.ExtendedGaussianProfile
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Endpoint limits for the extended tilted-Gaussian mean

This module proves the two endpoint limits of the normalized mean of the
extended deficit profile.  At negative infinite tilt, the exceptional
coordinate `-1` dominates; the proof rescales by that atom and applies
Tannery's theorem with a summable Gaussian majorant.  At positive infinite
tilt, any prescribed finite threshold is beaten by comparing the finitely
many lower coordinates with one fixed higher natural coordinate.
-/

open Filter
open scoped Topology BigOperators

namespace Erdos625

noncomputable section

private theorem tendsto_exp_affine_atBot_of_pos_endpoint
    {c b : ℝ} (hc : 0 < c) :
    Tendsto (fun lambda : ℝ ↦ Real.exp (b + lambda * c)) atBot (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hlin : Tendsto (fun lambda : ℝ ↦ c * lambda + b) atBot atBot :=
    tendsto_atBot_add_const_right atBot b
      (tendsto_id.const_mul_atBot hc)
  simpa only [mul_comm, add_comm] using hlin

private theorem tendsto_extendedGaussianNaturalTerm_div_exceptional_atBot
    (a : ℝ) (d : ℕ) :
    Tendsto
      (fun lambda : ℝ ↦
        extendedGaussianNaturalTerm a lambda d /
          extendedGaussianExceptionalAtom a lambda)
      atBot (nhds 0) := by
  have hc : 0 < (d : ℝ) + 1 := by positivity
  convert tendsto_exp_affine_atBot_of_pos_endpoint
    (b := a / 2 - a / 2 * (d : ℝ) ^ 2)
    (c := (d : ℝ) + 1) hc using 1
  ext lambda
  rw [show extendedGaussianNaturalTerm a lambda d /
      extendedGaussianExceptionalAtom a lambda =
      Real.exp
        ((lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) -
          (-lambda - a / 2)) by
        simp [extendedGaussianNaturalTerm,
          extendedGaussianExceptionalAtom, Real.exp_sub]]
  congr 1
  ring

private theorem summable_bottomEndpointMajorant
    {a : ℝ} (ha : 0 < a) :
    Summable
      (fun d : ℕ ↦
        ((d : ℝ) + 1) *
          (Real.exp (a / 2) * extendedGaussianNaturalTerm a 0 d)) := by
  have hbase :
      Summable
        (fun d : ℕ ↦
          (d : ℝ) * extendedGaussianNaturalTerm a 0 d +
            extendedGaussianNaturalTerm a 0 d) :=
    (summable_extendedGaussianFirstMoment
      (a := a) (lambda := 0) ha).add
      (summable_extendedGaussianNaturalTerm
        (a := a) (lambda := 0) ha)
  have hscaled := hbase.mul_left (Real.exp (a / 2))
  simpa only [add_mul, one_mul, mul_add, mul_assoc, mul_left_comm,
    mul_comm] using hscaled

private theorem tendsto_bottomEndpointScaledFirstMass
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun lambda : ℝ ↦
        ∑' d : ℕ,
          ((d : ℝ) + 1) *
            (extendedGaussianNaturalTerm a lambda d /
              extendedGaussianExceptionalAtom a lambda))
      atBot (nhds 0) := by
  have hpoint : ∀ d : ℕ,
      Tendsto
        (fun lambda : ℝ ↦
          ((d : ℝ) + 1) *
            (extendedGaussianNaturalTerm a lambda d /
              extendedGaussianExceptionalAtom a lambda))
        atBot (nhds 0) := by
    intro d
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_extendedGaussianNaturalTerm_div_exceptional_atBot a d))
  have hbound :
      ∀ᶠ lambda : ℝ in atBot, ∀ d : ℕ,
        ‖((d : ℝ) + 1) *
            (extendedGaussianNaturalTerm a lambda d /
              extendedGaussianExceptionalAtom a lambda)‖ ≤
          ((d : ℝ) + 1) *
            (Real.exp (a / 2) * extendedGaussianNaturalTerm a 0 d) := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with lambda hlambda
    intro d
    have hratioNonneg :
        0 ≤ extendedGaussianNaturalTerm a lambda d /
          extendedGaussianExceptionalAtom a lambda :=
      div_nonneg (extendedGaussianNaturalTerm_pos a lambda d).le
        (extendedGaussianExceptionalAtom_pos a lambda).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hratioNonneg)]
    gcongr
    rw [show extendedGaussianNaturalTerm a lambda d /
        extendedGaussianExceptionalAtom a lambda =
        Real.exp
          ((lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) -
            (-lambda - a / 2)) by
          simp [extendedGaussianNaturalTerm,
            extendedGaussianExceptionalAtom, Real.exp_sub]]
    change Real.exp
        (lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2 -
          (-lambda - a / 2)) ≤
      Real.exp (a / 2) *
        Real.exp (0 * (d : ℝ) - a / 2 * (d : ℝ) ^ 2)
    rw [← Real.exp_add]
    apply (Real.exp_le_exp).2
    simp only [zero_mul]
    have hd : 0 ≤ (d : ℝ) + 1 := by positivity
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hlambda hd]
  simpa using tendsto_tsum_of_dominated_convergence
    (summable_bottomEndpointMajorant ha) hpoint hbound

theorem tendsto_extendedGaussianMean_atBot (a : ℝ) (ha : 0 < a) :
    Tendsto (extendedGaussianMean a) atBot (nhds (-1)) := by
  have hweightedIdentity : ∀ lambda : ℝ,
      extendedGaussianFirstNumerator a lambda +
          extendedGaussianPartition a lambda =
        ∑' d : ℕ,
          ((d : ℝ) + 1) * extendedGaussianNaturalTerm a lambda d := by
    intro lambda
    have hfirst :=
      summable_extendedGaussianFirstMoment
        (a := a) (lambda := lambda) ha
    have hmass :=
      summable_extendedGaussianNaturalTerm
        (a := a) (lambda := lambda) ha
    calc
      extendedGaussianFirstNumerator a lambda +
          extendedGaussianPartition a lambda =
        (∑' d : ℕ,
            (d : ℝ) * extendedGaussianNaturalTerm a lambda d) +
          ∑' d : ℕ, extendedGaussianNaturalTerm a lambda d := by
            simp only [extendedGaussianFirstNumerator,
              extendedGaussianPartition]
            ring
      _ = ∑' d : ℕ,
          ((d : ℝ) * extendedGaussianNaturalTerm a lambda d +
            extendedGaussianNaturalTerm a lambda d) :=
        (hfirst.tsum_add hmass).symm
      _ = ∑' d : ℕ,
          ((d : ℝ) + 1) * extendedGaussianNaturalTerm a lambda d := by
        congr 1
        funext d
        ring
  have hmeanAddOne : ∀ lambda : ℝ,
      extendedGaussianMean a lambda + 1 =
        (∑' d : ℕ,
            ((d : ℝ) + 1) * extendedGaussianNaturalTerm a lambda d) /
          extendedGaussianPartition a lambda := by
    intro lambda
    rw [extendedGaussianMean]
    rw [← hweightedIdentity lambda]
    field_simp [extendedGaussianPartition_ne_zero
      (a := a) (lambda := lambda) ha]
  have hnonneg : ∀ lambda : ℝ,
      0 ≤ extendedGaussianMean a lambda + 1 := by
    intro lambda
    rw [hmeanAddOne]
    exact div_nonneg (tsum_nonneg fun d ↦
      mul_nonneg (by positivity)
        (extendedGaussianNaturalTerm_pos a lambda d).le)
      (extendedGaussianPartition_pos
        (a := a) (lambda := lambda) ha).le
  have hupper : ∀ lambda : ℝ,
      extendedGaussianMean a lambda + 1 ≤
        ∑' d : ℕ,
          ((d : ℝ) + 1) *
            (extendedGaussianNaturalTerm a lambda d /
              extendedGaussianExceptionalAtom a lambda) := by
    intro lambda
    rw [hmeanAddOne]
    have hnumNonneg :
        0 ≤ ∑' d : ℕ,
          ((d : ℝ) + 1) * extendedGaussianNaturalTerm a lambda d :=
      tsum_nonneg fun d ↦
        mul_nonneg (by positivity)
          (extendedGaussianNaturalTerm_pos a lambda d).le
    have hatomPos := extendedGaussianExceptionalAtom_pos a lambda
    have hatomLe :
        extendedGaussianExceptionalAtom a lambda ≤
          extendedGaussianPartition a lambda := by
      have hlower := exceptionalAtom_add_one_le_extendedGaussianPartition
        (a := a) (lambda := lambda) ha
      linarith
    calc
      (∑' d : ℕ,
          ((d : ℝ) + 1) * extendedGaussianNaturalTerm a lambda d) /
          extendedGaussianPartition a lambda ≤
        (∑' d : ℕ,
          ((d : ℝ) + 1) * extendedGaussianNaturalTerm a lambda d) /
          extendedGaussianExceptionalAtom a lambda :=
        div_le_div_of_nonneg_left hnumNonneg hatomPos hatomLe
      _ = ∑' d : ℕ,
          ((d : ℝ) + 1) *
            (extendedGaussianNaturalTerm a lambda d /
              extendedGaussianExceptionalAtom a lambda) := by
        calc
          (∑' d : ℕ,
              ((d : ℝ) + 1) *
                extendedGaussianNaturalTerm a lambda d) /
              extendedGaussianExceptionalAtom a lambda =
            ∑' d : ℕ,
              (((d : ℝ) + 1) *
                extendedGaussianNaturalTerm a lambda d) /
                  extendedGaussianExceptionalAtom a lambda :=
            tsum_div_const.symm
          _ = ∑' d : ℕ,
              ((d : ℝ) + 1) *
                (extendedGaussianNaturalTerm a lambda d /
                  extendedGaussianExceptionalAtom a lambda) := by
            congr 1
            funext d
            ring
  have hzero :
      Tendsto (fun lambda ↦ extendedGaussianMean a lambda + 1)
        atBot (nhds 0) :=
    squeeze_zero (fun lambda ↦ hnonneg lambda)
      (fun lambda ↦ hupper lambda)
      (tendsto_bottomEndpointScaledFirstMass ha)
  simpa only [add_sub_cancel_right, zero_sub] using hzero.sub_const 1


/-! ## Positive infinite tilt -/

private theorem tendsto_exp_affine_atTop_of_neg_endpoint
    {c b : ℝ} (hc : c < 0) :
    Tendsto (fun lambda : ℝ ↦ Real.exp (b + lambda * c)) atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  have hlin : Tendsto (fun lambda : ℝ ↦ c * lambda + b) atTop atBot :=
    tendsto_atBot_add_const_right atTop b
      (tendsto_id.const_mul_atTop_of_neg hc)
  simpa only [mul_comm, add_comm] using hlin

private theorem tendsto_extendedGaussianExceptional_div_natural_atTop
    (a : ℝ) (k : ℕ) :
    Tendsto
      (fun lambda : ℝ ↦
        extendedGaussianExceptionalAtom a lambda /
          extendedGaussianNaturalTerm a lambda k)
      atTop (nhds 0) := by
  have hkNonneg : 0 ≤ (k : ℝ) := by positivity
  have hc : -((k : ℝ) + 1) < 0 := by linarith
  convert tendsto_exp_affine_atTop_of_neg_endpoint
    (b := a / 2 * ((k : ℝ) ^ 2 - 1))
    (c := -((k : ℝ) + 1)) hc using 1
  ext lambda
  rw [show extendedGaussianExceptionalAtom a lambda /
      extendedGaussianNaturalTerm a lambda k =
      Real.exp
        ((-lambda - a / 2) -
          (lambda * (k : ℝ) - a / 2 * (k : ℝ) ^ 2)) by
        simp [extendedGaussianNaturalTerm,
          extendedGaussianExceptionalAtom, Real.exp_sub]]
  congr 1
  ring

private theorem tendsto_extendedGaussianNatural_div_natural_atTop
    (a : ℝ) {d k : ℕ} (hdk : d < k) :
    Tendsto
      (fun lambda : ℝ ↦
        extendedGaussianNaturalTerm a lambda d /
          extendedGaussianNaturalTerm a lambda k)
      atTop (nhds 0) := by
  have hcast : (d : ℝ) < (k : ℝ) := by exact_mod_cast hdk
  have hc : (d : ℝ) - (k : ℝ) < 0 := sub_neg.mpr hcast
  convert tendsto_exp_affine_atTop_of_neg_endpoint
    (b := a / 2 * ((k : ℝ) ^ 2 - (d : ℝ) ^ 2))
    (c := (d : ℝ) - (k : ℝ)) hc using 1
  ext lambda
  rw [show extendedGaussianNaturalTerm a lambda d /
      extendedGaussianNaturalTerm a lambda k =
      Real.exp
        ((lambda * (d : ℝ) - a / 2 * (d : ℝ) ^ 2) -
          (lambda * (k : ℝ) - a / 2 * (k : ℝ) ^ 2)) by
        simp [extendedGaussianNaturalTerm, Real.exp_sub]]
  congr 1
  ring

theorem tendsto_extendedGaussianMean_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (extendedGaussianMean a) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  obtain ⟨k, hk⟩ := exists_nat_gt R
  have hkPos : 0 < (k : ℝ) - R := sub_pos.mpr hk
  have hkMem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have htermLimit : ∀ d ∈ Finset.range (k + 1),
      Tendsto
        (fun lambda : ℝ ↦
          ((d : ℝ) - R) *
            (extendedGaussianNaturalTerm a lambda d /
              extendedGaussianNaturalTerm a lambda k))
        atTop
        (nhds (if d = k then (k : ℝ) - R else 0)) := by
    intro d hd
    by_cases hdk : d = k
    · subst d
      have heq :
          (fun lambda : ℝ ↦
            ((k : ℝ) - R) *
              (extendedGaussianNaturalTerm a lambda k /
                extendedGaussianNaturalTerm a lambda k)) =
            fun _ : ℝ ↦ (k : ℝ) - R := by
        funext lambda
        rw [div_self (ne_of_gt
          (extendedGaussianNaturalTerm_pos a lambda k))]
        ring
      rw [if_pos rfl, heq]
      exact tendsto_const_nhds
    · have hlt : d < k := by
        have hle : d < k + 1 := Finset.mem_range.mp hd
        omega
      simpa [hdk] using
        tendsto_const_nhds.mul
          (tendsto_extendedGaussianNatural_div_natural_atTop a hlt)
  have hsumLimit :
      Tendsto
        (fun lambda : ℝ ↦
          ∑ d ∈ Finset.range (k + 1),
            ((d : ℝ) - R) *
              (extendedGaussianNaturalTerm a lambda d /
                extendedGaussianNaturalTerm a lambda k))
        atTop (nhds ((k : ℝ) - R)) := by
    have h := tendsto_finsetSum (Finset.range (k + 1)) htermLimit
    simpa [hkMem] using h
  have hexcLimit :
      Tendsto
        (fun lambda : ℝ ↦
          (-(R + 1)) *
            (extendedGaussianExceptionalAtom a lambda /
              extendedGaussianNaturalTerm a lambda k))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_extendedGaussianExceptional_div_natural_atTop a k)
  have hscaledLimit :
      Tendsto
        (fun lambda : ℝ ↦
          (-(R + 1)) *
              (extendedGaussianExceptionalAtom a lambda /
                extendedGaussianNaturalTerm a lambda k) +
            ∑ d ∈ Finset.range (k + 1),
              ((d : ℝ) - R) *
                (extendedGaussianNaturalTerm a lambda d /
                  extendedGaussianNaturalTerm a lambda k))
        atTop (nhds ((k : ℝ) - R)) := by
    simpa using hexcLimit.add hsumLimit
  have hscaledPos : ∀ᶠ lambda : ℝ in atTop,
      0 <
        (-(R + 1)) *
            (extendedGaussianExceptionalAtom a lambda /
              extendedGaussianNaturalTerm a lambda k) +
          ∑ d ∈ Finset.range (k + 1),
            ((d : ℝ) - R) *
              (extendedGaussianNaturalTerm a lambda d /
                extendedGaussianNaturalTerm a lambda k) :=
    hscaledLimit.eventually (Ioi_mem_nhds hkPos)
  filter_upwards [hscaledPos] with lambda hscaled
  have htermPos := extendedGaussianNaturalTerm_pos a lambda k
  have htermNe := ne_of_gt htermPos
  have hlowerPos :
      0 <
        -(R + 1) * extendedGaussianExceptionalAtom a lambda +
          ∑ d ∈ Finset.range (k + 1),
            ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d := by
    have hmul := mul_pos hscaled htermPos
    have heq :
        ((-(R + 1)) *
              (extendedGaussianExceptionalAtom a lambda /
                extendedGaussianNaturalTerm a lambda k) +
            ∑ d ∈ Finset.range (k + 1),
              ((d : ℝ) - R) *
                (extendedGaussianNaturalTerm a lambda d /
                  extendedGaussianNaturalTerm a lambda k)) *
            extendedGaussianNaturalTerm a lambda k =
          -(R + 1) * extendedGaussianExceptionalAtom a lambda +
            ∑ d ∈ Finset.range (k + 1),
              ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d := by
      rw [add_mul, Finset.sum_mul]
      simp only [mul_assoc, div_mul_cancel₀ _ htermNe]
    rwa [heq] at hmul
  have hsigned :
      Summable
        (fun d : ℕ ↦
          ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d) := by
    have hfirst := summable_extendedGaussianFirstMoment
      (a := a) (lambda := lambda) ha
    have hmass := summable_extendedGaussianNaturalTerm
      (a := a) (lambda := lambda) ha
    simpa only [sub_mul] using hfirst.sub (hmass.mul_left R)
  have hfiniteLe :
      (∑ d ∈ Finset.range (k + 1),
          ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d) ≤
        ∑' d : ℕ,
          ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d := by
    apply hsigned.sum_le_tsum
    intro d hd
    have hkd : k + 1 ≤ d := by
      simpa [Finset.mem_range, not_lt] using hd
    have hcoef : 0 ≤ (d : ℝ) - R := by
      have : R < (d : ℝ) := lt_of_lt_of_le hk (by exact_mod_cast (show k ≤ d by omega))
      exact sub_nonneg.mpr this.le
    exact mul_nonneg hcoef (extendedGaussianNaturalTerm_pos a lambda d).le
  have htsumIdentity :
      (∑' d : ℕ,
          ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d) =
        (∑' d : ℕ,
            (d : ℝ) * extendedGaussianNaturalTerm a lambda d) -
          R * (∑' d : ℕ,
            extendedGaussianNaturalTerm a lambda d) := by
    have hfirst := summable_extendedGaussianFirstMoment
      (a := a) (lambda := lambda) ha
    have hmass := summable_extendedGaussianNaturalTerm
      (a := a) (lambda := lambda) ha
    calc
      (∑' d : ℕ,
          ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d) =
        ∑' d : ℕ,
          ((d : ℝ) * extendedGaussianNaturalTerm a lambda d -
            R * extendedGaussianNaturalTerm a lambda d) := by
          congr 1
          funext d
          ring
      _ = (∑' d : ℕ,
            (d : ℝ) * extendedGaussianNaturalTerm a lambda d) -
          ∑' d : ℕ, R * extendedGaussianNaturalTerm a lambda d :=
        hfirst.tsum_sub (hmass.mul_left R)
      _ = (∑' d : ℕ,
            (d : ℝ) * extendedGaussianNaturalTerm a lambda d) -
          R * (∑' d : ℕ,
            extendedGaussianNaturalTerm a lambda d) := by
        rw [tsum_mul_left]
  have hdiffPos :
      0 < extendedGaussianFirstNumerator a lambda -
        R * extendedGaussianPartition a lambda := by
    have hcombined :
        0 < -(R + 1) * extendedGaussianExceptionalAtom a lambda +
          ∑' d : ℕ,
            ((d : ℝ) - R) * extendedGaussianNaturalTerm a lambda d :=
      lt_of_lt_of_le hlowerPos (by linarith [hfiniteLe])
    rw [htsumIdentity] at hcombined
    rw [extendedGaussianFirstNumerator, extendedGaussianPartition]
    nlinarith [hcombined]
  have hlt : R < extendedGaussianMean a lambda := by
    rw [extendedGaussianMean]
    apply (lt_div_iff₀
      (extendedGaussianPartition_pos (a := a) (lambda := lambda) ha)).2
    linarith
  exact hlt.le


end

end Erdos625
