import Erdos625.ColoringProfileDeficitTilt
import Erdos625.ColoringProfileDeficitUniformMeanConvergence
import Erdos625.ExtendedGaussianTilt

/-!
# Uniform convergence of selected deficit tilts

This module transfers uniform convergence of the finite deficit means to
uniform convergence of their selected inverse tilts on every compact target
interval strictly above `-1`.

The proof order is important.  First, the finite selector theorem supplies a
single eventual tilt bound simultaneously for every target in the compact
interval.  Independently, the limiting selector is trapped on the same kind
of bounded interval.  Only then is uniform mean convergence invoked.  A
strictly positive compact lower bound for the limiting variance is integrated
to a quantitative lower separation, and `uniform_inverse_close_of_lower_separation`
converts the mean error into inverse-parameter error.  No selected-tilt bound
is assumed through a Gaussian envelope.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

/-- On every compact target interval `[A,B]` with `-1 < A`, the selected
finite deficit tilt converges uniformly to the selected limiting extended
Gaussian tilt. -/
theorem tendstoUniformlyOn_profileDeficitTilt
    {A B : ℝ} (hA : -1 < A) (hAB : A ≤ B) :
    TendstoUniformlyOn
      (fun alpha target ↦ profileDeficitTilt alpha target)
      (fun target ↦ extendedGaussianTilt (Real.log 2) target)
      atTop (Icc A B) := by
  have hq : 0 < Real.log 2 := by positivity
  obtain ⟨Mfinite, hMfinite, hfiniteBound⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      hA hAB
  obtain ⟨Mlimit, hMlimit, hlimitBound⟩ :=
    exists_abs_extendedGaussianTilt_le_on_compact
      hq hA hAB
  let M : ℝ := max Mfinite Mlimit
  have hMfiniteM : Mfinite ≤ M := by
    exact le_max_left Mfinite Mlimit
  have hMlimitM : Mlimit ≤ M := by
    exact le_max_right Mfinite Mlimit
  have hM : 0 ≤ M := hMfinite.trans hMfiniteM
  obtain ⟨c, hc, hcLower⟩ :=
    exists_pos_extendedGaussianRawVariance_lower_bound_on_Icc
      (Real.log 2) M hq hM
  have hseparation :
      ∀ u ∈ Icc (-M) M, ∀ v ∈ Icc (-M) M,
        c * |u - v| ≤
          |extendedGaussianMean (Real.log 2) u -
            extendedGaussianMean (Real.log 2) v| :=
    extendedGaussianMean_lower_separation_on_Icc
      (Real.log 2) M c hq hc hcLower
  have hmeanUniform := tendstoUniformlyOn_profileDeficitMean M
  rw [Metric.tendstoUniformlyOn_iff] at hmeanUniform ⊢
  intro epsilon hepsilon
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hmeanClose := hmeanUniform (c * delta) (mul_pos hc hdelta)
  filter_upwards [hfiniteBound, hmeanClose,
      eventually_gt_atTop 0] with
      alpha hfiniteAlpha hmeanAlpha halpha
  have hfiniteRange : ∀ target ∈ Icc A B,
      profileDeficitTilt alpha target ∈ Icc (-M) M := by
    intro target htarget
    exact abs_le.mp
      ((hfiniteAlpha target htarget).2.trans hMfiniteM)
  have hlimitRange : ∀ target ∈ Icc A B,
      extendedGaussianTilt (Real.log 2) target ∈ Icc (-M) M := by
    intro target htarget
    exact abs_le.mp
      ((hlimitBound target htarget).trans hMlimitM)
  have hfiniteRoot : ∀ target ∈ Icc A B,
      profileDeficitMean alpha
          (profileDeficitTilt alpha target) = target := by
    intro target htarget
    exact profileDeficitMean_profileDeficitTilt halpha
      (hfiniteAlpha target htarget).1
  have hlimitRoot : ∀ target ∈ Icc A B,
      extendedGaussianMean (Real.log 2)
          (extendedGaussianTilt (Real.log 2) target) = target := by
    intro target htarget
    exact extendedGaussianMean_extendedGaussianTilt hq
      (hA.trans_le htarget.1)
  have hmeanError : ∀ lambda ∈ Icc (-M) M,
      |profileDeficitMean alpha lambda -
          extendedGaussianMean (Real.log 2) lambda| ≤
        c * delta := by
    intro lambda hlambda
    have hclose := hmeanAlpha lambda hlambda
    rw [Real.dist_eq] at hclose
    simpa only [abs_sub_comm] using hclose.le
  have hinverse :=
    uniform_inverse_close_of_lower_separation
      (f := profileDeficitMean alpha)
      (g := extendedGaussianMean (Real.log 2))
      (x := profileDeficitTilt alpha)
      (y := extendedGaussianTilt (Real.log 2))
      (L := -M) (R := M) (A := A) (B := B)
      (c := c) (ε := delta)
      hc hfiniteRange hlimitRange hfiniteRoot hlimitRoot
      hseparation hmeanError
  intro target htarget
  rw [Real.dist_eq]
  calc
    |extendedGaussianTilt (Real.log 2) target -
        profileDeficitTilt alpha target| =
        |profileDeficitTilt alpha target -
          extendedGaussianTilt (Real.log 2) target| := abs_sub_comm _ _
    _ ≤ delta := hinverse target htarget
    _ < epsilon := by
      dsimp [delta]
      linarith

end

end Erdos625
