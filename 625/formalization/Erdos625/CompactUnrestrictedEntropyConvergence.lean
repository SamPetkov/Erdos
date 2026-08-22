import Erdos625.FiniteUnrestrictedEntropyErrorBound
import Erdos625.ColoringProfileDeficitTiltConvergence
import Erdos625.ColoringProfileDeficitUniformMomentConvergence
import Erdos625.ExtendedGaussianCalculus
import Mathlib.Tactic

/-!
# Compact-uniform convergence of the finite unrestricted entropy

The exact objective-gap ledger and the deterministic three-term entropy bound
reduce the remaining unrestricted finite-to-limiting passage to existing
uniform partition and selected-tilt convergence.

This module supplies the last analytic transport.  On every compact target
interval strictly inside `(2,5)`, the attained finite unrestricted deficit
entropy converges uniformly to the extended-Gaussian entropy value.

The proof uses one common bounded tilt interval for all targets and all
sufficiently large finite supports.  The limiting partition is Lipschitz on
that interval, with an explicit first-moment derivative bound.  Since both
partition functions are at least one, the logarithm introduces no denominator
loss.

No root existence, derivative corridor, root-gap asymptotic, first moment,
chromatic lower tail, partial diagonal, skeleton, second moment, or final
Erdős statement is proved here.
-/

namespace Erdos625

open Filter Set
open scoped Topology BigOperators

noncomputable section

set_option autoImplicit false

/-- Explicit derivative bound for the extended-Gaussian partition on the
bounded tilt interval `[-M,M]`. -/
noncomputable def extendedGaussianPartitionLipschitzBound (M : ℝ) : ℝ :=
  Real.exp M +
    ∑' d : ℕ,
      (d : ℝ) * extendedGaussianNaturalTerm q M d

/-- The partition Lipschitz constant is strictly positive. -/
theorem extendedGaussianPartitionLipschitzBound_pos (M : ℝ) :
    0 < extendedGaussianPartitionLipschitzBound M := by
  unfold extendedGaussianPartitionLipschitzBound
  exact add_pos_of_pos_of_nonneg (Real.exp_pos M)
    (tsum_nonneg fun d ↦ mul_nonneg (Nat.cast_nonneg d)
      (extendedGaussianNaturalTerm_pos q M d).le)

/-- The extended-Gaussian partition is Lipschitz on every bounded tilt
interval, with the explicit first-moment bound above. -/
theorem abs_extendedGaussianPartition_sub_le_on_Icc
    (M : ℝ) {u v : ℝ}
    (hu : u ∈ Icc (-M) M) (hv : v ∈ Icc (-M) M) :
    |extendedGaussianPartition q u -
        extendedGaussianPartition q v| ≤
      extendedGaussianPartitionLipschitzBound M * |u - v| := by
  let C : ℝ := extendedGaussianPartitionLipschitzBound M
  have hC : 0 ≤ C :=
    (extendedGaussianPartitionLipschitzBound_pos M).le
  have hDerivativeBound : ∀ x ∈ Icc (-M) M,
      ‖extendedGaussianFirstNumerator q x‖ ≤ C := by
    intro x hx
    rw [Real.norm_eq_abs]
    dsimp only [C, extendedGaussianPartitionLipschitzBound]
    simpa only [q] using
      (abs_extendedGaussianFirstNumerator_le_upper_tilt hx)
  rcases le_total u v with huv | hvu
  · have hCont : ContinuousOn (extendedGaussianPartition q) (Icc u v) := by
      intro x _
      exact (hasDerivAt_extendedGaussianPartition q x q_pos).continuousAt.continuousWithinAt
    have hDeriv : ∀ x ∈ Ico u v,
        HasDerivWithinAt (extendedGaussianPartition q)
          (extendedGaussianFirstNumerator q x) (Ici x) x := by
      intro x _
      exact (hasDerivAt_extendedGaussianPartition q x q_pos).hasDerivWithinAt
    have hBound : ∀ x ∈ Ico u v,
        ‖extendedGaussianFirstNumerator q x‖ ≤ C := by
      intro x hx
      apply hDerivativeBound x
      exact ⟨hu.1.trans hx.1,
        hx.2.le.trans hv.2⟩
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment
      hCont hDeriv hBound v (right_mem_Icc.mpr huv)
    rw [Real.norm_eq_abs, abs_sub_comm] at h
    have habs : |u - v| = v - u := by
      rw [abs_of_nonpos (sub_nonpos.mpr huv)]
      ring
    rw [habs]
    simpa only [C] using h
  · have hCont : ContinuousOn (extendedGaussianPartition q) (Icc v u) := by
      intro x _
      exact (hasDerivAt_extendedGaussianPartition q x q_pos).continuousAt.continuousWithinAt
    have hDeriv : ∀ x ∈ Ico v u,
        HasDerivWithinAt (extendedGaussianPartition q)
          (extendedGaussianFirstNumerator q x) (Ici x) x := by
      intro x _
      exact (hasDerivAt_extendedGaussianPartition q x q_pos).hasDerivWithinAt
    have hBound : ∀ x ∈ Ico v u,
        ‖extendedGaussianFirstNumerator q x‖ ≤ C := by
      intro x hx
      apply hDerivativeBound x
      exact ⟨hv.1.trans hx.1,
        hx.2.le.trans hu.2⟩
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment
      hCont hDeriv hBound u (right_mem_Icc.mpr hvu)
    rw [Real.norm_eq_abs] at h
    have habs : |u - v| = u - v := by
      rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    rw [habs]
    simpa only [C] using h

/-- The limiting log-partition inherits the same Lipschitz bound because the
partition is everywhere at least one. -/
theorem abs_log_extendedGaussianPartition_sub_le_on_Icc
    (M : ℝ) {u v : ℝ}
    (hu : u ∈ Icc (-M) M) (hv : v ∈ Icc (-M) M) :
    |Real.log (extendedGaussianPartition q u) -
        Real.log (extendedGaussianPartition q v)| ≤
      extendedGaussianPartitionLipschitzBound M * |u - v| := by
  exact
    (abs_log_sub_log_le_abs_sub_of_one_le
      (one_le_extendedGaussianPartition q_pos)
      (one_le_extendedGaussianPartition q_pos)).trans
        (abs_extendedGaussianPartition_sub_le_on_Icc M hu hv)

/-- On every compact target interval strictly inside `(2,5)`, the finite
unrestricted deficit entropy converges uniformly to the limiting
extended-Gaussian entropy. -/
theorem tendstoUniformlyOn_finiteUnrestrictedDeficitEntropy
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5) :
    TendstoUniformlyOn
      (fun alpha target ↦
        finiteUnrestrictedDeficitEntropy alpha target)
      extendedGaussianEntropyValue
      atTop (Icc A B) := by
  have hAneg : -1 < A := by linarith
  obtain ⟨Mfinite, hMfinite, hFiniteBound⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
      hAneg hAB
  obtain ⟨Mlimit, hMlimit, hLimitBound⟩ :=
    exists_abs_extendedGaussianTilt_le_on_compact
      q_pos hAneg hAB
  let M : ℝ := max Mfinite Mlimit
  have hMfiniteM : Mfinite ≤ M := le_max_left _ _
  have hMlimitM : Mlimit ≤ M := le_max_right _ _
  have hM : 0 ≤ M := hMfinite.trans hMfiniteM
  let C : ℝ := extendedGaussianPartitionLipschitzBound M
  have hC : 0 < C := by
    exact extendedGaussianPartitionLipschitzBound_pos M
  let Tbound : ℝ := max |A| |B|
  have hTbound : 0 ≤ Tbound :=
    (abs_nonneg A).trans (le_max_left _ _)
  have hPartitionUniform :=
    tendstoUniformlyOn_profileDeficitPartition M
  have hTiltUniform :=
    tendstoUniformlyOn_profileDeficitTilt hAneg hAB
  rw [Metric.tendstoUniformlyOn_iff] at hPartitionUniform
  rw [Metric.tendstoUniformlyOn_iff] at hTiltUniform
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let scale : ℝ := 1 + C + Tbound
  have hscale : 0 < scale := by
    dsimp only [scale]
    linarith
  let delta : ℝ := epsilon / scale
  have hdelta : 0 < delta := div_pos hepsilon hscale
  have hPartitionClose := hPartitionUniform delta hdelta
  have hTiltClose := hTiltUniform delta hdelta
  filter_upwards [hFiniteBound, hPartitionClose, hTiltClose,
    eventually_gt_atTop 0] with
    alpha hFiniteAlpha hPartitionAlpha hTiltAlpha halpha
  intro target htarget
  have htargetInterior : target ∈ Ioo (2 : ℝ) 5 :=
    ⟨hA.trans_le htarget.1,
      htarget.2.trans_lt hB⟩
  have hFiniteTilt : profileDeficitTilt alpha target ∈ Icc (-M) M :=
    abs_le.mp ((hFiniteAlpha target htarget).2.trans hMfiniteM)
  have hLimitTilt : extendedGaussianTilt q target ∈ Icc (-M) M :=
    abs_le.mp ((hLimitBound target htarget).trans hMlimitM)
  have hPartitionError :
      |profileDeficitPartition alpha
          (profileDeficitTilt alpha target) -
        extendedGaussianPartition q
          (profileDeficitTilt alpha target)| < delta := by
    have h := hPartitionAlpha
      (profileDeficitTilt alpha target) hFiniteTilt
    rw [Real.dist_eq, abs_sub_comm] at h
    simpa only [q] using h
  have hTiltError :
      |profileDeficitTilt alpha target -
        extendedGaussianTilt q target| < delta := by
    have h := hTiltAlpha target htarget
    rw [Real.dist_eq, abs_sub_comm] at h
    simpa only [q] using h
  have hLogTransport :
      |Real.log
          (extendedGaussianPartition q
            (profileDeficitTilt alpha target)) -
        Real.log
          (extendedGaussianPartition q
            (extendedGaussianTilt q target))| ≤
      C * |profileDeficitTilt alpha target -
        extendedGaussianTilt q target| := by
    dsimp only [C]
    exact abs_log_extendedGaussianPartition_sub_le_on_Icc
      M hFiniteTilt hLimitTilt
  have hLogTransportDelta :
      |Real.log
          (extendedGaussianPartition q
            (profileDeficitTilt alpha target)) -
        Real.log
          (extendedGaussianPartition q
            (extendedGaussianTilt q target))| ≤
      C * delta := by
    exact hLogTransport.trans
      (mul_le_mul_of_nonneg_left hTiltError.le hC.le)
  have htargetAbs : |target| ≤ Tbound :=
    abs_le_max_abs_abs htarget.1 htarget.2
  have hTargetTilt :
      |target| *
          |profileDeficitTilt alpha target -
            extendedGaussianTilt q target| ≤
        Tbound * delta :=
    mul_le_mul htargetAbs hTiltError.le
      (abs_nonneg _) hTbound
  have hError := abs_finiteUnrestrictedEntropyError_le
    alpha halpha htargetInterior
  rw [Real.dist_eq, abs_sub_comm]
  change |finiteUnrestrictedEntropyError alpha target| < epsilon
  calc
    |finiteUnrestrictedEntropyError alpha target| ≤
        |profileDeficitPartition alpha
            (profileDeficitTilt alpha target) -
          extendedGaussianPartition q
            (profileDeficitTilt alpha target)| +
        |Real.log
            (extendedGaussianPartition q
              (profileDeficitTilt alpha target)) -
          Real.log
            (extendedGaussianPartition q
              (extendedGaussianTilt q target))| +
        |target| *
          |profileDeficitTilt alpha target -
            extendedGaussianTilt q target| := hError
    _ < delta + C * delta + Tbound * delta := by
      have hSumLe :
          |Real.log
              (extendedGaussianPartition q
                (profileDeficitTilt alpha target)) -
            Real.log
              (extendedGaussianPartition q
                (extendedGaussianTilt q target))| +
          |target| *
            |profileDeficitTilt alpha target -
              extendedGaussianTilt q target| ≤
          C * delta + Tbound * delta :=
        add_le_add hLogTransportDelta hTargetTilt
      linarith
    _ = epsilon := by
      dsimp only [delta, scale]
      field_simp [hscale.ne']

#print axioms extendedGaussianPartitionLipschitzBound_pos
#print axioms abs_extendedGaussianPartition_sub_le_on_Icc
#print axioms abs_log_extendedGaussianPartition_sub_le_on_Icc
#print axioms tendstoUniformlyOn_finiteUnrestrictedDeficitEntropy

end

end Erdos625