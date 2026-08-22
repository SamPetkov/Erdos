import Erdos625.CompactFiniteSignedMarginConvergence
import Mathlib.Tactic

/-!
# Evaluating the finite signed margin along moving targets

The compact-uniform theorem is stated with the finite support index and target
as independent variables.  Concrete root geometry supplies sequences
`alpha_n` and `T_n`.  This module provides the exact filter adapter from the
uniform statement to those moving sequences.

The only hypotheses are that the finite support index tends to infinity and
that all sufficiently late targets remain in one fixed compact subinterval of
`(2,5)`.  No convergence of the target sequence is required, which is crucial
because the Erdős phase need not converge.

No root existence, derivative estimate, root-gap asymptotic, first moment,
chromatic lower tail, partial diagonal, skeleton, second moment, or final
Erdős statement is proved here.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Compact-uniform finite-margin convergence may be evaluated along any
support and target sequences that eventually remain in the compact domain. -/
theorem tendsto_finiteSignedFourMargin_sub_limiting_along_compactTarget
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5)
    (alpha : ℕ → ℕ) (target : ℕ → ℝ)
    (hAlpha : Tendsto alpha atTop atTop)
    (hTarget : ∀ᶠ n : ℕ in atTop, target n ∈ Icc A B) :
    Tendsto
      (fun n : ℕ ↦
        finiteSignedFourMargin (alpha n) (target n) -
          (q - fourEntropyLoss (target n)))
      atTop (𝓝 0) := by
  have hUniform :=
    tendstoUniformlyOn_finiteSignedFourMargin hA hAB hB
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  refine Metric.tendsto_atTop.2 ?_
  intro epsilon hepsilon
  have hClose := hUniform epsilon hepsilon
  have hAlong : ∀ᶠ n : ℕ in atTop,
      ∀ target' ∈ Icc A B,
        dist
          (finiteSignedFourMargin (alpha n) target')
          (q - fourEntropyLoss target') < epsilon :=
    hAlpha hClose
  filter_upwards [hAlong, hTarget] with n hn htarget
  have hn' := hn (target n) htarget
  rw [Real.dist_eq] at hn' ⊢
  simpa only [sub_zero] using hn'

/-- Absolute-value form of the moving-target convergence. -/
theorem tendsto_abs_finiteSignedFourMargin_sub_limiting_along_compactTarget
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5)
    (alpha : ℕ → ℕ) (target : ℕ → ℝ)
    (hAlpha : Tendsto alpha atTop atTop)
    (hTarget : ∀ᶠ n : ℕ in atTop, target n ∈ Icc A B) :
    Tendsto
      (fun n : ℕ ↦
        |finiteSignedFourMargin (alpha n) (target n) -
          (q - fourEntropyLoss (target n))|)
      atTop (𝓝 0) := by
  have h :=
    tendsto_finiteSignedFourMargin_sub_limiting_along_compactTarget
      hA hAB hB alpha target hAlpha hTarget
  simpa using h.abs

#print axioms tendsto_finiteSignedFourMargin_sub_limiting_along_compactTarget
#print axioms tendsto_abs_finiteSignedFourMargin_sub_limiting_along_compactTarget

end

end Erdos625