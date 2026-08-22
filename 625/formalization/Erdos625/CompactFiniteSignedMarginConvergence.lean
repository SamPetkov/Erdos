import Erdos625.CompactUnrestrictedEntropyConvergence
import Erdos625.FourDeficitScoreConvergence
import Mathlib.Tactic

/-!
# Compact-uniform convergence of the finite signed four-size margin

The exact signed-versus-unrestricted objective gap contains the finite margin

`q - finiteSignedFourEntropyLoss alpha T`.

Its decomposition has two independent finite errors: the four-score entropy
error and the unrestricted finite-entropy error.  The former converges
uniformly on the whole interior interval `(2,5)`; the latter now converges
uniformly on every compact subinterval.

This module combines those two results.  It does not construct roots or assume
a root-gap asymptotic.  Its output is the coefficient convergence needed to
turn the exact secant/root-gap ledger into the manuscript phase-varying root-
gap expansion.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- On every compact target interval strictly inside `(2,5)`, the exact finite
signed margin converges uniformly to the manuscript limiting margin
`q - fourEntropyLoss T`. -/
theorem tendstoUniformlyOn_finiteSignedFourMargin
    {A B : ℝ} (hA : 2 < A) (hAB : A ≤ B) (hB : B < 5) :
    TendstoUniformlyOn
      (fun alpha target ↦ finiteSignedFourMargin alpha target)
      (fun target ↦ q - fourEntropyLoss target)
      atTop (Icc A B) := by
  have hUnrestricted :=
    tendstoUniformlyOn_finiteUnrestrictedDeficitEntropy
      hA hAB hB
  rw [Metric.tendstoUniformlyOn_iff] at hUnrestricted ⊢
  intro epsilon hepsilon
  let delta : ℝ := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hUnrestrictedClose := hUnrestricted delta hdelta
  obtain ⟨N, hFourN⟩ :=
    eventually_uniform_fourDeficitOptimizedValue delta hdelta
  have hFourClose : ∀ᶠ alpha : ℕ in atTop,
      ∀ target ∈ Icc A B,
        |finiteFourScoreEntropyError alpha target| < delta := by
    filter_upwards [eventually_ge_atTop N] with alpha halpha
    intro target htarget
    have htargetInterior : target ∈ Ioo (2 : ℝ) 5 :=
      ⟨hA.trans_le htarget.1,
        htarget.2.trans_lt hB⟩
    have h := hFourN alpha halpha target htargetInterior
    unfold finiteFourScoreEntropyError
    simpa only [abs_sub_comm] using h
  filter_upwards [hUnrestrictedClose, hFourClose] with
    alpha hUnrestrictedAlpha hFourAlpha
  intro target htarget
  have hUnrestrictedError :
      |finiteUnrestrictedEntropyError alpha target| < delta := by
    have h := hUnrestrictedAlpha target htarget
    rw [Real.dist_eq, abs_sub_comm] at h
    simpa only [finiteUnrestrictedEntropyError] using h
  have hMarginIdentity :
      finiteSignedFourMargin alpha target -
          (q - fourEntropyLoss target) =
        -finiteFourScoreEntropyError alpha target -
          finiteUnrestrictedEntropyError alpha target := by
    rw [finiteSignedFourMargin_eq_limiting_sub_errors]
    ring
  rw [Real.dist_eq, abs_sub_comm, hMarginIdentity]
  calc
    |-finiteFourScoreEntropyError alpha target -
        finiteUnrestrictedEntropyError alpha target| =
      |finiteFourScoreEntropyError alpha target +
        finiteUnrestrictedEntropyError alpha target| := by
      rw [show -finiteFourScoreEntropyError alpha target -
          finiteUnrestrictedEntropyError alpha target =
        -(finiteFourScoreEntropyError alpha target +
          finiteUnrestrictedEntropyError alpha target) by ring,
        abs_neg]
    _ ≤ |finiteFourScoreEntropyError alpha target| +
        |finiteUnrestrictedEntropyError alpha target| :=
      abs_add_le _ _
    _ < delta + delta :=
      add_lt_add (hFourAlpha target htarget) hUnrestrictedError
    _ = epsilon := by
      dsimp only [delta]
      ring

#print axioms tendstoUniformlyOn_finiteSignedFourMargin

end

end Erdos625