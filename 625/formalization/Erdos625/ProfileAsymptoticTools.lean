import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Generic analytic tools for profile asymptotics

This module records three small analytic facts used when passing from finite
profile identities to asymptotic estimates: the exceptional top-deficit
correction tends to zero, normalized first moments are stable under explicit
numerator and denominator errors, and the change of variables `s = n / k`
has the expected product-chain derivative.

These results do not prove growing-support convergence, a bounded selected
tilt, a phase root, or a root-slope estimate.  Those require separate uniform
estimates before these tools can be applied.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-- The exceptional deficit `-1` logarithmic correction tends to zero. -/
theorem tendsto_log_nat_div_nat_add_one :
    Tendsto
      (fun a : ℕ ↦
        Real.log ((a : ℝ) / ((a : ℝ) + 1)))
      atTop (𝓝 0) := by
  have hratio :
      Tendsto (fun a : ℕ ↦ (a : ℝ) / ((a : ℝ) + 1)) atTop (𝓝 1) := by
    have hinv :
        Tendsto (fun a : ℕ ↦ ((a : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      apply Tendsto.comp tendsto_inv_atTop_zero
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have hsub :
        Tendsto (fun a : ℕ ↦ 1 - ((a : ℝ) + 1)⁻¹) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    simp only [sub_zero] at hsub
    refine hsub.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hne : (a : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hlog :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  change Tendsto
    (fun a : ℕ ↦ Real.log ((a : ℝ) / ((a : ℝ) + 1)))
    atTop (𝓝 (Real.log 1)) at hlog
  simpa using hlog

/-- Explicit stability of a quotient when both normalizing denominators are
uniformly separated from zero.  The bound is deterministic and does not
supply any of the four error estimates in its hypotheses. -/
theorem abs_div_sub_div_le_of_denominator_ge
    {A a B b epsA epsB M z : ℝ}
    (hz : 0 < z)
    (hepsA : 0 ≤ epsA) (hepsB : 0 ≤ epsB) (hM : 0 ≤ M)
    (hB : z ≤ B) (hb : z ≤ b)
    (hAa : |A - a| ≤ epsA)
    (hBb : |B - b| ≤ epsB)
    (ha : |a| ≤ M) :
    |A / B - a / b| ≤
      epsA / z + M * epsB / z ^ 2 := by
  have hBne : B ≠ 0 := by linarith
  have hbne : b ≠ 0 := by linarith
  have hidentity :
      A / B - a / b =
        (A - a) / B + a * (b - B) / (B * b) := by
    field_simp [hBne, hbne]
    ring
  have htriangle :
      |A / B - a / b| ≤
        |(A - a) / B| + |a * (b - B) / (B * b)| := by
    rw [hidentity]
    exact abs_add_le _ _
  refine le_trans htriangle (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_nonneg (by linarith : 0 ≤ B)]
    gcongr
  · rw [abs_div, abs_mul]
    gcongr
    · rwa [abs_sub_comm]
    · rw [abs_of_nonneg] <;> nlinarith

/-- Exact chain rule for the reparametrization `s = n / k` used to pass from
a normalized profile objective to its derivative in the real part count. -/
theorem hasDerivAt_mul_comp_div
    {psi : ℝ → ℝ} {n k d : ℝ}
    (hk : k ≠ 0)
    (hpsi : HasDerivAt psi d (n / k)) :
    HasDerivAt
      (fun x : ℝ ↦ x * psi (n / x))
      (psi (n / k) - (n / k) * d) k := by
  have hdiv :
      HasDerivAt (fun x : ℝ ↦ n / x) (-n / k ^ 2) k := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hk).const_mul n
  have hraw : HasDerivAt
      (fun x : ℝ ↦ x * psi (n / x))
      (psi (n / k) + k * (d * (-n / k ^ 2))) k := by
    have hprod := (hasDerivAt_id k).mul (hpsi.comp k hdiv)
    have hprod' := hprod.congr_of_eventuallyEq
      (f₁ := fun x : ℝ ↦ x * psi (n / x))
      (Filter.Eventually.of_forall fun _ ↦ rfl)
    simpa only [Function.comp_apply, id_eq, one_mul] using hprod'
  apply hraw.congr_deriv
  field_simp [hk]
  ring

/-- The exact `s = n/k` chain rule with an additive scalar term, together
with a quantitative positive lower bound for the corresponding part-count
derivative. -/
theorem hasDerivAt_mul_comp_div_add_const_and_lower
    {psi : ℝ → ℝ} {n k c d E sMin D : ℝ}
    (hk : k ≠ 0)
    (hsMin : 0 ≤ sMin) (hD : 0 ≤ D)
    (hs : sMin ≤ n / k)
    (hpsi : HasDerivAt psi d (n / k))
    (hvalue : -E ≤ psi (n / k) + c)
    (hderiv : d ≤ -D) :
    HasDerivAt
      (fun x : ℝ ↦ x * (psi (n / x) + c))
      (psi (n / k) + c - (n / k) * d) k ∧
    -E + sMin * D ≤ psi (n / k) + c - (n / k) * d := by
  constructor
  · simpa using hasDerivAt_mul_comp_div hk (hpsi.add_const c)
  · nlinarith

end

end Erdos625
