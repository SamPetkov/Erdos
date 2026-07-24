import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Quantitative compact inverse-convergence tools

This module isolates three generic facts used to transfer convergence of
strictly monotone mean maps to convergence of their selected inverse
parameters.  The hypotheses expose the quantitative separation estimate
explicitly; strict monotonicity alone is not silently treated as a uniform
inverse modulus.
-/

namespace Erdos625

open Set

noncomputable section

/-- A continuous pointwise-positive function on a nonempty compact interval
has a uniform strictly positive lower bound there. -/
theorem exists_pos_lower_bound_on_Icc
    {f : ℝ → ℝ} {L R : ℝ}
    (hLR : L ≤ R)
    (hcont : ContinuousOn f (Icc L R))
    (hpos : ∀ x ∈ Icc L R, 0 < f x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Icc L R, c ≤ f x := by
  obtain ⟨x₀, hx₀, hmin⟩ :=
    IsCompact.exists_isMinOn isCompact_Icc ⟨L, left_mem_Icc.mpr hLR⟩ hcont
  exact ⟨f x₀, hpos x₀ hx₀, hmin⟩

/-- A quantitative lower separation for a limiting mean converts function
error at an approximate inverse into parameter error. -/
theorem inverse_error_le_of_lower_separation
    {f g : ℝ → ℝ} {x y target c ε : ℝ}
    (hc : 0 < c)
    (hsep : c * |x - y| ≤ |f x - f y|)
    (hx : f x = target)
    (hy : g y = target)
    (herr : |g y - f y| ≤ ε) :
    |x - y| ≤ ε / c := by
  have h : c * |x - y| ≤ ε := by
    calc
      c * |x - y| ≤ |f x - f y| := hsep
      _ = |g y - f y| := by rw [hx, ← hy]
      _ ≤ ε := herr
  rw [le_div_iff₀ hc, mul_comm]
  exact h

/-- One quantitative step transferring uniform convergence of mean maps on a
parameter interval to uniform convergence of their target-matching inverses. -/
theorem uniform_inverse_close_of_lower_separation
    {f g x y : ℝ → ℝ} {L R A B c ε : ℝ}
    (hc : 0 < c)
    (hxRange : ∀ T ∈ Icc A B, x T ∈ Icc L R)
    (hyRange : ∀ T ∈ Icc A B, y T ∈ Icc L R)
    (hxRoot : ∀ T ∈ Icc A B, f (x T) = T)
    (hyRoot : ∀ T ∈ Icc A B, g (y T) = T)
    (hsep : ∀ u ∈ Icc L R, ∀ v ∈ Icc L R,
      c * |u - v| ≤ |g u - g v|)
    (hunif : ∀ z ∈ Icc L R, |f z - g z| ≤ c * ε) :
    ∀ T ∈ Icc A B, |x T - y T| ≤ ε := by
  intro T hT
  have hxT := hxRange T hT
  have hyT := hyRange T hT
  have hstep := hsep (x T) hxT (y T) hyT
  have hclose := hunif (x T) hxT
  have hrootFinite := hxRoot T hT
  have hrootLimit := hyRoot T hT
  have hscaled : c * |x T - y T| ≤ c * ε := by
    calc
      c * |x T - y T| ≤ |g (x T) - g (y T)| := hstep
      _ = |f (x T) - g (x T)| := by
        rw [hrootFinite, hrootLimit, abs_sub_comm]
      _ ≤ c * ε := hclose
  exact le_of_mul_le_mul_left hscaled hc

end

end Erdos625
