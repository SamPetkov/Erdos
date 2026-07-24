import Mathlib

/-!
# Generic corridor tools for the profile argument

This module records four finite-dimensional order and calculus lemmas used by
the planned root-corridor and rounding stages.  They are deliberately stated
for arbitrary real functions.  In particular, nothing here supplies a phase
bracket, a derivative lower bound for the coloring-profile value, or any
asymptotic estimate.
-/

namespace Erdos625

open Set

/-! ## A unique zero in a decreasing corridor -/

/-- A continuous function that is strictly decreasing on a closed interval
and changes sign at its endpoints has a unique zero in the open interval. -/
theorem existsUnique_root_mem_Ioo_of_strictAntiOn
    {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
  (hanti : StrictAntiOn f (Icc a b))
  (hab : a < b) (ha : 0 < f a) (hb : f b < 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ f x = 0 := by
  have hExists : ∃ c ∈ Ioo a b, f c = 0 := by
    exact intermediate_value_Ioo' hab.le hcont ⟨hb, ha⟩
  refine ⟨hExists.choose, hExists.choose_spec, ?_⟩
  intro x hx
  exact hanti.injOn
    (Ioo_subset_Icc_self hx.1)
    (Ioo_subset_Icc_self hExists.choose_spec.1)
    (hx.2.trans hExists.choose_spec.2.symm)

/-- A center-value error strictly smaller than the integrated derivative
margin gives a unique zero in the open symmetric corridor. -/
theorem existsUnique_root_mem_corridor_of_center_bound_deriv_upper
    {psi : ℝ → ℝ} {s0 Delta E D : ℝ}
    (hDelta : 0 < Delta) (hD : 0 < D)
    (hmargin : E < D * Delta)
    (hcenter : |psi s0| ≤ E)
    (hcont : ContinuousOn psi (Icc (s0 - Delta) (s0 + Delta)))
    (hdiff : DifferentiableOn ℝ psi (Ioo (s0 - Delta) (s0 + Delta)))
    (hupper : ∀ s ∈ Ioo (s0 - Delta) (s0 + Delta),
      deriv psi s ≤ -D) :
    ∃! s : ℝ, s ∈ Ioo (s0 - Delta) (s0 + Delta) ∧ psi s = 0 := by
  have hab : s0 - Delta < s0 + Delta := by linarith
  have hanti : StrictAntiOn psi (Icc (s0 - Delta) (s0 + Delta)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
    rw [interior_Icc]
    intro s hs
    linarith [hupper s hs]
  have hrightStep :
      psi (s0 + Delta) - psi s0 ≤ (-D) * ((s0 + Delta) - s0) := by
    refine Convex.image_sub_le_mul_sub_of_deriv_le
      (convex_Icc (s0 - Delta) (s0 + Delta)) hcont ?_ ?_
      s0 ?_ (s0 + Delta) ?_ ?_
    · simpa only [interior_Icc] using hdiff
    · simpa only [interior_Icc] using hupper
    · constructor <;> linarith
    · exact right_mem_Icc.mpr hab.le
    · linarith
  have hleftStep :
      psi s0 - psi (s0 - Delta) ≤ (-D) * (s0 - (s0 - Delta)) := by
    refine Convex.image_sub_le_mul_sub_of_deriv_le
      (convex_Icc (s0 - Delta) (s0 + Delta)) hcont ?_ ?_
      (s0 - Delta) ?_ s0 ?_ ?_
    · simpa only [interior_Icc] using hdiff
    · simpa only [interior_Icc] using hupper
    · exact left_mem_Icc.mpr hab.le
    · constructor <;> linarith
    · linarith
  have hleft : 0 < psi (s0 - Delta) := by
    rcases abs_le.mp hcenter with ⟨hcenterLower, _⟩
    nlinarith
  have hright : psi (s0 + Delta) < 0 := by
    rcases abs_le.mp hcenter with ⟨_, hcenterUpper⟩
    nlinarith
  exact existsUnique_root_mem_Ioo_of_strictAntiOn
    hcont hanti hab hleft hright

/-! ## Integrating a pointwise derivative lower bound -/

/-- A derivative lower bound on the open interval gives the corresponding
finite increment lower bound across the closed interval. -/
theorem derivative_lower_bound_mul_sub_le_sub
    {f : ℝ → ℝ} {a b s : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hlower : ∀ x ∈ Ioo a b, s ≤ deriv f x) :
    s * (b - a) ≤ f b - f a := by
  have hconv : Convex ℝ (Icc a b) := convex_Icc a b
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  refine Convex.mul_sub_le_image_sub_of_le_deriv hconv hcont ?_ ?_
    a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  · rw [hint]
    exact hdiff
  · intro x hx
    rw [hint] at hx
    exact hlower x hx

/-! ## Trapping a target-matching tilt -/

/-- Endpoint mean brackets trap a target-matching point in the same open
interval when the mean map is strictly increasing. -/
theorem tilt_mem_Ioo_of_strictMono_mean_eq
    {mean : ℝ → ℝ} {M target tilt : ℝ}
    (hmono : StrictMono mean)
    (hleft : mean (-M) < target) (hright : target < mean M)
    (heq : mean tilt = target) :
    tilt ∈ Ioo (-M) M := by
  constructor
  · apply hmono.lt_iff_lt.mp
    rw [heq]
    exact hleft
  · apply hmono.lt_iff_lt.mp
    rw [heq]
    exact hright

/-! ## Exact integer rounding at a real root -/

/-- Moving left from a real root by flooring the root and subtracting
`⌈N⌉` creates a displacement of at least `N`.  A nonnegative derivative
lower bound converts that displacement into the stated value decrement. -/
theorem rounded_left_value_le
    {F : ℝ → ℝ} {r N slope : ℝ}
    (hN : 0 < N) (hslope : 0 ≤ slope)
    (hcont : ContinuousOn F
      (Icc ((((⌊r⌋ : ℤ) - ⌈N⌉ : ℤ) : ℝ)) r))
    (hdiff : DifferentiableOn ℝ F
      (Ioo ((((⌊r⌋ : ℤ) - ⌈N⌉ : ℤ) : ℝ)) r))
    (hlower : ∀ x ∈
      Ioo ((((⌊r⌋ : ℤ) - ⌈N⌉ : ℤ) : ℝ)) r,
      slope ≤ deriv F x)
    (hroot : F r = 0) :
    F ((((⌊r⌋ : ℤ) - ⌈N⌉ : ℤ) : ℝ)) ≤ -slope * N := by
  set a : ℝ := (((⌊r⌋ : ℤ) - ⌈N⌉ : ℤ) : ℝ) with ha
  have hint : interior (Icc a r) = Ioo a r := interior_Icc
  have hNle : N ≤ r - a := by
    have hFloor : (⌊r⌋ : ℝ) ≤ r := Int.floor_le r
    have hCeil : N ≤ (⌈N⌉ : ℝ) := Int.le_ceil N
    push_cast [ha]
    linarith
  have hale : a ≤ r := by
    linarith
  have hIncrement := Convex.mul_sub_le_image_sub_of_le_deriv
    (convex_Icc a r) hcont
    (by
      rw [hint]
      exact hdiff)
    (C := slope)
    (by
      rw [hint]
      exact hlower)
    a (left_mem_Icc.mpr hale) r (right_mem_Icc.mpr hale) hale
  rw [hroot] at hIncrement
  have hScaled : slope * N ≤ slope * (r - a) :=
    mul_le_mul_of_nonneg_left hNle hslope
  nlinarith [hIncrement]

end Erdos625
