import Erdos625.ExtendedGaussianCalculus
import Erdos625.ExtendedGaussianEndpoints

/-!
# Ordered brackets and inversion of endpoint-controlled means

The generic lemmas in this module convert lower/upper endpoint limits into
ordered finite brackets and combine such a bracket with continuity and strict
monotonicity to obtain unique inversion.  The final corollaries apply these
interfaces to the extended tilted-Gaussian deficit mean.
-/

open Filter
open scoped Topology

namespace Erdos625

/-- Endpoint limits produce two ordered finite parameters that bracket every
target in a prescribed compact interval above the lower endpoint. -/
theorem exists_ordered_mean_bracket
    {m : ℝ → ℝ} {ell A B : ℝ}
    (hbot : Tendsto m atBot (nhds ell))
    (htop : Tendsto m atTop atTop)
    (hell : ell < A) (_hAB : A ≤ B) :
    ∃ L R : ℝ, L < R ∧ m L < A ∧ B < m R := by
  have hleft : ∀ᶠ L : ℝ in atBot, m L < A :=
    hbot.eventually (Iio_mem_nhds hell)
  obtain ⟨L, hL⟩ := hleft.exists
  have hright : ∀ᶠ R : ℝ in atTop, B < m R :=
    htop.eventually_gt_atTop B
  have horder : ∀ᶠ R : ℝ in atTop, L < R := eventually_gt_atTop L
  obtain ⟨R, hLR, hR⟩ := (horder.and hright).exists
  exact ⟨L, R, hLR, hL, hR⟩

/-- A continuous strictly increasing mean with lower endpoint `ell` and no
upper endpoint takes every target above `ell` exactly once. -/
theorem existsUnique_eq_of_strictMono_endpoint_limits
    {m : ℝ → ℝ} {ell T : ℝ}
    (hcont : Continuous m)
    (hmono : StrictMono m)
    (hbot : Tendsto m atBot (nhds ell))
    (htop : Tendsto m atTop atTop)
    (hT : ell < T) :
    ∃! lambda : ℝ, m lambda = T := by
  obtain ⟨L, R, hLR, hLT, hTR⟩ :=
    exists_ordered_mean_bracket hbot htop hT le_rfl
  obtain ⟨lambda, _, hlambda⟩ :=
    intermediate_value_Icc hLR.le hcont.continuousOn
      ⟨hLT.le, hTR.le⟩
  refine ⟨lambda, hlambda, ?_⟩
  intro y hy
  apply hmono.injective
  exact hy.trans hlambda.symm

/-- Every compact target interval strictly above `-1` is bracketed by two
finite tilt parameters for the extended Gaussian mean. -/
theorem exists_ordered_extendedGaussianMean_bracket
    {a A B : ℝ} (ha : 0 < a) (hA : -1 < A) (hAB : A ≤ B) :
    ∃ L R : ℝ, L < R ∧
      extendedGaussianMean a L < A ∧ B < extendedGaussianMean a R := by
  exact exists_ordered_mean_bracket
    (tendsto_extendedGaussianMean_atBot a ha)
    (tendsto_extendedGaussianMean_atTop a ha) hA hAB

/-- Every target deficit strictly above `-1` is attained by a unique finite
tilt in the extended Gaussian profile. -/
theorem existsUnique_extendedGaussianMean_eq
    {a T : ℝ} (ha : 0 < a) (hT : -1 < T) :
    ∃! lambda : ℝ, extendedGaussianMean a lambda = T := by
  exact existsUnique_eq_of_strictMono_endpoint_limits
    (continuous_extendedGaussianMean a ha)
    (strictMono_extendedGaussianMean a ha)
    (tendsto_extendedGaussianMean_atBot a ha)
    (tendsto_extendedGaussianMean_atTop a ha) hT

end Erdos625
