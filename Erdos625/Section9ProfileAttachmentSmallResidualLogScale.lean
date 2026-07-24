import Erdos625.Section9ProfileAttachmentSmallResidualScale
import Erdos625.PhaseEstimates
import Mathlib.Tactic

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

set_option autoImplicit false

theorem eventually_profileHighSkeletonAttachment_le_smallResidual_logScale :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ {b : ℕ} {k : ColoringProfile b}
          (row₀ : OrderedProfilePartition n k) (U : ℕ),
          U ≤ phaseNat n →
          (∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) →
          ∀ demand : ProfileCanonicalHighSkeleton k U,
            (canonicalDemandResidualTotal (profileBlockMargin k)
                (profileBlockMargin k) U demand : ℝ) <
                (n : ℝ) / Real.log (n : ℝ) ^ 6 →
            profileHighSkeletonAttachment row₀ U demand ≤
              ENNReal.ofReal
                (Real.exp (C * ((n : ℝ) / Real.log (n : ℝ) ^ 5))) := by
  refine ⟨2 * Real.log 2,
    mul_nonneg (by norm_num) (Real.log_nonneg one_le_two), ?_⟩
  filter_upwards
    [eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
      eventually_log_growth_bounds] with n hphase hlog
  intro b k row₀ U hU hcap demand hm
  have hUreal : (U : ℝ) ≤ 4 * Real.log (n : ℝ) :=
    (Nat.cast_le.mpr hU).trans hphase.2
  have h := profileHighSkeletonAttachment_le_smallResidualExpScale
    row₀ U hcap demand (Real.log (n : ℝ)) 4 hlog.1 (by norm_num) hUreal hm.le
  convert h using 1 ; ring

end

end Erdos625
