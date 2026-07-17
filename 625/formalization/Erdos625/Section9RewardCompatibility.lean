import Erdos625.LocalSignReward
import Erdos625.Section9CappedFixedFExpansion

/-!
# Section IX: compatibility of the two local reward presentations

The fixed-`F` threshold expansion and the small-residual deterministic bound
were developed from two syntactically different presentations of the same
local reward.  This module records their exact equality.
-/

namespace Erdos625

/-- The fixed-`F` residual reward is exactly the local sign reward. -/
theorem residualReward_eq_localSignRewardNat (x : ℕ) :
    residualReward x = localSignRewardNat x := by
  by_cases h : x ≤ 2
  · have hnot : ¬ 3 ≤ x := by omega
    simp [residualReward, localSignRewardNat, h, hnot]
  · have hthree : 3 ≤ x := by omega
    simp [residualReward, localSignRewardNat, h, hthree]

/-- Consequently, the threshold increment is the discrete increment of the
local sign reward. -/
theorem residualRewardIncrement_eq_localSignRewardNat_sub (x : ℕ) :
    residualRewardIncrement x =
      localSignRewardNat x - localSignRewardNat (x - 1) := by
  simp only [residualRewardIncrement, residualReward_eq_localSignRewardNat]

#print axioms residualReward_eq_localSignRewardNat
#print axioms residualRewardIncrement_eq_localSignRewardNat_sub

end Erdos625
