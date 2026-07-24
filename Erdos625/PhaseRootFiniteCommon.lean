import Erdos625.ColoringProfilePhaseRootCenter
import Erdos625.ColoringProfileDeficitTilt
import Erdos625.ColoringProfileDeficitPartitionBounds
import Erdos625.PhaseAsymptotic
import Mathlib.Tactic

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

noncomputable def phaseRootDeficitTarget (n : ℕ) : ℝ :=
  (phaseNat n : ℝ) - (n : ℝ) / phaseRootCenter n

noncomputable def phaseRootScalarTerm (n : ℕ) : ℝ :=
  ((n : ℝ) * Real.log (n : ℝ) - n) / phaseRootCenter n + 1 -
    Real.log (phaseRootCenter n) +
    profileDeficitAffineA (phaseNat n) +
    profileDeficitAffineB (phaseNat n) * phaseRootDeficitTarget n

noncomputable def phaseRootSelectedDeficitTerm (n : ℕ) : ℝ :=
  Real.log
      (profileDeficitPartition (phaseNat n)
        (profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n))) -
    profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) *
      phaseRootDeficitTarget n

noncomputable def phaseRootAlgebraicCore (n : ℕ) : ℝ :=
  phaseExpansionMain n +
    phaseRootDeficitTarget n *
      (profileDeficitAffineB (phaseNat n) - logOrder n) -
    phaseRootS0 n + 1 - Real.log (phaseRootCenter n)

theorem phaseRootDeficitTarget_eq {n : ℕ} (hn : PhaseDomain n) :
    phaseRootDeficitTarget n = 1 + 2 / q - phaseDelta n := by
  simpa [phaseRootDeficitTarget] using phaseRoot_target_identity hn

theorem unrestrictedPhaseObjective_center_div_decomposition {n : ℕ}
    (hn : PhaseDomain n) (hs0 : 0 < phaseRootS0 n) :
    unrestrictedPhaseObjective n (phaseRootCenter n) / phaseRootCenter n =
      phaseRootScalarTerm n + phaseRootSelectedDeficitTerm n := by
  have hnPos : 0 < n := lt_trans Nat.zero_lt_one hn.1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hc : phaseRootCenter n ≠ 0 :=
    div_ne_zero hn0 hs0.ne'
  rw [unrestrictedPhaseObjective, profileDualOptimalValue]
  unfold profileDualEntropyValue
  have ht :
      profileDualTilt (phaseNat n + 1)
          ((n : ℝ) / phaseRootCenter n) =
        profileDeficitAffineB (phaseNat n) -
          profileDeficitTilt (phaseNat n) (phaseRootDeficitTarget n) := by
    simp [profileDeficitTilt, phaseRootDeficitTarget]
  rw [ht, log_profileDualPartition_eq_deficitCentered]
  unfold phaseRootScalarTerm phaseRootSelectedDeficitTerm
  unfold phaseRootDeficitTarget
  field_simp [hc]
  ring

end

end Erdos625
