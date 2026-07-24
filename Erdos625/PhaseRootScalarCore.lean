import Erdos625.PhaseRootFiniteCommon

namespace Erdos625

open Filter Asymptotics

noncomputable section

set_option autoImplicit false

theorem phaseRootScalarTerm_eq_stirlingForm {n : ℕ}
    (hn : PhaseDomain n) (hs0 : 0 < phaseRootS0 n)
    (ha : 0 < phaseNat n) :
    phaseRootScalarTerm n =
      phaseStirlingMain n (phaseNat n) +
        phaseRootDeficitTarget n *
          (profileDeficitAffineB (phaseNat n) - logOrder n) -
        phaseRootS0 n + 1 - Real.log (phaseRootCenter n) -
        stirlingLogRemainder (phaseNat n) := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn.1)
  have hnNe : (n : ℝ) ≠ 0 := hnPos.ne'
  have hs0Ne : phaseRootS0 n ≠ 0 := ne_of_gt hs0
  have hdiv : (n : ℝ) / phaseRootCenter n = phaseRootS0 n := by
    unfold phaseRootCenter
    field_simp [hnNe, hs0Ne]
  have hquot :
      ((n : ℝ) * Real.log (n : ℝ) - n) / phaseRootCenter n =
        phaseRootS0 n * (Real.log (n : ℝ) - 1) := by
    calc
      ((n : ℝ) * Real.log (n : ℝ) - n) / phaseRootCenter n =
          ((n : ℝ) / phaseRootCenter n) * Real.log (n : ℝ) -
            (n : ℝ) / phaseRootCenter n := by ring
      _ = phaseRootS0 n * (Real.log (n : ℝ) - 1) := by rw [hdiv]; ring
  have haReal : (0 : ℝ) < phaseNat n := by exact_mod_cast ha
  have hChoose :
      ((phaseNat n).choose 2 : ℝ) =
        (phaseNat n : ℝ) * ((phaseNat n : ℝ) - 1) / 2 := by
    simpa using (Nat.cast_choose_two ℝ (phaseNat n) :
      ((phaseNat n).choose 2 : ℝ) =
        (phaseNat n : ℝ) * ((phaseNat n : ℝ) - 1) / 2)
  have hLogProduct :
      Real.log (2 * Real.pi * (phaseNat n : ℝ)) =
        Real.log (2 * Real.pi) + Real.log (phaseNat n : ℝ) := by
    rw [Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0) haReal.ne']
  simp only [phaseRootScalarTerm, profileDeficitAffineA,
    coloringClassLogCost, phaseStirlingMain, stirlingLogRemainder]
  rw [hquot, hLogProduct, hChoose, phaseRootDeficitTarget_eq hn]
  rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hn]
  simp only [logOrder, q]
  ring_nf

theorem phaseRootScalarTerm_eq_core {n : ℕ}
    (hn : PhaseDomain n) (hs0 : 0 < phaseRootS0 n)
    (ha : 0 < phaseNat n) :
    phaseRootScalarTerm n =
      phaseRootAlgebraicCore n + phaseExpansionResidual n -
        phaseStirlingResidual n - stirlingLogRemainder (phaseNat n) := by
  rw [phaseRootScalarTerm_eq_stirlingForm hn hs0 ha]
  simp only [phaseRootAlgebraicCore, phaseExpansionResidual,
    phaseStirlingResidual]
  ring

end

end Erdos625
