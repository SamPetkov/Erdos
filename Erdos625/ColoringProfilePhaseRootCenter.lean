import Erdos625.ColoringProfilePhaseObjective
import Erdos625.PhaseEstimates

/-!
# Unrestricted-profile phase center

This module gives one canonical home to the manuscript reference center and
the raw attained unrestricted-profile objective.  The reference center is
not asserted here to be a zero of that objective, and the unrestricted
objective is not identified with the signed four-size objective.

The exact objective decomposition and eventual center corridor were returned
by Aristotle projects `d6b5395c-0535-4eb3-b8cf-0ebcf1d4f6ba` and
`e7c1b257-9afe-4344-9e0b-a62f9ba5065a`, tasks
`a6e0e6c8-82e7-4d8a-b67d-641aacca5284` and
`f8127c71-676f-41b8-84f4-48f08e32ad2b`, and independently audited before
integration.
-/

namespace Erdos625

open Filter

noncomputable section

set_option autoImplicit false

/-- The manuscript reference center in the average-class-size variable:
`s₀ = α₀ - 1 - 2 / log 2`. -/
noncomputable def phaseRootS0 (n : ℕ) : ℝ :=
  alphaZero n - 1 - 2 / q

/-- The corresponding reference center `n / s₀` in the part-count variable.
No root equation is asserted by this definition. -/
noncomputable def phaseRootCenter (n : ℕ) : ℝ :=
  (n : ℝ) / phaseRootS0 n

/-- The raw attained unrestricted profile objective, before adding the
finite profile-box multiplicity term. -/
noncomputable def unrestrictedPhaseObjective (n : ℕ) (parts : ℝ) : ℝ :=
  profileDualOptimalValue (phaseNat n + 1) (n : ℝ) parts

/-- `profilePhaseObjective` is not the raw manuscript objective: it is the
raw attained profile value plus the exact logarithmic profile-box term. -/
theorem profilePhaseObjective_eq_profileBoxTerm_add_unrestricted
    (n : ℕ) (parts : ℝ) :
    profilePhaseObjective n parts =
      ((phaseNat n + 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) +
        unrestrictedPhaseObjective n parts := by
  rfl

/-- Exact finite target identity at the phase center. `PhaseDomain` is used
both to identify the natural phase with the floor and to make the graph-order
denominator nonzero. No assumption `phaseRootS0 n ≠ 0` is needed.

The proof was returned by Aristotle project
`22c01ff7-472b-475a-90fd-445cab08eca8`, task
`3130c2d8-4abe-43e3-bc51-754fc6836146`, and independently audited before
integration. -/
theorem phaseRoot_target_identity {n : ℕ} (hn : PhaseDomain n) :
    (phaseNat n : ℝ) - (n : ℝ) / phaseRootCenter n =
      1 + 2 / q - phaseDelta n := by
  rw [show phaseRootCenter n =
    (n : ℝ) / (alphaZero n - 1 - 2 / q) from rfl]
  rw [div_div_cancel₀] <;> norm_num [phaseDelta]
  · rw [phaseNat_cast_real hn]
    ring
  · linarith [hn.1]

/-- Eventually the phase center is defined on the genuine floor domain,
`s₀` is positive, and its exact four-size target belongs to the full closed
phase interval used by the uniform four-point estimates. -/
theorem eventually_phaseRoot_domain_pos_and_target_corridor :
    ∀ᶠ n : ℕ in atTop,
      PhaseDomain n ∧
      0 < phaseRootS0 n ∧
      (phaseNat n : ℝ) - (n : ℝ) / phaseRootCenter n ∈
        Set.Icc (2 / q) (1 + 2 / q) := by
  have hqLower : (1 / 2 : ℝ) < q := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hqUpper : q < 2 := by
    exact Real.log_two_lt_d9.trans (by norm_num)
  have hTwoDivQBounds : (1 : ℝ) < 2 / q ∧ 2 / q < 4 := by
    constructor
    · rw [lt_div_iff₀ q_pos]
      linarith
    · rw [div_lt_iff₀ q_pos]
      linarith
  have hLogLarge : ∀ᶠ n : ℕ in atTop, 5 < logOrder n :=
    tendsto_logOrder_atTop.eventually_gt_atTop 5
  filter_upwards [eventually_phaseDomain,
    eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder,
    hLogLarge, eventually_gt_atTop (0 : ℕ)] with n hn hphase hlog hnPos
  have hPhaseLarge : (5 : ℝ) < phaseNat n := lt_of_lt_of_le hlog hphase.1
  have hs0Pos : 0 < phaseRootS0 n := by
    rw [phaseRootS0, alphaZero_eq_phaseNat_add_delta hn]
    linarith [phaseDelta_nonneg n, hTwoDivQBounds.1, hTwoDivQBounds.2]
  have hnNe : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnPos.ne'
  have hs0Ne : phaseRootS0 n ≠ 0 := hs0Pos.ne'
  have hCenterNe : phaseRootCenter n ≠ 0 := by
    exact div_ne_zero hnNe hs0Ne
  have hDivide : (n : ℝ) / phaseRootCenter n = phaseRootS0 n := by
    unfold phaseRootCenter
    field_simp
  refine ⟨hn, hs0Pos, ?_⟩
  rw [hDivide, phaseRootS0, alphaZero_eq_phaseNat_add_delta hn]
  constructor <;> linarith [phaseDelta_nonneg n, phaseDelta_lt_one n]

end

end Erdos625
