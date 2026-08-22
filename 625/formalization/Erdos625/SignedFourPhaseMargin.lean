import Erdos625.UniformLimitingEntropyCertificate
import Mathlib.Tactic

/-!
# The phase-varying signed four-size entropy margin

This module gives a name and finite uniform bounds to the phase coefficient
which appears in the normalized E625-10 first moment:

`q - fourEntropyLoss (1 + 2/q - phaseDelta n)`.

The coefficient does not converge to a single scalar because the phase may
vary with `n`.  What is needed for asymptotic transport is a uniform positive
lower margin and a uniform boundedness statement.  Both follow directly from
the welded limiting entropy certificate.

No root, part-count, first-moment, chromatic-tail, partial-diagonal, second-
moment, or final Erdős theorem is used.
-/

namespace Erdos625

open Set

noncomputable section

set_option autoImplicit false

/-- The limiting deficit target at the current integer phase. -/
noncomputable def signedFourPhaseTarget (n : ℕ) : ℝ :=
  1 + 2 / q - phaseDelta n

/-- The phase-varying support-loss margin entering the midpoint signed first
moment. -/
noncomputable def signedFourPhaseMargin (n : ℕ) : ℝ :=
  q - fourEntropyLoss (signedFourPhaseTarget n)

/-- The fractional phase always lies in the closed certificate interval. -/
theorem phaseDelta_mem_Icc (n : ℕ) :
    phaseDelta n ∈ Icc (0 : ℝ) 1 :=
  ⟨phaseDelta_nonneg n, (phaseDelta_lt_one n).le⟩

/-- The phase target lies in the exact four-size mean domain. -/
theorem signedFourPhaseTarget_mem_Ioo (n : ℕ) :
    signedFourPhaseTarget n ∈ Ioo (2 : ℝ) 5 := by
  have h := uniform_limiting_four_entropy_certificate
    (phaseDelta n) (phaseDelta_mem_Icc n)
  simpa only [signedFourPhaseTarget] using h.1

/-- The finite certificate gives the explicit uniform positive margin used in
the manuscript. -/
theorem log_200_div_153_lt_signedFourPhaseMargin (n : ℕ) :
    Real.log ((200 : ℝ) / 153) < signedFourPhaseMargin n := by
  have h := uniform_limiting_four_entropy_certificate
    (phaseDelta n) (phaseDelta_mem_Icc n)
  simpa only [signedFourPhaseMargin, signedFourPhaseTarget] using h.2.2.2.2

/-- The phase margin is strictly positive. -/
theorem signedFourPhaseMargin_pos (n : ℕ) :
    0 < signedFourPhaseMargin n :=
  log_200_div_153_pos.trans
    (log_200_div_153_lt_signedFourPhaseMargin n)

/-- Positivity of the entropy loss bounds the phase margin strictly below
`q`. -/
theorem signedFourPhaseMargin_lt_q (n : ℕ) :
    signedFourPhaseMargin n < q := by
  have h := uniform_limiting_four_entropy_certificate
    (phaseDelta n) (phaseDelta_mem_Icc n)
  unfold signedFourPhaseMargin
  have hLoss : 0 < fourEntropyLoss (signedFourPhaseTarget n) := by
    simpa only [signedFourPhaseTarget] using h.2.1
  linarith

/-- Closed uniform interval for the phase margin. -/
theorem signedFourPhaseMargin_mem_Icc (n : ℕ) :
    signedFourPhaseMargin n ∈ Icc (0 : ℝ) q :=
  ⟨(signedFourPhaseMargin_pos n).le,
    (signedFourPhaseMargin_lt_q n).le⟩

/-- Absolute boundedness form used when multiplying a vanishing uniform error
by the varying phase margin. -/
theorem abs_signedFourPhaseMargin_le_q (n : ℕ) :
    |signedFourPhaseMargin n| ≤ q := by
  rw [abs_of_nonneg (signedFourPhaseMargin_mem_Icc n).1]
  exact (signedFourPhaseMargin_mem_Icc n).2

/-- The certified lower endpoint is itself positive. -/
theorem signedFourPhaseMargin_uniform_lower_pos :
    0 < Real.log ((200 : ℝ) / 153) :=
  log_200_div_153_pos

#print axioms phaseDelta_mem_Icc
#print axioms signedFourPhaseTarget_mem_Ioo
#print axioms log_200_div_153_lt_signedFourPhaseMargin
#print axioms signedFourPhaseMargin_pos
#print axioms signedFourPhaseMargin_lt_q
#print axioms signedFourPhaseMargin_mem_Icc
#print axioms abs_signedFourPhaseMargin_le_q
#print axioms signedFourPhaseMargin_uniform_lower_pos

end

end Erdos625
