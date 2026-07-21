import Erdos625.Section9ActualAttachmentLargeResidualEnvelope

/-!
# Section IX: finite exponential transport

This module supplies the coercion bridge needed after the large-residual
attachment exponent has been proved finite.  It contains no asymptotic or
probabilistic estimate by itself.

The proof was returned by Aristotle project
`15e91c74-dfdb-4770-a7dc-62e52b3c98b3`, task
`34d791e3-60c3-4dec-8499-5d8a69732926`, and independently audited before
integration.
-/

namespace Erdos625

open scoped ENNReal

noncomputable section

set_option autoImplicit false

/-- A finite `ENNReal` exponent lets an `EReal.exp` upper bound be transported
back to the ordinary finite `ENNReal.ofReal (Real.exp ...)` endpoint. -/
theorem ennreal_le_of_coe_le_ereal_exp_toReal
    (x y : ENNReal)
    (hy : y ≠ ∞)
    (h : (x : EReal) ≤ EReal.exp (y : EReal)) :
    x ≤ ENNReal.ofReal (Real.exp y.toReal) := by
  rw [← EReal.coe_ennreal_toReal hy, EReal.exp_coe] at h
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mp h

end

end Erdos625
