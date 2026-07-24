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

/-- The coarse Section IX large-residual exponent is finite whenever its
absolute constants are finite and the residual mass is positive.

The proof was returned by Aristotle project
`b887515e-44b4-4ec2-97ab-dd94cb29b641`, task
`1df65d4f-00b0-4af2-9ca4-68c8c65ba85f`, and independently audited before
integration. -/
theorem residualLargeEnvelope_ne_top
    (kappaLambda kappaQ : ENNReal)
    (cardA matchingCard U m : ℕ)
    (hkappaLambdaTop : kappaLambda ≠ ∞)
    (hkappaQTop : kappaQ ≠ ∞)
    (hm : 0 < m) :
    (kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) +
      2 * (cardA : ENNReal) *
        (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 +
      (((6 * matchingCard : ℕ) : ENNReal) *
        (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)))) ≠ ∞ := by
  have hUTop : (U : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top U
  have hm0 : (m : ENNReal) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hcardATop : (cardA : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top cardA
  have hmatchingTop : ((6 * matchingCard : ℕ) : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top (6 * matchingCard)
  have htwoTop : (2 : ENNReal) ≠ ∞ := ENNReal.ofNat_ne_top
  have hUPow4Top : (U : ENNReal) ^ 4 ≠ ∞ := ENNReal.pow_ne_top hUTop
  have hUPow3Top : (U : ENNReal) ^ 3 ≠ ∞ := ENNReal.pow_ne_top hUTop
  have hlambdaMulTop : kappaLambda * (U : ENNReal) ^ 4 ≠ ∞ :=
    ENNReal.mul_ne_top hkappaLambdaTop hUPow4Top
  have hlambdaDivTop : kappaLambda * (U : ENNReal) ^ 4 / (m : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top hlambdaMulTop hm0
  have hqMulTop : kappaQ * (U : ENNReal) ^ 3 ≠ ∞ :=
    ENNReal.mul_ne_top hkappaQTop hUPow3Top
  have hqDivTop : kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal) ≠ ∞ :=
    ENNReal.div_ne_top hqMulTop hm0
  have hqPowTop : (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 ≠ ∞ :=
    ENNReal.pow_ne_top hqDivTop
  have htwoCardTop : (2 : ENNReal) * (cardA : ENNReal) ≠ ∞ :=
    ENNReal.mul_ne_top htwoTop hcardATop
  have hmiddleTop :
      2 * (cardA : ENNReal) *
        (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ^ 4 ≠ ∞ :=
    ENNReal.mul_ne_top htwoCardTop hqPowTop
  have hlastTop :
      ((6 * matchingCard : ℕ) : ENNReal) *
        (kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal)) ≠ ∞ :=
    ENNReal.mul_ne_top hmatchingTop hqDivTop
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.add_ne_top.mpr ⟨hlambdaDivTop, hmiddleTop⟩, hlastTop⟩

end

end Erdos625
