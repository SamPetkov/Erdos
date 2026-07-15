import Erdos625.ConfigurationModelProbability

/-!
# Normalized labelled-witness incidence for Section VIII

This module isolates the algebraic normalized labelled-exposure incidence
used in manuscript (8.3).  It is not, by itself, the full configuration-model
event-probability identity: that application still requires equal ambient
row and column totals, matching-extension normalization, and specialization
to the canonical partial-matching demand.
-/

namespace Erdos625

open scoped BigOperators ENNReal

/-- The number of labelled prescribed-demand witnesses, normalized by the
ambient row-stub descending factorial `(m)_J`. -/
noncomputable def labelledWitnessIncidence
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) : ℝ≥0∞ :=
  (Fintype.card (PrescribedDemandWitness demand row col) : ℝ≥0∞) /
    ((Finset.univ.sum row).descFactorial (totalDemand demand) : ℝ≥0∞)

/-- Exact algebraic form of the normalized labelled-witness incidence.  The
displayed total-demand hypothesis makes every ENNReal denominator nonzero;
the result remains a counting identity rather than the full probability
statement of manuscript (8.3). -/
theorem labelledWitnessIncidence_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ)
    (hDemand : totalDemand demand ≤ Finset.univ.sum row) :
    labelledWitnessIncidence demand row col =
      ((rowDescendingProduct demand row *
        columnDescendingProduct demand col : ℕ) : ℝ≥0∞) /
      (((Finset.univ.sum row).descFactorial (totalDemand demand) *
        demandFactorialProduct demand : ℕ) : ℝ≥0∞) := by
  have hdesc_pos :
      0 < (Finset.univ.sum row).descFactorial (totalDemand demand) :=
    Nat.descFactorial_pos.mpr hDemand
  have hfactorial_pos : 0 < demandFactorialProduct demand := by
    exact Finset.prod_pos fun a _ ↦
      Finset.prod_pos fun b _ ↦ Nat.factorial_pos _
  unfold labelledWitnessIncidence
  rw [ENNReal.div_eq_div_iff]
  · norm_cast
    simpa only [demandFactorialProduct, rowDescendingProduct,
      columnDescendingProduct, mul_assoc, mul_comm, mul_left_comm] using
      congr_arg
        (fun n ↦
          (Finset.univ.sum row).descFactorial (totalDemand demand) * n)
        (card_prescribedDemandWitness_mul_factorials demand row col)
  · exact ne_of_gt (by exact_mod_cast mul_pos hdesc_pos hfactorial_pos)
  · exact ENNReal.natCast_ne_top _
  · exact ne_of_gt (by exact_mod_cast hdesc_pos)
  · exact ENNReal.natCast_ne_top _

#print axioms labelledWitnessIncidence_eq

end Erdos625
