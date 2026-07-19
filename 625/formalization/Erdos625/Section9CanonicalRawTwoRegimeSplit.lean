import Erdos625.Section9ProfileAttachmentPolymerAssembly
import Mathlib.Tactic

/-!
# Section IX: faithful raw two-regime split

The positive-residual attained demands are partitioned by their literal
residual mass.  Both branches retain `canonicalDemandRawAttachmentTerm`; in
particular, the small branch is not replaced by the unrestricted polymer
majorant.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Exact partition of the positive-residual raw attachment sum at a natural
mass threshold.  Positivity remains explicit in both branches, including
when the threshold is zero. -/
theorem sum_canonicalDemandRawAttachmentTerm_positive_eq_small_add_large
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U T : ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b) :
    (∑ demand ∈ (Finset.univ.filter fun demand :
        canonicalDemandImage row col U =>
          0 < canonicalDemandResidualTotal row col U demand),
      canonicalDemandRawAttachmentTerm row col U htotal demand) =
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage row col U =>
            0 < canonicalDemandResidualTotal row col U demand ∧
            canonicalDemandResidualTotal row col U demand < T),
        canonicalDemandRawAttachmentTerm row col U htotal demand) +
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage row col U =>
            0 < canonicalDemandResidualTotal row col U demand ∧
            T ≤ canonicalDemandResidualTotal row col U demand),
        canonicalDemandRawAttachmentTerm row col U htotal demand) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun demand : canonicalDemandImage row col U =>
      0 < canonicalDemandResidualTotal row col U demand)
    (fun demand => canonicalDemandResidualTotal row col U demand < T)]
  simp only [Finset.filter_filter, not_lt, and_assoc]

/-- Pointwise bounds in the two residual regimes combine into a bound for the
entire positive-residual raw attachment sum. -/
theorem sum_canonicalDemandRawAttachmentTerm_positive_le_twoRegime
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U T : ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b)
    (smallTerm largeTerm : canonicalDemandImage row col U → ENNReal)
    (hsmall : ∀ demand,
      0 < canonicalDemandResidualTotal row col U demand →
      canonicalDemandResidualTotal row col U demand < T →
      canonicalDemandRawAttachmentTerm row col U htotal demand ≤
        smallTerm demand)
    (hlarge : ∀ demand,
      0 < canonicalDemandResidualTotal row col U demand →
      T ≤ canonicalDemandResidualTotal row col U demand →
      canonicalDemandRawAttachmentTerm row col U htotal demand ≤
        largeTerm demand) :
    (∑ demand ∈ (Finset.univ.filter fun demand :
        canonicalDemandImage row col U =>
          0 < canonicalDemandResidualTotal row col U demand),
      canonicalDemandRawAttachmentTerm row col U htotal demand) ≤
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage row col U =>
            0 < canonicalDemandResidualTotal row col U demand ∧
            canonicalDemandResidualTotal row col U demand < T),
        smallTerm demand) +
      (∑ demand ∈ (Finset.univ.filter fun demand :
          canonicalDemandImage row col U =>
            0 < canonicalDemandResidualTotal row col U demand ∧
            T ≤ canonicalDemandResidualTotal row col U demand),
        largeTerm demand) := by
  rw [sum_canonicalDemandRawAttachmentTerm_positive_eq_small_add_large]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro demand hdemand
    have hdemand' := Finset.mem_filter.mp hdemand
    exact hsmall demand hdemand'.2.1 hdemand'.2.2
  · apply Finset.sum_le_sum
    intro demand hdemand
    have hdemand' := Finset.mem_filter.mp hdemand
    exact hlarge demand hdemand'.2.1 hdemand'.2.2

#print axioms sum_canonicalDemandRawAttachmentTerm_positive_eq_small_add_large
#print axioms sum_canonicalDemandRawAttachmentTerm_positive_le_twoRegime

end

end Erdos625
