import Erdos625.Section8CanonicalEventCardinality
import Erdos625.Section8CanonicalEventProbabilityNormalization
import Erdos625.Section8LabelledIncidence
import Erdos625.Section8ResidualDegreeTotal
import Erdos625.Section8ResidualEventProbabilityNormalization
import Erdos625.Section8WitnessDemandFeasibility
import Mathlib.Tactic

/-!
# Section 8: exact canonical-event probability factorization

This module combines only finite uniform-event normalizations, the exact
once-only canonical-event cardinality, and factorial cancellation. Its
right-hand side is a residual uniform-event probability, not a literal
conditional-probability assertion for the ambient event; the corresponding
conditional-law bookkeeping remains a separate obligation.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance instFintypeCanonicalDemandEventProbabilityFactorization
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

local instance instFintypeCanonicalResidualCellEventProbabilityFactorization
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

local instance instFintypeFixedWitnessCanonicalDemandEventProbabilityFactorization
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Fintype (fixedWitnessCanonicalDemandEvent witness U) :=
  Fintype.ofFinite _

private theorem card_factorial_factorization
    (m J W R : ℕ) (hJ : J ≤ m) :
    ((W * R : ℕ) : ℝ≥0∞) / (m.factorial : ℝ≥0∞) =
      ((W : ℝ≥0∞) / (m.descFactorial J : ℝ≥0∞)) *
        ((R : ℝ≥0∞) / ((m - J).factorial : ℝ≥0∞)) := by
  have hdescPos : 0 < m.descFactorial J := Nat.descFactorial_pos.mpr hJ
  have hdescZero : (m.descFactorial J : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hdescPos.ne'
  have hdescTop : (m.descFactorial J : ℝ≥0∞) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  have hfactorialNat : m.factorial =
      m.descFactorial J * (m - J).factorial := by
    simpa only [Nat.mul_comm] using (Nat.factorial_mul_descFactorial hJ).symm
  have hfactorialENNReal : (m.factorial : ℝ≥0∞) =
      (m.descFactorial J : ℝ≥0∞) * ((m - J).factorial : ℝ≥0∞) := by
    exact_mod_cast hfactorialNat
  calc
    ((W * R : ℕ) : ℝ≥0∞) / (m.factorial : ℝ≥0∞) =
        ((W : ℝ≥0∞) * (R : ℝ≥0∞)) / (m.factorial : ℝ≥0∞) := by
      simp only [Nat.cast_mul]
    _ = ((W : ℝ≥0∞) * (R : ℝ≥0∞)) /
        ((m.descFactorial J : ℝ≥0∞) * ((m - J).factorial : ℝ≥0∞)) := by
      rw [hfactorialENNReal]
    _ = ((W : ℝ≥0∞) / (m.descFactorial J : ℝ≥0∞)) *
        ((R : ℝ≥0∞) / ((m - J).factorial : ℝ≥0∞)) := by
      exact ENNReal.mul_div_mul_comm
        (a := (W : ℝ≥0∞)) (b := (R : ℝ≥0∞))
        (c := (m.descFactorial J : ℝ≥0∞))
        (d := ((m - J).factorial : ℝ≥0∞))
        (Or.inl hdescZero) (Or.inl hdescTop)

/-- Under the uniform ambient configuration law, one fixed labelled
canonical witness has the exact extension incidence `1 / (m)_J` times the
uniform residual cap/no-return event probability. The strict high-demand
condition identifies this fixed canonical fibre with the residual event.

This is only a fixed-witness probability factorization. It does not sum over
physical skeletons or supply any quantitative residual-event estimate. -/
theorem uniformConfigurationMatching_fixedWitnessCanonicalDemandEvent_eq_residualFactor
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (fixedWitnessCanonicalDemandEvent witness U) =
      (1 / (((∑ a, row a).descFactorial (totalDemand demand) : ℕ) : ℝ≥0∞)) *
        ((uniformConfigurationMatching
          (residualRowDegree witness) (residualColumnDegree witness)
          (sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness)).toOuterMeasure
          (canonicalResidualCellEvent witness U)) := by
  have hJ : totalDemand demand ≤ ∑ a, row a :=
    totalDemand_le_rowTotal_of_witness witness
  have hres : (∑ a, residualRowDegree witness a) =
      ∑ b, residualColumnDegree witness b :=
    sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness
  have hrem : (∑ a, residualRowDegree witness a) =
      (∑ a, row a) - totalDemand demand :=
    sum_residualRowDegree_eq_rowTotal_sub_totalDemand witness
  rw [uniformConfigurationMatching_event_apply row col htotal
    (Subtype.val '' fixedWitnessCanonicalDemandEvent witness U)]
  rw [show Fintype.card (Subtype.val '' fixedWitnessCanonicalDemandEvent witness U) =
      Fintype.card (fixedWitnessCanonicalDemandEvent witness U) from
    Fintype.card_congr (Equiv.Set.image Subtype.val
      (fixedWitnessCanonicalDemandEvent witness U) Subtype.val_injective).symm]
  rw [show Fintype.card (fixedWitnessCanonicalDemandEvent witness U) =
      Fintype.card (canonicalResidualCellEvent witness U) from
    Fintype.card_congr
      (fixedWitnessCanonicalDemandEventEquivResidual witness U hhigh)]
  rw [uniformConfigurationMatching_canonicalResidualCellEvent_apply
    witness U hres, hrem]
  simpa only [Nat.one_mul, Nat.cast_one] using
    (card_factorial_factorization
      (∑ a, row a) (totalDemand demand) 1
      (Fintype.card ↑(canonicalResidualCellEvent witness U)) hJ)

/-- Exact finite factorization of the ambient canonical-demand event into its
normalised labelled-witness incidence and the residual canonical-event
probability. -/
theorem uniformConfigurationMatching_canonicalDemandEvent_eq_incidence_mul_residual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : ∑ a, row a = ∑ b, col b)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (witness₀ : PrescribedDemandWitness demand row col) :
    (uniformConfigurationMatching row col htotal).toOuterMeasure
        (canonicalDemandEvent demand row col U) =
      labelledWitnessIncidence demand row col *
        ((uniformConfigurationMatching
          (residualRowDegree witness₀) (residualColumnDegree witness₀)
          (sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness₀)).toOuterMeasure
          (canonicalResidualCellEvent witness₀ U)) := by
  have hJ : totalDemand demand ≤ ∑ a, row a :=
    totalDemand_le_rowTotal_of_witness witness₀
  have hres : (∑ a, residualRowDegree witness₀ a) =
      ∑ b, residualColumnDegree witness₀ b :=
    sum_residualRowDegree_eq_sum_residualColumnDegree htotal witness₀
  have hrem : (∑ a, residualRowDegree witness₀ a) =
      (∑ a, row a) - totalDemand demand :=
    sum_residualRowDegree_eq_rowTotal_sub_totalDemand witness₀
  rw [uniformConfigurationMatching_canonicalDemandEvent_apply
    demand row col U htotal]
  rw [card_canonicalDemandEvent_eq_witness_mul_residual
    demand row col U hhigh witness₀]
  rw [uniformConfigurationMatching_canonicalResidualCellEvent_apply
    witness₀ U hres, hrem]
  unfold labelledWitnessIncidence
  exact card_factorial_factorization
    (∑ a, row a) (totalDemand demand)
    (Fintype.card (PrescribedDemandWitness demand row col))
    (Fintype.card ↑(canonicalResidualCellEvent witness₀ U)) hJ

#print axioms uniformConfigurationMatching_canonicalDemandEvent_eq_incidence_mul_residual
#print axioms uniformConfigurationMatching_fixedWitnessCanonicalDemandEvent_eq_residualFactor

end

end Erdos625
