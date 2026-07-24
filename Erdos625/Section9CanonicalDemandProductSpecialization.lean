import Erdos625.Section9CanonicalDemandProductEstimate
import Erdos625.Section9ProfileAttachmentPolymerAssembly
import Erdos625.Section9CanonicalSupportMatching
import Mathlib.Tactic

/-!
# Section IX: canonical-demand specialization of the residual product bound

This module transports the generic positive-residual product estimate to the
reference residual profile of one attained canonical demand.  It remains a
finite strict-regime theorem: the eventual large-residual corridor and its
comparison with the Section IX asymptotic scale are separate obligations.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- The reference witness of an attained canonical demand supplies exactly
the matching, degree-cap, and balance data required by the residual product
estimate. -/
theorem canonicalReference_residual_parameters
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (htotal : (∑ a, row a) = ∑ b, col b)
    (hrowCap : ∀ a, row a ≤ U) (hcolCap : ∀ b, col b ≤ U)
    (demand : canonicalDemandImage row col U) :
    let witness := canonicalDemandReferenceWitness row col U demand
    IsBipartiteMatching (positiveDemandSupport demand.1) ∧
      (∀ a, residualRowDegree witness a ≤ U) ∧
      (∀ b, residualColumnDegree witness b ≤ U) ∧
      ((∑ a, residualRowDegree witness a) =
        ∑ b, residualColumnDegree witness b) := by
  dsimp only
  let witness := canonicalDemandReferenceWitness row col U demand
  have hprofile := residualDegreeProfile_of_witness htotal witness
  exact ⟨positiveDemandSupport_isBipartiteMatching_of_canonicalDemandImage
      U hrowCap hcolCap demand,
    fun a => (hprofile.1 a).trans (hrowCap a),
    fun b => (hprofile.2.1 b).trans (hcolCap b),
    hprofile.2.2⟩

/-- Absolute constants from the generic product theorem bound the literal
canonical-demand polymer majorant throughout the strict residual corridor. -/
theorem exists_absolute_canonicalDemandPolymer_strict_bound :
    ∃ kappaLambda kappaQ : ENNReal,
      0 < kappaLambda ∧ kappaLambda ≠ ∞ ∧
      0 < kappaQ ∧ kappaQ ≠ ∞ ∧
      ∀ {A B : Type*} [Fintype A] [Fintype B]
          [DecidableEq A] [DecidableEq B]
          (row : A → ℕ) (col : B → ℕ) (U m : ℕ)
          (demand : canonicalDemandImage row col U),
        (∑ a, row a) = ∑ b, col b →
        (∀ a, row a ≤ U) →
        (∀ b, col b ≤ U) →
        m = canonicalDemandResidualTotal row col U demand →
        0 < m →
        2 ^ U ≤ m ^ 3 →
        kappaQ * (U : ENNReal) ^ 3 / (m : ENNReal) <
          (1 / 3 : ENNReal) →
        canonicalDemandPolymerMajorant row col U demand ≤
          EReal.exp
            ((residualProductExponentMajorant kappaLambda kappaQ
              (Fintype.card A) (positiveDemandSupport demand.1).card U m :
                ENNReal) : EReal) := by
  obtain ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, hbound⟩ :=
    exists_absolute_residual_product_exponential_majorant
  refine ⟨kappaLambda, kappaQ, hkLpos, hkLtop, hkQpos, hkQtop, ?_⟩
  intro A B _ _ _ _ row col U m demand htotal hrowCap hcolCap
    hm hmpos hpow htau
  let witness := canonicalDemandReferenceWitness row col U demand
  have hparameters := canonicalReference_residual_parameters
    row col U htotal hrowCap hcolCap demand
  have hrowSum : (∑ a, residualRowDegree witness a) = m := by
    simpa only [canonicalDemandResidualTotal, witness] using hm.symm
  have hcolSum : (∑ b, residualColumnDegree witness b) = m := by
    exact hparameters.2.2.2.symm.trans hrowSum
  have h := hbound (positiveDemandSupport demand.1) U (U / 2) m
    (residualRowDegree witness) (residualColumnDegree witness)
    hparameters.1 hmpos hrowSum hcolSum hparameters.2.1 hparameters.2.2.1
    rfl hpow htau
  simpa only [canonicalDemandPolymerMajorant, witness] using h.2.2

#print axioms canonicalReference_residual_parameters
#print axioms exists_absolute_canonicalDemandPolymer_strict_bound

end

end Erdos625
