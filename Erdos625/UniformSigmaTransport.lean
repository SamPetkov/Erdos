import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Uniform finite probability on a dependent sum

For a finite dependent sum, this module calculates the marginal of the
uniform law under the first projection.  It is an exact finite probability
identity only: it makes no configuration-model, canonical-event, or
asymptotic assertion.  In particular, the base coordinate is generally not
uniform; its mass is proportional to the cardinality of its fibre.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Under the uniform law on a nonempty finite dependent sum, the mass of a
base point is the cardinality of its fibre divided by the total cardinality. -/
theorem uniformOfFintype_sigma_map_fst_apply
    {D : Type*} {X : D -> Type*}
    [Fintype D] [(d : D) -> Fintype (X d)]
    [Nonempty (Sigma X)]
    (d : D) :
    ((PMF.uniformOfFintype (Sigma X)).map
        (fun z : Sigma X => z.1)) d =
      (Fintype.card (X d) : ENNReal) /
        (Fintype.card (Sigma X) : ENNReal) := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [PMF.uniformOfFintype_apply]
  rw [Fintype.sum_sigma]
  have hinner : forall x : D,
      (∑ _y : X x,
          if d = x then (Fintype.card (Sigma X) : ENNReal)⁻¹ else 0) =
        if d = x then
          (Fintype.card (X x) : ENNReal) *
            (Fintype.card (Sigma X) : ENNReal)⁻¹ else 0 := by
    intro x
    by_cases h : d = x
    · subst x
      simp [nsmul_eq_mul]
    · simp [h]
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  rw [show (∑ x : D,
      if d = x then
        (Fintype.card (X x) : ENNReal) *
          (Fintype.card (Sigma X) : ENNReal)⁻¹ else 0) =
      ∑ x : D,
        if x = d then
          (Fintype.card (X x) : ENNReal) *
            (Fintype.card (Sigma X) : ENNReal)⁻¹ else 0 by
      simp_rw [eq_comm]]
  rw [Finset.sum_ite_eq' Finset.univ d]
  simp only [Finset.mem_univ, if_true]
  rw [ENNReal.div_eq_inv_mul]
  ac_rfl

#print axioms uniformOfFintype_sigma_map_fst_apply

end

end Erdos625
