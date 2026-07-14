import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

namespace Erdos625

/-!
# Uniform finite probability under equivalence

This finite transport lemma is an atomic ingredient for identifying the law
of the unused-stub matching after the deterministic residual equivalence.  It
does not assert that the original conditional law is uniform; that pushforward
statement remains a separate proof obligation.
-/

theorem uniformOfFintype_map_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  ext b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    rw [if_neg]
    intro h
    apply ha
    rw [h, Equiv.symm_apply_apply]

end Erdos625
