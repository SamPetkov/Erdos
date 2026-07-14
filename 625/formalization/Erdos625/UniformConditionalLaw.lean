import Erdos625.UniformEquivTransport
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

/-!
# Conditioning a finite uniform law

This module proves the generic probability statement needed after exposing a
fixed skeleton: conditioning a uniform law on a nonempty finite event is the
pushforward of the uniform law on the event subtype.  It does not identify any
particular configuration-model event with a residual matching space.
-/

namespace Erdos625

noncomputable section

/-- A nonempty subset of a finite uniform sample space meets its support. -/
def uniformFilterWitness
    {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [Fintype s] [Nonempty s] :
    ∃ a ∈ s, a ∈ (PMF.uniformOfFintype α).support := by
  let x : s := Classical.choice inferInstance
  exact ⟨x.1, x.2, PMF.mem_support_uniformOfFintype x.1⟩

/-- Conditioning a uniform law on a nonempty finite subset is exactly the
pushforward of the uniform law on that subtype. -/
theorem uniform_filter_eq_uniformSubtype_map
    {α : Type*} [Fintype α] [Nonempty α]
    (s : Set α) [Fintype s] [Nonempty s] :
    (PMF.uniformOfFintype α).filter s (uniformFilterWitness s) =
      (PMF.uniformOfFintype s).map (fun x : s => x.1) := by
  classical
  ext a
  rw [PMF.filter_apply, PMF.map_apply]
  have hsum :
      (∑' a' : α,
        s.indicator (PMF.uniformOfFintype α : α → ENNReal) a') =
        (Fintype.card s : ENNReal) / (Fintype.card α : ENNReal) := by
    rw [← PMF.toOuterMeasure_apply,
      PMF.toOuterMeasure_uniformOfFintype_apply]
  by_cases ha : a ∈ s
  · let x : s := ⟨a, ha⟩
    have hmap :
        (∑' y : s,
          if a = (y : α) then PMF.uniformOfFintype s y else 0) =
          (Fintype.card s : ENNReal)⁻¹ := by
      rw [tsum_eq_single x]
      · simp [x, PMF.uniformOfFintype_apply]
      · intro y hy
        rw [if_neg]
        intro hay
        apply hy
        apply Subtype.ext
        exact hay.symm
    rw [Set.indicator_of_mem ha, PMF.uniformOfFintype_apply, hsum, hmap]
    have hcardα : (Fintype.card α : ENNReal) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hcardαtop : (Fintype.card α : ENNReal) ≠ (⊤ : ENNReal) :=
      ENNReal.natCast_ne_top _
    rw [ENNReal.inv_div (Or.inl hcardαtop) (Or.inl hcardα),
      div_eq_mul_inv, ← mul_assoc,
      ENNReal.inv_mul_cancel hcardα hcardαtop, one_mul]
  · rw [Set.indicator_of_notMem ha, zero_mul]
    symm
    rw [ENNReal.tsum_eq_zero]
    intro x
    rw [if_neg]
    intro hax
    exact ha (hax ▸ x.2)

end

end Erdos625
