import Erdos625.QuarterDensityDegree
import Mathlib.Tactic

/-!
# Section 10: one deterministic neighbourhood-deletion step

This module contains exactly the local deterministic step used in the
complement-neighbourhood construction for Lemma 10.1.  From quarter density
on one finite set it produces a vertex and its neighbourhood inside that set,
with the denominator-cleared recurrence inequality.

It does not construct a clique chain, prove a survival estimate, establish a
simultaneous random event, or invoke the greedy-colouring theorem.
-/

open Finset

namespace Erdos625

noncomputable section

/-- From a nonempty quarter-dense finite vertex set, choose a vertex and keep
its neighbours inside the current set.  The retained neighbourhood has size
at least one quarter of the current cardinality, up to the exact additive-one
loss used in the recurrence. -/
theorem quarterDense_neighbor_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (S : Finset V) (hSpos : 0 < S.card)
    (hDense : QuarterDenseOn H S) :
    ∃ v ∈ S, ∃ T : Finset V,
      T ⊆ S ∧ (∀ w ∈ T, H.Adj v w) ∧ S.card - 1 ≤ 4 * T.card := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hSpos
  letI : Nonempty (↥(↑S : Set V)) := ⟨⟨x, by simpa using hx⟩⟩
  have hDense' : Fintype.card (↥(↑S : Set V)) *
      (Fintype.card (↥(↑S : Set V)) - 1) ≤
      8 * (H.induce (↑S : Set V)).edgeFinset.card := by
    simpa [QuarterDenseOn, Fintype.card_coe] using hDense
  obtain ⟨v, hv⟩ := exists_vertex_quarter_degree (H.induce (↑S : Set V)) hDense'
  let T : Finset V := S.filter (fun w => H.Adj v.1 w)
  have hTcard : T.card = (H.induce (↑S : Set V)).degree v := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    refine Finset.card_bij
      (fun w hw => (⟨w, (Finset.mem_filter.mp hw).1⟩ : ↥(↑S : Set V))) ?_ ?_ ?_
    · intro w hw
      rw [SimpleGraph.mem_neighborFinset]
      exact (Finset.mem_filter.mp hw).2
    · intro w₁ hw₁ w₂ hw₂ h
      exact congrArg Subtype.val h
    · intro w hw
      refine ⟨w.1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨w.2, ?_⟩
        rw [SimpleGraph.mem_neighborFinset] at hw
        change H.Adj v.1 w.1 at hw
        exact hw
      · exact Subtype.ext rfl
  refine ⟨v.1, v.2, T, ?_, ?_, ?_⟩
  · exact Finset.filter_subset _ _
  · intro w hw
    exact (Finset.mem_filter.mp hw).2
  · calc
      S.card - 1 = Fintype.card (↥(↑S : Set V)) - 1 := by simp
      _ ≤ 4 * (H.induce (↑S : Set V)).degree v := hv
      _ = 4 * T.card := by rw [hTcard]

#print axioms quarterDense_neighbor_step

end

end Erdos625
