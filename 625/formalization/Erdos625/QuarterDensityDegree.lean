import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A high-degree vertex in a quarter-dense graph

This is the finite deterministic averaging step used by manuscript Lemma 10.1.
The density premise and the conclusion are both denominator-free natural-number
inequalities.
-/

open Finset

namespace Erdos625

/-- If a finite nonempty simple graph has edge density at least one quarter,
then some vertex has degree at least one quarter of `card - 1`.

The premise is `card * (card - 1) ≤ 8 * edges`, which is exactly
`edges / choose(card, 2) ≥ 1/4` after clearing denominators. -/
theorem exists_vertex_quarter_degree
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hDense : Fintype.card V * (Fintype.card V - 1) ≤
      8 * G.edgeFinset.card) :
    ∃ v : V, Fintype.card V - 1 ≤ 4 * G.degree v := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  refine ⟨v, ?_⟩
  rw [← hv]
  have hDegreeSum :
      2 * G.edgeFinset.card ≤ Fintype.card V * G.maxDegree := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc
      ∑ w : V, G.degree w ≤ ∑ _w : V, G.maxDegree := by
        exact Finset.sum_le_sum fun _ _ ↦ G.degree_le_maxDegree _
      _ = Fintype.card V * G.maxDegree := by simp
  have hMultiplied :
      Fintype.card V * (Fintype.card V - 1) ≤
        Fintype.card V * (4 * G.maxDegree) := by
    calc
      Fintype.card V * (Fintype.card V - 1) ≤
          8 * G.edgeFinset.card := hDense
      _ = 4 * (2 * G.edgeFinset.card) := by
        change (4 * 2) * G.edgeFinset.card = _
        rw [Nat.mul_assoc]
      _ ≤ 4 * (Fintype.card V * G.maxDegree) := by
        exact Nat.mul_le_mul_left 4 hDegreeSum
      _ = Fintype.card V * (4 * G.maxDegree) := by
        simp only [Nat.mul_left_comm]
  exact (Nat.mul_le_mul_left_iff Fintype.card_pos).mp hMultiplied

#print axioms exists_vertex_quarter_degree

end Erdos625
