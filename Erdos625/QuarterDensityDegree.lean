import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

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

/-- A finite vertex set spans at least one quarter of all possible edges,
written as a denominator-free natural-number inequality. -/
noncomputable def QuarterDenseOn
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) : Prop := by
  classical
  exact S.card * (S.card - 1) ≤
    8 * (H.induce (↑S : Set V)).edgeFinset.card

private noncomputable def quarterDenseInducedEdgeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (H.induce (↑S : Set V)).edgeFinset.card

private lemma quarterDenseInducedEdgeCount_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) :
    quarterDenseInducedEdgeCount H S = (by
      classical
      exact (H.induce (↑S : Set V)).edgeFinset.card) := by
  rfl

private lemma card_powersetCard_containing_pair
    {V : Type*} [DecidableEq V] (S : Finset V) (u : ℕ) (x y : V)
    (hxy : x ≠ y) (hx : x ∈ S) (hy : y ∈ S) (hu : 2 ≤ u) :
    ((S.powersetCard u).filter (fun T => x ∈ T ∧ y ∈ T)).card =
      (S.card - 2).choose (u - 2) := by
  convert Finset.card_powersetCard (u - 2) (S \ {x, y}) using 1
  · refine' Finset.card_bij (fun T hT => T \ {x, y}) _ _ _ <;>
      simp_all +decide [Finset.subset_iff]
    · intro a ha ha' hx hy
      rw [Finset.card_sdiff]
      simp +decide [*]
    · intro a₁ ha₁ ha₂ ha₃ ha₄ a₂ ha₅ ha₆ ha₇ ha₈ h
      ext z
      by_cases hz : z = x <;> by_cases hz' : z = y <;>
        simp_all +decide [Finset.ext_iff]
    · intro b hb hb'
      use Insert.insert x (Insert.insert y b)
      simp_all +decide
      grind
  · grind

private noncomputable def ambientEdgeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact (H.edgeFinset.filter (fun e => e.toFinset ⊆ S)).card

private lemma quarterDenseInducedEdgeCount_eq_filter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) :
    quarterDenseInducedEdgeCount H S = ambientEdgeCount H S := by
  classical
  refine' Finset.card_bij _ _ _ _
  use fun a ha => Sym2.map (fun x => x.val) a
  · rintro ⟨x, y⟩ hxy
    have hadj : H.Adj (x : V) (y : V) := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hxy
      exact hxy
    simp_all +decide [Finset.subset_iff]
  · intro a₁ ha₁ a₂ ha₂ h
    induction a₁ using Sym2.inductionOn
    induction a₂ using Sym2.inductionOn
    aesop
  · simp +decide [Finset.subset_iff]
    rintro ⟨x, y⟩ hxy hxS
    use s(⟨x, hxS (by simp)⟩, ⟨y, hxS (by simp)⟩)
    aesop

private lemma sum_induced_edges_over_fixed_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) (u : ℕ) (hu : 2 ≤ u) :
    (∑ T ∈ S.powersetCard u, quarterDenseInducedEdgeCount H T) =
      (S.card - 2).choose (u - 2) * quarterDenseInducedEdgeCount H S := by
  classical
  rw [Finset.sum_congr rfl (fun T _ => quarterDenseInducedEdgeCount_eq_filter_card H T)]
  unfold ambientEdgeCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  convert Finset.sum_congr rfl fun y hy => ?_ using 1
  rotate_left
  use fun y => if y.toFinset ⊆ S then (S.card - 2).choose (u - 2) else 0
  · split_ifs <;> simp_all +decide [Finset.subset_iff]
    · rcases y with ⟨x, y⟩
      simp_all +decide
      convert card_powersetCard_containing_pair S u x y hy.ne
        (by tauto) (by tauto) hu using 1
    · grind
  · simp +decide [Finset.sum_ite, quarterDenseInducedEdgeCount_eq_filter_card]
    exact mul_comm _ _

private lemma choose_two_incidence_identity
    (n u : ℕ) (hu : 2 ≤ u) (hun : u ≤ n) :
    n.choose u * (u * (u - 1)) =
      (n * (n - 1)) * ((n - 2).choose (u - 2)) := by
  rcases n with (_ | _ | n) <;> rcases u with (_ | _ | u) <;>
    simp_all +arith +decide
  nlinarith [Nat.add_one_mul_choose_eq n u,
    Nat.add_one_mul_choose_eq (n + 1) (u + 1)]

/-- If every `u`-set is quarter-dense, then every larger finite set is
quarter-dense. -/
theorem quarterDense_all_larger_of_all_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (u : ℕ) (hu : 2 ≤ u)
    (hExact : ∀ T : Finset V, T.card = u → QuarterDenseOn H T) :
    ∀ S : Finset V, u ≤ S.card → QuarterDenseOn H S := by
  intro S hS
  set c := Nat.choose (S.card - 2) (u - 2) with hc_def
  have h_sum :
      ∑ T ∈ S.powersetCard u, (T.card * (T.card - 1)) ≤
        ∑ T ∈ S.powersetCard u, 8 * quarterDenseInducedEdgeCount H T := by
    exact Finset.sum_le_sum fun T hT =>
      hExact T (Finset.mem_powersetCard.mp hT |>.2)
  have h_sum_identity :
      ∑ T ∈ S.powersetCard u, (T.card * (T.card - 1)) =
        (S.card * (S.card - 1)) * c := by
    convert choose_two_incidence_identity S.card u hu hS using 1
    rw [Finset.sum_congr rfl fun x hx => by
      rw [Finset.mem_powersetCard.mp hx |>.2]]
    simp +decide [mul_left_comm]
  have h_sum_identity :
      ∑ T ∈ S.powersetCard u, 8 * quarterDenseInducedEdgeCount H T =
        8 * c * quarterDenseInducedEdgeCount H S := by
    rw [← Finset.mul_sum _ _ _, sum_induced_edges_over_fixed_card H S u hu]
    ring
  unfold QuarterDenseOn
  simp_all +decide [mul_assoc, mul_comm]
  nlinarith! [Nat.choose_pos
    (show u - 2 ≤ S.card - 2 from Nat.sub_le_sub_right hS 2)]

#print axioms exists_vertex_quarter_degree
#print axioms quarterDense_all_larger_of_all_exact

end Erdos625
