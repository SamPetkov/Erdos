import Erdos625.LocalSignReward
import Erdos625.Section6CompatibleSignsComponents
import Erdos625.Section9ActualResidualCycleSpaceEquiv
import Mathlib.Tactic

/-!
# Section VI: exact signed-overlap local factor

This module proves the finite, denominator-free local-factor identity from
Lemma 6.1.  It includes isolated support-graph vertices, so their free Boolean
signs are counted by the connected-component factor.
-/

namespace Erdos625

open SimpleGraph
open scoped BigOperators

noncomputable section

/-- The bipartite support graph of overlap cells of multiplicity at least two. -/
def signedOverlapSupportGraph {A B : Type*}
    (r : A → B → ℕ) : SimpleGraph (A ⊕ B) :=
  bipartiteGraph fun a b => 2 ≤ r a b

/-- Total number of edge bits duplicated by a pair of profile partitions. -/
noncomputable def overlapDuplicateEdgeCount
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → ℕ) : ℕ :=
  ∑ a, ∑ b, (r a b).choose 2

/-- The local signed-overlap reward, including its binary cycle factor. -/
noncomputable def signedOverlapReward
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → ℕ) : ℕ :=
  (∏ a, ∏ b, localSignRewardNat (r a b)) *
    2 ^ cycleRank (signedOverlapSupportGraph r)

/-- Row and column signs compatible across every multiplicity-two support edge. -/
noncomputable def CompatibleOverlapSignAssignments
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) := by
  classical
  exact CompatibleBoolSignAssignments (signedOverlapSupportGraph r)

/-- The support graph has exactly one edge for every supported row--column
cell. -/
theorem signedOverlapSupportGraph_edgeSet_natCard
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    Nat.card (signedOverlapSupportGraph r).edgeSet =
      (Finset.univ.filter fun e : A × B => 2 ≤ r e.1 e.2).card := by
  classical
  let P : A → B → Prop := fun a b => 2 ≤ r a b
  calc
    Nat.card (signedOverlapSupportGraph r).edgeSet =
        Nat.card {e : A × B // P e.1 e.2} := by
      simpa [signedOverlapSupportGraph, P] using
        Nat.card_congr (supportedCellEquivBipartiteGraphEdge P).symm
    _ = (Finset.univ.filter fun e : A × B => 2 ≤ r e.1 e.2).card := by
      simpa [P] using
        (Fintype.card_subtype (fun e : A × B => 2 ≤ r e.1 e.2))

private lemma localSignRewardNat_eq_pow_choose_sub_indicator (x : ℕ) :
    localSignRewardNat x =
      2 ^ (x.choose 2 - if 2 ≤ x then 1 else 0) := by
  by_cases h3 : 3 ≤ x
  · simp [localSignRewardNat, h3, le_trans (by omega : 2 ≤ 3) h3]
  · have hx : x ≤ 2 := by omega
    interval_cases x <;> norm_num [localSignRewardNat]

private lemma indicator_two_le_le_choose (x : ℕ) :
    (if 2 ≤ x then 1 else 0) ≤ x.choose 2 := by
  by_cases h2 : 2 ≤ x
  · simp only [if_pos h2]
    have hchoose : (2 : ℕ).choose 2 ≤ x.choose 2 :=
      Nat.choose_le_choose 2 h2
    norm_num at hchoose ⊢
    exact hchoose
  · simp [h2]

/-- The product of local rewards is exactly `2` to the duplicated-bit count
minus the number of support edges. -/
theorem prod_localSignRewardNat_matrix_eq_pow
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    (∏ a, ∏ b, localSignRewardNat (r a b)) =
      2 ^ (overlapDuplicateEdgeCount r -
        Nat.card (signedOverlapSupportGraph r).edgeSet) := by
  classical
  let f : A × B → ℕ := fun e => (r e.1 e.2).choose 2
  let q : A × B → ℕ := fun e => if 2 ≤ r e.1 e.2 then 1 else 0
  have hsumSub :
      (∑ e : A × B, (f e - q e)) =
        (∑ e : A × B, f e) - ∑ e : A × B, q e := by
    exact Finset.sum_tsub_distrib
        (s := (Finset.univ : Finset (A × B))) (f := f) (g := q)
        (by
          intro e _
          exact indicator_two_le_le_choose (r e.1 e.2))
  have hsupportSum :
      (∑ e : A × B, q e) =
        Nat.card (signedOverlapSupportGraph r).edgeSet := by
    rw [signedOverlapSupportGraph_edgeSet_natCard r]
    simp [q]
  have hduplicateSum :
      (∑ e : A × B, f e) = overlapDuplicateEdgeCount r := by
    simpa [f, overlapDuplicateEdgeCount] using
      (Fintype.sum_prod_type'
        (fun a : A => fun b : B => (r a b).choose 2))
  calc
    (∏ a, ∏ b, localSignRewardNat (r a b)) =
        ∏ e : A × B, localSignRewardNat (r e.1 e.2) :=
      (Fintype.prod_prod_type'
        (fun a : A => fun b : B => localSignRewardNat (r a b))).symm
    _ = ∏ e : A × B, 2 ^ (f e - q e) := by
      apply Fintype.prod_congr
      intro e
      exact localSignRewardNat_eq_pow_choose_sub_indicator (r e.1 e.2)
    _ = 2 ^ ∑ e : A × B, (f e - q e) := by
      simpa using
        (Finset.prod_pow_eq_pow_sum
          (s := (Finset.univ : Finset (A × B))) (f := fun e => f e - q e) 2)
    _ = 2 ^ (overlapDuplicateEdgeCount r -
          Nat.card (signedOverlapSupportGraph r).edgeSet) := by
      rw [hsumSub, hsupportSum, hduplicateSum]

/-- Every finite graph has at most one more vertex than edge per connected
component, summed over all components. -/
private theorem card_vertices_le_edges_add_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card V ≤
      Nat.card G.edgeSet + Fintype.card G.ConnectedComponent := by
  classical
  let A := graphIncidenceMatrix G
  have hTranspose :
      A.rank + Fintype.card G.ConnectedComponent = Fintype.card V := by
    calc
      A.rank + Fintype.card G.ConnectedComponent =
          (Matrix.transpose A).rank + Module.finrank (ZMod 2)
            (LinearMap.ker (Matrix.transpose A).mulVecLin) := by
        rw [Matrix.rank_transpose,
          finrank_ker_graphIncidenceMatrix_transpose G]
      _ = Module.finrank (ZMod 2)
            (LinearMap.range (Matrix.transpose A).mulVecLin) +
          Module.finrank (ZMod 2)
            (LinearMap.ker (Matrix.transpose A).mulVecLin) := rfl
      _ = Module.finrank (ZMod 2) (V → ZMod 2) :=
        LinearMap.finrank_range_add_finrank_ker
          (Matrix.transpose A).mulVecLin
      _ = Fintype.card V := by simp
  have hRank : A.rank ≤ Nat.card G.edgeSet := by
    simpa only [Nat.card_eq_fintype_card] using A.rank_le_card_width
  omega

/-- Exact denominator-free finite form of the signed local factor. -/
theorem signedOverlapLocalFactor_cross
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    Nat.card (CompatibleOverlapSignAssignments r) *
        2 ^ overlapDuplicateEdgeCount r =
      2 ^ (Fintype.card A + Fintype.card B) *
        signedOverlapReward r := by
  classical
  let G := signedOverlapSupportGraph r
  let E := Nat.card G.edgeSet
  let C := Fintype.card G.ConnectedComponent
  let V := Fintype.card A + Fintype.card B
  let W := overlapDuplicateEdgeCount r
  have hSigns :
      Nat.card (CompatibleOverlapSignAssignments r) = 2 ^ C := by
    simpa [CompatibleOverlapSignAssignments, G, C] using
      natCard_compatibleBoolSignAssignments_eq_two_pow_components G
  have hReward :
      (∏ a, ∏ b, localSignRewardNat (r a b)) = 2 ^ (W - E) := by
    simpa [G, E, W] using prod_localSignRewardNat_matrix_eq_pow r
  have hEW : E ≤ W := by
    change Nat.card (signedOverlapSupportGraph r).edgeSet ≤
      overlapDuplicateEdgeCount r
    rw [signedOverlapSupportGraph_edgeSet_natCard r]
    calc
      (Finset.univ.filter fun e : A × B => 2 ≤ r e.1 e.2).card =
          ∑ e : A × B, if 2 ≤ r e.1 e.2 then 1 else 0 := by simp
      _ ≤ ∑ e : A × B, (r e.1 e.2).choose 2 :=
        Finset.sum_le_sum fun e _ => indicator_two_le_le_choose (r e.1 e.2)
      _ = overlapDuplicateEdgeCount r := by
        simpa [overlapDuplicateEdgeCount] using
          (Fintype.sum_prod_type'
            (fun a : A => fun b : B => (r a b).choose 2))
  have hVE : V ≤ E + C := by
    simpa [G, E, C, V] using card_vertices_le_edges_add_components G
  have hCycle : cycleRank G = E + C - V := by
    let M := graphIncidenceMatrix G
    have hTranspose :
        M.rank + Fintype.card G.ConnectedComponent = Fintype.card (A ⊕ B) := by
      calc
        M.rank + Fintype.card G.ConnectedComponent =
            (Matrix.transpose M).rank + Module.finrank (ZMod 2)
              (LinearMap.ker (Matrix.transpose M).mulVecLin) := by
          rw [Matrix.rank_transpose,
            finrank_ker_graphIncidenceMatrix_transpose G]
        _ = Module.finrank (ZMod 2)
              (LinearMap.range (Matrix.transpose M).mulVecLin) +
            Module.finrank (ZMod 2)
              (LinearMap.ker (Matrix.transpose M).mulVecLin) := rfl
        _ = Module.finrank (ZMod 2) ((A ⊕ B) → ZMod 2) :=
          LinearMap.finrank_range_add_finrank_ker
            (Matrix.transpose M).mulVecLin
        _ = Fintype.card (A ⊕ B) := by simp
    have hOriginal :
        M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
          Fintype.card G.edgeSet := by
      calc
        M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
            Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) +
              Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) := rfl
        _ = Module.finrank (ZMod 2) (G.edgeSet → ZMod 2) :=
          LinearMap.finrank_range_add_finrank_ker M.mulVecLin
        _ = Fintype.card G.edgeSet := by simp
    have hDimension :
        Module.finrank (ZMod 2) (graphCycleSpace G) = E + C - V := by
      change Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = _
      simp only [E, C, V, G, Nat.card_eq_fintype_card,
        Fintype.card_sum] at hTranspose hOriginal ⊢
      omega
    exact (finrank_graphCycleSpace_eq_cycleRank G).symm.trans hDimension
  have hExponent :
      C + W = V + ((W - E) + (E + C - V)) := by
    omega
  rw [hSigns]
  unfold signedOverlapReward
  rw [hReward]
  change 2 ^ C * 2 ^ W = 2 ^ V * (2 ^ (W - E) * 2 ^ cycleRank G)
  rw [hCycle]
  simp only [← pow_add]
  exact congrArg (fun x : ℕ => 2 ^ x) hExponent

/-- The exponent `W + c(H) - |V(H)|` is an honest subtraction: the
subtrahend is at most the preceding sum. -/
theorem signedOverlap_exponent_nonnegative
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    Fintype.card A + Fintype.card B ≤
      overlapDuplicateEdgeCount r +
        Nat.card (signedOverlapSupportGraph r).ConnectedComponent := by
  classical
  let G := signedOverlapSupportGraph r
  let E := Nat.card G.edgeSet
  have hVertices :
      Fintype.card A + Fintype.card B ≤
        E + Nat.card G.ConnectedComponent := by
    simpa only [G, E, Nat.card_eq_fintype_card, Fintype.card_sum] using
      card_vertices_le_edges_add_components G
  have hEdges : E ≤ overlapDuplicateEdgeCount r := by
    change Nat.card (signedOverlapSupportGraph r).edgeSet ≤
      overlapDuplicateEdgeCount r
    rw [signedOverlapSupportGraph_edgeSet_natCard r]
    calc
      (Finset.univ.filter fun e : A × B => 2 ≤ r e.1 e.2).card =
          ∑ e : A × B, if 2 ≤ r e.1 e.2 then 1 else 0 := by simp
      _ ≤ ∑ e : A × B, (r e.1 e.2).choose 2 :=
        Finset.sum_le_sum fun e _ => indicator_two_le_le_choose (r e.1 e.2)
      _ = overlapDuplicateEdgeCount r := by
        simpa [overlapDuplicateEdgeCount] using
          (Fintype.sum_prod_type'
            (fun a : A => fun b : B => (r a b).choose 2))
  simpa [G] using hVertices.trans
    (Nat.add_le_add_right hEdges
      (Nat.card G.ConnectedComponent))

/-- Rational form of the normalized local-factor identity.  This is the
division form used in the manuscript, with the nonzero denominator handled
inside the proof. -/
theorem signedOverlapLocalFactor_div_pow_eq_reward_rat
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    ((Nat.card (CompatibleOverlapSignAssignments r) : ℚ) *
          (2 : ℚ) ^ overlapDuplicateEdgeCount r) /
        (2 : ℚ) ^ (Fintype.card A + Fintype.card B) =
      (signedOverlapReward r : ℚ) := by
  have hcross := signedOverlapLocalFactor_cross r
  have hcast := congrArg (fun x : ℕ => (x : ℚ)) hcross
  norm_num only [Nat.cast_mul, Nat.cast_pow] at hcast
  apply (div_eq_iff (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hcast

/-- The same normalized factor written as the manuscript exponent
`W + c(H) - |V(H)|`. -/
theorem signedOverlapLocalFactor_div_pow_eq_pow_exponent_rat
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    ((Nat.card (CompatibleOverlapSignAssignments r) : ℚ) *
          (2 : ℚ) ^ overlapDuplicateEdgeCount r) /
        (2 : ℚ) ^ (Fintype.card A + Fintype.card B) =
      (2 : ℚ) ^
        (overlapDuplicateEdgeCount r +
          Nat.card (signedOverlapSupportGraph r).ConnectedComponent -
            (Fintype.card A + Fintype.card B)) := by
  classical
  let C := Nat.card
    (signedOverlapSupportGraph r).ConnectedComponent
  let W := overlapDuplicateEdgeCount r
  let V := Fintype.card A + Fintype.card B
  have hSigns :
      Nat.card (CompatibleOverlapSignAssignments r) = 2 ^ C := by
    simpa only [CompatibleOverlapSignAssignments, C,
      ← Nat.card_eq_fintype_card] using
      natCard_compatibleBoolSignAssignments_eq_two_pow_components
        (signedOverlapSupportGraph r)
  have hNonnegative : V ≤ W + C := by
    simpa [V, W, C] using signedOverlap_exponent_nonnegative r
  have hSplit : W + C - V + V = W + C := Nat.sub_add_cancel hNonnegative
  rw [hSigns]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  change ((2 : ℚ) ^ C * 2 ^ W) / 2 ^ V = 2 ^ (W + C - V)
  calc
    ((2 : ℚ) ^ C * 2 ^ W) / 2 ^ V = 2 ^ (W + C) / 2 ^ V := by
      rw [← pow_add, Nat.add_comm C W]
    _ = (2 ^ (W + C - V) * 2 ^ V) / 2 ^ V := by
      congr 1
      rw [← pow_add, hSplit]
    _ = 2 ^ (W + C - V) :=
      mul_div_cancel_right₀ _
        (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))

#print axioms signedOverlapSupportGraph_edgeSet_natCard
#print axioms prod_localSignRewardNat_matrix_eq_pow
#print axioms signedOverlapLocalFactor_cross
#print axioms signedOverlap_exponent_nonnegative
#print axioms signedOverlapLocalFactor_div_pow_eq_reward_rat
#print axioms signedOverlapLocalFactor_div_pow_eq_pow_exponent_rat

end

end Erdos625
