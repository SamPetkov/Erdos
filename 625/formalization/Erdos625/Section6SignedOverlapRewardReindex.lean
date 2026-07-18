import Erdos625.Section6SignedOverlapLocalFactor
import Mathlib.Tactic

/-!
# Reindexing invariance of the signed overlap reward

The signed local factor is independent of the names used for its row and
column index types.  This finite-equivalence transport is the interface used
to pass from ordered block slots to the kernel parts of the corresponding
unordered profile partitions.
-/

namespace Erdos625

open SimpleGraph
open scoped BigOperators

noncomputable section

/-- Transport an overlap matrix along equivalences of its row and column
indexing types. -/
def reindexOverlapMatrix {A B A' B' : Type*}
    (eA : A ≃ A') (eB : B ≃ B') (r : A → B → Nat) : A' → B' → Nat :=
  fun a' b' => r (eA.symm a') (eB.symm b')

/-- The bipartite support graph commutes with reindexing its two sides. -/
noncomputable def signedOverlapSupportGraphReindexIso
    {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (eA : A ≃ A') (eB : B ≃ B') (r : A → B → Nat) :
    signedOverlapSupportGraph r ≃g
      signedOverlapSupportGraph (reindexOverlapMatrix eA eB r) where
  toEquiv := Equiv.sumCongr eA eB
  map_rel_iff' := by
    intro u v
    rcases u with a | b <;> rcases v with a' | b' <;>
      simp [signedOverlapSupportGraph, bipartiteGraph, reindexOverlapMatrix]

/-- Cycle rank of the signed support graph is invariant under a pair of
finite index equivalences. -/
theorem cycleRank_signedOverlapSupportGraph_reindex
    {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (eA : A ≃ A') (eB : B ≃ B') (r : A → B → Nat) :
    cycleRank (signedOverlapSupportGraph r) =
      cycleRank (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)) := by
  classical
  letI : DecidableEq (A ⊕ B) := Classical.decEq _
  letI : DecidableEq (A' ⊕ B') := Classical.decEq _
  let φ := signedOverlapSupportGraphReindexIso eA eB r
  have hEdge : (signedOverlapSupportGraph r).edgeFinset.card =
      (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).edgeFinset.card := by
    calc
      (signedOverlapSupportGraph r).edgeFinset.card =
          Fintype.card (signedOverlapSupportGraph r).edgeSet :=
        SimpleGraph.edgeFinset_card
      _ = Fintype.card
          (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).edgeSet :=
        Fintype.card_congr φ.mapEdgeSet
      _ = (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).edgeFinset.card :=
        SimpleGraph.edgeFinset_card.symm
  have hComp : Fintype.card (signedOverlapSupportGraph r).ConnectedComponent =
      Fintype.card
        (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).ConnectedComponent :=
    Fintype.card_congr φ.connectedComponentEquiv
  have hVert : Fintype.card (A ⊕ B) = Fintype.card (A' ⊕ B') :=
    φ.card_eq
  unfold cycleRank
  calc
    (signedOverlapSupportGraph r).edgeFinset.card +
          Fintype.card (signedOverlapSupportGraph r).ConnectedComponent -
        Fintype.card (A ⊕ B) =
      (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).edgeFinset.card +
          Fintype.card (signedOverlapSupportGraph r).ConnectedComponent -
        Fintype.card (A ⊕ B) := by rw [hEdge]
    _ = (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).edgeFinset.card +
          Fintype.card
            (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).ConnectedComponent -
        Fintype.card (A ⊕ B) := by rw [hComp]
    _ = (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).edgeFinset.card +
          Fintype.card
            (signedOverlapSupportGraph (reindexOverlapMatrix eA eB r)).ConnectedComponent -
        Fintype.card (A' ⊕ B') := by rw [hVert]

/-- The exact signed-overlap reward is invariant under reindexing either
side of the overlap matrix by a finite equivalence. -/
theorem signedOverlapReward_reindex
    {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (eA : A ≃ A') (eB : B ≃ B') (r : A → B → Nat) :
    signedOverlapReward r =
      signedOverlapReward (reindexOverlapMatrix eA eB r) := by
  have hprod :
      (∏ a, ∏ b, localSignRewardNat (r a b)) =
        ∏ a', ∏ b', localSignRewardNat
          (reindexOverlapMatrix eA eB r a' b') := by
    calc
      (∏ a, ∏ b, localSignRewardNat (r a b)) =
          ∏ x : A × B, localSignRewardNat (r x.1 x.2) :=
        (Fintype.prod_prod_type' fun a : A => fun b : B =>
          localSignRewardNat (r a b)).symm
      _ = ∏ x' : A' × B', localSignRewardNat
          (reindexOverlapMatrix eA eB r x'.1 x'.2) := by
        apply Fintype.prod_equiv (eA.prodCongr eB)
        intro x
        simp [reindexOverlapMatrix]
      _ = ∏ a', ∏ b', localSignRewardNat
          (reindexOverlapMatrix eA eB r a' b') :=
        Fintype.prod_prod_type'
          (fun a' : A' => fun b' : B' =>
            localSignRewardNat (reindexOverlapMatrix eA eB r a' b'))
  unfold signedOverlapReward
  rw [hprod, cycleRank_signedOverlapSupportGraph_reindex eA eB r]

#print axioms signedOverlapSupportGraphReindexIso
#print axioms cycleRank_signedOverlapSupportGraph_reindex
#print axioms signedOverlapReward_reindex

end

end Erdos625
