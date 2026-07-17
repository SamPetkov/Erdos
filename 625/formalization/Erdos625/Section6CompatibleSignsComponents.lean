import Erdos625.Section9CycleSpaceCardinality
import Mathlib.Tactic

/-!
# E3: compatible Boolean signs and connected components

This file isolates the exact finite component-sign count used in the signed
overlap argument.  It contains no probability or asymptotic assertion.
-/

namespace Erdos625

open SimpleGraph

noncomputable section

/-- Boolean vertex signs that agree across every graph edge. -/
def CompatibleBoolSignAssignments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  {sigma : V -> Bool //
    forall u v : V, G.Adj u v -> sigma u = sigma v}

/-- A compatible Boolean sign assignment is exactly one Boolean choice per
connected component, including isolated vertices. -/
noncomputable def compatibleBoolSignAssignmentsEquivComponents
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    CompatibleBoolSignAssignments G ≃
      (G.ConnectedComponent -> Bool) := by
  let toFun : CompatibleBoolSignAssignments G → G.ConnectedComponent → Bool := fun sigma =>
    SimpleGraph.ConnectedComponent.lift sigma.1 (by
      intro u v p hp
      induction p with
      | nil => rfl
      | cons hadj p ih =>
          have hpt : p.IsPath := by simpa using hp.tail
          exact (sigma.2 _ _ hadj).trans (ih hpt))
  let invFun : (G.ConnectedComponent → Bool) → CompatibleBoolSignAssignments G := fun f =>
    ⟨fun v => f (G.connectedComponentMk v), by
      intro u v huv
      exact congrArg f
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj huv)⟩
  refine ⟨toFun, invFun, ?_, ?_⟩
  · intro sigma
    apply Subtype.ext
    funext v
    rfl
  · intro f
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl

/-- Hence the number of compatible Boolean sign assignments is
`2 ^ c(G)`. -/
theorem natCard_compatibleBoolSignAssignments_eq_two_pow_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card (CompatibleBoolSignAssignments G) =
      2 ^ Fintype.card G.ConnectedComponent := by
  rw [Nat.card_congr (compatibleBoolSignAssignmentsEquivComponents G), Nat.card_fun,
    Nat.card_eq_fintype_card]
  norm_num [Nat.card_eq_fintype_card]

#print axioms compatibleBoolSignAssignmentsEquivComponents
#print axioms natCard_compatibleBoolSignAssignments_eq_two_pow_components

end

end Erdos625
