import Erdos625.Section8EndpointFoundation
import Mathlib.Tactic

/-!
# Target F2: one full-cell stub-matching count

This is the literal single-cell factor
`(u)_x (v)_x / x!`; it makes no claim about selecting or pairing profile
blocks.
-/

namespace Erdos625

set_option autoImplicit false

abbrev SingleCellStubMatching (u v x : Nat) :=
  {S : UnlabelledTypedSkeleton (fun _ : Unit => u) (fun _ : Unit => v) //
    S.typeTable () () = x}

theorem card_singleCellStubMatching_mul_factorial
    (u v x : Nat) :
    Fintype.card (SingleCellStubMatching u v x) * x.factorial =
      u.descFactorial x * v.descFactorial x := by
  let L : Unit → Unit → Nat := fun _ _ => x
  have hPred (S : UnlabelledTypedSkeleton
      (fun _ : Unit => u) (fun _ : Unit => v)) :
      S.typeTable () () = x ↔ S.typeTable = L := by
    constructor
    · intro h
      funext i j
      cases i
      cases j
      exact h
    · intro h
      exact congrFun (congrFun h ()) ()
  have hCard :
      Fintype.card (SingleCellStubMatching u v x) =
        Fintype.card
          {S : UnlabelledTypedSkeleton
              (fun _ : Unit => u) (fun _ : Unit => v) //
            S.typeTable = L} := by
    exact Fintype.card_congr
      (Equiv.subtypeEquiv (Equiv.refl _) hPred)
  rw [hCard]
  simpa [L] using
    (card_unlabelledTypedSkeleton_typeTable_mul_factorials
      L (fun _ : Unit => u) (fun _ : Unit => v))

end Erdos625
