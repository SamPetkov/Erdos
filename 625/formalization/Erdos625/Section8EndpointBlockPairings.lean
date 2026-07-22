import Erdos625.Section8EndpointFoundation
import Mathlib.Tactic

/-!
# Target F1: block-pairing factorial identity

This packages the selection and pairing of endpoint blocks only. It does not
choose any stubs inside a selected block pair.
-/

namespace Erdos625

open scoped BigOperators

set_option autoImplicit false

abbrev FourEndpointBlockPairing (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :=
  {S : UnlabelledTypedSkeleton
      (fun i : Fin 4 => fourEndpointMultiplicity alpha hAlpha k i)
      (fun j : Fin 4 => fourEndpointMultiplicity alpha hAlpha k j) //
    S.typeTable = L.toFun}

theorem card_fourEndpointBlockPairing_mul_cellFactorials
    (alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1)) (L : FourEndpointFullTable) :
    Fintype.card (FourEndpointBlockPairing alpha hAlpha k L) *
        fourEndpointCellFactorialProduct L =
      fourEndpointRowSelectionProduct alpha hAlpha k L *
        fourEndpointColumnSelectionProduct alpha hAlpha k L := by
  simpa [FourEndpointBlockPairing, fourEndpointCellFactorialProduct,
    fourEndpointRowSelectionProduct, fourEndpointColumnSelectionProduct,
    fourEndpointMarginSelectionProduct, fourEndpointRowMargin,
    fourEndpointColumnMargin] using
    (card_unlabelledTypedSkeleton_typeTable_mul_factorials
      L.toFun
      (fun i : Fin 4 => fourEndpointMultiplicity alpha hAlpha k i)
      (fun j : Fin 4 => fourEndpointMultiplicity alpha hAlpha k j))

end Erdos625
