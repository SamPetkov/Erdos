import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

theorem fourEndpoint_rowAssignment_product_expansion
    {R : Type*} [CommSemiring R]
    (r : Fin 4 → Nat) (q : Fin 4 → Fin 4 → R) :
    (∑ f : ((i : Fin 4) → Fin (r i) → Fin 4),
      ∏ i : Fin 4, ∏ x : Fin (r i), q i (f i x)) =
    ∏ i : Fin 4, (∑ j : Fin 4, q i j) ^ r i := by
  simp_rw [Fintype.sum_pow]
  rw [Fintype.prod_sum]

end

end Erdos625
