import Erdos625.ProfileOverlapCanonicalTable
import Mathlib.Tactic

/-!
# Realized-profile block cardinality

The proof was returned by Aristotle project
`2a7a3660-f15c-4904-b2d8-fa5bfed9b61b`, task
`52cb2ed2-a586-4fca-8c97-2648faeba329`, and independently audited before
integration.
-/

namespace Erdos625

set_option autoImplicit false

/-- Any actually realized ordered profile has at most one block slot per
ambient vertex. -/
theorem card_profileBlockIndex_le_vertex_count_of_orderedProfilePartition
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    Fintype.card (ProfileBlockIndex k) ≤ n := by
  calc
    Fintype.card (ProfileBlockIndex k) =
        ∑ _q : ProfileBlockIndex k, 1 := by simp
    _ ≤ ∑ q : ProfileBlockIndex k, profileBlockMargin k q := by
      apply Finset.sum_le_sum
      intro q _hq
      change 1 ≤ (q.1 : ℕ)
      exact pos_of_mem_profileSizes (Multiset.mem_toFinset.mp q.1.2)
    _ = ColoringProfile.vertexMass k :=
      sum_profileBlockMargin_eq_vertexMass k
    _ = n := row₀.vertexMass_eq

end Erdos625
