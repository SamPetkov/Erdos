import Erdos625.SignedFourSizeObjective

/-!
# Concrete four-deficit profile coordinates

The finite map below places four natural multiplicities at the class-size
coordinates corresponding to deficits `2, 3, 4, 5`.  It is intentionally a
plain finite sum so that image and off-image statements are genuine finite
facts, not properties hidden in a subtype or a choice function.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- The stored profile coordinate represents the class size obtained by
subtracting the corresponding deficit from `alpha`. -/
theorem fourDeficitCoordinate_val_add_one_eq
    (alpha : Nat) (hAlpha : 5 < alpha) (i : Fin 4) :
    (fourDeficitCoordinate alpha hAlpha i).val + 1 =
      alpha - fourDeficit i := by
  unfold fourDeficitCoordinate
  rw [Fin.val_rev, Fin.val_succ]
  have hle : fourDeficit i ≤ 5 := by
    fin_cases i <;> norm_num [fourDeficit]
  change alpha + 1 - (fourDeficit i + 1 + 1) + 1 =
    alpha - fourDeficit i
  omega

/-- Embed four multiplicities into the full profile indexed by class sizes
`1, ..., alpha + 1`. -/
def fourDeficitEmbedding (alpha : Nat) (hAlpha : 5 < alpha)
    (m : Fin 4 -> Nat) : ColoringProfile (alpha + 1) :=
  fun j =>
    ∑ i : Fin 4,
      if fourDeficitCoordinate alpha hAlpha i = j then m i else 0

end

end Erdos625
