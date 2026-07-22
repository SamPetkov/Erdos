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

/-- The natural deficit `alpha * K - n`, cast to the reals, is exactly the
number of parts times the four-size target mean deficit. -/
theorem deficit_cast_eq_parts_mul_fourSizeTarget
    (n alpha K : Nat) (hK : 0 < K) (hn : n ≤ alpha * K) :
    ((alpha * K - n : Nat) : Real) =
      (K : Real) * fourSizeTarget n alpha (K : Real) := by
  rw [Nat.cast_sub hn]
  unfold fourSizeTarget
  push_cast
  have hK_real : (K : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hK)
  field_simp

/-- Embed four multiplicities into the full profile indexed by class sizes
`1, ..., alpha + 1`. -/
def fourDeficitEmbedding (alpha : Nat) (hAlpha : 5 < alpha)
    (m : Fin 4 -> Nat) : ColoringProfile (alpha + 1) :=
  fun j =>
    ∑ i : Fin 4,
      if fourDeficitCoordinate alpha hAlpha i = j then m i else 0

theorem fourDeficitEmbedding_profile_invariants
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 -> Nat) :
    ColoringProfile.partCount (fourDeficitEmbedding alpha hAlpha m) =
      (∑ i : Fin 4, m i) ∧
    ColoringProfile.vertexMass (fourDeficitEmbedding alpha hAlpha m) =
      (∑ i : Fin 4, (alpha - fourDeficit i) * m i) ∧
    IsFourDeficitSupported alpha (fourDeficitEmbedding alpha hAlpha m) := by
  constructor
  · rw [ColoringProfile.partCount_eq_sum]
    simp [fourDeficitEmbedding, Finset.sum_comm]
  constructor
  · rw [ColoringProfile.vertexMass_eq_sum]
    simp only [fourDeficitEmbedding, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mul_ite, mul_zero, Fintype.sum_ite_eq]
    congr 1
    unfold fourDeficitCoordinate
    rw [Fin.val_rev, Fin.val_succ]
    fin_cases i <;> simp [fourDeficit] <;> omega
  · intro j hj
    by_contra h
    simp only [not_exists] at h
    have hc : ∀ i : Fin 4, fourDeficitCoordinate alpha hAlpha i ≠ j := by
      intro i hij
      apply h i
      rw [← hij, profileDeficit_fourDeficitCoordinate]
    have hz : fourDeficitEmbedding alpha hAlpha m j = 0 := by
      rw [fourDeficitEmbedding]
      simp [hc]
    exact hj hz

/-- The four-deficit embedding has the prescribed value at each distinguished
coordinate and vanishes away from the four distinguished coordinates. -/
theorem fourDeficitEmbedding_eval_and_off_image
    (alpha : Nat) (hAlpha : 5 < alpha) (m : Fin 4 → Nat) :
    (∀ i : Fin 4,
      fourDeficitEmbedding alpha hAlpha m
        (fourDeficitCoordinate alpha hAlpha i) = m i) ∧
    (∀ j : Fin (alpha + 1),
      (∀ i : Fin 4, fourDeficitCoordinate alpha hAlpha i ≠ j) →
        fourDeficitEmbedding alpha hAlpha m j = 0) := by
  have hcoord : Function.Injective (fourDeficitCoordinate alpha hAlpha) := by
    intro i k hik
    have h := congrArg (profileDeficit alpha) hik
    rw [profileDeficit_fourDeficitCoordinate,
      profileDeficit_fourDeficitCoordinate] at h
    simp [fourDeficit] at h
    exact Fin.ext h
  constructor
  · intro i
    unfold fourDeficitEmbedding
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki
      simp [hcoord.ne hki]
    · simp
  · intro j hj
    unfold fourDeficitEmbedding
    apply Finset.sum_eq_zero
    intro i _
    simp [hj i]

#print axioms fourDeficitEmbedding_eval_and_off_image

end

end Erdos625
