import Erdos625.PartialDiagonalRateBound
import Erdos625.FourDeficitScoreConvergence
import Mathlib.Tactic

/-!
# Section VII four-deficit partial-diagonal rate bridge

The sole proof obligation derives the two scalar structural inequalities from
the actual four-deficit profile geometry and invokes the already checked scalar
rate bound.  It is a finite deterministic bridge only; it does not assert a
Stirling estimate, a midpoint construction, or an asymptotic diagonal-mass
limit.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

theorem partialDiagonalRate_uniform_negative_fourDeficit
    (T : Real) (p y : Fin 4 → Real)
    (hTupper : T ≤ 4)
    (hyNonneg : ∀ i, 0 ≤ y i)
    (hyLe : ∀ i, y i ≤ p i)
    (hpSum : ∑ i, p i = 1)
    (hpMean : ∑ i, (fourDeficit i : Real) * p i = T)
    (hRlower : (1 : Real) / 64 ≤ ∑ i, (p i - y i)) :
    partialDiagonalRate T
        (∑ i, (p i - y i))
        (∑ i, (fourDeficit i : Real) * (p i - y i))
      ≤ -(1 - ∑ i, (p i - y i)) / 5000 := by
  have hRupper : ∑ i, (p i - y i) ≤ 1 := by
    rw [Finset.sum_sub_distrib, hpSum]
    exact sub_le_self _ (Finset.sum_nonneg (fun i _ ↦ hyNonneg i))
  have hLeft :
      (∑ i, (fourDeficit i : Real) * (p i - y i)) -
          T * (∑ i, (p i - y i)) ≤
        (5 - T) * (∑ i, (p i - y i)) := by
    have h0 := hyLe (0 : Fin 4)
    have h1 := hyLe (1 : Fin 4)
    have h2 := hyLe (2 : Fin 4)
    have h3 := hyLe (3 : Fin 4)
    simp only [Fin.sum_univ_four, fourDeficit_zero, fourDeficit_one,
      fourDeficit_two, fourDeficit_three, Nat.cast_ofNat]
    nlinarith
  have hRight :
      (∑ i, (fourDeficit i : Real) * (p i - y i)) -
          T * (∑ i, (p i - y i)) ≤
        (T - 2) * (1 - ∑ i, (p i - y i)) := by
    have hy0 := hyNonneg (0 : Fin 4)
    have hy1 := hyNonneg (1 : Fin 4)
    have hy2 := hyNonneg (2 : Fin 4)
    have hy3 := hyNonneg (3 : Fin 4)
    simp only [Fin.sum_univ_four, fourDeficit_zero, fourDeficit_one,
      fourDeficit_two, fourDeficit_three, Nat.cast_ofNat] at hpSum hpMean ⊢
    nlinarith
  exact partialDiagonalRate_uniform_negative T _ _ hTupper hRlower hRupper hLeft hRight

end

end Erdos625
