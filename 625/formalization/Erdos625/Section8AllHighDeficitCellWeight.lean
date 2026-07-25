import Erdos625.Section8NearCellChoiceLink
import Erdos625.Section8AllHighDeficitArithmetic
import Mathlib.Tactic

/-!
# Section VIII: literal all-high one-cell weight bound

This module connects the all-high deficit parametrization to the repository's
literal one-cell stub-matching weight `nearCellTerm`. Despite the historical
name, the same exact local weight applies to every endpoint deficit above the
high-cell cutoff.

The main result charges one physical deficit `e` by a single geometric base.
It does not yet multiply the bound over an endpoint block pairing or perform
the phase asymptotics.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Geometric base used for one all-high endpoint deficit. -/
def allHighCellBase (n m : Nat) : ENNReal :=
  (n : ENNReal) * (m : ENNReal) /
    (2 : ENNReal) ^ ((2 * m) / 3)

/-- The literal finite choices for every nonzero endpoint deficit compatible
with the strict global high-cell cutoff. -/
def allHighCellAllowed (a m : Nat) : Fin 1 → Finset (Fin (m + 1)) :=
  nearCellAllowed m (allHighDeficitCut a m)

/-- Exact optional-deficit expansion for one distinguishable endpoint cell over
the full high range. -/
theorem allHighCellChoiceExpansion
    (n a m d : Nat) :
    (∑ choice : NearSkeletonChoice (Fin 1) (Fin (m + 1))
        (allHighCellAllowed a m),
      nearSkeletonChoiceWeight (allHighCellAllowed a m)
        (nearCellWeight n m d (allHighDeficitCut a m)) choice) =
      1 + ∑ q ∈ allHighCellAllowed a m 0,
        nearCellTerm n m d q.1 := by
  rw [sum_nearSkeletonChoiceWeight_eq_product]
  simp [allHighCellAllowed, nearCellWeight]

/-- The exact charged local stub-matching weight is bounded by one power of the
all-high geometric base whenever the deficit is below half the endpoint size. -/
theorem nearCellTerm_le_allHighCellBase_pow
    (n m d e : Nat) (hhalf : 2 * e < m) :
    nearCellTerm n m d e ≤ allHighCellBase n m ^ e := by
  let den : Nat := ∏ t ∈ Finset.Icc 1 e, (d + t : Nat)
  let exponent : Nat := e * m - e * (e + 1) / 2
  let budget : Nat := (2 * m) / 3
  have hdenPos : 0 < den := by
    dsimp [den]
    apply Finset.prod_pos
    intro t ht
    simp only [Finset.mem_Icc] at ht
    omega
  have hdenOne : 1 ≤ den := Nat.one_le_iff_ne_zero.mpr hdenPos.ne'
  have hdenZero : (den : ENNReal) ≠ 0 := by
    exact_mod_cast hdenPos.ne'
  have hdenTop : (den : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top den
  have hchooseNat : Nat.choose m e ≤ m ^ e := Nat.choose_le_pow m e
  have hchoose : (Nat.choose m e : ENNReal) ≤ (m : ENNReal) ^ e := by
    exact_mod_cast hchooseNat
  have hdiv :
      ((n : ENNReal) ^ e * (Nat.choose m e : ENNReal)) /
          (den : ENNReal) ≤
        (n : ENNReal) ^ e * (Nat.choose m e : ENNReal) := by
    apply (ENNReal.div_le_iff_le_mul (Or.inl hdenZero) (Or.inl hdenTop)).2
    exact le_mul_of_one_le_right bot_le (by exact_mod_cast hdenOne)
  have hfirst :
      ((n : ENNReal) ^ e * (Nat.choose m e : ENNReal)) /
          (den : ENNReal) ≤
        (n : ENNReal) ^ e * (m : ENNReal) ^ e :=
    hdiv.trans (mul_le_mul_right hchoose _)
  have hbudgetNat : e * budget ≤ exponent := by
    dsimp [budget, exponent]
    exact highDeficit_twoThird_exponent_budget m e hhalf
  have hpowNat : 2 ^ (e * budget) ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) hbudgetNat
  have hpow :
      (2 : ENNReal) ^ (e * budget) ≤ (2 : ENNReal) ^ exponent := by
    exact_mod_cast hpowNat
  have hinv :
      ((2 : ENNReal) ^ exponent)⁻¹ ≤
        ((2 : ENNReal) ^ (e * budget))⁻¹ := by
    rw [ENNReal.inv_le_inv]
    exact hpow
  calc
    nearCellTerm n m d e =
        (((n : ENNReal) ^ e * (Nat.choose m e : ENNReal)) /
          (den : ENNReal)) * ((2 : ENNReal) ^ exponent)⁻¹ := by
      simp only [nearCellTerm, den, exponent]
    _ ≤ ((n : ENNReal) ^ e * (m : ENNReal) ^ e) *
          ((2 : ENNReal) ^ (e * budget))⁻¹ :=
      mul_le_mul' hfirst hinv
    _ = ((n : ENNReal) ^ e * (m : ENNReal) ^ e) *
          (((2 : ENNReal) ^ budget)⁻¹) ^ e := by
      have heb : e * budget = budget * e := Nat.mul_comm _ _
      rw [heb, pow_mul, ← inv_pow]
    _ = allHighCellBase n m ^ e := by
      simp only [allHighCellBase, budget, div_eq_mul_inv, mul_pow]

/-- Every allowed nonzero all-high deficit satisfies the hypothesis of the
literal one-cell geometric bound. -/
theorem nearCellTerm_le_allHighCellBase_pow_of_mem
    (n a m d : Nat) (hm : m ≤ a) (hmHigh : a / 2 < m)
    (e : Fin (m + 1))
    (he : e ∈ allHighCellAllowed a m 0) :
    nearCellTerm n m d e.1 ≤ allHighCellBase n m ^ e.1 := by
  have hmem : e.1 ∈ Finset.Icc 1 (allHighDeficitCut a m) := by
    simpa only [allHighCellAllowed, nearCellAllowed, Finset.mem_filter,
      Finset.mem_univ, true_and] using he
  have heCut : e.1 ≤ allHighDeficitCut a m :=
    (Finset.mem_Icc.mp hmem).2
  have hjHigh := allHighDeficit_reconstructs_highMultiplicity a m e.1 hmHigh heCut
  have hhalf := highMultiplicity_deficit_twice_lt a m (m - e.1)
    hm hjHigh (Nat.sub_le _ _)
  have hreconstruct : m - (m - e.1) = e.1 := by omega
  rw [hreconstruct] at hhalf
  exact nearCellTerm_le_allHighCellBase_pow n m d e.1 hhalf

#print axioms allHighCellChoiceExpansion
#print axioms nearCellTerm_le_allHighCellBase_pow
#print axioms nearCellTerm_le_allHighCellBase_pow_of_mem

end

end Erdos625
