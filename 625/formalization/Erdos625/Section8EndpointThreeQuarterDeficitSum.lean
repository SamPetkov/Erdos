import Erdos625.Section8EndpointAllHighDecoration
import Erdos625.Section8SharpDeficitProduct
import Erdos625.Section8ThreeQuarterDeficitArithmetic
import Mathlib.Tactic

/-!
# Section VIII: three-quarter endpoint deficit sum

For one attained four-endpoint block support, sum every admissible positive
high deficit in each selected cell before taking the product over cells.  The
strict-high condition supplies the three-quarter binary exponent budget, so
the complete positive-deficit fibre is controlled by a genuine geometric
series with no factor proportional to the number of possible deficits.

This module does not sum over block supports, transport endpoint tables, prove
the phase-dependent smallness hypothesis, or assert the final skeleton bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Cellwise geometric base supplied by the strict-high three-quarter
exponent budget. -/
def threeQuarterHighCellBase (n m : Nat) : ENNReal :=
  (n : ENNReal) * (m : ENNReal) /
    (2 : ENNReal) ^ ((3 * m - 1) / 4)

/-- The literal charged local weight is bounded by one power of the
three-quarter base whenever the deficit remains in the strict-high range. -/
theorem nearCellTerm_le_threeQuarterHighCellBase_pow
    (n m d e : Nat) (hhalf : 2 * e < m) :
    nearCellTerm n m d e ≤ threeQuarterHighCellBase n m ^ e := by
  let den : Nat := ∏ t ∈ Finset.Icc 1 e, (d + t : Nat)
  let exponent : Nat := e * m - e * (e + 1) / 2
  let budget : Nat := (3 * m - 1) / 4
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
    exact highDeficit_threeQuarter_exponent_budget m e hhalf
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
      rw [heb, pow_mul, ENNReal.inv_pow]
    _ = threeQuarterHighCellBase n m ^ e := by
      simp only [threeQuarterHighCellBase, budget, div_eq_mul_inv, mul_pow]

/-- A finite initial segment of positive powers is at most `2*rho` when
`rho ≤ 1/2`. -/
theorem sum_range_pow_succ_le_two_mul_of_le_half
    (rho : ENNReal) (L : Nat) (hrho : rho ≤ (1 / 2 : ENNReal)) :
    (∑ ell ∈ Finset.range L, rho ^ (ell + 1)) ≤ 2 * rho := by
  have hgeometric :
      (∑ ell ∈ Finset.range L, rho ^ (ell + 1)) ≤
        rho * (1 - rho)⁻¹ := by
    calc
      (∑ ell ∈ Finset.range L, rho ^ (ell + 1)) ≤
          ∑' ell : Nat, rho ^ (ell + 1) := ENNReal.sum_le_tsum _
      _ = rho * (1 - rho)⁻¹ := ENNReal.tsum_geometric_add_one rho
  have hrhoOne : rho ≤ 1 := hrho.trans (by norm_num)
  have hrhoTop : rho ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num : (1 / 2 : ENNReal) ≠ ∞) hrho
  have hhalfSub : (1 / 2 : ENNReal) ≤ 1 - rho := by
    rw [ENNReal.le_sub_iff_add_le_right hrhoTop hrhoOne]
    calc
      (1 / 2 : ENNReal) + rho ≤ (1 / 2 : ENNReal) + (1 / 2 : ENNReal) :=
        by simpa [add_comm] using add_le_add_left hrho (1 / 2 : ENNReal)
      _ = 1 := by
        simpa only [one_div] using ENNReal.inv_two_add_inv_two
  have hsubZero : (1 - rho : ENNReal) ≠ 0 := by
    have hhalfPos : (0 : ENNReal) < 1 / 2 := by norm_num
    exact ne_of_gt (hhalfPos.trans_le hhalfSub)
  have hsubTop : (1 - rho : ENNReal) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  refine hgeometric.trans ?_
  rw [← div_eq_mul_inv]
  apply (ENNReal.div_le_iff_le_mul (Or.inl hsubZero) (Or.inl hsubTop)).2
  calc
    rho = rho * 1 := by simp
    _ = rho * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by
      rw [ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top]
    _ = (2 * rho) * (1 / 2 : ENNReal) := by
      simp only [one_div]
      ac_rfl
    _ ≤ (2 * rho) * (1 - rho) := mul_le_mul_right hhalfSub _

/-- Any finite set of distinct positive exponents in `Fin (A+1)` is bounded
by the same positive geometric tail. -/
theorem sum_fin_pow_le_two_mul_of_pos_of_le_half
    (rho : ENNReal) (A : Nat) (s : Finset (Fin (A + 1)))
    (hpos : ∀ e ∈ s, 1 ≤ e.1) (hrho : rho ≤ (1 / 2 : ENNReal)) :
    (∑ e ∈ s, rho ^ e.1) ≤ 2 * rho := by
  classical
  calc
    (∑ e ∈ s, rho ^ e.1) =
        ∑ h ∈ s.image (fun e => e.1), rho ^ h := by
      rw [Finset.sum_image Fin.val_injective.injOn]
    _ ≤ ∑ h ∈ Finset.Ico 1 (A + 1), rho ^ h := by
      apply Finset.sum_le_sum_of_subset
      intro h hh
      rcases Finset.mem_image.mp hh with ⟨e, he, rfl⟩
      exact Finset.mem_Ico.mpr ⟨hpos e he, e.isLt⟩
    _ = ∑ ell ∈ Finset.range A, rho ^ (ell + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    _ ≤ 2 * rho := sum_range_pow_succ_le_two_mul_of_le_half rho A hrho

/-- Every allowed endpoint deficit receives the three-quarter power bound. -/
theorem fourEndpointAllHighWeight_le_threeQuarterHighCellBase_pow
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (cell : ↥P.1.edges) (deficit : FourEndpointDeficit alpha)
    (hdeficit : deficit ∈ fourEndpointAllHighAllowed alpha hAlpha P cell) :
    fourEndpointAllHighWeight n alpha hAlpha P cell deficit ≤
      threeQuarterHighCellBase n
        (fourEndpointOverlapSize alpha hAlpha
          cell.1.1.1 cell.1.2.1) ^ deficit.1 := by
  let i : Fin 4 := cell.1.1.1
  let j : Fin 4 := cell.1.2.1
  let m := fourEndpointOverlapSize alpha hAlpha i j
  have hmem : deficit.1 ∈ Finset.Icc 1
      (allHighDeficitCut (fourEndpointLargestSize alpha hAlpha) m) := by
    simpa only [fourEndpointAllHighAllowed, i, j, m,
      Finset.mem_filter, Finset.mem_univ, true_and] using hdeficit
  have hcut : deficit.1 ≤
      allHighDeficitCut (fourEndpointLargestSize alpha hAlpha) m :=
    (Finset.mem_Icc.mp hmem).2
  have hm : m ≤ fourEndpointLargestSize alpha hAlpha :=
    fourEndpointOverlapSize_le_largest alpha hAlpha i j
  have hmHigh : fourEndpointLargestSize alpha hAlpha / 2 < m :=
    fourEndpointOverlapSize_above_half_largest alpha hAlpha hHigh i j
  have hjHigh := allHighDeficit_reconstructs_highMultiplicity
    (fourEndpointLargestSize alpha hAlpha) m deficit.1 hmHigh hcut
  have hhalf := highMultiplicity_deficit_twice_lt
    (fourEndpointLargestSize alpha hAlpha) m (m - deficit.1)
    hm hjHigh (Nat.sub_le _ _)
  have hreconstruct : m - (m - deficit.1) = deficit.1 := by omega
  rw [hreconstruct] at hhalf
  have hlocal := nearCellTerm_le_threeQuarterHighCellBase_pow n m
    (Nat.dist i.val j.val) deficit.1 hhalf
  simpa only [fourEndpointAllHighWeight, i, j, m] using hlocal

/-- The complete positive-deficit fibre of one selected endpoint cell is at
most twice its three-quarter base. -/
theorem sum_fourEndpointAllHighWeight_le_two_threeQuarterHighCellBase
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (cell : ↥P.1.edges)
    (hsmall : threeQuarterHighCellBase n
      (fourEndpointOverlapSize alpha hAlpha
        cell.1.1.1 cell.1.2.1) ≤ (1 / 2 : ENNReal)) :
    (∑ deficit ∈ fourEndpointAllHighAllowed alpha hAlpha P cell,
      fourEndpointAllHighWeight n alpha hAlpha P cell deficit) ≤
        2 * threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1) := by
  calc
    (∑ deficit ∈ fourEndpointAllHighAllowed alpha hAlpha P cell,
        fourEndpointAllHighWeight n alpha hAlpha P cell deficit) ≤
      ∑ deficit ∈ fourEndpointAllHighAllowed alpha hAlpha P cell,
        threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1) ^ deficit.1 := by
      apply Finset.sum_le_sum
      intro deficit hdeficit
      exact fourEndpointAllHighWeight_le_threeQuarterHighCellBase_pow
        n alpha hAlpha hHigh P cell deficit hdeficit
    _ ≤ 2 * threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1) := by
      apply sum_fin_pow_le_two_mul_of_pos_of_le_half
      · intro deficit hdeficit
        have hmem : deficit.1 ∈ Finset.Icc 1
            (allHighDeficitCut (fourEndpointLargestSize alpha hAlpha)
              (fourEndpointOverlapSize alpha hAlpha
                cell.1.1.1 cell.1.2.1)) := by
          simpa only [fourEndpointAllHighAllowed, Finset.mem_filter,
            Finset.mem_univ, true_and] using hdeficit
        exact (Finset.mem_Icc.mp hmem).1
      · exact hsmall

/-- Sharp fixed-support partition bound for every admissible positive high
deficit.  The corresponding analytic estimate is the explicit sixteen
endpoint-type bases are eventually at most `1/2`. -/
theorem sum_fourEndpointAllHighChoiceWeight_le_threeQuarterProduct
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (hsmall : ∀ i j : Fin 4,
      threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha i j) ≤ (1 / 2 : ENNReal)) :
    (∑ choice : NearSkeletonChoice (↥P.1.edges)
        (FourEndpointDeficit alpha)
        (fourEndpointAllHighAllowed alpha hAlpha P),
      nearSkeletonChoiceWeight
        (fourEndpointAllHighAllowed alpha hAlpha P)
        (fourEndpointAllHighWeight n alpha hAlpha P) choice) ≤
      ∏ cell : ↥P.1.edges,
        (1 + 2 * threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1)) := by
  apply sum_nearSkeletonChoiceWeight_le_cellwise_two_rho
  intro cell
  exact sum_fourEndpointAllHighWeight_le_two_threeQuarterHighCellBase
    n alpha hAlpha hHigh P cell
    (hsmall cell.1.1.1 cell.1.2.1)

#print axioms nearCellTerm_le_threeQuarterHighCellBase_pow
#print axioms sum_range_pow_succ_le_two_mul_of_le_half
#print axioms sum_fin_pow_le_two_mul_of_pos_of_le_half
#print axioms fourEndpointAllHighWeight_le_threeQuarterHighCellBase_pow
#print axioms sum_fourEndpointAllHighWeight_le_two_threeQuarterHighCellBase
#print axioms sum_fourEndpointAllHighChoiceWeight_le_threeQuarterProduct

end

end Erdos625
