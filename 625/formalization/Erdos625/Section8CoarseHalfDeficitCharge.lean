import Erdos625.Section8DirectHalfDeficitAssembly
import Erdos625.Section8ThreeQuarterDeficitArithmetic
import Erdos625.Section8AllHighDeficitProductBound
import Mathlib.Tactic

/-!
# Section VIII: coarse uniform charge for the half-deficit envelope

The exact local ratio contains a binomial factor and an endpoint-distance
factor.  Neither is needed in the final asymptotic argument.  Under the sole
condition `2h<m`, discard the distance denominator, bound `choose m h` by
`m^h`, and use the three-quarter exponent budget.

This yields the endpoint-only base

`rho(n,m) = n*m / 2^floor((3m-1)/4)`.

For maximum formal simplicity, this module does not sum a geometric series.
It uses the generic cardinality interface: there are at most
`alpha+1` positive deficit candidates in one cell, and each candidate has
weight at most `rho^h <= rho` when `rho<=1`.  The resulting extra factor of
`alpha+1` is asymptotically harmless and removes another analytic lemma from the
remaining proof.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Coarse endpoint-only charge for one unit of deficit. -/
def threeQuarterCellBase (n m : Nat) : ENNReal :=
  (n : ENNReal) * (m : ENNReal) /
    (2 : ENNReal) ^ ((3 * m - 1) / 4)

/-- The charged exact local ratio is bounded by one power of the three-quarter
base.  The bound is independent of the endpoint distance `d`. -/
theorem nearCellTerm_le_threeQuarterCellBase_pow
    (n m d h : Nat) (hhalf : 2 * h < m) :
    nearCellTerm n m d h ≤ threeQuarterCellBase n m ^ h := by
  let den : Nat := ∏ t ∈ Finset.Icc 1 h, (d + t : Nat)
  let exponent : Nat := h * m - h * (h + 1) / 2
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
  have hchooseNat : Nat.choose m h ≤ m ^ h := Nat.choose_le_pow m h
  have hchoose : (Nat.choose m h : ENNReal) ≤ (m : ENNReal) ^ h := by
    exact_mod_cast hchooseNat
  have hdiv :
      ((n : ENNReal) ^ h * (Nat.choose m h : ENNReal)) /
          (den : ENNReal) ≤
        (n : ENNReal) ^ h * (Nat.choose m h : ENNReal) := by
    apply (ENNReal.div_le_iff_le_mul (Or.inl hdenZero) (Or.inl hdenTop)).2
    exact le_mul_of_one_le_right bot_le (by exact_mod_cast hdenOne)
  have hfirst :
      ((n : ENNReal) ^ h * (Nat.choose m h : ENNReal)) /
          (den : ENNReal) ≤
        (n : ENNReal) ^ h * (m : ENNReal) ^ h :=
    hdiv.trans (mul_le_mul_right hchoose _)
  have hbudgetNat : h * budget ≤ exponent := by
    dsimp only [budget, exponent]
    exact highDeficit_threeQuarter_exponent_budget m h hhalf
  have hpowNat : 2 ^ (h * budget) ≤ 2 ^ exponent :=
    Nat.pow_le_pow_right (by decide) hbudgetNat
  have hpow :
      (2 : ENNReal) ^ (h * budget) ≤ (2 : ENNReal) ^ exponent := by
    exact_mod_cast hpowNat
  have hinv :
      ((2 : ENNReal) ^ exponent)⁻¹ ≤
        ((2 : ENNReal) ^ (h * budget))⁻¹ := by
    rw [ENNReal.inv_le_inv]
    exact hpow
  calc
    nearCellTerm n m d h =
        (((n : ENNReal) ^ h * (Nat.choose m h : ENNReal)) /
          (den : ENNReal)) * ((2 : ENNReal) ^ exponent)⁻¹ := by
      simp only [nearCellTerm, den, exponent]
    _ ≤ ((n : ENNReal) ^ h * (m : ENNReal) ^ h) *
          ((2 : ENNReal) ^ (h * budget))⁻¹ :=
      mul_le_mul' hfirst hinv
    _ = ((n : ENNReal) ^ h * (m : ENNReal) ^ h) *
          (((2 : ENNReal) ^ budget)⁻¹) ^ h := by
      have hcomm : h * budget = budget * h := Nat.mul_comm _ _
      rw [hcomm, pow_mul, ENNReal.inv_pow]
    _ = threeQuarterCellBase n m ^ h := by
      simp only [threeQuarterCellBase, budget, div_eq_mul_inv, mul_pow]

/-- Every deficit admitted by the enlarged half-envelope has positive exponent
and satisfies the coarse three-quarter charge. -/
theorem fourEndpointHalfDeficitWeight_le_threeQuarterBase_pow_of_mem
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges) (deficit : FourEndpointDeficit alpha)
    (hdeficit : deficit ∈
      fourEndpointHalfDeficitAllowed alpha hAlpha P cell) :
    fourEndpointHalfDeficitWeight n alpha hAlpha P cell deficit ≤
      threeQuarterCellBase n
        (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1) ^
          deficit.1 := by
  have hmem : 0 < deficit.1 ∧
      2 * deficit.1 <
        fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1 := by
    simpa only [fourEndpointHalfDeficitAllowed, Finset.mem_filter,
      Finset.mem_univ, true_and] using hdeficit
  exact nearCellTerm_le_threeQuarterCellBase_pow n
    (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1)
    (Nat.dist cell.1.1.1.val cell.1.2.1.val) deficit.1 hmem.2

/-- The enlarged positive-deficit set has at most `alpha+1` elements. -/
theorem card_fourEndpointHalfDeficitAllowed_le
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges) :
    (fourEndpointHalfDeficitAllowed alpha hAlpha P cell).card ≤ alpha + 1 := by
  have hsubset : fourEndpointHalfDeficitAllowed alpha hAlpha P cell ⊆
      (Finset.univ : Finset (FourEndpointDeficit alpha)) := by
    intro deficit _
    exact Finset.mem_univ deficit
  calc
    (fourEndpointHalfDeficitAllowed alpha hAlpha P cell).card ≤
        (Finset.univ : Finset (FourEndpointDeficit alpha)).card :=
      Finset.card_le_card hsubset
    _ = alpha + 1 := by simp [FourEndpointDeficit]

/-- Coarse uniform product bound on one fixed block support.  This deliberately
pays the harmless factor `alpha+1` instead of requiring a finite geometric-
series theorem. -/
theorem sum_fourEndpointHalfDeficitChoiceWeight_le_uniform
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (rho : ENNReal) (hrho : rho ≤ 1)
    (hbase : ∀ cell : ↥P.edges,
      threeQuarterCellBase n
        (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1) ≤ rho) :
    (∑ choice : NearSkeletonChoice (↥P.edges) (FourEndpointDeficit alpha)
        (fourEndpointHalfDeficitAllowed alpha hAlpha P),
      nearSkeletonChoiceWeight
        (fourEndpointHalfDeficitAllowed alpha hAlpha P)
        (fourEndpointHalfDeficitWeight n alpha hAlpha P) choice) ≤
      (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^ P.edges.card := by
  have hbound :
      (∑ choice : NearSkeletonChoice (↥P.edges) (FourEndpointDeficit alpha)
          (fourEndpointHalfDeficitAllowed alpha hAlpha P),
        nearSkeletonChoiceWeight
          (fourEndpointHalfDeficitAllowed alpha hAlpha P)
          (fourEndpointHalfDeficitWeight n alpha hAlpha P) choice) ≤
        (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^
          Fintype.card (↥P.edges) := by
    apply sum_nearSkeletonChoiceWeight_le_uniform_pow
      (fourEndpointHalfDeficitAllowed alpha hAlpha P)
      (fourEndpointHalfDeficitWeight n alpha hAlpha P)
      (fun deficit => deficit.1) (alpha + 1) rho hrho
    · exact card_fourEndpointHalfDeficitAllowed_le alpha hAlpha P
    · intro cell deficit hdeficit
      have hmem :
          0 < deficit.1 ∧
            2 * deficit.1 <
              fourEndpointOverlapSize alpha hAlpha
                cell.1.1.1 cell.1.2.1 := by
        simpa only [fourEndpointHalfDeficitAllowed, Finset.mem_filter,
          Finset.mem_univ, true_and] using hdeficit
      exact hmem.1
    · intro cell deficit hdeficit
      exact (fourEndpointHalfDeficitWeight_le_threeQuarterBase_pow_of_mem
        n alpha hAlpha P cell deficit hdeficit).trans
          (ENNReal.pow_le_pow_left (hbase cell))
  simpa using hbound

/-- Global attained-demand bound after replacing every support's exact local
partition function by the same coarse base. -/
theorem sum_profileCanonicalHighSkeleton_le_uniformHalfDeficitSupportSum
    (n alpha : Nat) (hAlpha : 5 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (weightDemand : ProfileCanonicalHighSkeleton k
      (fourEndpointLargestSize alpha hAlpha) → ENNReal)
    (reference : FourEndpointAbstractBlockSkeleton alpha hAlpha k → ENNReal)
    (rho : ENNReal) (hrho : rho ≤ 1)
    (hweight : ∀ demand,
      weightDemand demand ≤
        fourEndpointSupportChoiceChargedWeight n alpha hAlpha reference
          (fourEndpointDemandSupportChoiceEncoding
            alpha hAlpha k hcover slotIndex demand))
    (hbase : ∀ (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
      (cell : ↥P.edges),
      threeQuarterCellBase n
        (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1) ≤ rho) :
    (∑ demand, weightDemand demand) ≤
      ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        reference P *
          (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^ P.edges.card := by
  calc
    (∑ demand, weightDemand demand) ≤
        ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          reference P *
            ∏ cell : ↥P.edges,
              (1 + ∑ deficit ∈
                fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
                fourEndpointHalfDeficitWeight
                  n alpha hAlpha P cell deficit) :=
      sum_profileCanonicalHighSkeleton_le_directSupportChoiceProduct
        n alpha hAlpha k hcover slotIndex weightDemand reference hweight
    _ ≤ ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
          reference P *
            (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^ P.edges.card := by
      apply Finset.sum_le_sum
      intro P _
      have hlocal :=
        sum_fourEndpointHalfDeficitChoiceWeight_le_uniform
          n alpha hAlpha P rho hrho (hbase P)
      rw [sum_nearSkeletonChoiceWeight_eq_product] at hlocal
      simpa only [mul_comm] using
        mul_le_mul_right hlocal (reference P)

#print axioms nearCellTerm_le_threeQuarterCellBase_pow
#print axioms sum_fourEndpointHalfDeficitChoiceWeight_le_uniform
#print axioms sum_profileCanonicalHighSkeleton_le_uniformHalfDeficitSupportSum

end

end Erdos625
