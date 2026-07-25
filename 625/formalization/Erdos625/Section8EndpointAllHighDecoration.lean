import Erdos625.Section8EndpointBlockPairings
import Erdos625.Section8AllHighDeficitCellWeight
import Erdos625.Section8AllHighDeficitProductBound
import Mathlib.Tactic

/-!
# Section VIII: all-high decorations of one physical endpoint block pairing

For a fixed endpoint block pairing, every selected physical cell may retain its
full endpoint multiplicity or choose one nonzero deficit still above the global
high-cell cutoff. This module expresses that literal family as one
`NearSkeletonChoice` product and applies the generic uniform product theorem.

The only analytic input retained at the endpoint is the eventual smallness of
one explicit sum over the sixteen endpoint types.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Largest of the four endpoint sizes. -/
def fourEndpointLargestSize (alpha : Nat) (hAlpha : 5 < alpha) : Nat :=
  fourEndpointOverlapSize alpha hAlpha 0 0

/-- Every endpoint overlap size is at most the largest endpoint size. -/
theorem fourEndpointOverlapSize_le_largest
    (alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    fourEndpointOverlapSize alpha hAlpha i j ≤
      fourEndpointLargestSize alpha hAlpha := by
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointLargestSize, fourEndpointOverlapSize,
      fourEndpointSize, fourEndpointCoordinate, fourDeficitCoordinate,
      fourDeficit] <;> omega

/-- Once `alpha > 8`, all four endpoint sizes lie strictly above half the
largest endpoint size. -/
theorem fourEndpointOverlapSize_above_half_largest
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (i j : Fin 4) :
    fourEndpointLargestSize alpha hAlpha / 2 <
      fourEndpointOverlapSize alpha hAlpha i j := by
  fin_cases i <;> fin_cases j <;>
    simp [fourEndpointLargestSize, fourEndpointOverlapSize,
      fourEndpointSize, fourEndpointCoordinate, fourDeficitCoordinate,
      fourDeficit] <;> omega

/-- Global deficit type used for every selected endpoint cell. -/
abbrev FourEndpointDeficit (alpha : Nat) := Fin (alpha + 1)

/-- Allowed nonzero deficits for one selected physical endpoint cell. -/
def fourEndpointAllHighAllowed
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (cell : ↥P.1.edges) : Finset (FourEndpointDeficit alpha) :=
  let i := cell.1.1.1
  let j := cell.1.2.1
  let m := fourEndpointOverlapSize alpha hAlpha i j
  Finset.univ.filter fun deficit =>
    deficit.1 ∈ Finset.Icc 1
      (allHighDeficitCut (fourEndpointLargestSize alpha hAlpha) m)

/-- Literal charged local factor attached to one selected endpoint cell and one
candidate deficit. -/
def fourEndpointAllHighWeight
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (cell : ↥P.1.edges) (deficit : FourEndpointDeficit alpha) : ENNReal :=
  nearCellTerm n
    (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1)
    (Nat.dist cell.1.1.1.val cell.1.2.1.val) deficit.1

/-- Exact optional-deficit expansion over all distinguishable selected cells of
one physical endpoint block pairing. -/
theorem sum_fourEndpointAllHighChoiceWeight_eq_product
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L) :
    (∑ choice : NearSkeletonChoice (↥P.1.edges)
        (FourEndpointDeficit alpha)
        (fourEndpointAllHighAllowed alpha hAlpha P),
      nearSkeletonChoiceWeight
        (fourEndpointAllHighAllowed alpha hAlpha P)
        (fourEndpointAllHighWeight n alpha hAlpha P) choice) =
      ∏ cell : ↥P.1.edges,
        (1 + ∑ deficit ∈ fourEndpointAllHighAllowed alpha hAlpha P cell,
          fourEndpointAllHighWeight n alpha hAlpha P cell deficit) := by
  exact sum_nearSkeletonChoiceWeight_eq_product
    (fourEndpointAllHighAllowed alpha hAlpha P)
    (fourEndpointAllHighWeight n alpha hAlpha P)

/-- Uniform finite product bound for all literal high deficits decorating one
endpoint block pairing. The phase-dependent task is reduced to proving that
`rho ≤ 1` and that it dominates every local `allHighCellBase`. -/
theorem sum_fourEndpointAllHighChoiceWeight_le_uniform
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (rho : ENNReal) (hrho : rho ≤ 1)
    (hbase : ∀ cell : ↥P.1.edges,
      allHighCellBase n
        (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1) ≤ rho) :
    (∑ choice : NearSkeletonChoice (↥P.1.edges)
        (FourEndpointDeficit alpha)
        (fourEndpointAllHighAllowed alpha hAlpha P),
      nearSkeletonChoiceWeight
        (fourEndpointAllHighAllowed alpha hAlpha P)
        (fourEndpointAllHighWeight n alpha hAlpha P) choice) ≤
      (1 + ((alpha + 1 : Nat) : ENNReal) * rho) ^ P.1.edges.card := by
  classical
  apply sum_nearSkeletonChoiceWeight_le_uniform_pow
    (fourEndpointAllHighAllowed alpha hAlpha P)
    (fourEndpointAllHighWeight n alpha hAlpha P)
    (fun deficit => deficit.1) (alpha + 1) rho hrho
  · intro cell
    exact Finset.card_le_univ _
  · intro cell deficit hdeficit
    have hmem : deficit.1 ∈ Finset.Icc 1
        (allHighDeficitCut (fourEndpointLargestSize alpha hAlpha)
          (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1)) := by
      simpa only [fourEndpointAllHighAllowed, Finset.mem_filter,
        Finset.mem_univ, true_and] using hdeficit
    exact (Finset.mem_Icc.mp hmem).1
  · intro cell deficit hdeficit
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
    have hlocal := nearCellTerm_le_allHighCellBase_pow n m
      (Nat.dist i.val j.val) deficit.1 hhalf
    exact hlocal.trans (ENNReal.pow_le_pow_left (hbase cell))

/-- Explicit common base: the sum of the sixteen endpoint-type bases. -/
def fourEndpointAllHighRho
    (n alpha : Nat) (hAlpha : 5 < alpha) : ENNReal :=
  ∑ i : Fin 4, ∑ j : Fin 4,
    allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i j)

/-- Every endpoint-type base is bounded by the explicit sixteen-type sum. -/
theorem allHighCellBase_le_fourEndpointAllHighRho
    (n alpha : Nat) (hAlpha : 5 < alpha) (i j : Fin 4) :
    allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i j) ≤
      fourEndpointAllHighRho n alpha hAlpha := by
  have hrow :
      allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i j) ≤
        ∑ j' : Fin 4,
          allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i j') :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun j' : Fin 4 =>
        allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i j'))
      (fun _ _ => bot_le) (Finset.mem_univ j)
  have houter :
      (∑ j' : Fin 4,
          allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i j')) ≤
        ∑ i' : Fin 4, ∑ j' : Fin 4,
          allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i' j') :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun i' : Fin 4 => ∑ j' : Fin 4,
        allHighCellBase n (fourEndpointOverlapSize alpha hAlpha i' j'))
      (fun _ _ => bot_le) (Finset.mem_univ i)
  exact hrow.trans houter

/-- The physical decoration sum is controlled by the explicit sixteen-type
base; no pairing-dependent analytic hypothesis remains. -/
theorem sum_fourEndpointAllHighChoiceWeight_le_rho
    (n alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    {k : ColoringProfile (alpha + 1)} {L : FourEndpointFullTable}
    (P : FourEndpointBlockPairing alpha hAlpha k L)
    (hrho : fourEndpointAllHighRho n alpha hAlpha ≤ 1) :
    (∑ choice : NearSkeletonChoice (↥P.1.edges)
        (FourEndpointDeficit alpha)
        (fourEndpointAllHighAllowed alpha hAlpha P),
      nearSkeletonChoiceWeight
        (fourEndpointAllHighAllowed alpha hAlpha P)
        (fourEndpointAllHighWeight n alpha hAlpha P) choice) ≤
      (1 + ((alpha + 1 : Nat) : ENNReal) *
        fourEndpointAllHighRho n alpha hAlpha) ^ P.1.edges.card := by
  apply sum_fourEndpointAllHighChoiceWeight_le_uniform
    n alpha hAlpha hHigh P (fourEndpointAllHighRho n alpha hAlpha) hrho
  intro cell
  exact allHighCellBase_le_fourEndpointAllHighRho
    n alpha hAlpha cell.1.1.1 cell.1.2.1

#print axioms fourEndpointOverlapSize_le_largest
#print axioms fourEndpointOverlapSize_above_half_largest
#print axioms sum_fourEndpointAllHighChoiceWeight_eq_product
#print axioms sum_fourEndpointAllHighChoiceWeight_le_uniform
#print axioms allHighCellBase_le_fourEndpointAllHighRho
#print axioms sum_fourEndpointAllHighChoiceWeight_le_rho

end

end Erdos625
