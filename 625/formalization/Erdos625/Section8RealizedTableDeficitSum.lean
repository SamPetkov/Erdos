import Erdos625.Section8DirectHalfDeficitAssembly
import Erdos625.Section8EncodedFullSupportCharge
import Erdos625.Section8EndpointThreeQuarterDeficitSum
import Erdos625.Section8WeightedReferenceRegrouping

/-!
# Section VIII: realized-table deficit sum

This module sums the encoded full-support comparison over attained canonical
high skeletons, controls each positive half-deficit fibre by the three-quarter
geometric estimate, and preserves the resulting endpoint-table product through
the exact weighted realized-table regrouping.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

private theorem sum_halfDeficitWeight_le_two_threeQuarterHighCellBase
    (n alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (cell : ↥P.edges)
    (hsmall : threeQuarterHighCellBase n
      (fourEndpointOverlapSize alpha hAlpha
        cell.1.1.1 cell.1.2.1) ≤ (1 / 2 : ENNReal)) :
    (∑ deficit ∈ fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
      fourEndpointHalfDeficitWeight n alpha hAlpha P cell deficit) ≤
        2 * threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1) := by
  calc
    (∑ deficit ∈ fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
        fourEndpointHalfDeficitWeight n alpha hAlpha P cell deficit) ≤
      ∑ deficit ∈ fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
        threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1) ^ deficit.1 := by
      apply Finset.sum_le_sum
      intro deficit hdeficit
      have hmem : 0 < deficit.1 ∧
          2 * deficit.1 < fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1 := by
        simpa only [fourEndpointHalfDeficitAllowed, Finset.mem_filter,
          Finset.mem_univ, true_and] using hdeficit
      exact nearCellTerm_le_threeQuarterHighCellBase_pow n
        (fourEndpointOverlapSize alpha hAlpha cell.1.1.1 cell.1.2.1)
        (Nat.dist cell.1.1.1.val cell.1.2.1.val) deficit.1 hmem.2
    _ ≤ 2 * threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha
            cell.1.1.1 cell.1.2.1) := by
      apply sum_fin_pow_le_two_mul_of_pos_of_le_half
      · intro deficit hdeficit
        have hmem : 0 < deficit.1 ∧
            2 * deficit.1 < fourEndpointOverlapSize alpha hAlpha
              cell.1.1.1 cell.1.2.1 := by
          simpa only [fourEndpointHalfDeficitAllowed, Finset.mem_filter,
            Finset.mem_univ, true_and] using hdeficit
        exact hmem.1
      · exact hsmall

private theorem prod_over_support_eq_typeTable
    (alpha : Nat) (hAlpha : 5 < alpha)
    {k : ColoringProfile (alpha + 1)}
    (P : FourEndpointAbstractBlockSkeleton alpha hAlpha k)
    (f : Fin 4 → Fin 4 → ENNReal) :
    (∏ e : ↥P.edges, f e.1.1.1 e.1.2.1) =
      ∏ i : Fin 4, ∏ j : Fin 4, (f i j) ^ P.typeTable i j := by
  classical
  rw [← Finset.prod_subtype P.edges (fun _ => Iff.rfl)
    (fun e => f e.1.1 e.2.1)]
  rw [← Finset.prod_fiberwise' P.edges
    (fun e => (e.1.1, e.2.1))
    (fun ij : Fin 4 × Fin 4 => f ij.1 ij.2)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_const]
  apply congrArg (fun count => (f i j) ^ count)
  calc
    (P.edges.filter (fun e => (e.1.1, e.2.1) = (i, j))).card =
        (P.edges.filter (fun e => e.1.1 = i ∧ e.2.1 = j)).card := by
      congr 1
      ext e
      simp [Prod.ext_iff]
    _ = P.typeTable i j := rfl

theorem sum_profileHighSkeletonWeight_le_realizedTableThreeQuarterProduct
    (alpha : Nat) (hAlpha : 5 < alpha) (hHigh : 8 < alpha)
    (k : ColoringProfile (alpha + 1))
    (hcover : IsFourEndpointProfileCover alpha hAlpha k)
    (slotIndex : FourEndpointSlotIndexing alpha hAlpha k)
    (hsmall : ∀ i j : Fin 4,
      threeQuarterHighCellBase
          (Finset.univ.sum (profileBlockMargin k))
          (fourEndpointOverlapSize alpha hAlpha i j) ≤
        (1 / 2 : ENNReal)) :
    (∑ demand : ProfileCanonicalHighSkeleton k
        (fourEndpointLargestSize alpha hAlpha),
      profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand) ≤
      ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
        fourEndpointW
            (Finset.univ.sum (profileBlockMargin k))
            alpha hAlpha k L.1 *
          ∏ i : Fin 4, ∏ j : Fin 4,
            (1 + 2 * threeQuarterHighCellBase
              (Finset.univ.sum (profileBlockMargin k))
              (fourEndpointOverlapSize alpha hAlpha i j)) ^
                L.1.toFun i j := by
  classical
  let n : Nat := Finset.univ.sum (profileBlockMargin k)
  let tableWeight : FourEndpointFullTable → ENNReal := fun L =>
    ∏ i : Fin 4, ∏ j : Fin 4,
      (1 + 2 * threeQuarterHighCellBase n
        (fourEndpointOverlapSize alpha hAlpha i j)) ^ L.toFun i j
  calc
    (∑ demand : ProfileCanonicalHighSkeleton k
        (fourEndpointLargestSize alpha hAlpha),
      profileHighSkeletonWeight k
        (fourEndpointLargestSize alpha hAlpha) demand) ≤
      ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
          ∏ cell : ↥P.edges,
            (1 + ∑ deficit ∈
              fourEndpointHalfDeficitAllowed alpha hAlpha P cell,
              fourEndpointHalfDeficitWeight n alpha hAlpha P cell deficit) := by
      apply sum_profileCanonicalHighSkeleton_le_directSupportChoiceProduct
        n alpha hAlpha k hcover slotIndex
      intro demand
      exact profileHighSkeletonWeight_le_fourEndpointEncodedFullSupportCharge
        alpha hAlpha hHigh k hcover slotIndex demand
    _ ≤ ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
          ∏ cell : ↥P.edges,
            (1 + 2 * threeQuarterHighCellBase n
              (fourEndpointOverlapSize alpha hAlpha
                cell.1.1.1 cell.1.2.1)) := by
      apply Finset.sum_le_sum
      intro P _
      apply mul_le_mul_right
      apply Finset.prod_le_prod
      · intro cell _
        exact bot_le
      · intro cell _
        simpa [add_comm] using add_le_add_left
          (sum_halfDeficitWeight_le_two_threeQuarterHighCellBase
            n alpha hAlpha P cell (hsmall cell.1.1.1 cell.1.2.1)) 1
    _ = ∑ P : FourEndpointAbstractBlockSkeleton alpha hAlpha k,
        fourEndpointFullSupportReferenceWeight n alpha hAlpha P *
          tableWeight (fourEndpointSupportTable alpha hAlpha P) := by
      apply Finset.sum_congr rfl
      intro P _
      apply congrArg (fun x => fourEndpointFullSupportReferenceWeight
        n alpha hAlpha P * x)
      unfold tableWeight
      exact prod_over_support_eq_typeTable alpha hAlpha P
        (fun i j => 1 + 2 * threeQuarterHighCellBase n
          (fourEndpointOverlapSize alpha hAlpha i j))
    _ = ∑ L : ↥(fourEndpointRealizedFullTables alpha hAlpha k),
        fourEndpointW n alpha hAlpha k L.1 * tableWeight L.1 :=
      sum_fourEndpointFullSupportReferenceWeight_mul_tableWeight_eq_sum_realized_W_mul_tableWeight
        n alpha hAlpha k tableWeight
    _ = _ := rfl

end

end Erdos625
