import Erdos625.OrderedSignedProfileSemantics
import Erdos625.ProfileOverlapCanonicalTable
import Erdos625.ProfileOverlapFibrationRegrouping
import Erdos625.Section6SignedSecondMomentFubini
import Erdos625.Section6SignedJointMass
import Erdos625.Section6SignedSecondMomentPackage
import Erdos625.Section6SignedExpectationDenominator
import Erdos625.Section6SignedOverlapRewardReindex
import Erdos625.SignedProfileSemanticLift
import Mathlib.Tactic

/-!
# Section VI: assembly of the signed second-moment identity

This module is the integration point for the exact finite ingredients of
Lemma 6.1.  It keeps the row-independent overlap-table law in `ENNReal`,
where the graph-level first and second moments already live, and records the
denominator-free identities before using the feasible ordered row to cancel
the first-moment square.

The final semantic quotient/reindexing lemma is deliberately factored into
small named statements below, so that every remaining interface between the
unordered graph-level witness count and the ordered overlap-table model is
visible in the dependency graph.
-/

namespace Erdos625

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The row-independent probability of a canonical profile-overlap table,
measured by the literal fixed-margin fibre based at `row₀`.  The denominator
is nonzero because `row₀` itself is an ordered profile partition. -/
def profileOverlapTableProbabilityENNReal
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (table : ProfileOverlapTable n k) : ENNReal :=
  (Fintype.card ((profileOverlapTableEquivBounded row₀ table).event row₀.1
      (profileBlockMargin k)) : ENNReal) /
    (Fintype.card (OrderedProfilePartition n k) : ENNReal)

/-- The canonical `ENNReal` right-hand side of the normalized signed
second-moment identity. -/
def signedProfileSecondMomentTableSumENNReal
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) : ENNReal :=
  ∑ table : ProfileOverlapTable n k,
    profileOverlapTableProbabilityENNReal row₀ table *
      (signedOverlapReward table.tableNat : ENNReal)

/-- The total signed pair mass of two unordered profile partitions, with all
Boolean signs summed out. -/
def signedProfilePairMassTotal
    {b : Nat} (n : Nat) {k : ColoringProfile b} : ENNReal :=
  ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
    signedProfilePairMassSum n P Q

/-- The corresponding unordered sum of exact signed-overlap rewards. -/
def unorderedSignedOverlapRewardSum
    {b n : Nat} {k : ColoringProfile b} : ENNReal :=
  ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
    (signedOverlapReward
      (fun A B => P.overlapCellCount Q A B) : ENNReal)

/-- The canonical ordered-pair sum of exact signed-overlap rewards. -/
def orderedSignedOverlapRewardSum
    {b n : Nat} {k : ColoringProfile b} : ENNReal :=
  ∑ row : OrderedProfilePartition n k, ∑ column : OrderedProfilePartition n k,
    (signedOverlapReward
      (profileOverlapTableOfOrderedPair row column).tableNat : ENNReal)

/-- The reward of an ordered pair is exactly the reward of the two kernel
profile partitions obtained by forgetting the ordered slot names. -/
theorem signedOverlapReward_orderedPair_eq_kernelPair
    {b n : Nat} {k : ColoringProfile b}
    (row column : OrderedProfilePartition n k) :
    signedOverlapReward
        (profileOverlapTableOfOrderedPair row column).tableNat =
      signedOverlapReward
        (fun A B =>
          (orderedSlotProfilePartition row).overlapCellCount
            (orderedSlotProfilePartition column) A B) := by
  let eRow := orderedSlotEquivKernelParts row
  let eColumn := orderedSlotEquivKernelParts column
  let r : ProfileBlockIndex k → ProfileBlockIndex k → Nat :=
    fun q s => orderedOverlapCount row.1 column.1 q s
  have hmatrix : reindexOverlapMatrix eRow eColumn r =
      fun A B =>
        (orderedSlotProfilePartition row).overlapCellCount
          (orderedSlotProfilePartition column) A B := by
    funext A B
    have hrowPart : orderedSlotPart row (eRow.symm A) = A := by
      dsimp [eRow]
      rw [← orderedSlotEquivKernelParts_apply]
      exact (orderedSlotEquivKernelParts row).apply_symm_apply A
    have hcolumnPart : orderedSlotPart column (eColumn.symm B) = B := by
      dsimp [eColumn]
      rw [← orderedSlotEquivKernelParts_apply]
      exact (orderedSlotEquivKernelParts column).apply_symm_apply B
    have h := orderedOverlapCount_eq_profileOverlapCellCount row column
      (eRow.symm A) (eColumn.symm B)
    simpa [reindexOverlapMatrix, r, eRow, eColumn, hrowPart, hcolumnPart] using h
  have hr : r = (profileOverlapTableOfOrderedPair row column).tableNat := by
    funext q s
    exact (profileOverlapTableOfOrderedPair_tableNat row column q s).symm
  have hreindex := signedOverlapReward_reindex eRow eColumn r
  rw [hr] at hreindex
  have hmatrix' : reindexOverlapMatrix eRow eColumn
      (profileOverlapTableOfOrderedPair row column).tableNat =
      fun A B =>
        (orderedSlotProfilePartition row).overlapCellCount
          (orderedSlotProfilePartition column) A B := by
    rw [← hr]
    exact hmatrix
  rw [hmatrix'] at hreindex
  exact hreindex

/-- The Fubini expansion is exactly the sum of sign-summed pair masses after
regrouping the two sigma indices by their underlying profile partitions. -/
theorem signedProfileSecondMoment_eq_signedProfilePairMassTotal
    {b n : Nat} (k : ColoringProfile b) :
    signedProfileSecondMoment n k = signedProfilePairMassTotal n (k := k) := by
  classical
  rw [signedProfileSecondMoment_eq_sum_pairEvent]
  unfold signedProfilePairMassTotal signedProfilePairMassSum
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro P hP
  rw [Finset.sum_comm]
  -- The two names for a fixed pair event are definitionally the same.
  simp only [signedProfileWitnessPairIntersection, signedProfilePairEvent]

/-- Clearing the common one-witness edge-probability denominator from the
graph-level second moment leaves the unordered overlap-reward sum. -/
theorem signedProfileSecondMoment_mul_two_pow_forbiddenEdges
    {b n : Nat} (k : ColoringProfile b) :
    signedProfileSecondMoment n k *
        (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
      (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) *
        unorderedSignedOverlapRewardSum (n := n) (k := k) := by
  classical
  rw [signedProfileSecondMoment_eq_signedProfilePairMassTotal]
  unfold signedProfilePairMassTotal unorderedSignedOverlapRewardSum
  calc
    (∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
        signedProfilePairMassSum n P Q) *
        (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
      ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
        signedProfilePairMassSum n P Q *
          (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro P hP
        rw [Finset.sum_mul]
    _ = ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
        (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) *
          (signedOverlapReward
            (fun A B => P.overlapCellCount Q A B) : ENNReal) := by
        apply Finset.sum_congr rfl
        intro P hP
        apply Finset.sum_congr rfl
        intro Q hQ
        exact signedProfilePairMassSum_mul_two_pow_forbiddenEdges P Q
    _ = (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) *
        ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
          (signedOverlapReward
            (fun A B => P.overlapCellCount Q A B) : ENNReal) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P hP
        rw [Finset.mul_sum]

/-- The elementary reciprocal cancellation used to clear the common
one-witness edge probability. -/
private theorem half_pow_mul_two_pow (m : Nat) :
    (1 / 2 : ENNReal) ^ m * (2 : ENNReal) ^ m = 1 := by
  rw [← mul_pow, ENNReal.div_eq_inv_mul, mul_one,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]

/-- Clearing the one-witness edge-probability denominator from the exact
signed first moment. -/
theorem signedProfileExpectation_mul_two_pow_forbiddenEdges
    {b n : Nat} (k : ColoringProfile b) :
    signedProfileExpectation n k *
        (2 : ENNReal) ^ ColoringProfile.forbiddenEdges k =
      (2 : ENNReal) ^ ColoringProfile.partCount k *
        (Nat.card (ProfilePartition n k) : ENNReal) := by
  rw [signedProfileExpectation_eq, profileColoringExpectation_eq_card_mul]
  calc
    ((2 : ENNReal) ^ ColoringProfile.partCount k *
        ((Nat.card (ProfilePartition n k) : ENNReal) *
          (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k)) *
        (2 : ENNReal) ^ ColoringProfile.forbiddenEdges k =
      (2 : ENNReal) ^ ColoringProfile.partCount k *
        ((Nat.card (ProfilePartition n k) : ENNReal) *
          ((1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k *
            (2 : ENNReal) ^ ColoringProfile.forbiddenEdges k)) := by
        ac_rfl
    _ = (2 : ENNReal) ^ ColoringProfile.partCount k *
        (Nat.card (ProfilePartition n k) : ENNReal) := by
        rw [half_pow_mul_two_pow, mul_one]

/-- Squared version of the exact first-moment denominator clearing. -/
theorem signedProfileExpectation_sq_mul_two_pow_twice_forbiddenEdges
    {b n : Nat} (k : ColoringProfile b) :
    signedProfileExpectation n k ^ 2 *
        (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
      (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) *
        (Nat.card (ProfilePartition n k) : ENNReal) ^ 2 := by
  have h := congrArg (fun x : ENNReal => x ^ 2)
    (signedProfileExpectation_mul_two_pow_forbiddenEdges (n := n) k)
  have hforbidden :
      (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
        ((2 : ENNReal) ^ ColoringProfile.forbiddenEdges k) ^ 2 := by
    calc
      (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
          (2 : ENNReal) ^ (ColoringProfile.forbiddenEdges k * 2) := by
            rw [Nat.mul_comm]
      _ = ((2 : ENNReal) ^ ColoringProfile.forbiddenEdges k) ^ 2 :=
        pow_mul _ _ _
  have hparts :
      ((2 : ENNReal) ^ ColoringProfile.partCount k) ^ 2 =
        (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) := by
    calc
      ((2 : ENNReal) ^ ColoringProfile.partCount k) ^ 2 =
          (2 : ENNReal) ^ (ColoringProfile.partCount k * 2) :=
        (pow_mul _ _ _).symm
      _ = (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) := by
        rw [Nat.mul_comm]
  calc
    signedProfileExpectation n k ^ 2 *
        (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k) =
      (signedProfileExpectation n k *
        (2 : ENNReal) ^ ColoringProfile.forbiddenEdges k) ^ 2 := by
        rw [hforbidden, mul_pow]
    _ = ((2 : ENNReal) ^ ColoringProfile.partCount k *
        (Nat.card (ProfilePartition n k) : ENNReal)) ^ 2 := h
    _ = (2 : ENNReal) ^ (2 * ColoringProfile.partCount k) *
        (Nat.card (ProfilePartition n k) : ENNReal) ^ 2 := by
        rw [mul_pow, hparts]

/-- The fibre-cardinality numerator in the canonical table law.  Naming it
separately makes the exact final quotient interface readable. -/
def profileOverlapTableFibreCard
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (table : ProfileOverlapTable n k) : Nat :=
  Fintype.card ((profileOverlapTableEquivBounded row₀ table).event row₀.1
    (profileBlockMargin k))

/-- The unnormalised canonical reward numerator: a table reward weighted by
the exact cardinality of its literal overlap fibre. -/
def canonicalSignedOverlapRewardNumerator
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) : ENNReal :=
  ∑ table : ProfileOverlapTable n k,
    (profileOverlapTableFibreCard row₀ table : ENNReal) *
      (signedOverlapReward table.tableNat : ENNReal)

/-- The cardinality of a canonical overlap-table fibre is independent of the
chosen ordered row.  This is a finite multinomial statement, not an
exchangeability assumption: both rows have exactly the prescribed slot
margins, and the common product of cell factorials is cancellable in `Nat`. -/
theorem profileOverlapTableFibreCard_invariant
    {b n : Nat} {k : ColoringProfile b}
    (row row' : OrderedProfilePartition n k)
    (table : ProfileOverlapTable n k) :
    profileOverlapTableFibreCard row table =
      profileOverlapTableFibreCard row' table := by
  classical
  let F : Nat := ∏ a : ProfileBlockIndex k, ∏ b : ProfileBlockIndex k,
    (table.tableNat a b).factorial
  have hF : F ≠ 0 := by
    unfold F
    exact Finset.prod_ne_zero_iff.mpr fun a ha =>
      Finset.prod_ne_zero_iff.mpr fun b hb => Nat.factorial_ne_zero _
  have hrow : ∀ a : ProfileBlockIndex k,
      ∑ b : ProfileBlockIndex k, table.tableNat a b =
        labelingFiberCount row.1 a := by
    intro a
    calc
      ∑ b : ProfileBlockIndex k, table.tableNat a b = profileBlockMargin k a :=
        table.tableNat_rowMargin a
      _ = labelingFiberCount row.1 a := (row.2 a).symm
  have hrow' : ∀ a : ProfileBlockIndex k,
      ∑ b : ProfileBlockIndex k, table.tableNat a b =
        labelingFiberCount row'.1 a := by
    intro a
    calc
      ∑ b : ProfileBlockIndex k, table.tableNat a b = profileBlockMargin k a :=
        table.tableNat_rowMargin a
      _ = labelingFiberCount row'.1 a := (row'.2 a).symm
  have hrowCount :=
    card_orderedOverlapLabeling_mul_factorials row.1 table.tableNat hrow
  have hrowCount' :=
    card_orderedOverlapLabeling_mul_factorials row'.1 table.tableNat hrow'
  have hrowEvent :
      profileOverlapTableFibreCard row table =
        Fintype.card (OrderedOverlapLabeling row.1 table.tableNat) := by
    unfold profileOverlapTableFibreCard
    exact card_fixedMarginOverlapEvent row.1 table.tableNat
      (profileBlockMargin k) table.columnMargin
  have hrowEvent' :
      profileOverlapTableFibreCard row' table =
        Fintype.card (OrderedOverlapLabeling row'.1 table.tableNat) := by
    unfold profileOverlapTableFibreCard
    exact card_fixedMarginOverlapEvent row'.1 table.tableNat
      (profileBlockMargin k) table.columnMargin
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hF)
  rw [hrowEvent, hrowEvent']
  calc
    Fintype.card (OrderedOverlapLabeling row.1 table.tableNat) * F =
        ∏ a : ProfileBlockIndex k, (profileBlockMargin k a).factorial := by
      simpa only [F] using hrowCount.trans (by
        apply Finset.prod_congr rfl
        intro a ha
        rw [row.2 a])
    _ = Fintype.card (OrderedOverlapLabeling row'.1 table.tableNat) * F := by
      symm
      simpa only [F] using hrowCount'.trans (by
        apply Finset.prod_congr rfl
        intro a ha
        rw [row'.2 a])

/-- The literal fibre-weighted canonical reward numerator is independent of
which feasible ordered row is used as its base. -/
theorem canonicalSignedOverlapRewardNumerator_invariant
    {b n : Nat} {k : ColoringProfile b}
    (row row' : OrderedProfilePartition n k) :
    canonicalSignedOverlapRewardNumerator row =
      canonicalSignedOverlapRewardNumerator row' := by
  unfold canonicalSignedOverlapRewardNumerator
  apply Finset.sum_congr rfl
  intro table htable
  rw [profileOverlapTableFibreCard_invariant row row' table]

/-- The complete ordered-pair reward sum is the number of ordered base rows
times the canonical fibre-weighted reward numerator. -/
theorem orderedSignedOverlapRewardSum_eq_card_mul_numerator
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    orderedSignedOverlapRewardSum (n := n) (k := k) =
      (Fintype.card (OrderedProfilePartition n k) : ENNReal) *
        canonicalSignedOverlapRewardNumerator row₀ := by
  classical
  unfold orderedSignedOverlapRewardSum
  calc
    (∑ row : OrderedProfilePartition n k,
      ∑ column : OrderedProfilePartition n k,
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair row column).tableNat : ENNReal)) =
      ∑ row : OrderedProfilePartition n k,
        canonicalSignedOverlapRewardNumerator row := by
      apply Finset.sum_congr rfl
      intro row hrow
      unfold canonicalSignedOverlapRewardNumerator profileOverlapTableFibreCard
      have h :=
        sum_weight_profileOverlapTableOfOrderedPair_eq_sum_card_nsmul
          (R := ENNReal) row
          (fun table : ProfileOverlapTable n k =>
            (signedOverlapReward table.tableNat : ENNReal))
      simpa only [nsmul_eq_mul] using h
    _ = ∑ _row : OrderedProfilePartition n k,
        canonicalSignedOverlapRewardNumerator row₀ := by
      apply Finset.sum_congr rfl
      intro row hrow
      exact canonicalSignedOverlapRewardNumerator_invariant row row₀
    _ = (Fintype.card (OrderedProfilePartition n k) : ENNReal) *
        canonicalSignedOverlapRewardNumerator row₀ := by
      simp [nsmul_eq_mul]

/-- Semantic reindexing of both ordered profile partitions turns the ordered
reward sum into the unordered reward sum times the square of the constant
block-label multiplier.  This is the ordered/unordered quotient cancellation
in its explicit finite-sum form. -/
theorem orderedSignedOverlapRewardSum_eq_labelMultiplier_sq_mul_unordered
    {b n : Nat} (k : ColoringProfile b) :
    orderedSignedOverlapRewardSum (n := n) (k := k) =
      (profileBlockLabelMultiplier k : ENNReal) ^ 2 *
        unorderedSignedOverlapRewardSum (n := n) (k := k) := by
  classical
  let e := labeledProfilePartitionEquivOrderedSemantic (n := n) k
  have hreward (x y : LabeledProfilePartition n k) :
      (signedOverlapReward
        (profileOverlapTableOfOrderedPair (e x) (e y)).tableNat : ENNReal) =
      (signedOverlapReward
        (fun A B => x.1.overlapCellCount y.1 A B) : ENNReal) := by
    change (signedOverlapReward
      (profileOverlapTableOfOrderedPair
        (labeledProfilePartitionToOrdered x)
        (labeledProfilePartitionToOrdered y)).tableNat : ENNReal) = _
    rw [signedOverlapReward_orderedPair_eq_kernelPair,
      orderedSlotProfilePartition_labeledProfilePartitionToOrdered,
      orderedSlotProfilePartition_labeledProfilePartitionToOrdered]
  calc
    orderedSignedOverlapRewardSum (n := n) (k := k) =
      ∑ x : LabeledProfilePartition n k,
        ∑ column : OrderedProfilePartition n k,
          (signedOverlapReward
            (profileOverlapTableOfOrderedPair (e x) column).tableNat : ENNReal) := by
      unfold orderedSignedOverlapRewardSum
      exact (Equiv.sum_comp e fun row =>
        ∑ column : OrderedProfilePartition n k,
          (signedOverlapReward
            (profileOverlapTableOfOrderedPair row column).tableNat : ENNReal)).symm
    _ = ∑ x : LabeledProfilePartition n k,
        ∑ y : LabeledProfilePartition n k,
          (signedOverlapReward
            (profileOverlapTableOfOrderedPair (e x) (e y)).tableNat : ENNReal) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Equiv.sum_comp e fun column =>
        (signedOverlapReward
          (profileOverlapTableOfOrderedPair (e x) column).tableNat : ENNReal)).symm
    _ = ∑ x : LabeledProfilePartition n k,
        ∑ y : LabeledProfilePartition n k,
          (signedOverlapReward
            (fun A B => x.1.overlapCellCount y.1 A B) : ENNReal) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact hreward x y
    _ = ∑ P : ProfilePartition n k, ∑ dx : ProfileBlockLabeling P,
        ∑ Q : ProfilePartition n k, ∑ dy : ProfileBlockLabeling Q,
          (signedOverlapReward
            (fun A B => P.overlapCellCount Q A B) : ENNReal) := by
      rw [Fintype.sum_sigma]
      simp_rw [Fintype.sum_sigma]
    _ = ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
        ∑ _dx : ProfileBlockLabeling P, ∑ _dy : ProfileBlockLabeling Q,
          (signedOverlapReward
            (fun A B => P.overlapCellCount Q A B) : ENNReal) := by
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.sum_comm]
    _ = ∑ P : ProfilePartition n k, ∑ Q : ProfilePartition n k,
        (profileBlockLabelMultiplier k : ENNReal) ^ 2 *
          (signedOverlapReward
            (fun A B => P.overlapCellCount Q A B) : ENNReal) := by
      apply Finset.sum_congr rfl
      intro P hP
      apply Finset.sum_congr rfl
      intro Q hQ
      let r : ENNReal := (signedOverlapReward
        (fun A B => P.overlapCellCount Q A B) : ENNReal)
      calc
        (∑ _dx : ProfileBlockLabeling P, ∑ _dy : ProfileBlockLabeling Q, r) =
          (Fintype.card (ProfileBlockLabeling P) : ENNReal) *
            ((Fintype.card (ProfileBlockLabeling Q) : ENNReal) * r) := by
              simp [nsmul_eq_mul]
        _ = (profileBlockLabelMultiplier k : ENNReal) ^ 2 * r := by
              rw [card_profileBlockLabeling P, card_profileBlockLabeling Q,
                pow_two]
              ac_rfl
    _ = (profileBlockLabelMultiplier k : ENNReal) ^ 2 *
        unorderedSignedOverlapRewardSum (n := n) (k := k) := by
      unfold unorderedSignedOverlapRewardSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.mul_sum]

/-- The finite quotient identity transporting the unordered profile-pair
reward sum to the ordered canonical table model.  It is purely a finite
reindexing assertion: the left side counts the possible ordered base rows,
while the right side counts two unordered profile partitions.  No random-graph
probability occurs in this interface. -/
def SignedOverlapQuotientBridge
    {b n : Nat} (k : ColoringProfile b)
    (row₀ : OrderedProfilePartition n k) : Prop :=
  (Fintype.card (OrderedProfilePartition n k) : ENNReal) *
      unorderedSignedOverlapRewardSum (n := n) (k := k) =
    (Nat.card (ProfilePartition n k) : ENNReal) ^ 2 *
      canonicalSignedOverlapRewardNumerator row₀

/-- The finite ordered/unordered quotient bridge.  The two independently
computed descriptions of the ordered reward sum differ only by the square of
the constant block-label multiplier; cancelling one copy converts the
ordered-row cardinality into the unordered-partition cardinality. -/
theorem signedOverlapQuotientBridge
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    SignedOverlapQuotientBridge (n := n) k row₀ := by
  let O : ENNReal := Fintype.card (OrderedProfilePartition n k)
  let U : ENNReal := unorderedSignedOverlapRewardSum (n := n) (k := k)
  let N : ENNReal := Nat.card (ProfilePartition n k)
  let M : ENNReal := profileBlockLabelMultiplier k
  let R : ENNReal := canonicalSignedOverlapRewardNumerator row₀
  have hMnat : profileBlockLabelMultiplier k ≠ 0 := by
    unfold profileBlockLabelMultiplier
    exact Finset.prod_ne_zero_iff.mpr fun s hs => Nat.factorial_ne_zero _
  have hM0 : M ≠ 0 := by
    dsimp [M]
    exact Nat.cast_ne_zero.mpr hMnat
  have hMtop : M ≠ ∞ := by
    dsimp [M]
    exact ENNReal.natCast_ne_top _
  have hordered : O * R = M ^ 2 * U := by
    calc
      O * R = orderedSignedOverlapRewardSum (n := n) (k := k) := by
        simpa only [O, R] using
          (orderedSignedOverlapRewardSum_eq_card_mul_numerator row₀).symm
      _ = M ^ 2 * U := by
        simpa only [M, U] using
          orderedSignedOverlapRewardSum_eq_labelMultiplier_sq_mul_unordered
            (n := n) k
  have hcardNat :
      Fintype.card (OrderedProfilePartition n k) =
        Fintype.card (ProfilePartition n k) * profileBlockLabelMultiplier k := by
    calc
      Fintype.card (OrderedProfilePartition n k) =
          Fintype.card (LabeledProfilePartition n k) :=
        (Fintype.card_congr
          (labeledProfilePartitionEquivOrderedSemantic (n := n) k)).symm
      _ = Fintype.card (ProfilePartition n k) *
          profileBlockLabelMultiplier k := card_labeledProfilePartition k
  have hcard : O = N * M := by
    have h := congrArg (fun z : Nat => (z : ENNReal)) hcardNat
    simpa only [O, N, M, Nat.card_eq_fintype_card, Nat.cast_mul] using h
  have hNR : N * R = M * U := by
    calc
      N * R = M⁻¹ * (M * (N * R)) := by
        symm
        exact ENNReal.inv_mul_cancel_left hM0 hMtop
      _ = M⁻¹ * ((N * M) * R) := by
        congr 1
        ac_rfl
      _ = M⁻¹ * (O * R) := by rw [← hcard]
      _ = M⁻¹ * (M ^ 2 * U) := by rw [hordered]
      _ = M⁻¹ * (M * (M * U)) := by
        rw [pow_two]
        ac_rfl
      _ = (M⁻¹ * M) * (M * U) := by ac_rfl
      _ = M * U := by
        rw [ENNReal.inv_mul_cancel hM0 hMtop, one_mul]
  change O * U = N ^ 2 * R
  calc
    O * U = (N * M) * U := by rw [hcard]
    _ = N * (M * U) := by ac_rfl
    _ = N * (N * R) := by rw [hNR]
    _ = N ^ 2 * R := by
      rw [pow_two]
      ac_rfl

/-- The finite ordered-profile sample space is nonempty as soon as the
displayed base row is available. -/
theorem orderedProfilePartition_card_ne_zero
    {b n : Nat} {k : ColoringProfile b}
  (row₀ : OrderedProfilePartition n k) :
    (Fintype.card (OrderedProfilePartition n k) : ENNReal) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr
    (Fintype.card_pos_iff.mpr ⟨row₀⟩).ne'

/-- The finite ordered-profile sample-space cardinality is never infinite. -/
theorem orderedProfilePartition_card_ne_top
    {b n : Nat} (k : ColoringProfile b) :
    (Fintype.card (OrderedProfilePartition n k) : ENNReal) ≠ ∞ :=
  ENNReal.natCast_ne_top _

/-- The canonical overlap fibres partition the ordered-column sample space.
This is the natural-number denominator identity behind the probability law. -/
theorem card_orderedProfilePartition_eq_sum_profileOverlapTableFibreCard
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    Fintype.card (OrderedProfilePartition n k) =
      ∑ table : ProfileOverlapTable n k,
        profileOverlapTableFibreCard row₀ table := by
  classical
  have h :=
    sum_weight_profileOverlapTableOfOrderedPair_eq_sum_card_nsmul
      (R := Nat) row₀ (fun _ : ProfileOverlapTable n k => 1)
  simpa [profileOverlapTableFibreCard] using h

/-- The canonical table weights are a probability mass function whenever an
ordered row exists. -/
theorem sum_profileOverlapTableProbabilityENNReal_eq_one
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    ∑ table : ProfileOverlapTable n k,
      profileOverlapTableProbabilityENNReal row₀ table = 1 := by
  classical
  let N : ENNReal := Fintype.card (OrderedProfilePartition n k)
  change (∑ table : ProfileOverlapTable n k,
    (profileOverlapTableFibreCard row₀ table : ENNReal) / N) = 1
  calc
    (∑ table : ProfileOverlapTable n k,
      (profileOverlapTableFibreCard row₀ table : ENNReal) / N) =
        ((∑ table : ProfileOverlapTable n k,
          profileOverlapTableFibreCard row₀ table : Nat) : ENNReal) / N := by
      calc
        (∑ table : ProfileOverlapTable n k,
          (profileOverlapTableFibreCard row₀ table : ENNReal) / N) =
            ∑ table : ProfileOverlapTable n k,
              N⁻¹ * (profileOverlapTableFibreCard row₀ table : ENNReal) := by
              apply Finset.sum_congr rfl
              intro table htable
              rw [ENNReal.div_eq_inv_mul]
        _ = N⁻¹ * ∑ table : ProfileOverlapTable n k,
            (profileOverlapTableFibreCard row₀ table : ENNReal) := by
              rw [Finset.mul_sum]
        _ = N⁻¹ * ((∑ table : ProfileOverlapTable n k,
            profileOverlapTableFibreCard row₀ table : Nat) : ENNReal) := by
              rw [Nat.cast_sum]
        _ = ((∑ table : ProfileOverlapTable n k,
            profileOverlapTableFibreCard row₀ table : Nat) : ENNReal) / N := by
              rw [ENNReal.div_eq_inv_mul]
    _ = (Fintype.card (OrderedProfilePartition n k) : ENNReal) / N := by
      rw [card_orderedProfilePartition_eq_sum_profileOverlapTableFibreCard row₀]
    _ = 1 := by
      change N / N = 1
      exact ENNReal.div_self
        (orderedProfilePartition_card_ne_zero row₀)
        (orderedProfilePartition_card_ne_top k)

/-- Table regrouping in its normalized `ENNReal` form: an average over all
ordered columns equals the canonical table sum weighted by the literal
fixed-margin overlap law. -/
theorem orderedSignedOverlapRewardAverage_eq_tableSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    (∑ column : OrderedProfilePartition n k,
      (signedOverlapReward
        (profileOverlapTableOfOrderedPair row₀ column).tableNat : ENNReal)) /
      (Fintype.card (OrderedProfilePartition n k) : ENNReal) =
      signedProfileSecondMomentTableSumENNReal row₀ := by
  classical
  unfold signedProfileSecondMomentTableSumENNReal
    profileOverlapTableProbabilityENNReal
  have h :=
    sum_weight_profileOverlapTableOfOrderedPair_eq_sum_card_nsmul
      (R := ENNReal) row₀
      (fun table : ProfileOverlapTable n k =>
        (signedOverlapReward table.tableNat : ENNReal))
  rw [h]
  simp only [nsmul_eq_mul]
  rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro table htable
  rw [ENNReal.div_eq_inv_mul]
  simp only [mul_left_comm, mul_comm]

/-- The normalized canonical table sum is the unnormalised reward numerator
divided by the ordered fixed-margin sample-space size. -/
theorem signedProfileSecondMomentTableSumENNReal_eq_numerator_div
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    signedProfileSecondMomentTableSumENNReal row₀ =
      canonicalSignedOverlapRewardNumerator row₀ /
        (Fintype.card (OrderedProfilePartition n k) : ENNReal) := by
  classical
  unfold signedProfileSecondMomentTableSumENNReal
    profileOverlapTableProbabilityENNReal
    canonicalSignedOverlapRewardNumerator profileOverlapTableFibreCard
  rw [ENNReal.div_eq_inv_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro table htable
  rw [ENNReal.div_eq_inv_mul]
  exact mul_assoc _ _ _

/-- Multiplying the normalized canonical table sum by the nonzero finite
ordered sample-space cardinality recovers the literal fibre numerator. -/
theorem orderedProfilePartition_card_mul_tableSumENNReal
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    (Fintype.card (OrderedProfilePartition n k) : ENNReal) *
        signedProfileSecondMomentTableSumENNReal row₀ =
      canonicalSignedOverlapRewardNumerator row₀ := by
  rw [signedProfileSecondMomentTableSumENNReal_eq_numerator_div]
  exact ENNReal.mul_div_cancel
    (orderedProfilePartition_card_ne_zero row₀)
    (orderedProfilePartition_card_ne_top k)

/-- The denominator-free integration interface between the graph-level pair
mass and the canonical ordered-table model.  It states the exact equality
consumed by the safe final division step, with no probability heuristic. -/
def SignedProfileSecondMomentTableBridge
    {b n : Nat} (k : ColoringProfile b)
    (row₀ : OrderedProfilePartition n k) : Prop :=
  (Fintype.card (OrderedProfilePartition n k) : ENNReal) *
      signedProfileSecondMoment n k =
    signedProfileExpectation n k ^ 2 *
      canonicalSignedOverlapRewardNumerator row₀

/-- All probabilistic and denominator algebra in the final identity is now
mechanical.  The only input here is the finite semantic quotient bridge that
transports the unordered overlap-reward sum into the ordered canonical table
model. -/
theorem signedProfileSecondMomentTableBridge_of_overlapQuotientBridge
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (hquot : SignedOverlapQuotientBridge (n := n) k row₀) :
    SignedProfileSecondMomentTableBridge (n := n) k row₀ := by
  let O : ENNReal := Fintype.card (OrderedProfilePartition n k)
  let U : ENNReal := unorderedSignedOverlapRewardSum (n := n) (k := k)
  let N : ENNReal := Nat.card (ProfilePartition n k)
  let R : ENNReal := canonicalSignedOverlapRewardNumerator row₀
  let X : ENNReal := signedProfileSecondMoment n k
  let D : ENNReal := signedProfileExpectation n k ^ 2
  let C : ENNReal := (2 : ENNReal) ^ (2 * ColoringProfile.forbiddenEdges k)
  let A : ENNReal := (2 : ENNReal) ^ (2 * ColoringProfile.partCount k)
  have hC0 : C ≠ 0 := by
    dsimp [C]
    exact ENNReal.pow_ne_zero (by norm_num) _
  have hCtop : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.pow_ne_top (by norm_num)
  have hsecond : X * C = A * U := by
    simpa only [X, C, A, U] using
      signedProfileSecondMoment_mul_two_pow_forbiddenEdges (n := n) k
  have hfirst : D * C = A * N ^ 2 := by
    simpa only [D, C, A, N] using
      signedProfileExpectation_sq_mul_two_pow_twice_forbiddenEdges (n := n) k
  have hfinite : O * U = N ^ 2 * R := by
    simpa only [SignedOverlapQuotientBridge, O, U, N, R] using hquot
  change O * X = D * R
  calc
    O * X = C⁻¹ * (C * (O * X)) := by
      symm
      exact ENNReal.inv_mul_cancel_left hC0 hCtop
    _ = C⁻¹ * (O * (X * C)) := by
      congr 1
      ac_rfl
    _ = C⁻¹ * (O * (A * U)) := by rw [hsecond]
    _ = C⁻¹ * (A * (O * U)) := by
      congr 1
      ac_rfl
    _ = C⁻¹ * (A * (N ^ 2 * R)) := by rw [hfinite]
    _ = C⁻¹ * ((A * N ^ 2) * R) := by
      congr 1
      ac_rfl
    _ = C⁻¹ * ((D * C) * R) := by rw [hfirst]
    _ = (C⁻¹ * C) * (D * R) := by ac_rfl
    _ = D * R := by rw [ENNReal.inv_mul_cancel hC0 hCtop, one_mul]

/-- Safe final cancellation: once the exact finite semantic/table bridge has
been established, the normalized graph-level identity follows with no
divide-by-zero convention. -/
theorem normalizedSignedProfileSecondMoment_eq_tableSum_of_bridge
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (hbridge : SignedProfileSecondMomentTableBridge (n := n) k row₀) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 =
      signedProfileSecondMomentTableSumENNReal row₀ := by
  let N : ENNReal := Fintype.card (OrderedProfilePartition n k)
  let D : ENNReal := signedProfileExpectation n k ^ 2
  let T : ENNReal := signedProfileSecondMomentTableSumENNReal row₀
  let R : ENNReal := canonicalSignedOverlapRewardNumerator row₀
  have hN0 : N ≠ 0 := by
    simpa only [N] using orderedProfilePartition_card_ne_zero row₀
  have hNtop : N ≠ ∞ := by
    simpa only [N] using orderedProfilePartition_card_ne_top k
  have hNR : N * T = R := by
    simpa only [N, T, R] using orderedProfilePartition_card_mul_tableSumENNReal row₀
  have hcross : N * signedProfileSecondMoment n k = D * R := by
    simpa only [SignedProfileSecondMomentTableBridge, N, D, R] using hbridge
  have hdenominatorFree : signedProfileSecondMoment n k = D * T := by
    calc
      signedProfileSecondMoment n k = N⁻¹ *
          (N * signedProfileSecondMoment n k) := by
            symm
            exact ENNReal.inv_mul_cancel_left hN0 hNtop
      _ = N⁻¹ * (D * R) := by rw [hcross]
      _ = N⁻¹ * (D * (N * T)) := by rw [hNR]
      _ = (N⁻¹ * N) * (D * T) := by ac_rfl
      _ = D * T := by rw [ENNReal.inv_mul_cancel hN0 hNtop, one_mul]
  exact normalized_eq_of_eq_signedProfileExpectation_sq_mul row₀
    (by simpa only [D, T] using hdenominatorFree)

/-- The unconditional exact signed second-moment identity.  The right hand
side is the row-independent fixed-margin overlap-table law, and every
ordered/unordered semantic multiplier has been cancelled in the preceding
finite quotient bridge. -/
theorem normalizedSignedProfileSecondMoment_eq_tableSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 =
      signedProfileSecondMomentTableSumENNReal row₀ := by
  apply normalizedSignedProfileSecondMoment_eq_tableSum_of_bridge row₀
  exact signedProfileSecondMomentTableBridge_of_overlapQuotientBridge row₀
    (signedOverlapQuotientBridge row₀)

/-- Fully expanded form of the normalized identity: the probability of a
table is its literal fixed-margin fibre cardinality divided by the finite
ordered-profile sample-space cardinality. -/
theorem normalizedSignedProfileSecondMoment_eq_profileOverlapTableSum
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 =
      ∑ table : ProfileOverlapTable n k,
        profileOverlapTableProbabilityENNReal row₀ table *
          (signedOverlapReward table.tableNat : ENNReal) := by
  simpa only [signedProfileSecondMomentTableSumENNReal] using
    normalizedSignedProfileSecondMoment_eq_tableSum row₀

#print axioms signedProfileSecondMoment_eq_signedProfilePairMassTotal
#print axioms signedProfileSecondMoment_mul_two_pow_forbiddenEdges
#print axioms card_orderedProfilePartition_eq_sum_profileOverlapTableFibreCard
#print axioms sum_profileOverlapTableProbabilityENNReal_eq_one
#print axioms orderedSignedOverlapRewardAverage_eq_tableSum
#print axioms signedProfileSecondMomentTableSumENNReal_eq_numerator_div
#print axioms orderedProfilePartition_card_mul_tableSumENNReal
#print axioms normalizedSignedProfileSecondMoment_eq_tableSum_of_bridge
#print axioms signedOverlapReward_orderedPair_eq_kernelPair
#print axioms orderedSignedOverlapRewardSum_eq_labelMultiplier_sq_mul_unordered
#print axioms signedOverlapQuotientBridge
#print axioms normalizedSignedProfileSecondMoment_eq_tableSum
#print axioms normalizedSignedProfileSecondMoment_eq_profileOverlapTableSum

end

end Erdos625
