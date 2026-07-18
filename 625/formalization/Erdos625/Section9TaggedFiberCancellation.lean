import Erdos625.Section8CanonicalDemandGlobalResidual
import Erdos625.Section8LabelledIncidence
import Erdos625.Section8ResidualDegreeTotal
import Erdos625.Section8WitnessDemandFeasibility
import Erdos625.Section8ResidualEventToSection9
import Erdos625.Section9FixedFFubiniBridge
import Mathlib.Tactic

/-!
# Section VIII--IX weighted tagged-fibre cancellation seam

For one attained canonical demand, the global uniform law on dependent
`demand/witness/residual` tags assigns every tagged state mass `1 / m!`.
The manuscript instead writes the same contribution as the labelled-witness
incidence `#witnesses / (m)_J` times an unnormalised residual numerator under
the uniform residual matching law.  The target theorem below is the exact
finite equality between those two presentations.

This theorem does not estimate either side and does not cancel or divide by
the cap/no-return event probability.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance instFintypeCanonicalResidualCellEventTaggedCancellation
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A -> B -> Nat} {row : A -> Nat} {col : B -> Nat}
    (witness : PrescribedDemandWitness demand row col) (U : Nat) :
    Fintype (canonicalResidualCellEvent witness U) :=
  Fintype.ofFinite _

/-- The literal residual attachment observable carried by one tagged state.
The residual configuration is already in the canonical cap/no-return subtype,
so no additional event indicator appears here. -/
def taggedResidualAttachmentValue
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat}
    (demand : A -> B -> Nat) (U : Nat)
    (witness : PrescribedDemandWitness demand row col)
    (residual : canonicalResidualCellEvent witness U) : ENNReal :=
  (Finset.univ.prod fun a : A =>
    Finset.univ.prod fun b : B =>
      (residualReward (configurationCellCount residual.1 a b) : ENNReal)) *
    ((actualResidualEvenEdgeSets
      (positiveDemandSupport demand) residual.1).card : ENNReal)

private theorem uniformSigmaCanonicalDemandResidual_apply_eq_factorial_inv
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (z : Sigma fun demand : canonicalDemandImage row col U =>
      Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
        canonicalResidualCellEvent witness U) :
    uniformSigmaCanonicalDemandResidual row col U htotal z =
      ((Finset.univ.sum row).factorial : ENNReal)⁻¹ := by
  unfold uniformSigmaCanonicalDemandResidual
  simp [PMF.uniformOfFintype_apply]
  have h_card : ∃ matching : ConfigurationMatching row col, True := by
    exact ⟨configurationMatchingEquiv row col htotal, trivial⟩
  obtain ⟨matching, _⟩ := h_card
  have hmap := uniformConfigurationMatching_map_sigmaCanonicalDemandResidual
    row col U htotal
  replace hmap := congr_arg
    (fun p => p
      (configurationMatchingEquivSigmaCanonicalDemandResidual row col U matching))
    hmap
  simp [uniformSigmaCanonicalDemandResidual] at hmap
  unfold uniformConfigurationMatching at hmap
  simp at hmap
  rw [← hmap, card_configurationMatching row col htotal]

private theorem sum_taggedResidualAttachmentValue_fiber
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A -> Nat} {col : B -> Nat} (U : Nat)
    (demand : A -> B -> Nat)
    (witness0 : PrescribedDemandWitness demand row col) :
    (Finset.univ.sum fun z :
      Sigma fun witness : PrescribedDemandWitness demand row col =>
        canonicalResidualCellEvent witness U =>
      taggedResidualAttachmentValue demand U z.1 z.2) =
      (Fintype.card (PrescribedDemandWitness demand row col) : ENNReal) *
        (Finset.univ.sum fun residual : canonicalResidualCellEvent witness0 U =>
          taggedResidualAttachmentValue demand U witness0 residual) := by
  rw [Fintype.sum_sigma]
  change (∑ _witness : PrescribedDemandWitness demand row col,
      ∑ residual : canonicalResidualCellEvent witness0 U,
        taggedResidualAttachmentValue demand U witness0 residual) = _
  simp

private theorem residualActualAttachmentNumerator_eq_factorial_inv_mul_sum
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A -> B -> Nat} {row : A -> Nat} {col : B -> Nat}
    (witness : PrescribedDemandWitness demand row col) (U : Nat)
    (hres : Finset.univ.sum (residualRowDegree witness) =
      Finset.univ.sum (residualColumnDegree witness)) :
    residualActualAttachmentNumerator
        (positiveDemandSupport demand) (U / 2)
        (residualRowDegree witness) (residualColumnDegree witness) hres =
      ((Finset.univ.sum (residualRowDegree witness)).factorial : ENNReal)⁻¹ *
        (Finset.univ.sum fun residual : canonicalResidualCellEvent witness U =>
          taggedResidualAttachmentValue demand U witness residual) := by
  classical
  unfold residualActualAttachmentNumerator uniformConfigurationMatching
  simp only [PMF.uniformOfFintype_apply]
  rw [card_configurationMatching _ _ hres]
  let weight := fun matching : ConfigurationMatching
      (residualRowDegree witness) (residualColumnDegree witness) =>
    (Finset.univ.prod fun a : A =>
      Finset.univ.prod fun b : B =>
        (residualReward (configurationCellCount matching a b) : ENNReal)) *
      ((actualResidualEvenEdgeSets
        (positiveDemandSupport demand) matching).card : ENNReal)
  calc
    _ = ((Finset.univ.sum (residualRowDegree witness)).factorial : ENNReal)⁻¹ *
        ∑ matching, if matching ∈ ResidualCapNoReturnEvent
          (positiveDemandSupport demand) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness)
          then weight matching else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro matching _
      by_cases hmatching : matching ∈ ResidualCapNoReturnEvent
        (positiveDemandSupport demand) (U / 2)
        (residualRowDegree witness) (residualColumnDegree witness)
      · simp [hmatching, weight, mul_assoc]
      · simp [hmatching]
    _ = _ := by
      congr 1
      unfold taggedResidualAttachmentValue weight
      convert (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset (ConfigurationMatching
            (residualRowDegree witness) (residualColumnDegree witness))))
          (f := fun matching =>
            (Finset.univ.prod fun a : A =>
              Finset.univ.prod fun b : B =>
                (residualReward
                  (configurationCellCount matching a b) : ENNReal)) *
              ((actualResidualEvenEdgeSets
                (positiveDemandSupport demand) matching).card : ENNReal))
          (p := fun matching => matching ∈ ResidualCapNoReturnEvent
            (positiveDemandSupport demand) (U / 2)
            (residualRowDegree witness) (residualColumnDegree witness))).symm using 1
      · rw [Finset.sum_filter]
      ·
        refine' Finset.sum_bij ( fun x _ => ⟨ x.1, by
          grind +suggestions ⟩ ) _ _ _ _ <;> simp +decide;
        grind +suggestions

/-- Exact per-demand factorial cancellation and weighted tagged-law
integration.  The left side is the contribution of one attained demand fibre
inside the global dependent uniform law.  The right side is precisely its
labelled-witness incidence times the unnormalised residual attachment
numerator used by Section IX.
-/
theorem sum_taggedResidualAttachmentValue_eq_incidence_mul_numerator
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (demand : canonicalDemandImage row col U)
    (witness0 : PrescribedDemandWitness demand.1 row col) :
    (Finset.univ.sum fun z :
      Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
        canonicalResidualCellEvent witness U =>
      uniformSigmaCanonicalDemandResidual row col U htotal
          ⟨demand, z⟩ *
        taggedResidualAttachmentValue demand.1 U z.1 z.2) =
      labelledWitnessIncidence demand.1 row col *
        residualActualAttachmentNumerator
          (positiveDemandSupport demand.1) (U / 2)
          (residualRowDegree witness0) (residualColumnDegree witness0)
          (sum_residualRowDegree_eq_sum_residualColumnDegree
            htotal witness0) := by
  convert congr_arg _ ( sum_taggedResidualAttachmentValue_fiber U demand.1 witness0 ) using 1;
  rotate_right;
  use fun x => x * ( ( Finset.univ.sum row |> Nat.factorial ) : ENNReal ) ⁻¹;
  · rw [ Finset.sum_mul _ _ _ ];
    refine' Finset.sum_congr rfl fun x hx => _;
    rw [ mul_comm, uniformSigmaCanonicalDemandResidual_apply_eq_factorial_inv ];
  · rw [ residualActualAttachmentNumerator_eq_factorial_inv_mul_sum ];
    unfold labelledWitnessIncidence;
    rw [ show ( Finset.univ.sum ( residualRowDegree witness0 ) ) = Finset.univ.sum row - totalDemand ( demand : A → B → ℕ ) from sum_residualRowDegree_eq_rowTotal_sub_totalDemand witness0 ];
    rw [ Nat.descFactorial_eq_factorial_mul_choose ];
    rw [ ← Nat.choose_mul_factorial_mul_factorial ( show totalDemand ( demand : A → B → ℕ ) ≤ Finset.univ.sum row from totalDemand_le_rowTotal_of_witness witness0 ) ] ; ring;
    simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
    simp +decide [ ← mul_assoc, ENNReal.mul_inv ];
    rw [ ENNReal.mul_inv, ENNReal.mul_inv ] ; ring;
    · exact Or.inr ( ENNReal.natCast_ne_top _ );
    · exact Or.inl ENNReal.coe_ne_top;
    · exact Or.inr ( ENNReal.natCast_ne_top _ );
    · exact Or.inl ENNReal.coe_ne_top

end

end Erdos625
