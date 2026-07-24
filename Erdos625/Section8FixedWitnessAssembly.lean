import Erdos625.ConfigurationResidualCellConstraints
import Erdos625.UniformConditionalLaw

/-!
# Section VIII fixed-witness assembly

This module composes the accepted deterministic and finite-uniform pieces for
one fixed labelled prescribed-demand witness.  It packages:

* conditioning the ambient finite uniform law on the extension event;
* transport of the uniform extension law to the residual configuration space;
* the exact cell-count split `full = demand + residual`; and
* simultaneous transport of cell caps and "no additional pair" constraints.

It does **not** choose a canonical skeleton, prove uniqueness of an exposure,
or estimate the probability of any skeleton event.  Those are separate
Section VIII obligations.
-/

namespace Erdos625

open Set

noncomputable section

/-- The event that a full configuration matching extends one fixed labelled
prescribed-demand witness. -/
def fixedWitnessExtensionEvent
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Set (ConfigurationMatching row col) :=
  {matching | ExtendsPrescribedDemandWitness matching witness}

/-- The fixed-witness extension event is finite because the ambient matching
space is finite.  This explicit instance avoids making the event predicate's
decidability part of downstream theorem signatures. -/
noncomputable instance instFintypeFixedWitnessExtensionEvent
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    Fintype (fixedWitnessExtensionEvent witness) :=
  Fintype.ofFinite _

/-- The extension-event subtype is the domain of the accepted exact residual
configuration equivalence. -/
def fixedWitnessExtensionEquivResidual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) :
    fixedWitnessExtensionEvent witness ≃
      ConfigurationMatching (residualRowDegree witness)
        (residualColumnDegree witness) :=
  extensionsOfWitnessEquivResidualConfiguration witness

/-- Simultaneous constraints on full cells.  Every cell is capped, while the
cells selected by `noAdditional` must contain exactly the exposed demand and
therefore no additional matched pair. -/
def FixedWitnessFullCellConstraints
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (cap : A → B → ℕ) (noAdditional : A → B → Prop)
    (extension : fixedWitnessExtensionEvent witness) : Prop :=
  ∀ a b,
    configurationCellCount extension.1 a b ≤ cap a b ∧
      (noAdditional a b →
        configurationCellCount extension.1 a b = demand a b)

/-- The residual form of `FixedWitnessFullCellConstraints`: cell caps lose the
already exposed demand, and a no-additional-pair constraint becomes a zero
residual-cell constraint. -/
def FixedWitnessResidualCellConstraints
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (cap : A → B → ℕ) (noAdditional : A → B → Prop)
    (residual : ConfigurationMatching (residualRowDegree witness)
      (residualColumnDegree witness)) : Prop :=
  ∀ a b,
    configurationCellCount residual a b ≤ cap a b - demand a b ∧
      (noAdditional a b → configurationCellCount residual a b = 0)

/-- Conditioning the ambient uniform law on the fixed-witness extension event
is the pushforward of the uniform law on the extension subtype. -/
theorem uniform_filter_fixedWitnessExtensionEvent
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    [Nonempty (ConfigurationMatching row col)]
    [Nonempty (fixedWitnessExtensionEvent witness)] :
    (PMF.uniformOfFintype (ConfigurationMatching row col)).filter
        (fixedWitnessExtensionEvent witness)
        (uniformFilterWitness (fixedWitnessExtensionEvent witness)) =
      (PMF.uniformOfFintype
        (fixedWitnessExtensionEvent witness)).map Subtype.val := by
  exact uniform_filter_eq_uniformSubtype_map
    (fixedWitnessExtensionEvent witness)

/-- The uniform extension-subtype law pushes forward to the uniform law on
the degree-labelled residual configuration space. -/
theorem uniform_fixedWitnessExtension_map_residual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    [Nonempty (fixedWitnessExtensionEvent witness)]
    [Nonempty (ConfigurationMatching (residualRowDegree witness)
      (residualColumnDegree witness))] :
    (PMF.uniformOfFintype
        (fixedWitnessExtensionEvent witness)).map
        (fixedWitnessExtensionEquivResidual witness) =
      PMF.uniformOfFintype
        (ConfigurationMatching (residualRowDegree witness)
          (residualColumnDegree witness)) := by
  letI : Nonempty {matching : ConfigurationMatching row col //
      ExtendsPrescribedDemandWitness matching witness} := by
    let extension : fixedWitnessExtensionEvent witness :=
      Classical.choice inferInstance
    have hExtension := extension.2
    change ExtendsPrescribedDemandWitness extension.1 witness at hExtension
    exact ⟨⟨extension.1, hExtension⟩⟩
  exact uniform_extensionSubtype_map_residual witness

/-- All full-cell cap and no-additional-pair constraints transport through the
fixed-witness residual equivalence, simultaneously over every cell. -/
theorem fixedWitnessFullCellConstraints_iff_residual
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (cap : A → B → ℕ) (noAdditional : A → B → Prop)
    (hcap : ∀ a b, demand a b ≤ cap a b)
    (extension : fixedWitnessExtensionEvent witness) :
    FixedWitnessFullCellConstraints witness cap noAdditional extension ↔
      FixedWitnessResidualCellConstraints witness cap noAdditional
        (fixedWitnessExtensionEquivResidual witness extension) := by
  constructor
  · intro hFull a b
    have hCell := configurationCell_constraints_iff_residual
      witness extension a b (cap a b) (hcap a b)
    exact ⟨hCell.2.mp (hFull a b).1,
      fun hNoAdditional ↦ hCell.1.mp ((hFull a b).2 hNoAdditional)⟩
  · intro hResidual a b
    have hCell := configurationCell_constraints_iff_residual
      witness extension a b (cap a b) (hcap a b)
    exact ⟨hCell.2.mpr (hResidual a b).1,
      fun hNoAdditional ↦ hCell.1.mpr
        ((hResidual a b).2 hNoAdditional)⟩

/-- Fixed-witness Section VIII seam.  The conclusion contains only results
already justified for a fixed labelled witness.  In particular, it does not
assert that such a witness is canonical or that its event is likely. -/
theorem fixedWitnessSection8Assembly
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col)
    (cap : A → B → ℕ) (noAdditional : A → B → Prop)
    (hcap : ∀ a b, demand a b ≤ cap a b)
    [Nonempty (ConfigurationMatching row col)]
    [Nonempty (fixedWitnessExtensionEvent witness)]
    [Nonempty (ConfigurationMatching (residualRowDegree witness)
      (residualColumnDegree witness))] :
    ((PMF.uniformOfFintype (ConfigurationMatching row col)).filter
          (fixedWitnessExtensionEvent witness)
          (uniformFilterWitness (fixedWitnessExtensionEvent witness)) =
        (PMF.uniformOfFintype
          (fixedWitnessExtensionEvent witness)).map Subtype.val) ∧
      ((PMF.uniformOfFintype
          (fixedWitnessExtensionEvent witness)).map
          (fixedWitnessExtensionEquivResidual witness) =
        PMF.uniformOfFintype
          (ConfigurationMatching (residualRowDegree witness)
            (residualColumnDegree witness))) ∧
      (∀ extension a b,
        configurationCellCount extension.1 a b =
          demand a b +
            configurationCellCount
              (fixedWitnessExtensionEquivResidual witness extension) a b) ∧
      (∀ extension,
        FixedWitnessFullCellConstraints witness cap noAdditional extension ↔
          FixedWitnessResidualCellConstraints witness cap noAdditional
            (fixedWitnessExtensionEquivResidual witness extension)) := by
  refine ⟨uniform_filter_fixedWitnessExtensionEvent witness,
    uniform_fixedWitnessExtension_map_residual witness, ?_, ?_⟩
  · intro extension a b
    exact configurationCellCount_eq_demand_add_residual
      witness extension a b
  · intro extension
    exact fixedWitnessFullCellConstraints_iff_residual
      witness cap noAdditional hcap extension

end

end Erdos625
