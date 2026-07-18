import Erdos625.ConfigurationModelCellMarginals
import Erdos625.ConfigurationModelProbability
import Erdos625.ProfileOverlapFibrationRegrouping
import Erdos625.UniformEquivTransport
import Erdos625.UniformSigmaTransport
import Mathlib.Tactic

/-!
# The profile-overlap/configuration-model bridge

Fixing an ordered profile row identifies its vertices with the row stubs of
the bipartite configuration model.  A configuration matching then gives a
second fixed-margin profile labeling, together with an ordering of every one
of its column fibres.  This file makes that finite equivalence explicit.

The extra fibre orderings are essential: they are exactly the constant
``\prod_b m_b!`` multiplicity which turns a uniform configuration matching
into the uniform fixed-fibre labeling law after the column orders are
forgotten.  The cell matrix of the matching is proved equal to the literal
overlap table, so the resulting expectation transport is semantic rather
than a cardinality-only identification.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## Stub coordinates induced by a fixed row -/

/-- A fixed ordered profile row has a chosen, finite ordering of each of its
block fibres.  The choice is used only to identify vertices with labelled row
stubs; all statements below are independent of that auxiliary ordering. -/
noncomputable def profileRowFiberOrder
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (a : ProfileBlockIndex k) :
    {v : Fin n // row₀.1 v = a} ≃ Fin (profileBlockMargin k a) :=
  Fintype.equivOfCardEq (by
    rw [card_labelingFiber]
    simpa using row₀.2 a)

/-- The vertex-to-row-stub equivalence determined by the chosen fibre
orders.  Its first coordinate is exactly the fixed row label. -/
noncomputable def profileRowToStubEquiv
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    Fin n ≃ RowStub (profileBlockMargin k) :=
  sigmaEquivOfFiberOrders (profileBlockMargin k) row₀.1
    (profileRowFiberOrder row₀)

@[simp] theorem profileRowToStubEquiv_fst
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (v : Fin n) :
    (profileRowToStubEquiv row₀ v).1 = row₀.1 v := by
  simp [profileRowToStubEquiv]

/-- Restrict the vertex-to-row-stub equivalence to a single row block.  This
is the canonical fibre equivalence used below, so no dependent cast of a
stub index is hidden in the cell-table comparison. -/
noncomputable def profileRowFiberToStubEquiv
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (a : ProfileBlockIndex k) :
    {v : Fin n // row₀.1 v = a} ≃ Fin (profileBlockMargin k a) :=
  ((profileRowToStubEquiv row₀).subtypeEquiv (fun v => by
      rw [profileRowToStubEquiv_fst])).trans (Equiv.sigmaSubtype a)

/-- The ordering data above a fixed-margin column labeling.  This is the
constant fibre that records which labelled column stub is attached to each
vertex in a column block. -/
abbrev ProfileColumnFiberOrders
    {b n : Nat} {k : ColoringProfile b}
    (column : OrderedProfilePartition n k) :=
  ∀ q : ProfileBlockIndex k,
    {v : Fin n // column.1 v = q} ≃ Fin (profileBlockMargin k q)

/-- Turn a profile column labeling and its fibre orders into its labelled
column-stub coordinate system. -/
noncomputable def profileColumnToStubEquiv
    {b n : Nat} {k : ColoringProfile b}
    (column : OrderedProfilePartition n k)
    (orders : ProfileColumnFiberOrders column) :
    Fin n ≃ ColumnStub (profileBlockMargin k) :=
  sigmaEquivOfFiberOrders (profileBlockMargin k) column.1 orders

@[simp] theorem profileColumnToStubEquiv_fst
    {b n : Nat} {k : ColoringProfile b}
    (column : OrderedProfilePartition n k)
    (orders : ProfileColumnFiberOrders column) (v : Fin n) :
    (profileColumnToStubEquiv column orders v).1 = column.1 v := by
  simp [profileColumnToStubEquiv]

/-! ## The constant-fibre lift -/

/-- A configuration matching, after fixing row-stub coordinates, is exactly
a vertex-to-column-stub equivalence. -/
noncomputable def configurationMatchingToVertexColumnStubEquiv
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    ConfigurationMatching (profileBlockMargin k) (profileBlockMargin k) ≃
      (Fin n ≃ ColumnStub (profileBlockMargin k)) where
  toFun matching := (profileRowToStubEquiv row₀).trans matching
  invFun columnStubs := (profileRowToStubEquiv row₀).symm.trans columnStubs
  left_inv matching := by
    apply Equiv.ext
    intro stub
    simp
  right_inv columnStubs := by
    apply Equiv.ext
    intro v
    simp

/-- Explicitly lift a configuration matching to its induced fixed-margin
column labeling and a labelled ordering of every column fibre. -/
noncomputable def configurationMatchingEquivColumnWithOrders
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    ConfigurationMatching (profileBlockMargin k) (profileBlockMargin k) ≃
      Σ column : OrderedProfilePartition n k, ProfileColumnFiberOrders column :=
  (configurationMatchingToVertexColumnStubEquiv row₀).trans
    (fixedFiberLabelingWithOrdersEquiv (profileBlockMargin k))

/-- Forget the column-stub orders associated to a configuration matching. -/
noncomputable def orderedProfileColumnOfConfigurationMatching
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (matching : ConfigurationMatching (profileBlockMargin k)
      (profileBlockMargin k)) : OrderedProfilePartition n k :=
  (configurationMatchingEquivColumnWithOrders row₀ matching).1

/-- The column-stub orders carried by the canonical lift of a matching. -/
noncomputable def configurationMatchingColumnOrders
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (matching : ConfigurationMatching (profileBlockMargin k)
      (profileBlockMargin k)) :
    ProfileColumnFiberOrders
      (orderedProfileColumnOfConfigurationMatching row₀ matching) :=
  (configurationMatchingEquivColumnWithOrders row₀ matching).2

/-- Reconstruct a matching from a fixed-margin column labeling and the
ordering of each of its column fibres. -/
noncomputable def configurationMatchingOfColumnWithOrders
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (data : Σ column : OrderedProfilePartition n k, ProfileColumnFiberOrders column) :
    ConfigurationMatching (profileBlockMargin k) (profileBlockMargin k) :=
  (configurationMatchingEquivColumnWithOrders row₀).symm data

/-- Evaluation of the reconstructed matching has the expected vertex-level
description: first recover the vertex from its row stub, then read its
labelled column stub. -/
@[simp] theorem configurationMatchingOfColumnWithOrders_apply_stub
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (column : OrderedProfilePartition n k)
    (orders : ProfileColumnFiberOrders column)
    (a : ProfileBlockIndex k) (stub : Fin (profileBlockMargin k a)) :
    configurationMatchingOfColumnWithOrders row₀ ⟨column, orders⟩ ⟨a, stub⟩ =
      profileColumnToStubEquiv column orders
        ((profileRowFiberToStubEquiv row₀ a).symm stub).1 := by
  change ((profileRowToStubEquiv row₀).symm.trans
      (profileColumnToStubEquiv column orders)) ⟨a, stub⟩ = _
  simp [profileRowFiberToStubEquiv]
  rfl

@[simp] theorem configurationMatchingOfColumnWithOrders_apply
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (data : Σ column : OrderedProfilePartition n k, ProfileColumnFiberOrders column) :
    configurationMatchingEquivColumnWithOrders row₀
      (configurationMatchingOfColumnWithOrders row₀ data) = data := by
  exact (configurationMatchingEquivColumnWithOrders row₀).apply_symm_apply data

/-- A configuration matching is recovered exactly from its induced column
labeling and the remembered column-stub orders. -/
@[simp] theorem configurationMatching_reconstruct
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (matching : ConfigurationMatching (profileBlockMargin k)
      (profileBlockMargin k)) :
    configurationMatchingOfColumnWithOrders row₀
      ⟨orderedProfileColumnOfConfigurationMatching row₀ matching,
        configurationMatchingColumnOrders row₀ matching⟩ = matching := by
  exact (configurationMatchingEquivColumnWithOrders row₀).symm_apply_apply matching

/-! ## Literal agreement of cell matrices -/

/-- The cell count in a configuration matching is the cardinality of the
corresponding subtype of row stubs. -/
private theorem configurationCellCount_eq_card_subtype
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {row : A → Nat} {col : B → Nat}
    (matching : ConfigurationMatching row col) (a : A) (b : B) :
    configurationCellCount matching a b =
      Fintype.card {stub : Fin (row a) // (matching ⟨a, stub⟩).1 = b} := by
  rw [Fintype.card_subtype]
  rfl

/-- The overlap count of two literal vertex labelings is the cardinality of
the subtype of vertices in the indicated matrix cell. -/
private theorem orderedOverlapCount_eq_card_subtype
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {n : Nat} (row : Fin n → A) (column : Fin n → B) (a : A) (b : B) :
    orderedOverlapCount row column a b =
      Fintype.card {v : Fin n // row v = a ∧ column v = b} := by
  rw [Fintype.card_subtype]
  rfl

/-- For a column labeling with chosen stub orders, the configuration cell
matrix agrees entrywise with the literal vertex-overlap matrix. -/
theorem configurationCellCount_ofColumnWithOrders_eq_orderedOverlapCount
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (column : OrderedProfilePartition n k)
    (orders : ProfileColumnFiberOrders column)
    (a q : ProfileBlockIndex k) :
    configurationCellCount
        (configurationMatchingOfColumnWithOrders row₀ ⟨column, orders⟩) a q =
      orderedOverlapCount row₀.1 column.1 a q := by
  classical
  let eRow : Fin (profileBlockMargin k a) ≃
      {v : Fin n // row₀.1 v = a} :=
    (profileRowFiberToStubEquiv row₀ a).symm
  let eCell :
      {stub : Fin (profileBlockMargin k a) //
        (configurationMatchingOfColumnWithOrders row₀ ⟨column, orders⟩
          ⟨a, stub⟩).1 = q} ≃
        {v : {v : Fin n // row₀.1 v = a} // column.1 v.1 = q} :=
    eRow.subtypeEquiv (fun stub => by
      rw [configurationMatchingOfColumnWithOrders_apply_stub]
      simp [eRow])
  let eAnd :
      {v : {v : Fin n // row₀.1 v = a} // column.1 v.1 = q} ≃
        {v : Fin n // row₀.1 v = a ∧ column.1 v = q} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun v : Fin n => row₀.1 v = a) (fun v => column.1 v = q)
  let toVertex := eCell.trans eAnd
  rw [configurationCellCount_eq_card_subtype,
    orderedOverlapCount_eq_card_subtype]
  exact Fintype.card_congr toVertex

/-- The canonical profile overlap table read from a configuration matching. -/
noncomputable def profileOverlapTableOfConfigurationMatching
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (matching : ConfigurationMatching (profileBlockMargin k)
      (profileBlockMargin k)) : ProfileOverlapTable n k :=
  profileOverlapTableOfOrderedPair row₀
    (orderedProfileColumnOfConfigurationMatching row₀ matching)

/-- The table carried by a configuration matching is its actual cell-count
matrix, not merely an equinumerous contingency table. -/
theorem profileOverlapTableOfConfigurationMatching_tableNat_eq_cellCount
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (matching : ConfigurationMatching (profileBlockMargin k)
      (profileBlockMargin k)) (a q : ProfileBlockIndex k) :
    (profileOverlapTableOfConfigurationMatching row₀ matching).tableNat a q =
      configurationCellCount matching a q := by
  let column := orderedProfileColumnOfConfigurationMatching row₀ matching
  let orders := configurationMatchingColumnOrders row₀ matching
  have hreconstruct := configurationMatching_reconstruct row₀ matching
  change orderedOverlapCount row₀.1 column.1 a q = configurationCellCount matching a q
  rw [← hreconstruct]
  exact (configurationCellCount_ofColumnWithOrders_eq_orderedOverlapCount
    row₀ column orders a q).symm

/-! ## Constant fibre cardinality and uniform-law transport -/

/-- The number of possible orderings of the fibres of any fixed-margin
profile column is independent of that column. -/
theorem card_profileColumnFiberOrders
    {b n : Nat} {k : ColoringProfile b}
    (column : OrderedProfilePartition n k) :
    Fintype.card (ProfileColumnFiberOrders column) =
      ∏ q : ProfileBlockIndex k, (profileBlockMargin k q).factorial := by
  classical
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro q _
  let e : {v : Fin n // column.1 v = q} ≃ Fin (profileBlockMargin k q) :=
    Fintype.equivOfCardEq (by
      rw [card_labelingFiber]
      simpa using column.2 q)
  calc
    Fintype.card ({v : Fin n // column.1 v = q} ≃
        Fin (profileBlockMargin k q)) =
        (Fintype.card {v : Fin n // column.1 v = q}).factorial :=
      Fintype.card_equiv e
    _ = (profileBlockMargin k q).factorial := by
      rw [Fintype.card_congr e, Fintype.card_fin]

/-- The total number of lifted columns is the number of ordinary columns
times the constant product of within-column stub permutations. -/
theorem card_sigma_profileColumnFiberOrders
    {b n : Nat} {k : ColoringProfile b} :
    Fintype.card (Σ column : OrderedProfilePartition n k,
      ProfileColumnFiberOrders column) =
      Fintype.card (OrderedProfilePartition n k) *
        ∏ q : ProfileBlockIndex k, (profileBlockMargin k q).factorial := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [card_profileColumnFiberOrders]
  simp [Finset.sum_const]

/-- The fixed profile row witnesses the equal-total-degree condition needed
by the configuration-model PMF. -/
theorem profileBlockMargin_total_eq_self
    {b n : Nat} {k : ColoringProfile b}
    (_row₀ : OrderedProfilePartition n k) :
    (Finset.univ.sum (profileBlockMargin k)) =
      Finset.univ.sum (profileBlockMargin k) := rfl

/-- The uniform distribution on ordered profile partitions, with the
nonemptiness witness supplied by the fixed row. -/
noncomputable def uniformOrderedProfilePartition
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    PMF (OrderedProfilePartition n k) := by
  letI : Nonempty (OrderedProfilePartition n k) := ⟨row₀⟩
  exact PMF.uniformOfFintype _

/-- Uniform configuration matching, after forgetting the constant number of
column-stub orderings, is exactly the uniform fixed-fibre profile-column law.

This is a PMF equality, hence it is stronger than equality of table-event
cardinalities. -/
theorem uniformConfigurationMatching_map_orderedProfileColumn
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    (uniformConfigurationMatching (profileBlockMargin k) (profileBlockMargin k)
      (profileBlockMargin_total_eq_self row₀)).map
        (orderedProfileColumnOfConfigurationMatching row₀) =
      uniformOrderedProfilePartition row₀ := by
  classical
  let m := profileBlockMargin k
  let E := configurationMatchingEquivColumnWithOrders row₀
  let K : Nat := ∏ q : ProfileBlockIndex k, (m q).factorial
  letI : Nonempty (OrderedProfilePartition n k) := ⟨row₀⟩
  letI : Nonempty (ConfigurationMatching m m) :=
    ⟨configurationMatchingEquiv m m (profileBlockMargin_total_eq_self row₀)⟩
  let matching₀ : ConfigurationMatching m m :=
    configurationMatchingEquiv m m (profileBlockMargin_total_eq_self row₀)
  letI : Nonempty (Σ column : OrderedProfilePartition n k,
      ProfileColumnFiberOrders column) := ⟨E matching₀⟩
  have hE :
      (PMF.uniformOfFintype (ConfigurationMatching m m)).map E =
        PMF.uniformOfFintype
          (Σ column : OrderedProfilePartition n k, ProfileColumnFiberOrders column) :=
    uniformOfFintype_map_equiv E
  have hcardFiber : ∀ column : OrderedProfilePartition n k,
      Fintype.card (ProfileColumnFiberOrders column) = K := by
    intro column
    exact card_profileColumnFiberOrders column
  have hcardSigma :
      Fintype.card (Σ column : OrderedProfilePartition n k,
        ProfileColumnFiberOrders column) =
        Fintype.card (OrderedProfilePartition n k) * K := by
    exact card_sigma_profileColumnFiberOrders
  ext column
  have hmapComp := PMF.map_comp
    (p := PMF.uniformOfFintype (ConfigurationMatching m m))
    (f := E) (g := fun z : Σ column : OrderedProfilePartition n k,
      ProfileColumnFiberOrders column => z.1)
  change
    ((PMF.uniformOfFintype (ConfigurationMatching m m)).map
        (orderedProfileColumnOfConfigurationMatching row₀)) column = _
  rw [show orderedProfileColumnOfConfigurationMatching row₀ =
      (fun z : Σ column : OrderedProfilePartition n k,
        ProfileColumnFiberOrders column => z.1) ∘ E by rfl]
  rw [← hmapComp, hE, uniformOfFintype_sigma_map_fst_apply]
  change _ = (PMF.uniformOfFintype (OrderedProfilePartition n k)) column
  rw [PMF.uniformOfFintype_apply]
  rw [hcardFiber column, hcardSigma, Nat.cast_mul]
  have hKpos : (K : ENNReal) ≠ 0 := by
    dsimp [K]
    exact_mod_cast Finset.prod_ne_zero_iff.mpr (fun q _ => Nat.factorial_ne_zero _)
  have hKtop : (K : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_eq_inv_mul]
  calc
    (↑(Fintype.card (OrderedProfilePartition n k)) * (K : ENNReal))⁻¹ *
        (K : ENNReal) =
        ((Fintype.card (OrderedProfilePartition n k) : ENNReal)⁻¹ *
          (K : ENNReal)⁻¹) *
          (K : ENNReal) := by
      rw [ENNReal.mul_inv (Or.inr hKtop) (Or.inr hKpos)]
    _ = (Fintype.card (OrderedProfilePartition n k) : ENNReal)⁻¹ *
        ((K : ENNReal)⁻¹ * (K : ENNReal)) := by ac_rfl
    _ = (Fintype.card (OrderedProfilePartition n k) : ENNReal)⁻¹ := by
      rw [ENNReal.inv_mul_cancel hKpos hKtop, mul_one]

/-- The uniform configuration and uniform fixed-fibre laws give the same
weighted expectation for every `ENNReal` function of the canonical overlap
matrix. -/
private theorem sum_pmf_mul_comp_eq_sum_pmf_map
    {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (weight : β → ENNReal) :
    (∑ x : α, p x * weight (f x)) =
      ∑ y : β, (p.map f) y * weight y := by
  classical
  calc
    (∑ x : α, p x * weight (f x)) =
        ∑ x : α, ∑ y : β,
          (if y = f x then p x else 0) * weight y := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' Finset.univ (f x)]
      simp
    _ = ∑ y : β, ∑ x : α,
          (if y = f x then p x else 0) * weight y := Finset.sum_comm
    _ = ∑ y : β,
        (∑ x : α, if y = f x then p x else 0) * weight y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
    _ = ∑ y : β, (p.map f) y * weight y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [PMF.map_apply, tsum_fintype]

/-- The entire canonical overlap-table distribution induced by a uniform
configuration matching is the existing uniform fixed-fibre overlap-table
distribution.  The entrywise cell-table theorem above makes this a semantic
transport, not merely an equality of finite cardinalities. -/
theorem uniformConfigurationMatching_map_profileOverlapTable
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) :
    (uniformConfigurationMatching (profileBlockMargin k) (profileBlockMargin k)
      (profileBlockMargin_total_eq_self row₀)).map
        (profileOverlapTableOfConfigurationMatching row₀) =
      (uniformOrderedProfilePartition row₀).map
        (profileOverlapTableOfOrderedPair row₀) := by
  let p := uniformConfigurationMatching (profileBlockMargin k)
    (profileBlockMargin k) (profileBlockMargin_total_eq_self row₀)
  let f := orderedProfileColumnOfConfigurationMatching row₀
  let g := profileOverlapTableOfOrderedPair row₀
  change p.map (g ∘ f) = (uniformOrderedProfilePartition row₀).map g
  calc
    p.map (g ∘ f) = (p.map f).map g :=
      (PMF.map_comp (p := p) (f := f) (g := g)).symm
    _ = (uniformOrderedProfilePartition row₀).map g := by
      rw [uniformConfigurationMatching_map_orderedProfileColumn row₀]

theorem weightedExpectation_uniformConfigurationMatching_eq_uniformProfile
    {b n : Nat} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k)
    (weight : (ProfileBlockIndex k → ProfileBlockIndex k → Nat) → ENNReal) :
    (∑ matching : ConfigurationMatching (profileBlockMargin k)
        (profileBlockMargin k),
      uniformConfigurationMatching (profileBlockMargin k) (profileBlockMargin k)
        (profileBlockMargin_total_eq_self row₀) matching *
        weight (profileOverlapTableOfConfigurationMatching row₀ matching).tableNat) =
      ∑ column : OrderedProfilePartition n k,
        uniformOrderedProfilePartition row₀ column *
          weight (profileOverlapTableOfOrderedPair row₀ column).tableNat := by
  classical
  let p := uniformConfigurationMatching (profileBlockMargin k)
    (profileBlockMargin k) (profileBlockMargin_total_eq_self row₀)
  let f := orderedProfileColumnOfConfigurationMatching row₀
  let w : OrderedProfilePartition n k → ENNReal := fun column =>
    weight (profileOverlapTableOfOrderedPair row₀ column).tableNat
  calc
    (∑ matching : ConfigurationMatching (profileBlockMargin k)
        (profileBlockMargin k),
      uniformConfigurationMatching (profileBlockMargin k) (profileBlockMargin k)
        (profileBlockMargin_total_eq_self row₀) matching *
        weight (profileOverlapTableOfConfigurationMatching row₀ matching).tableNat) =
      ∑ matching : ConfigurationMatching (profileBlockMargin k)
        (profileBlockMargin k), p matching * w (f matching) := by
      apply Finset.sum_congr rfl
      intro matching _
      rfl
    _ = ∑ column : OrderedProfilePartition n k,
        (p.map f) column * w column :=
      sum_pmf_mul_comp_eq_sum_pmf_map p f w
    _ = ∑ column : OrderedProfilePartition n k,
        uniformOrderedProfilePartition row₀ column *
          weight (profileOverlapTableOfOrderedPair row₀ column).tableNat := by
      rw [uniformConfigurationMatching_map_orderedProfileColumn row₀]

#print axioms profileRowToStubEquiv
#print axioms configurationMatchingEquivColumnWithOrders
#print axioms configurationCellCount_ofColumnWithOrders_eq_orderedOverlapCount
#print axioms profileOverlapTableOfConfigurationMatching_tableNat_eq_cellCount
#print axioms card_profileColumnFiberOrders
#print axioms uniformConfigurationMatching_map_orderedProfileColumn
#print axioms uniformConfigurationMatching_map_profileOverlapTable
#print axioms weightedExpectation_uniformConfigurationMatching_eq_uniformProfile

end

end Erdos625
