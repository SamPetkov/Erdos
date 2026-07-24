import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-!
# Exact ordered overlap law

This module formalizes the finite counting identity behind manuscript
equations (6.1)--(6.2).  One row labeling is fixed.  Column labelings with
prescribed fibers are counted uniformly, and the subfamily realizing a fixed
overlap table is counted exactly by a product of rowwise multinomial factors.

The final theorem is stated both without division, over `ℕ`, and as the exact
rational probability of the overlap table.  No asymptotics or probabilistic
independence assumptions enter this finite bridge.
-/

namespace Erdos625

open scoped BigOperators

/-- Cardinality of one fiber of a finite labeling. -/
def labelingFiberCount
    {V A : Type*} [Fintype V] [DecidableEq A]
    (label : V → A) (a : A) : ℕ :=
  (Finset.univ.filter fun v ↦ label v = a).card

/-- Cardinality of one cell in the overlap of two finite labelings. -/
def orderedOverlapCount
    {V A B : Type*} [Fintype V] [DecidableEq A] [DecidableEq B]
    (row : V → A) (column : V → B) (a : A) (b : B) : ℕ :=
  (Finset.univ.filter fun v ↦ row v = a ∧ column v = b).card

/-- Column labelings whose fibers have the prescribed sizes. -/
def FixedFiberLabeling
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq B]
    (margin : B → ℕ) :=
  {column : V → B // ∀ b, labelingFiberCount column b = margin b}

/-- Column labelings whose overlap with a fixed row labeling is a prescribed
table. -/
def OrderedOverlapLabeling
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) :=
  {column : V → B //
    ∀ a b, orderedOverlapCount row column a b = table a b}

instance instFiniteFixedFiberLabeling
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq B]
    (margin : B → ℕ) :
    Finite (FixedFiberLabeling (V := V) margin) := by
  unfold FixedFiberLabeling
  infer_instance

noncomputable instance instFintypeFixedFiberLabeling
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq B]
    (margin : B → ℕ) :
    Fintype (FixedFiberLabeling (V := V) margin) :=
  Fintype.ofFinite _

instance instFiniteOrderedOverlapLabeling
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) :
    Finite (OrderedOverlapLabeling row table) := by
  unfold OrderedOverlapLabeling
  infer_instance

noncomputable instance instFintypeOrderedOverlapLabeling
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) :
    Fintype (OrderedOverlapLabeling row table) :=
  Fintype.ofFinite _

/-- Fiber counts of a finite labeling sum to the ambient cardinality. -/
theorem sum_labelingFiberCount
    {V A : Type*} [Fintype V] [Fintype A] [DecidableEq A]
    (label : V → A) :
    ∑ a, labelingFiberCount label a = Fintype.card V := by
  simp only [labelingFiberCount, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

/-- The filtered-set definition of a fiber count is the cardinality of the
corresponding subtype. -/
theorem card_labelingFiber
    {V A : Type*} [Fintype V] [DecidableEq A]
    (label : V → A) (a : A) :
    Fintype.card {v : V // label v = a} = labelingFiberCount label a := by
  rw [Fintype.card_subtype]
  rfl

/-- An equivalence with a sigma type canonically orders every fiber. -/
noncomputable def fiberOrderOfSigmaEquiv
    {V B : Type*} [DecidableEq B]
    (margin : B → ℕ) (equiv : V ≃ Σ b, Fin (margin b)) (b : B) :
    {v : V // (equiv v).1 = b} ≃ Fin (margin b) where
  toFun v := v.2 ▸ (equiv v.1).2
  invFun i := ⟨equiv.symm ⟨b, i⟩, by simp⟩
  left_inv := by
    rintro ⟨v, rfl⟩
    simp
  right_inv := by
    intro i
    have h := equiv.apply_symm_apply (⟨b, i⟩ : Σ b, Fin (margin b))
    refine eq_of_heq ?_
    rw [eqRec_heq_iff_heq, h]

/-- Assemble a global sigma equivalence from a labeling and an ordering of
each of its fibers.  The named construction keeps the reduction rule below
available without unfolding the proof fields of `Equiv.trans`. -/
noncomputable def sigmaEquivOfFiberOrders
    {V B : Type*} [DecidableEq B]
    (margin : B → ℕ) (column : V → B)
    (orders : ∀ b, {v : V // column v = b} ≃ Fin (margin b)) :
    V ≃ Σ b, Fin (margin b) :=
  (Equiv.sigmaFiberEquiv column).symm.trans
    (Equiv.sigmaCongrRight orders)

@[simp]
theorem sigmaEquivOfFiberOrders_apply
    {V B : Type*} [DecidableEq B]
    (margin : B → ℕ) (column : V → B)
    (orders : ∀ b, {v : V // column v = b} ≃ Fin (margin b))
    (v : V) :
    sigmaEquivOfFiberOrders margin column orders v =
      ⟨column v, orders (column v) ⟨v, rfl⟩⟩ := by
  rfl

/-- A bijection to the labeled sigma type is equivalent to a raw labeling
together with an ordering of each fiber.  The existence of those orders
already forces the prescribed fiber cardinalities. -/
noncomputable def rawFiberLabelingWithOrdersEquiv
    {V B : Type*} [DecidableEq B] (margin : B → ℕ) :
    (V ≃ Σ b, Fin (margin b)) ≃
      Σ column : V → B,
        ∀ b, {v : V // column v = b} ≃ Fin (margin b) where
  toFun equiv :=
    ⟨fun v ↦ (equiv v).1, fun b ↦ fiberOrderOfSigmaEquiv margin equiv b⟩
  invFun data := sigmaEquivOfFiberOrders margin data.1 data.2
  left_inv := by
    intro equiv
    apply Equiv.ext
    intro v
    simp [fiberOrderOfSigmaEquiv]
  right_inv := by
    rintro ⟨column, orders⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    funext b
    apply Equiv.ext
    rintro ⟨v, hv⟩
    have hvb : column v = b := by
      simpa only [sigmaEquivOfFiberOrders_apply] using hv
    cases hvb
    change column v = column v at hv
    have hvProof : hv = rfl := Subsingleton.elim _ _
    cases hvProof
    rfl

/-- Adding the proof that the raw labeling has the prescribed fibers changes
no data: that proof follows from the supplied fiber orders. -/
noncomputable def rawFiberOrdersToFixedEquiv
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq B]
    (margin : B → ℕ) :
    (Σ column : V → B,
        ∀ b, {v : V // column v = b} ≃ Fin (margin b)) ≃
      Σ column : FixedFiberLabeling (V := V) margin,
        ∀ b, {v : V // column.1 v = b} ≃ Fin (margin b) where
  toFun data := by
    have hmargin : ∀ b, labelingFiberCount data.1 b = margin b := by
      intro b
      rw [← card_labelingFiber data.1 b]
      simpa using Fintype.card_congr (data.2 b)
    exact ⟨⟨data.1, hmargin⟩, data.2⟩
  invFun data := ⟨data.1.1, data.2⟩
  left_inv := by
    intro data
    rfl
  right_inv := by
    rintro ⟨⟨column, hmargin⟩, orders⟩
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl

/-- A bijection to the labeled sigma type is equivalent to a labeling with
the prescribed fibers together with an ordering of each fiber. -/
noncomputable def fixedFiberLabelingWithOrdersEquiv
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq B]
    (margin : B → ℕ) :
    (V ≃ Σ b, Fin (margin b)) ≃
      Σ column : FixedFiberLabeling (V := V) margin,
        ∀ b, {v : V // column.1 v = b} ≃ Fin (margin b) :=
  (rawFiberLabelingWithOrdersEquiv margin).trans
    (rawFiberOrdersToFixedEquiv margin)

/-- Exact multinomial count for finite labelings with prescribed fiber sizes.
This theorem is assumption-minimal: the total-margin equation is precisely
the feasibility condition needed by the count. -/
theorem card_fixedFiberLabeling_mul_factorials
    {V B : Type*} [Fintype V] [Fintype B] [DecidableEq B]
    (margin : B → ℕ)
    (htotal : ∑ b, margin b = Fintype.card V) :
    Fintype.card (FixedFiberLabeling (V := V) margin) *
        ∏ b, (margin b).factorial =
      (Fintype.card V).factorial := by
  classical
  have hcardSigma : Fintype.card V = Fintype.card (Σ b, Fin (margin b)) := by
    rw [Fintype.card_sigma]
    simpa using htotal.symm
  let ambientEquiv : V ≃ Σ b, Fin (margin b) :=
    Fintype.equivOfCardEq hcardSigma
  have hambient :
      Fintype.card (V ≃ Σ b, Fin (margin b)) =
        (Fintype.card V).factorial := by
    exact Fintype.card_equiv ambientEquiv
  have horders : ∀ column : FixedFiberLabeling (V := V) margin,
      Fintype.card (∀ b, {v : V // column.1 v = b} ≃ Fin (margin b)) =
        ∏ b, (margin b).factorial := by
    intro column
    rw [Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b hb
    have hfiber :
        Fintype.card {v : V // column.1 v = b} = Fintype.card (Fin (margin b)) := by
      rw [card_labelingFiber, column.2 b, Fintype.card_fin]
    calc
      Fintype.card ({v : V // column.1 v = b} ≃ Fin (margin b)) =
          (Fintype.card {v : V // column.1 v = b}).factorial :=
        Fintype.card_equiv (Fintype.equivOfCardEq hfiber)
      _ = (margin b).factorial := by
        rw [hfiber, Fintype.card_fin]
  calc
    Fintype.card (FixedFiberLabeling (V := V) margin) *
          ∏ b, (margin b).factorial =
        ∑ _column : FixedFiberLabeling (V := V) margin,
          ∏ b, (margin b).factorial := by simp
    _ = ∑ column : FixedFiberLabeling (V := V) margin,
          Fintype.card
            (∀ b, {v : V // column.1 v = b} ≃ Fin (margin b)) := by
      apply Finset.sum_congr rfl
      intro column hcolumn
      exact (horders column).symm
    _ = Fintype.card
          (Σ column : FixedFiberLabeling (V := V) margin,
            ∀ b, {v : V // column.1 v = b} ≃ Fin (margin b)) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card (V ≃ Σ b, Fin (margin b)) := by
      exact Fintype.card_congr (fixedFiberLabelingWithOrdersEquiv margin).symm
    _ = (Fintype.card V).factorial := hambient

/-- Restricting a column labeling to a row fiber turns a fiber count into the
corresponding overlap-cell count. -/
theorem restricted_labelingFiberCount_eq_orderedOverlapCount
    {V A B : Type*}
    [Fintype V] [DecidableEq A] [DecidableEq B]
    (row : V → A) (column : V → B) (a : A) (b : B) :
    labelingFiberCount (fun v : {v : V // row v = a} ↦ column v.1) b =
      orderedOverlapCount row column a b := by
  rw [← card_labelingFiber]
  rw [orderedOverlapCount, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact
    { toFun := fun v ↦ ⟨v.1.1, v.1.2, v.2⟩
      invFun := fun v ↦ ⟨⟨v.1, v.2.1⟩, v.2.2⟩
      left_inv := fun v ↦ rfl
      right_inv := fun v ↦ rfl }

/-- The cells in one row of an overlap table sum to the size of that row
fiber. -/
theorem sum_orderedOverlapCount_row
    {V A B : Type*}
    [Fintype V] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : V → A) (column : V → B) (a : A) :
    ∑ b, orderedOverlapCount row column a b =
      labelingFiberCount row a := by
  calc
    ∑ b, orderedOverlapCount row column a b =
        ∑ b, labelingFiberCount
          (fun v : {v : V // row v = a} ↦ column v.1) b := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (restricted_labelingFiberCount_eq_orderedOverlapCount
        row column a b).symm
    _ = Fintype.card {v : V // row v = a} :=
      sum_labelingFiberCount _
    _ = labelingFiberCount row a := card_labelingFiber row a

/-- Swapping the two labelings transposes every overlap cell. -/
theorem orderedOverlapCount_comm
    {V A B : Type*}
    [Fintype V] [DecidableEq A] [DecidableEq B]
    (row : V → A) (column : V → B) (a : A) (b : B) :
    orderedOverlapCount row column a b =
      orderedOverlapCount column row b a := by
  unfold orderedOverlapCount
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

/-- The cells in one column of an overlap table sum to the size of that
column fiber. -/
theorem sum_orderedOverlapCount_column
    {V A B : Type*}
    [Fintype V] [Fintype A] [DecidableEq A] [DecidableEq B]
    (row : V → A) (column : V → B) (b : B) :
    ∑ a, orderedOverlapCount row column a b =
      labelingFiberCount column b := by
  calc
    ∑ a, orderedOverlapCount row column a b =
        ∑ a, orderedOverlapCount column row b a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact orderedOverlapCount_comm row column a b
    _ = labelingFiberCount column b :=
      sum_orderedOverlapCount_row column row b

/-- The overlap-table event inside the finite sample space of column
labelings with fixed margins. -/
def FixedMarginOverlapEvent
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ) :=
  {column : FixedFiberLabeling (V := V) columnMargin //
    ∀ a b, orderedOverlapCount row column.1 a b = table a b}

instance instFiniteFixedMarginOverlapEvent
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ) :
    Finite (FixedMarginOverlapEvent row table columnMargin) := by
  unfold FixedMarginOverlapEvent
  infer_instance

noncomputable instance instFintypeFixedMarginOverlapEvent
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ) :
    Fintype (FixedMarginOverlapEvent row table columnMargin) :=
  Fintype.ofFinite _

/-- Under the column-margin equations, unconstrained fixed-table labelings
are exactly the fixed-margin overlap event. -/
def orderedOverlapLabelingFixedMarginEventEquiv
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ)
    (hcolumn : ∀ b, ∑ a, table a b = columnMargin b) :
    OrderedOverlapLabeling row table ≃
      FixedMarginOverlapEvent row table columnMargin where
  toFun column := by
    have hmargin : ∀ b, labelingFiberCount column.1 b = columnMargin b := by
      intro b
      calc
        labelingFiberCount column.1 b =
            ∑ a, orderedOverlapCount row column.1 a b :=
          (sum_orderedOverlapCount_column row column.1 b).symm
        _ = ∑ a, table a b := by
          apply Finset.sum_congr rfl
          intro a ha
          exact column.2 a b
        _ = columnMargin b := hcolumn b
    exact ⟨⟨column.1, hmargin⟩, column.2⟩
  invFun column := ⟨column.1.1, column.2⟩
  left_inv := by
    intro column
    apply Subtype.ext
    rfl
  right_inv := by
    intro column
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The event cardinality is exactly the numerator cardinality in the ordered
overlap law. -/
theorem card_fixedMarginOverlapEvent
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ)
    (hcolumn : ∀ b, ∑ a, table a b = columnMargin b) :
    Fintype.card (FixedMarginOverlapEvent row table columnMargin) =
      Fintype.card (OrderedOverlapLabeling row table) :=
  Fintype.card_congr
    (orderedOverlapLabelingFixedMarginEventEquiv
      row table columnMargin hcolumn).symm

/-- A labeling with prescribed overlap table is equivalently an independent
choice, on every row fiber, of a labeling with the corresponding prescribed
cell sizes. -/
def orderedOverlapLabelingRowwiseEquiv
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) :
    OrderedOverlapLabeling row table ≃
      ∀ a, FixedFiberLabeling (V := {v : V // row v = a}) (table a) where
  toFun column a :=
    ⟨fun v ↦ column.1 v.1, fun b ↦ by
      rw [restricted_labelingFiberCount_eq_orderedOverlapCount]
      exact column.2 a b⟩
  invFun rows :=
    ⟨fun v ↦ (rows (row v)).1 ⟨v, rfl⟩, fun a b ↦ by
      rw [← restricted_labelingFiberCount_eq_orderedOverlapCount]
      have hfunctions :
          (fun v : {v : V // row v = a} ↦
            (rows (row v.1)).1 ⟨v.1, rfl⟩) = (rows a).1 := by
        funext v
        rcases v with ⟨v, hv⟩
        cases hv
        rfl
      rw [hfunctions]
      exact (rows a).2 b⟩
  left_inv := by
    intro column
    apply Subtype.ext
    funext v
    rfl
  right_inv := by
    intro rows
    funext a
    apply Subtype.ext
    funext v
    rcases v with ⟨v, hv⟩
    cases hv
    rfl

/-- Exact product of rowwise multinomial counts for column labelings with a
fixed overlap table.  This is the numerator count in manuscript (6.2). -/
theorem card_orderedOverlapLabeling_mul_factorials
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ)
    (hrow : ∀ a, ∑ b, table a b = labelingFiberCount row a) :
    Fintype.card (OrderedOverlapLabeling row table) *
        ∏ a, ∏ b, (table a b).factorial =
      ∏ a, (labelingFiberCount row a).factorial := by
  classical
  have hrowCard : ∀ a,
      ∑ b, table a b = Fintype.card {v : V // row v = a} := by
    intro a
    rw [hrow a, card_labelingFiber]
  have hrowCount : ∀ a,
      Fintype.card
          (FixedFiberLabeling (V := {v : V // row v = a}) (table a)) *
          ∏ b, (table a b).factorial =
        (labelingFiberCount row a).factorial := by
    intro a
    simpa [card_labelingFiber] using
      card_fixedFiberLabeling_mul_factorials (table a) (hrowCard a)
  rw [Fintype.card_congr (orderedOverlapLabelingRowwiseEquiv row table),
    Fintype.card_pi]
  calc
    (∏ a, Fintype.card
        (FixedFiberLabeling (V := {v : V // row v = a}) (table a))) *
          ∏ a, ∏ b, (table a b).factorial =
        ∏ a, (Fintype.card
          (FixedFiberLabeling (V := {v : V // row v = a}) (table a)) *
            ∏ b, (table a b).factorial) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ a, (labelingFiberCount row a).factorial := by
      apply Finset.prod_congr rfl
      intro a ha
      exact hrowCount a

/-- Cross-multiplied exact ordered-overlap law (6.2).  The left cardinal is
the number of column labelings realizing `table`; the right cardinal is the
number with the prescribed column margins. -/
theorem card_orderedOverlapLabeling_probability_identity
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ)
    (hrow : ∀ a, ∑ b, table a b = labelingFiberCount row a)
    (hcolumn : ∀ b, ∑ a, table a b = columnMargin b) :
    Fintype.card (OrderedOverlapLabeling row table) *
          (Fintype.card V).factorial *
          (∏ a, ∏ b, (table a b).factorial) =
      Fintype.card (FixedFiberLabeling (V := V) columnMargin) *
          (∏ a, (labelingFiberCount row a).factorial) *
          (∏ b, (columnMargin b).factorial) := by
  classical
  have htotal : ∑ b, columnMargin b = Fintype.card V := by
    calc
      ∑ b, columnMargin b = ∑ b, ∑ a, table a b := by
        apply Finset.sum_congr rfl
        intro b hb
        exact (hcolumn b).symm
      _ = ∑ a, ∑ b, table a b := Finset.sum_comm
      _ = ∑ a, labelingFiberCount row a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hrow a
      _ = Fintype.card V := sum_labelingFiberCount row
  have hoverlap := card_orderedOverlapLabeling_mul_factorials row table hrow
  have hmargin := card_fixedFiberLabeling_mul_factorials columnMargin htotal
  calc
    Fintype.card (OrderedOverlapLabeling row table) *
          (Fintype.card V).factorial *
          (∏ a, ∏ b, (table a b).factorial) =
        (Fintype.card (OrderedOverlapLabeling row table) *
          (∏ a, ∏ b, (table a b).factorial)) *
          (Fintype.card V).factorial := by ac_rfl
    _ = (∏ a, (labelingFiberCount row a).factorial) *
          (Fintype.card V).factorial := by rw [hoverlap]
    _ = (∏ a, (labelingFiberCount row a).factorial) *
          (Fintype.card (FixedFiberLabeling (V := V) columnMargin) *
            ∏ b, (columnMargin b).factorial) := by rw [hmargin]
    _ = Fintype.card (FixedFiberLabeling (V := V) columnMargin) *
          (∏ a, (labelingFiberCount row a).factorial) *
          (∏ b, (columnMargin b).factorial) := by ac_rfl

/-- Exact rational probability of a fixed overlap table when the column
labeling is uniform among all labelings with the prescribed column margins.
This is manuscript equation (6.2), with the row margins written as the actual
fiber sizes of `row`. -/
theorem orderedOverlapLabeling_probability_eq
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ)
    (hrow : ∀ a, ∑ b, table a b = labelingFiberCount row a)
    (hcolumn : ∀ b, ∑ a, table a b = columnMargin b) :
    (Fintype.card (OrderedOverlapLabeling row table) : ℚ) /
          Fintype.card (FixedFiberLabeling (V := V) columnMargin) =
      ((∏ a, (labelingFiberCount row a).factorial) *
          ∏ b, (columnMargin b).factorial : ℕ) /
        (((Fintype.card V).factorial *
          ∏ a, ∏ b, (table a b).factorial : ℕ) : ℚ) := by
  classical
  have htotal : ∑ b, columnMargin b = Fintype.card V := by
    calc
      ∑ b, columnMargin b = ∑ b, ∑ a, table a b := by
        apply Finset.sum_congr rfl
        intro b hb
        exact (hcolumn b).symm
      _ = ∑ a, ∑ b, table a b := Finset.sum_comm
      _ = ∑ a, labelingFiberCount row a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hrow a
      _ = Fintype.card V := sum_labelingFiberCount row
  have hmargin := card_fixedFiberLabeling_mul_factorials columnMargin htotal
  have hmarginNonzero :
      Fintype.card (FixedFiberLabeling (V := V) columnMargin) ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmargin
    exact Nat.factorial_ne_zero _ hmargin.symm
  have htableFactorialsNonzero :
      (∏ a, ∏ b, (table a b).factorial) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun a ha ↦
      Finset.prod_ne_zero_iff.mpr fun b hb ↦ Nat.factorial_ne_zero _
  have hdenominatorNonzero :
      (Fintype.card V).factorial *
          (∏ a, ∏ b, (table a b).factorial) ≠ 0 :=
    Nat.mul_ne_zero (Nat.factorial_ne_zero _) htableFactorialsNonzero
  have hcross :=
    card_orderedOverlapLabeling_probability_identity
      row table columnMargin hrow hcolumn
  have hcrossReassociated :
      Fintype.card (OrderedOverlapLabeling row table) *
          ((Fintype.card V).factorial *
            (∏ a, ∏ b, (table a b).factorial)) =
        ((∏ a, (labelingFiberCount row a).factorial) *
            ∏ b, (columnMargin b).factorial) *
          Fintype.card (FixedFiberLabeling (V := V) columnMargin) := by
    calc
      Fintype.card (OrderedOverlapLabeling row table) *
          ((Fintype.card V).factorial *
            (∏ a, ∏ b, (table a b).factorial)) =
        Fintype.card (OrderedOverlapLabeling row table) *
          (Fintype.card V).factorial *
          (∏ a, ∏ b, (table a b).factorial) := by ac_rfl
      _ = Fintype.card (FixedFiberLabeling (V := V) columnMargin) *
          (∏ a, (labelingFiberCount row a).factorial) *
          (∏ b, (columnMargin b).factorial) := hcross
      _ = ((∏ a, (labelingFiberCount row a).factorial) *
            ∏ b, (columnMargin b).factorial) *
          Fintype.card (FixedFiberLabeling (V := V) columnMargin) := by ac_rfl
  apply (div_eq_div_iff (by exact_mod_cast hmarginNonzero)
    (by exact_mod_cast hdenominatorNonzero)).2
  exact_mod_cast hcrossReassociated

/-- Event-space form of the exact rational probability law (6.2).  Its left
side is literally `card(event) / card(sample space)` for the uniform finite
sample space of fixed-margin column labelings. -/
theorem fixedMarginOverlapEvent_probability_eq
    {V A B : Type*}
    [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : V → A) (table : A → B → ℕ) (columnMargin : B → ℕ)
    (hrow : ∀ a, ∑ b, table a b = labelingFiberCount row a)
    (hcolumn : ∀ b, ∑ a, table a b = columnMargin b) :
    (Fintype.card (FixedMarginOverlapEvent row table columnMargin) : ℚ) /
          Fintype.card (FixedFiberLabeling (V := V) columnMargin) =
      ((∏ a, (labelingFiberCount row a).factorial) *
          ∏ b, (columnMargin b).factorial : ℕ) /
        (((Fintype.card V).factorial *
          ∏ a, ∏ b, (table a b).factorial : ℕ) : ℚ) := by
  rw [card_fixedMarginOverlapEvent row table columnMargin hcolumn]
  exact orderedOverlapLabeling_probability_eq
    row table columnMargin hrow hcolumn

end Erdos625
