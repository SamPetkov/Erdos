import Erdos625.EvenMatchingKernel

/-!
# Encoding finite bipartite edge sets as matrices over `ZMod 2`

This module gives the exact representation bridge needed before finite even
edge sets can be fed into the matching-restriction lemmas.  A finite subset of
`A × B` is encoded by its zero-one incidence matrix over `ZMod 2`.  The
encoding is injective, and the matrix has zero row and column sums exactly when
every row and column fibre of the edge set has even cardinality.

No support restriction, cycle decomposition, cycle-space count, residual
matching law, or probability bound is asserted here.
-/

namespace Erdos625

open scoped BigOperators

/-- Edges of `F` incident with a fixed row vertex. -/
def bipartiteEdgeRow
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (a : A) : Finset B :=
  Finset.univ.filter fun b ↦ (a, b) ∈ F

/-- Edges of `F` incident with a fixed column vertex. -/
def bipartiteEdgeColumn
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (b : B) : Finset A :=
  Finset.univ.filter fun a ↦ (a, b) ∈ F

/-- The zero-one incidence matrix of a finite bipartite edge set, with entries
in `ZMod 2`. -/
def bipartiteEdgeMatrix
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) : A → B → ZMod 2 :=
  fun a b ↦ if (a, b) ∈ F then 1 else 0

@[simp] theorem bipartiteEdgeMatrix_apply_eq_one_iff
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (a : A) (b : B) :
    bipartiteEdgeMatrix F a b = 1 ↔ (a, b) ∈ F := by
  simp [bipartiteEdgeMatrix]

@[simp] theorem bipartiteEdgeMatrix_apply_ne_zero_iff
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (a : A) (b : B) :
    bipartiteEdgeMatrix F a b ≠ 0 ↔ (a, b) ∈ F := by
  simp [bipartiteEdgeMatrix]

/-- The incidence-matrix encoding remembers the finite edge set exactly. -/
theorem bipartiteEdgeMatrix_injective
    {A B : Type*} [DecidableEq A] [DecidableEq B] :
    Function.Injective
      (bipartiteEdgeMatrix : Finset (A × B) → A → B → ZMod 2) := by
  intro F G h
  ext p
  have hp := congrFun (congrFun h p.1) p.2
  constructor
  · intro hpF
    apply (bipartiteEdgeMatrix_apply_eq_one_iff G p.1 p.2).mp
    rw [← hp]
    exact (bipartiteEdgeMatrix_apply_eq_one_iff F p.1 p.2).mpr hpF
  · intro hpG
    apply (bipartiteEdgeMatrix_apply_eq_one_iff F p.1 p.2).mp
    rw [hp]
    exact (bipartiteEdgeMatrix_apply_eq_one_iff G p.1 p.2).mpr hpG

/-- A row sum of the incidence matrix is the row-fibre cardinality reduced
modulo two. -/
theorem sum_bipartiteEdgeMatrix_row
    {A B : Type*} [Fintype B] [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (a : A) :
    ∑ b, bipartiteEdgeMatrix F a b =
      ((bipartiteEdgeRow F a).card : ZMod 2) := by
  change (∑ b, if (a, b) ∈ F then (1 : ZMod 2) else 0) =
    ((Finset.univ.filter (fun b ↦ (a, b) ∈ F)).card : ZMod 2)
  rw [← Finset.sum_filter]
  simp

/-- A column sum of the incidence matrix is the column-fibre cardinality
reduced modulo two. -/
theorem sum_bipartiteEdgeMatrix_column
    {A B : Type*} [Fintype A] [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) (b : B) :
    ∑ a, bipartiteEdgeMatrix F a b =
      ((bipartiteEdgeColumn F b).card : ZMod 2) := by
  change (∑ a, if (a, b) ∈ F then (1 : ZMod 2) else 0) =
    ((Finset.univ.filter (fun a ↦ (a, b) ∈ F)).card : ZMod 2)
  rw [← Finset.sum_filter]
  simp

/-- Every row and column fibre of a finite bipartite edge set has even
cardinality. -/
def BipartiteEvenEdgeSet
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) : Prop :=
  (∀ a, Even (bipartiteEdgeRow F a).card) ∧
    (∀ b, Even (bipartiteEdgeColumn F b).card)

/-- A finite bipartite edge set has all row and column degrees even exactly
when its incidence matrix has zero row and column sums over `ZMod 2`. -/
theorem bipartiteEdgeMatrix_even_iff
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : Finset (A × B)) :
    BipartiteEvenMatrix (bipartiteEdgeMatrix F) ↔
      BipartiteEvenEdgeSet F := by
  constructor
  · intro h
    constructor
    · intro a
      apply ZMod.natCast_eq_zero_iff_even.mp
      rw [← sum_bipartiteEdgeMatrix_row]
      exact h.1 a
    · intro b
      apply ZMod.natCast_eq_zero_iff_even.mp
      rw [← sum_bipartiteEdgeMatrix_column]
      exact h.2 b
  · intro h
    constructor
    · intro a
      rw [sum_bipartiteEdgeMatrix_row]
      exact ZMod.natCast_eq_zero_iff_even.mpr (h.1 a)
    · intro b
      rw [sum_bipartiteEdgeMatrix_column]
      exact ZMod.natCast_eq_zero_iff_even.mpr (h.2 b)

end Erdos625
