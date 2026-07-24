import Erdos625.OrderedSignedProfileSemantics
import Mathlib.Tactic

/-!
# Signed semantic lift from labelled profile partitions to ordered slots

The semantic equivalence between block-labelled profile partitions and ordered
fixed-margin slot labelings extends to Boolean sign data.  This file records
the extension explicitly, together with its restriction to graph-valid
witnesses.  It is intentionally independent of the second-moment assembly:
later modules can reindex finite sums through the equivalence without hiding a
cardinality-only quotient.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Precomposition with an equivalence transports Boolean functions between
their domains. -/
def boolFunctionEquiv {α β : Type*} (e : α ≃ β) :
    (α → Bool) ≃ (β → Bool) where
  toFun f := fun b => f (e.symm b)
  invFun g := fun a => g (e a)
  left_inv := by
    intro f
    funext a
    simp
  right_inv := by
    intro g
    funext b
    simp

@[simp] theorem boolFunctionEquiv_apply {α β : Type*} (e : α ≃ β)
    (f : α → Bool) (b : β) :
    boolFunctionEquiv e f b = f (e.symm b) := rfl

@[simp] theorem boolFunctionEquiv_symm_apply {α β : Type*} (e : α ≃ β)
    (g : β → Bool) (a : α) :
    (boolFunctionEquiv e).symm g a = g (e a) := rfl

/-- A block-labelled profile partition equipped with a Boolean sign on every
unlabelled part. -/
abbrev LabeledSignedProfileData {b : Nat} (n : Nat) (k : ColoringProfile b) :=
  Σ x : LabeledProfilePartition n k, x.1.1.parts → Bool

/-- An ordered profile partition equipped with a Boolean sign on every named
block slot. -/
abbrev OrderedSlotSignedProfileData {b : Nat} (n : Nat) (k : ColoringProfile b) :=
  Σ _ : OrderedProfilePartition n k, ProfileBlockIndex k → Bool

/-- The semantic labelled/ordered partition equivalence lifted to Boolean
sign data. -/
noncomputable def labeledSignedProfileDataEquivOrderedSlots
    {b n : Nat} (k : ColoringProfile b) :
    LabeledSignedProfileData n k ≃ OrderedSlotSignedProfileData n k :=
  Equiv.sigmaCongr (labeledProfilePartitionEquivOrderedSemantic k)
    (fun x => boolFunctionEquiv (labeledPartsEquivBlockIndex x))

@[simp] theorem labeledSignedProfileDataEquivOrderedSlots_apply_fst
    {b n : Nat} (k : ColoringProfile b)
    (x : LabeledProfilePartition n k) (σ : x.1.1.parts → Bool) :
    (labeledSignedProfileDataEquivOrderedSlots k ⟨x, σ⟩).1 =
      labeledProfilePartitionToOrdered x := rfl

@[simp] theorem labeledSignedProfileDataEquivOrderedSlots_apply_snd
    {b n : Nat} (k : ColoringProfile b)
    (x : LabeledProfilePartition n k) (σ : x.1.1.parts → Bool)
    (q : ProfileBlockIndex k) :
    (labeledSignedProfileDataEquivOrderedSlots k ⟨x, σ⟩).2 q =
      labeledSignsToOrderedSlots x σ q := rfl

/-- The preceding equivalence preserves the signed graph predicate exactly. -/
theorem labeledSignedProfileData_valid_iff
    {b n : Nat} {k : ColoringProfile b} (G : LabeledGraph n)
    (x : LabeledProfilePartition n k) (σ : x.1.1.parts → Bool) :
    profileSignValid G x.1 σ ↔
      orderedSlotSignValid G
        (labeledSignedProfileDataEquivOrderedSlots k ⟨x, σ⟩).1
        (labeledSignedProfileDataEquivOrderedSlots k ⟨x, σ⟩).2 := by
  change profileSignValid G x.1 σ ↔
    orderedSlotSignValid G (labeledProfilePartitionToOrdered x)
      (labeledSignsToOrderedSlots x σ)
  exact profileSignValid_iff_orderedSlotSignValid_labeled G x σ

/-- Graph-valid labelled signed data. -/
abbrev ValidLabeledSignedProfileData {b n : Nat}
    (G : LabeledGraph n) (k : ColoringProfile b) :=
  {w : LabeledSignedProfileData n k // profileSignValid G w.1.1 w.2}

/-- Graph-valid ordered slot signed data. -/
abbrev ValidOrderedSlotSignedProfileData {b n : Nat}
    (G : LabeledGraph n) (k : ColoringProfile b) :=
  {w : OrderedSlotSignedProfileData n k // orderedSlotSignValid G w.1 w.2}

noncomputable instance instFintypeValidLabeledSignedProfileData
    {b n : Nat} (G : LabeledGraph n) (k : ColoringProfile b) :
    Fintype (ValidLabeledSignedProfileData G k) :=
  Fintype.ofFinite _

noncomputable instance instFintypeValidOrderedSlotSignedProfileData
    {b n : Nat} (G : LabeledGraph n) (k : ColoringProfile b) :
    Fintype (ValidOrderedSlotSignedProfileData G k) :=
  Fintype.ofFinite _

/-- The signed semantic lift restricts to a genuine equivalence of valid
witness types. -/
noncomputable def validLabeledSignedProfileDataEquivOrderedSlots
    {b n : Nat} (G : LabeledGraph n) (k : ColoringProfile b) :
    ValidLabeledSignedProfileData G k ≃
      ValidOrderedSlotSignedProfileData G k where
  toFun w := ⟨labeledSignedProfileDataEquivOrderedSlots k w.1,
    (labeledSignedProfileData_valid_iff G w.1.1 w.1.2).mp w.2⟩
  invFun w := ⟨(labeledSignedProfileDataEquivOrderedSlots k).symm w.1, by
    have h := (labeledSignedProfileData_valid_iff G
      ((labeledSignedProfileDataEquivOrderedSlots k).symm w.1).1
      ((labeledSignedProfileDataEquivOrderedSlots k).symm w.1).2)
    rw [(labeledSignedProfileDataEquivOrderedSlots k).apply_symm_apply] at h
    exact h.mpr w.2⟩
  left_inv := by
    intro w
    apply Subtype.ext
    exact (labeledSignedProfileDataEquivOrderedSlots k).symm_apply_apply w.1
  right_inv := by
    intro w
    apply Subtype.ext
    exact (labeledSignedProfileDataEquivOrderedSlots k).apply_symm_apply w.1

/-- Reindex an arbitrary finite sum from labelled signed data to ordered slot
signed data. -/
theorem sum_labeledSignedProfileData_eq_sum_orderedSlots
    {b n : Nat} (k : ColoringProfile b) {R : Type*} [AddCommMonoid R]
    (f : OrderedSlotSignedProfileData n k → R) :
    ∑ w : LabeledSignedProfileData n k,
      f (labeledSignedProfileDataEquivOrderedSlots k w) =
    ∑ w : OrderedSlotSignedProfileData n k, f w := by
  exact (Equiv.sum_comp (labeledSignedProfileDataEquivOrderedSlots k) f)

/-- Reindex a finite sum restricted to graph-valid signed witnesses. -/
theorem sum_validLabeledSignedProfileData_eq_sum_validOrderedSlots
    {b n : Nat} (G : LabeledGraph n) (k : ColoringProfile b)
    {R : Type*} [AddCommMonoid R]
    (f : ValidOrderedSlotSignedProfileData G k → R) :
    ∑ w : ValidLabeledSignedProfileData G k,
      f (validLabeledSignedProfileDataEquivOrderedSlots G k w) =
    ∑ w : ValidOrderedSlotSignedProfileData G k, f w := by
  exact (Equiv.sum_comp (validLabeledSignedProfileDataEquivOrderedSlots G k) f)

#print axioms labeledSignedProfileDataEquivOrderedSlots
#print axioms labeledSignedProfileData_valid_iff
#print axioms validLabeledSignedProfileDataEquivOrderedSlots
#print axioms sum_labeledSignedProfileData_eq_sum_orderedSlots
#print axioms sum_validLabeledSignedProfileData_eq_sum_validOrderedSlots

end

end Erdos625
