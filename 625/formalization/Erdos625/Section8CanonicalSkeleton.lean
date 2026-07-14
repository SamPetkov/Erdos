import Mathlib

/-!
# Canonical high-support atoms for Section VIII

This module packages four finite deterministic facts used when the canonical
high-cell support is extracted from a configuration table.  It proves that
entries above half a common row/column cap form a partial matching, that zero
residual mass forces uniqueness of the selected fibres and their compatible
pairing, and that the full-cell cap/no-return event translates exactly to the
residual event.

These statements do not count canonical skeletons, prove the incidence formula
(8.3), or establish the endpoint/near/middle sums in Lemma 8.3.
-/

namespace Erdos625

open scoped BigOperators

/-- Retain the whole cell demand precisely above the cutoff `U / 2`. -/
def canonicalHighDemand {A B : Type*}
    (table : A → B → ℕ) (U : ℕ) : A → B → ℕ :=
  fun a b => if U / 2 < table a b then table a b else 0

/-- Once source and target fibres are fixed, compatibility with the ambient
matching determines their labelled pairing uniquely. -/
theorem compatiblePairing_unique
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (matching : X ≃ Y) (source : Finset X) (target : Finset Y)
    (pairing₁ pairing₂ : (↥source) ≃ (↥target))
    (hpairing₁ : ∀ x, (pairing₁ x).1 = matching x.1)
    (hpairing₂ : ∀ x, (pairing₂ x).1 = matching x.1) :
    pairing₁ = pairing₂ := by
  ext x
  exact (hpairing₁ x).trans (hpairing₂ x).symm

/-- A selected fibre with the full fibre's cardinality is the full fibre.  The
displayed demand-plus-residual equality is the form produced by the fixed-
witness decomposition. -/
theorem selectedFiber_eq_fullFiber_of_zero_residual
    {X : Type*} [Fintype X] [DecidableEq X]
    (selected fullFiber : Finset X) (demand residual : ℕ)
    (hsubset : selected ⊆ fullFiber)
    (hselected : selected.card = demand)
    (hfull : fullFiber.card = demand + residual)
    (hzero : residual = 0) :
    selected = fullFiber := by
  apply Finset.eq_of_subset_of_card_le hsubset
  rw [hselected, hfull, hzero]
  omega

/-- Under common row and column caps, the support of the canonical high demand
is a bipartite partial matching, with exact on- and off-support values. -/
theorem canonicalHighDemand_partialMatching_and_incidence
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (table : A → B → ℕ) (U : ℕ)
    (hrow : ∀ a, (∑ b, table a b) ≤ U)
    (hcolumn : ∀ b, (∑ a, table a b) ≤ U) :
    (∀ a b₁ b₂,
      canonicalHighDemand table U a b₁ ≠ 0 →
      canonicalHighDemand table U a b₂ ≠ 0 → b₁ = b₂) ∧
    (∀ b a₁ a₂,
      canonicalHighDemand table U a₁ b ≠ 0 →
      canonicalHighDemand table U a₂ b ≠ 0 → a₁ = a₂) ∧
    (∀ a b, U / 2 < table a b →
      canonicalHighDemand table U a b = table a b) ∧
    (∀ a b, ¬ U / 2 < table a b →
      canonicalHighDemand table U a b = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b₁ b₂ h₁ h₂
    by_contra hne
    have hb₁ : U / 2 < table a b₁ := by
      by_contra h
      simp [canonicalHighDemand, h] at h₁
    have hb₂ : U / 2 < table a b₂ := by
      by_contra h
      simp [canonicalHighDemand, h] at h₂
    have hsub : table a b₁ + table a b₂ ≤ ∑ b, table a b := by
      have hs : ({b₁, b₂} : Finset B) ⊆ Finset.univ := Finset.subset_univ _
      calc
        table a b₁ + table a b₂ =
            ∑ b ∈ ({b₁, b₂} : Finset B), table a b := by
          rw [Finset.sum_pair hne]
        _ ≤ ∑ b, table a b := Finset.sum_le_sum_of_subset hs
    have hcap := hrow a
    omega
  · intro b a₁ a₂ h₁ h₂
    by_contra hne
    have ha₁ : U / 2 < table a₁ b := by
      by_contra h
      simp [canonicalHighDemand, h] at h₁
    have ha₂ : U / 2 < table a₂ b := by
      by_contra h
      simp [canonicalHighDemand, h] at h₂
    have hsub : table a₁ b + table a₂ b ≤ ∑ a, table a b := by
      have hs : ({a₁, a₂} : Finset A) ⊆ Finset.univ := Finset.subset_univ _
      calc
        table a₁ b + table a₂ b =
            ∑ a ∈ ({a₁, a₂} : Finset A), table a b := by
          rw [Finset.sum_pair hne]
        _ ≤ ∑ a, table a b := Finset.sum_le_sum_of_subset hs
    have hcap := hcolumn b
    omega
  · intro a b h
    simp [canonicalHighDemand, h]
  · intro a b h
    simp [canonicalHighDemand, h]

/-- Translate the simultaneous full-cell cap/no-return condition into the
unshifted residual cap and zero residual mass on the canonical support. -/
theorem supportIndexed_fullConstraints_iff_residual
    {A B : Type*}
    (full demand residual cap : A → B → ℕ)
    (support : A → B → Prop)
    (hsplit : ∀ a b, full a b = demand a b + residual a b)
    (hdemandCap : ∀ a b, demand a b ≤ cap a b)
    (hdemandOff : ∀ a b, ¬ support a b → demand a b = 0) :
    (∀ a b,
        full a b ≤ cap a b ∧
          (support a b → full a b = demand a b)) ↔
      (∀ a b,
        residual a b ≤ cap a b ∧
          (support a b → residual a b = 0)) := by
  constructor
  · intro h a b
    obtain ⟨hcap, hsupp⟩ := h a b
    have hs := hsplit a b
    exact ⟨by omega, fun hsup => by
      have heq := hsupp hsup
      omega⟩
  · intro h a b
    obtain ⟨hcap, hsupp⟩ := h a b
    have hs := hsplit a b
    have hdc := hdemandCap a b
    refine ⟨?_, fun hsup => by
      have hzero := hsupp hsup
      omega⟩
    by_cases hsup : support a b
    · have hzero := hsupp hsup
      omega
    · have hoff := hdemandOff a b hsup
      omega

#print axioms compatiblePairing_unique
#print axioms selectedFiber_eq_fullFiber_of_zero_residual
#print axioms canonicalHighDemand_partialMatching_and_incidence
#print axioms supportIndexed_fullConstraints_iff_residual

end Erdos625
