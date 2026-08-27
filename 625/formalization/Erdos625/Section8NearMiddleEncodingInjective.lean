import Erdos625.Section8NearPrefixFoundation

/-!
# Section VIII raw near--middle encoding injectivity

The raw near and middle edge sets reconstruct the source high physical
skeleton, while the raw near edge set reconstructs the physical near prefix.
All remaining structure fields are propositions over those reconstructed
objects.  Hence the raw encoding introduces no additional multiplicity.

This is a deterministic finite reconstruction statement only.  It contains
no probability, weight, asymptotic, or quantitative estimate.
-/

namespace Erdos625

noncomputable section

private theorem cappedPhysicalHighFibre_ext_of_physical_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    {H₁ H₂ : CappedPhysicalHighFibre row col U}
    (hPhysical : H₁.physical.1 = H₂.physical.1) :
    H₁ = H₂ := by
  rcases H₁ with ⟨rowCap₁, colCap₁, demand₁, physical₁⟩
  rcases H₂ with ⟨rowCap₂, colCap₂, demand₂, physical₂⟩
  dsimp only at hPhysical
  have hDemandVal : demand₁.1 = demand₂.1 := by
    calc
      demand₁.1 = physical₁.1.typeTable := physical₁.2.symm
      _ = physical₂.1.typeTable :=
        congrArg
          (fun S : UnlabelledTypedSkeleton row col => S.typeTable)
          hPhysical
      _ = demand₂.1 := physical₂.2
  have hDemand : demand₁ = demand₂ := Subtype.ext hDemandVal
  subst demand₂
  have hPhysicalSubtype : physical₁ = physical₂ :=
    Subtype.ext hPhysical
  subst physical₂
  rfl

private theorem nearPrefix_ext_of_physical_eq
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    {endpoint : A → B → Nat}
    {H : CappedPhysicalHighFibre row col U}
    {P₁ P₂ : NearPrefix endpoint H}
    (hPhysical : P₁.physical = P₂.physical) :
    P₁ = P₂ := by
  rcases P₁ with ⟨physical₁, edgeSubset₁, wholeCell₁, near₁⟩
  rcases P₂ with ⟨physical₂, edgeSubset₂, wholeCell₂, near₂⟩
  dsimp only at hPhysical
  subst physical₂
  rfl

/-- The lossless raw near--middle encoding is injective.  The high physical
edge set is reconstructed as `nearEdges ∪ middleHighEdges`; the remaining
structure fields are determined by subtype extensionality and proof
irrelevance. -/
theorem encodeRawNearMiddle_injective
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → Nat} {col : B → Nat} {U : Nat}
    (endpoint : A → B → Nat) :
    Function.Injective
      (encodeRawNearMiddle
        (row := row) (col := col) (U := U) endpoint) := by
  intro C₁ C₂ hRaw
  have hNearPhysical :
      C₁.nearPrefix.physical = C₂.nearPrefix.physical := by
    apply UnlabelledTypedSkeleton.ext
    exact congrArg RawNearMiddleData.nearEdges hRaw
  have hHighEdges :
      C₁.high.physical.1.edges = C₂.high.physical.1.edges := by
    calc
      C₁.high.physical.1.edges =
          (encodeRawNearMiddle endpoint C₁).reconstructedHighEdges :=
        (encodeRawNearMiddle_reconstructs_and_is_disjoint endpoint C₁).2.symm
      _ = (encodeRawNearMiddle endpoint C₂).reconstructedHighEdges :=
        congrArg RawNearMiddleData.reconstructedHighEdges hRaw
      _ = C₂.high.physical.1.edges :=
        (encodeRawNearMiddle_reconstructs_and_is_disjoint endpoint C₂).2
  have hHighPhysical :
      C₁.high.physical.1 = C₂.high.physical.1 :=
    UnlabelledTypedSkeleton.ext hHighEdges
  have hHigh : C₁.high = C₂.high :=
    cappedPhysicalHighFibre_ext_of_physical_eq hHighPhysical
  rcases C₁ with ⟨H₁, P₁, noFurther₁⟩
  rcases C₂ with ⟨H₂, P₂, noFurther₂⟩
  dsimp only at hHigh hNearPhysical
  subst H₂
  have hPrefix : P₁ = P₂ :=
    nearPrefix_ext_of_physical_eq hNearPhysical
  subst P₂
  rfl

end

end Erdos625
