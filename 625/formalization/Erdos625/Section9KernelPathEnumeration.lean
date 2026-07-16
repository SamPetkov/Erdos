import Erdos625.Section9ExplicitPathTerms

/-!
# Section 9: exact finite enumeration of kernel paths

The endpoint kernel is a recursive sum over all intermediate vertices.  This
module exposes the corresponding finite code type.  A code records each
successive vertex, including the terminal equality witness at length zero, so
different internal vertex sequences remain different summands even when they
have the same weight.

The main identities below are exact finite sums.  They do not use row bounds,
geometric estimates, or an aggregate path certificate.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## Fixed-length paths -/

/-- Recursive codes for length-`ell` paths from `v` to `w`.

At positive length, the first successor `u` is stored and the remainder is a
code from `u` to `w`.  At length zero, the code stores a vertex proved equal
to both endpoints, so its fiber is empty or a singleton according as the
endpoints differ or agree.  Thus the nested sigma type preserves every
internal vertex choice and its multiplicity. -/
def KernelPathCode (V : Type*) : ℕ → V → V → Type _
  | 0, v, w => {x : V // x = v ∧ x = w}
  | ell + 1, _, w => Σ u : V, KernelPathCode V ell u w

noncomputable instance instFintypeKernelPathCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (ell : ℕ) (v w : V) : Fintype (KernelPathCode V ell v w) := by
  induction ell generalizing v with
  | zero =>
      change Fintype {x : V // x = v ∧ x = w}
      infer_instance
  | succ ell ih =>
      change Fintype (Σ u : V, KernelPathCode V ell u w)
      letI (u : V) : Fintype (KernelPathCode V ell u w) := ih u
      infer_instance

namespace KernelPathCode

/-- The vertex function represented by a recursive path code. -/
def vertex {V : Type*} :
    {ell : ℕ} → {v w : V} →
      KernelPathCode V ell v w → Fin (ell + 1) → V
  | 0, v, _, _ => fun _ => v
  | _ + 1, v, _, code =>
      Fin.cases v (vertex code.2)

@[simp]
theorem vertex_zero {V : Type*} {ell : ℕ} {v w : V}
    (code : KernelPathCode V ell v w) :
    code.vertex 0 = v := by
  cases ell with
  | zero => rfl
  | succ ell => rfl

@[simp]
theorem vertex_last {V : Type*} {ell : ℕ} {v w : V}
    (code : KernelPathCode V ell v w) :
    code.vertex (Fin.last ell) = w := by
  induction ell generalizing v with
  | zero =>
      exact code.2.1.symm.trans code.2.2
  | succ ell ih =>
      exact ih code.2

/-- Recursive product weight of one path code. -/
def weight {V : Type*} (K : V → V → ℝ≥0∞) :
    {ell : ℕ} → {v w : V} → KernelPathCode V ell v w → ℝ≥0∞
  | 0, _, _, _ => 1
  | _ + 1, v, _, code => K v code.1 * weight K code.2

@[simp]
theorem weight_zero {V : Type*} (K : V → V → ℝ≥0∞)
    {v w : V} (code : KernelPathCode V 0 v w) :
    code.weight K = 1 := rfl

@[simp]
theorem weight_succ {V : Type*} (K : V → V → ℝ≥0∞)
    {ell : ℕ} {v w : V} (code : KernelPathCode V (ell + 1) v w) :
    code.weight K = K v code.1 * code.2.weight K := rfl

/-- The recursive weight is exactly the product attached to the represented
vertex function by `explicitPathWeight`. -/
theorem weight_eq_explicitPathWeight
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞)
    {ell : ℕ} {v w : V} (code : KernelPathCode V ell v w) :
    code.weight K = explicitPathWeight K code.vertex := by
  induction ell generalizing v with
  | zero =>
      simp [explicitPathWeight]
  | succ ell ih =>
      rcases code with ⟨u, tail⟩
      rw [weight_succ, ih]
      simp only [explicitPathWeight]
      rw [Fin.prod_univ_succ]
      simp only [vertex, Fin.castSucc_zero, Fin.castSucc_succ,
        Fin.cases_zero, Fin.cases_succ, vertex_zero]

end KernelPathCode

/-- Summing the weights of all recursive codes gives exactly the
endpoint-refined kernel mass. -/
theorem sum_kernelPathCode_weight_eq_finiteKernelEndpointMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) (ell : ℕ) (v w : V) :
    (∑ code : KernelPathCode V ell v w, code.weight K) =
      finiteKernelEndpointMass K ell v w := by
  induction ell generalizing v with
  | zero =>
      by_cases h : v = w
      · subst w
        letI : Unique {x : V // x = v ∧ x = v} := {
          default := ⟨v, rfl, rfl⟩
          uniq x := Subtype.ext x.2.1
        }
        simp [KernelPathCode, KernelPathCode.weight,
          finiteKernelEndpointMass]
      · letI : IsEmpty {x : V // x = v ∧ x = w} :=
          ⟨fun x => h (x.2.1.symm.trans x.2.2)⟩
        simp [KernelPathCode, KernelPathCode.weight,
          finiteKernelEndpointMass, h]
  | succ ell ih =>
      change
        (∑ code : Σ u : V, KernelPathCode V ell u w,
            K v code.1 * code.2.weight K) =
          ∑ u, K v u * finiteKernelEndpointMass K ell u w
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro u hu
      change
        (∑ tail : KernelPathCode V ell u w, K v u * tail.weight K) =
          K v u * finiteKernelEndpointMass K ell u w
      rw [← Finset.mul_sum, ih u]

/-! ## All positive lengths up to a cutoff -/

/-- Codes for positive paths of lengths `1, ..., L` from `v` to `w`.

The `Fin L` coordinate is the length minus one. -/
abbrev PositiveKernelPathCode (V : Type*) (L : ℕ) (v w : V) : Type _ :=
  Σ ell : Fin L, KernelPathCode V (ell.1 + 1) v w

namespace PositiveKernelPathCode

/-- Length of a positive path code. -/
def length {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) : ℕ :=
  code.1.1 + 1

/-- Vertex function of a positive path code. -/
def vertex {V : Type*} {L : ℕ} {v w : V}
    (code : PositiveKernelPathCode V L v w) :
    Fin (code.length + 1) → V :=
  code.2.vertex

/-- Product weight of a positive path code. -/
def weight {V : Type*} (K : V → V → ℝ≥0∞)
    {L : ℕ} {v w : V} (code : PositiveKernelPathCode V L v w) : ℝ≥0∞ :=
  code.2.weight K

@[simp]
theorem weight_eq_explicitPathWeight
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞)
    {L : ℕ} {v w : V} (code : PositiveKernelPathCode V L v w) :
    code.weight K = explicitPathWeight K code.vertex :=
  KernelPathCode.weight_eq_explicitPathWeight K code.2

end PositiveKernelPathCode

/-- The total weight of all positive path codes up to length `L` is exactly
the endpoint-resolved positive walk kernel. -/
theorem sum_positiveKernelPathCode_weight_eq_finitePositiveWalkKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) (L : ℕ) (v w : V) :
    (∑ code : PositiveKernelPathCode V L v w, code.weight K) =
      finitePositiveWalkKernel K L v w := by
  rw [Fintype.sum_sigma]
  simp only [PositiveKernelPathCode.weight]
  simp_rw [sum_kernelPathCode_weight_eq_finiteKernelEndpointMass]
  rw [Fin.sum_univ_eq_sum_range
    (fun ell => finiteKernelEndpointMass K (ell + 1) v w)]
  unfold finitePositiveWalkKernel
  rfl

/-! ## Endpoint summation -/

/-- Summing the endpoint-refined mass over all terminal vertices recovers the
scalar finite walk mass. -/
theorem sum_finiteKernelEndpointMass_eq_finiteKernelWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) (ell : ℕ) (v : V) :
    (∑ w, finiteKernelEndpointMass K ell v w) =
      finiteKernelWalkMass K ell v := by
  induction ell generalizing v with
  | zero =>
      simp [finiteKernelEndpointMass, finiteKernelWalkMass]
  | succ ell ih =>
      simp only [finiteKernelEndpointMass, finiteKernelWalkMass]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [← Finset.mul_sum, ih u]

#print axioms sum_kernelPathCode_weight_eq_finiteKernelEndpointMass
#print axioms sum_positiveKernelPathCode_weight_eq_finitePositiveWalkKernel
#print axioms sum_finiteKernelEndpointMass_eq_finiteKernelWalkMass

end

end Erdos625
