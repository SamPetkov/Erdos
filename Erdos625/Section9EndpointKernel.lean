import Erdos625.Section9TraversalKernel

/-!
# Section 9: endpoint-refined positive walk kernels

The scalar walk mass in `Section9TraversalKernel` forgets the endpoint.  The
cycle-cutting argument also needs the endpoint-resolved kernel obtained by
summing all positive path lengths up to a finite cutoff.  This module proves
that summing over endpoints recovers the scalar walk mass and hence inherits
the same exact geometric row bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Endpoint-resolved mass of all length-`ell` walks. -/
def finiteKernelEndpointMass {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) : ℕ → V → V → ℝ≥0∞
  | 0, v, w => if v = w then 1 else 0
  | ell + 1, v, w => ∑ u, K v u * finiteKernelEndpointMass K ell u w

/-- The endpoint kernel obtained by summing lengths `1, ..., L`. -/
def finitePositiveWalkKernel {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) (L : ℕ) (v w : V) : ℝ≥0∞ :=
  ∑ ell ∈ Finset.range L, finiteKernelEndpointMass K (ell + 1) v w

/-- The endpoint-refined positive kernel has row mass bounded by the exact
finite geometric relaxation `tau * (1 - tau)⁻¹`. -/
theorem finitePositiveWalkKernel_rowSum_le_geometric
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (L : ℕ) :
    (∀ ell v,
        (∑ w, finiteKernelEndpointMass K ell v w) =
          finiteKernelWalkMass K ell v) ∧
      ∀ v, ∑ w, finitePositiveWalkKernel K L v w ≤
        tau * (1 - tau)⁻¹ := by
  have hEndpoint : ∀ ell v,
      (∑ w, finiteKernelEndpointMass K ell v w) =
        finiteKernelWalkMass K ell v := by
    intro ell v
    induction ell generalizing v with
    | zero => simp [finiteKernelEndpointMass, finiteKernelWalkMass]
    | succ ell ih =>
        simp only [finiteKernelEndpointMass, finiteKernelWalkMass]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        rw [← Finset.mul_sum, ih u]
  refine ⟨hEndpoint, ?_⟩
  intro v
  calc
    (∑ w, finitePositiveWalkKernel K L v w) =
        ∑ ell ∈ Finset.range L,
          ∑ w, finiteKernelEndpointMass K (ell + 1) v w := by
      simp only [finitePositiveWalkKernel]
      rw [Finset.sum_comm]
    _ = ∑ ell ∈ Finset.range L,
          finiteKernelWalkMass K (ell + 1) v := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [hEndpoint]
    _ ≤ ∑ ell ∈ Finset.range L, tau ^ (ell + 1) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact finiteKernelWalkMass_le_pow K tau hRow (ell + 1) v
    _ ≤ tau * (1 - tau)⁻¹ := sum_range_pow_succ_le_geometric tau L

#print axioms finitePositiveWalkKernel_rowSum_le_geometric

end

end Erdos625
