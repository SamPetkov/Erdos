import Erdos625.Section9EndpointKernel

/-!
# Section 9: explicit paths as kernel summands

Each residual path appearing in a cycle cut contributes one nonnegative term
to the endpoint kernel.  Likewise, every explicit sequence of block states is
one term of the scalar walk-mass recursion.  These are pointwise weight
transfers; no cycle encoding or aggregate enumeration is assumed.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Weight of one explicitly specified length-`ell` vertex path. -/
def explicitPathWeight {V : Type*} [Fintype V]
    (K : V → V → ℝ≥0∞) {ell : ℕ}
    (vertex : Fin (ell + 1) → V) : ℝ≥0∞ :=
  ∏ i : Fin ell, K (vertex i.castSucc) (vertex i.succ)

/-- Weight of one explicitly specified chain starting at `v`. -/
def explicitChainWeight {V : Type*}
    (K : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 1
  | v, w :: tail => K v w * explicitChainWeight K w tail

/-- An explicit path is one summand of its endpoint kernel, a positive path
of length at most `L` is one summand of the positive kernel, and an explicit
state chain is one summand of the scalar walk mass. -/
theorem explicit_terms_le_kernel_masses
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : V → V → ℝ≥0∞) :
    (∀ (ell : ℕ) (vertex : Fin (ell + 1) → V),
      explicitPathWeight K vertex ≤
        finiteKernelEndpointMass K ell (vertex 0) (vertex (Fin.last ell))) ∧
    (∀ (L ell : ℕ), 0 < ell → ell ≤ L →
      ∀ vertex : Fin (ell + 1) → V,
        explicitPathWeight K vertex ≤
          finitePositiveWalkKernel K L (vertex 0) (vertex (Fin.last ell))) ∧
    (∀ (v : V) (tail : List V),
      explicitChainWeight K v tail ≤
        finiteKernelWalkMass K tail.length v) := by
  have hPath : ∀ (ell : ℕ) (vertex : Fin (ell + 1) → V),
      explicitPathWeight K vertex ≤
        finiteKernelEndpointMass K ell (vertex 0) (vertex (Fin.last ell)) := by
    intro ell vertex
    induction' ell with ell ih
    · simp +decide [explicitPathWeight, finiteKernelEndpointMass]
    · have hsplit : explicitPathWeight K vertex =
          K (vertex 0) (vertex 1) *
            explicitPathWeight K (fun i : Fin (ell + 1) => vertex i.succ) := by
        simpa [explicitPathWeight, Fin.castSucc_succ] using
          (Fin.prod_univ_succ
            (fun i : Fin (ell + 1) =>
              K (vertex i.castSucc) (vertex i.succ)))
      rw [hsplit]
      refine (mul_le_mul_right
        (ih (fun i : Fin (ell + 1) => vertex i.succ))
        (K (vertex 0) (vertex 1))).trans ?_
      simpa [finiteKernelEndpointMass, Fin.succ_last] using
        (Finset.single_le_sum
          (s := Finset.univ)
          (f := fun u : V =>
            K (vertex 0) u *
              finiteKernelEndpointMass K ell u (vertex (Fin.last (ell + 1))))
          (fun u _ => bot_le) (Finset.mem_univ (vertex 1)))
  have hPositive : ∀ (L ell : ℕ), 0 < ell → ell ≤ L →
      ∀ vertex : Fin (ell + 1) → V,
        explicitPathWeight K vertex ≤
          finitePositiveWalkKernel K L (vertex 0) (vertex (Fin.last ell)) := by
    intro L ell hpos hle vertex
    refine (hPath ell vertex).trans ?_
    unfold finitePositiveWalkKernel
    have hmem : ell - 1 ∈ Finset.range L :=
      Finset.mem_range.mpr
        (show ell - 1 < L from
          lt_of_lt_of_le (Nat.pred_lt hpos.ne') hle)
    have hsingle :
        finiteKernelEndpointMass K ((ell - 1) + 1)
            (vertex 0) (vertex (Fin.last ell)) ≤
          ∑ j ∈ Finset.range L,
            finiteKernelEndpointMass K (j + 1)
              (vertex 0) (vertex (Fin.last ell)) :=
      Finset.single_le_sum
        (s := Finset.range L)
        (f := fun j => finiteKernelEndpointMass K (j + 1)
          (vertex 0) (vertex (Fin.last ell)))
        (fun j _ => bot_le) hmem
    simpa only [Nat.sub_add_cancel hpos] using hsingle
  have hChain : ∀ (v : V) (tail : List V),
      explicitChainWeight K v tail ≤
        finiteKernelWalkMass K tail.length v := by
    intro v tail
    induction tail generalizing v with
    | nil => rfl
    | cons w tail ih =>
        simp only [explicitChainWeight, List.length_cons,
          finiteKernelWalkMass]
        exact (mul_le_mul_right (ih w) (K v w)).trans
          (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun u : V => K v u * finiteKernelWalkMass K tail.length u)
            (fun u _ => bot_le) (Finset.mem_univ w))
  exact ⟨hPath, hPositive, hChain⟩

#print axioms explicit_terms_le_kernel_masses

end

end Erdos625
