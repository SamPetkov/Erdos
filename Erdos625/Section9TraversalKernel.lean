import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Finite traversal kernels for Section IX

This module isolates the deterministic kernel estimate used in manuscript
(9.16)--(9.18).  For a finite nonnegative kernel whose row sums are at most
`tau`, the total weight of all length-`ell` walks from any fixed vertex is at
most `tau ^ ell`.  A bipartite kernel inherits this hypothesis from separate
row and column bounds on its cell weights.

The final lemmas sum positive walk lengths over a finite cutoff and compare
them with the exact extended-nonnegative geometric series
`tau * (1 - tau)⁻¹`.  These statements formalize the finite traversal
estimate and its geometric relaxation only.  They do not assert the
cycle-to-walk injection, the marked-cycle count, or any probabilistic bound.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## Walk mass of a finite nonnegative kernel -/

/-- Total kernel weight of all length-`ell` walks starting at `v`.

The recursion sums over the first step.  At length zero there is one empty
walk, of weight one. -/
def finiteKernelWalkMass {V : Type*} [Fintype V]
    (K : V → V → ℝ≥0∞) : ℕ → V → ℝ≥0∞
  | 0, _ => 1
  | ell + 1, v => ∑ w, K v w * finiteKernelWalkMass K ell w

@[simp]
theorem finiteKernelWalkMass_zero {V : Type*} [Fintype V]
    (K : V → V → ℝ≥0∞) (v : V) :
    finiteKernelWalkMass K 0 v = 1 := rfl

@[simp]
theorem finiteKernelWalkMass_succ {V : Type*} [Fintype V]
    (K : V → V → ℝ≥0∞) (ell : ℕ) (v : V) :
    finiteKernelWalkMass K (ell + 1) v =
      ∑ w, K v w * finiteKernelWalkMass K ell w := rfl

/-- A row-sum bound propagates multiplicatively along every finite walk. -/
theorem finiteKernelWalkMass_le_pow
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (ell : ℕ) (v : V) :
    finiteKernelWalkMass K ell v ≤ tau ^ ell := by
  induction ell generalizing v with
  | zero => simp
  | succ ell ih =>
      calc
        finiteKernelWalkMass K (ell + 1) v =
            ∑ w, K v w * finiteKernelWalkMass K ell w := rfl
        _ ≤ ∑ w, K v w * tau ^ ell := by
          apply Finset.sum_le_sum
          intro w hw
          exact mul_le_mul_right (ih w) (K v w)
        _ = (∑ w, K v w) * tau ^ ell := by
          rw [Finset.sum_mul]
        _ ≤ tau * tau ^ ell :=
          mul_le_mul_left (hRow v) (tau ^ ell)
        _ = tau ^ (ell + 1) := by
          rw [pow_succ]
          ac_rfl

/-- Summing over a finite set of marked starting vertices costs exactly its
cardinality and no additional power of the walk-length parameter. -/
theorem sum_marked_finiteKernelWalkMass_le
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (S : Finset V) (ell : ℕ) :
    (∑ v ∈ S, finiteKernelWalkMass K ell v) ≤
      (S.card : ℝ≥0∞) * tau ^ ell := by
  calc
    (∑ v ∈ S, finiteKernelWalkMass K ell v) ≤
        ∑ v ∈ S, tau ^ ell := by
      apply Finset.sum_le_sum
      intro v hv
      exact finiteKernelWalkMass_le_pow K tau hRow ell v
    _ = (S.card : ℝ≥0∞) * tau ^ ell := by simp

/-! ## The bipartite cell kernel -/

/-- Symmetric kernel on the disjoint union induced by bipartite cell weights.
It vanishes on pairs of vertices in the same part. -/
def bipartiteCellKernel {A B : Type*} (q : A → B → ℝ≥0∞) :
    A ⊕ B → A ⊕ B → ℝ≥0∞
  | Sum.inl a, Sum.inr b => q a b
  | Sum.inr b, Sum.inl a => q a b
  | _, _ => 0

@[simp]
theorem sum_bipartiteCellKernel_inl
    {A B : Type*} [Fintype A] [Fintype B]
    (q : A → B → ℝ≥0∞) (a : A) :
    ∑ v, bipartiteCellKernel q (Sum.inl a) v = ∑ b, q a b := by
  rw [Fintype.sum_sum_type]
  simp [bipartiteCellKernel]

@[simp]
theorem sum_bipartiteCellKernel_inr
    {A B : Type*} [Fintype A] [Fintype B]
    (q : A → B → ℝ≥0∞) (b : B) :
    ∑ v, bipartiteCellKernel q (Sum.inr b) v = ∑ a, q a b := by
  rw [Fintype.sum_sum_type]
  simp [bipartiteCellKernel]

/-- Separate row and column bounds give the row-sum norm bound for the
symmetric bipartite kernel. -/
theorem bipartiteCellKernel_rowSum_le
    {A B : Type*} [Fintype A] [Fintype B]
    (q : A → B → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau) :
    ∀ v, ∑ w, bipartiteCellKernel q v w ≤ tau := by
  intro v
  rcases v with a | b
  · rw [sum_bipartiteCellKernel_inl]
    exact hRow a
  · rw [sum_bipartiteCellKernel_inr]
    exact hColumn b

/-- Bipartite row and column bounds control all alternating walk weights. -/
theorem bipartiteCellKernel_walkMass_le_pow
    {A B : Type*} [Fintype A] [Fintype B]
    (q : A → B → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau)
    (ell : ℕ) (v : A ⊕ B) :
    finiteKernelWalkMass (bipartiteCellKernel q) ell v ≤ tau ^ ell :=
  finiteKernelWalkMass_le_pow (bipartiteCellKernel q) tau
    (bipartiteCellKernel_rowSum_le q tau hRow hColumn) ell v

/-! ## Finite geometric relaxation -/

/-- Every finite initial segment of the positive-power geometric series is
bounded by its exact `ENNReal` infinite sum.  The right side is finite when
`tau < 1`; for `tau ≥ 1` it is top, so the inequality remains valid but is
quantitatively vacuous. -/
theorem sum_range_pow_succ_le_geometric (tau : ℝ≥0∞) (L : ℕ) :
    (∑ ell ∈ Finset.range L, tau ^ (ell + 1)) ≤
      tau * (1 - tau)⁻¹ := by
  calc
    (∑ ell ∈ Finset.range L, tau ^ (ell + 1)) ≤
        ∑' ell : ℕ, tau ^ (ell + 1) := ENNReal.sum_le_tsum _
    _ = tau * (1 - tau)⁻¹ := ENNReal.tsum_geometric_add_one tau

/-- Finite relaxation of the even-length geometric tail beginning at length
four, with exponents `4, 6, 8, ...`.  This is the scalar series in the
residual-only cycle estimate (9.16).  It is quantitative when `tau < 1`. -/
theorem sum_range_pow_even_add_four_le_geometric
    (tau : ℝ≥0∞) (L : ℕ) :
    (∑ k ∈ Finset.range L, tau ^ (2 * k + 4)) ≤
      tau ^ 4 * (1 - tau ^ 2)⁻¹ := by
  calc
    (∑ k ∈ Finset.range L, tau ^ (2 * k + 4)) =
        tau ^ 4 * ∑ k ∈ Finset.range L, (tau ^ 2) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← pow_mul]
      rw [← pow_add]
      congr 1
      omega
    _ ≤ tau ^ 4 * ∑' k : ℕ, (tau ^ 2) ^ k := by
      exact mul_le_mul_right (ENNReal.sum_le_tsum (Finset.range L)) (tau ^ 4)
    _ = tau ^ 4 * (1 - tau ^ 2)⁻¹ := by
      rw [ENNReal.tsum_geometric]

/-- Marked finite walks of even length at least four satisfy the scalar tail
from (9.16), with one cardinality factor for the selected starting vertex. -/
theorem sum_marked_range_finiteKernelWalkMass_even_add_four_le_geometric
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (S : Finset V) (L : ℕ) :
    (∑ v ∈ S, ∑ k ∈ Finset.range L,
        finiteKernelWalkMass K (2 * k + 4) v) ≤
      (S.card : ℝ≥0∞) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) := by
  calc
    (∑ v ∈ S, ∑ k ∈ Finset.range L,
        finiteKernelWalkMass K (2 * k + 4) v) ≤
        ∑ v ∈ S, ∑ k ∈ Finset.range L, tau ^ (2 * k + 4) := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro k hk
      exact finiteKernelWalkMass_le_pow K tau hRow (2 * k + 4) v
    _ = (S.card : ℝ≥0∞) *
        (∑ k ∈ Finset.range L, tau ^ (2 * k + 4)) := by simp
    _ ≤ (S.card : ℝ≥0∞) * (tau ^ 4 * (1 - tau ^ 2)⁻¹) :=
      mul_le_mul_right (sum_range_pow_even_add_four_le_geometric tau L)
        (S.card : ℝ≥0∞)

/-- A finite sum over all positive walk lengths is controlled by the geometric
kernel mass from manuscript (9.17). -/
theorem sum_range_finiteKernelWalkMass_succ_le_geometric
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (L : ℕ) (v : V) :
    (∑ ell ∈ Finset.range L, finiteKernelWalkMass K (ell + 1) v) ≤
      tau * (1 - tau)⁻¹ := by
  calc
    (∑ ell ∈ Finset.range L, finiteKernelWalkMass K (ell + 1) v) ≤
        ∑ ell ∈ Finset.range L, tau ^ (ell + 1) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact finiteKernelWalkMass_le_pow K tau hRow (ell + 1) v
    _ ≤ tau * (1 - tau)⁻¹ := sum_range_pow_succ_le_geometric tau L

/-- Finite positive-length traversals from a set of marked starts cost one
cardinality factor.  To apply this to the `2h` term in manuscript (9.18), one
must separately construct the oriented matching-edge start set and prove that
its post-cut transition kernel has the required row bound. -/
theorem sum_marked_range_finiteKernelWalkMass_succ_le_geometric
    {V : Type*} [Fintype V] (K : V → V → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ v, ∑ w, K v w ≤ tau) (S : Finset V) (L : ℕ) :
    (∑ v ∈ S, ∑ ell ∈ Finset.range L,
        finiteKernelWalkMass K (ell + 1) v) ≤
      (S.card : ℝ≥0∞) * (tau * (1 - tau)⁻¹) := by
  calc
    (∑ v ∈ S, ∑ ell ∈ Finset.range L,
        finiteKernelWalkMass K (ell + 1) v) ≤
        ∑ v ∈ S, tau * (1 - tau)⁻¹ := by
      apply Finset.sum_le_sum
      intro v hv
      exact sum_range_finiteKernelWalkMass_succ_le_geometric K tau hRow L v
    _ = (S.card : ℝ≥0∞) * (tau * (1 - tau)⁻¹) := by simp

/-- Bipartite form of the finite positive-length traversal bound. -/
theorem sum_range_bipartiteCellKernel_walkMass_succ_le_geometric
    {A B : Type*} [Fintype A] [Fintype B]
    (q : A → B → ℝ≥0∞) (tau : ℝ≥0∞)
    (hRow : ∀ a, ∑ b, q a b ≤ tau)
    (hColumn : ∀ b, ∑ a, q a b ≤ tau)
    (L : ℕ) (v : A ⊕ B) :
    (∑ ell ∈ Finset.range L,
        finiteKernelWalkMass (bipartiteCellKernel q) (ell + 1) v) ≤
      tau * (1 - tau)⁻¹ :=
  sum_range_finiteKernelWalkMass_succ_le_geometric
    (bipartiteCellKernel q) tau
    (bipartiteCellKernel_rowSum_le q tau hRow hColumn) L v

end

end Erdos625
