import Erdos625.Section9CyclePolymerBound
import Erdos625.Section9TraversalKernel

/-!
# Matching traversal bridge for Section IX

This module proves the finite operator-algebra bridge used after cutting a
mixed simple cycle at its matching edges.  The matching traversal is a partial
permutation with row norm at most one, so composing a residual-block kernel
with it does not introduce a new factor of `|M|`.  Marking and orienting the
first matching edge costs exactly `2 * |M|`, once, and the remaining finite
block-walk sum is bounded by a geometric series.

This is deliberately not the full cycle-to-walk theorem.  In particular, it
does not construct the positive residual-walk kernel from cell weights or the
injective, weight-preserving code from simple cycles to the relaxed block
walks below.  Those are the remaining combinatorial obligations in
manuscript (9.17)--(9.18).
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-- Symmetric zero-one traversal kernel of the distinguished matching. -/
def matchingTraversalKernel
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) : A ⊕ B → A ⊕ B → ℝ≥0∞
  | Sum.inl a, Sum.inr b => if (a, b) ∈ M then 1 else 0
  | Sum.inr b, Sum.inl a => if (a, b) ∈ M then 1 else 0
  | _, _ => 0

/-- A genuine bipartite matching defines a partial permutation: every row of
its traversal kernel has mass at most one. -/
theorem matchingTraversalKernel_rowSum_le_one
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M) :
    ∀ v, ∑ w, matchingTraversalKernel M v w ≤ 1 := by
  intro v
  rcases v with a | b
  · have hcard :
        (Finset.univ.filter (fun b => (a, b) ∈ M)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro b₁ hb₁ b₂ hb₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
      exact hM.1 a b₁ b₂ hb₁ hb₂
    rw [Fintype.sum_sum_type]
    simp only [matchingTraversalKernel, Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, zero_add] using
      (show ((Finset.univ.filter (fun b => (a, b) ∈ M)).card : ℝ≥0∞) ≤ 1 by
        exact_mod_cast hcard)
  · have hcard :
        (Finset.univ.filter (fun a => (a, b) ∈ M)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a₁ ha₁ a₂ ha₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha₁ ha₂
      exact hM.2 b a₁ a₂ ha₁ ha₂
    rw [Fintype.sum_sum_type]
    simp only [matchingTraversalKernel, Finset.sum_const_zero]
    rw [← Finset.sum_filter]
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, add_zero] using
      (show ((Finset.univ.filter (fun a => (a, b) ∈ M)).card : ℝ≥0∞) ≤ 1 by
        exact_mod_cast hcard)

/-- Composition of two finite nonnegative kernels. -/
def finiteKernelComp {V : Type*} [Fintype V]
    (K P : V → V → ℝ≥0∞) (v w : V) : ℝ≥0∞ :=
  ∑ u, K v u * P u w

/-- Row norms multiply under finite kernel composition. -/
theorem finiteKernelComp_rowSum_le
    {V : Type*} [Fintype V]
    (K P : V → V → ℝ≥0∞) (r s : ℝ≥0∞)
    (hK : ∀ v, ∑ u, K v u ≤ r)
    (hP : ∀ u, ∑ w, P u w ≤ s) :
    ∀ v, ∑ w, finiteKernelComp K P v w ≤ r * s := by
  intro v
  calc
    (∑ w, finiteKernelComp K P v w) =
        ∑ u, K v u * ∑ w, P u w := by
      simp only [finiteKernelComp]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
    _ ≤ ∑ u, K v u * s := by
      apply Finset.sum_le_sum
      intro u hu
      simpa only [mul_comm] using mul_le_mul_left (hP u) (K v u)
    _ = (∑ u, K v u) * s := by rw [Finset.sum_mul]
    _ ≤ r * s := by
      simpa only [mul_comm] using mul_le_mul_right (hK v) s

/-- Traversing a residual block and then the matching preserves the residual
block row-norm bound; in particular, no fresh matching-cardinality factor is
introduced. -/
theorem residualThenMatchingKernel_rowSum_le
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (S : A ⊕ B → A ⊕ B → ℝ≥0∞) (b : ℝ≥0∞)
    (hS : ∀ v, ∑ w, S v w ≤ b) :
    ∀ v,
      ∑ w, finiteKernelComp S (matchingTraversalKernel M) v w ≤ b := by
  intro v
  simpa using
    finiteKernelComp_rowSum_le S (matchingTraversalKernel M) b 1 hS
      (matchingTraversalKernel_rowSum_le_one M hM) v

/-- Matching edges with one of their two orientations. -/
def orientedMatchingStarts
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) : Finset ((A × B) × Bool) :=
  M.product Finset.univ

@[simp]
theorem card_orientedMatchingStarts
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) :
    (orientedMatchingStarts M).card = 2 * M.card := by
  simp [orientedMatchingStarts, Nat.mul_comm]

/-- State immediately after selecting an orientation of the marked matching
edge. -/
def orientedMatchingStartState
    {A B : Type*} : ((A × B) × Bool) → A ⊕ B
  | ((a, _), true) => Sum.inl a
  | ((_, b), false) => Sum.inr b

/-- The finite relaxed block-walk enumeration costs exactly one factor
`2 * |M|`.  Later matching traversals are carried by the partial-permutation
kernel and therefore introduce no additional cardinality factor. -/
theorem orientedMatchingStarts_blockWalkMass_le_geometric
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (S : A ⊕ B → A ⊕ B → ℝ≥0∞) (b : ℝ≥0∞)
    (hS : ∀ v, ∑ w, S v w ≤ b) (L : ℕ) :
    (∑ z ∈ orientedMatchingStarts M,
        ∑ r ∈ Finset.range L,
          finiteKernelWalkMass
            (finiteKernelComp S (matchingTraversalKernel M)) (r + 1)
            (orientedMatchingStartState z)) ≤
      (((2 * M.card : ℕ) : ℝ≥0∞) * (b * (1 - b)⁻¹)) := by
  have hBlock :
      ∀ v, ∑ w, finiteKernelComp S (matchingTraversalKernel M) v w ≤ b :=
    residualThenMatchingKernel_rowSum_le M hM S b hS
  calc
    _ ≤ ∑ z ∈ orientedMatchingStarts M, b * (1 - b)⁻¹ := by
      apply Finset.sum_le_sum
      intro z hz
      exact sum_range_finiteKernelWalkMass_succ_le_geometric
        (finiteKernelComp S (matchingTraversalKernel M)) b hBlock L
        (orientedMatchingStartState z)
    _ = (((2 * M.card : ℕ) : ℝ≥0∞) * (b * (1 - b)⁻¹)) := by
      simp

/-- The positive-walk ratio `b = tau / (1 - tau)` is strictly below one
under the manuscript's quantitative assumption `tau < 1/3`. -/
theorem residualWalkRatio_lt_one
    (tau : ℝ≥0∞) (htau : tau < (1 / 3 : ℝ≥0∞)) :
    tau * (1 - tau)⁻¹ < 1 := by
  have htau_one : tau < 1 := htau.trans (by norm_num)
  have hdenom : 0 < 1 - tau := tsub_pos_iff_lt.mpr htau_one
  have hsum : tau + tau < 1 := by
    calc
      tau + tau < (1 / 3 : ℝ≥0∞) + (1 / 3 : ℝ≥0∞) :=
        ENNReal.add_lt_add htau htau
      _ < 1 := by
        have hthird :
            ((↑((1 : NNReal) / (3 : NNReal)) : ENNReal)) =
              (1 / 3 : ENNReal) := by
          exact ENNReal.coe_div (p := 1) (r := 3) (by norm_num)
        rw [← hthird]
        norm_cast
        norm_num
  rw [← div_eq_mul_inv]
  exact (ENNReal.div_lt_iff (Or.inl hdenom.ne') (Or.inl (by simp))).mpr
    (by simpa using (lt_tsub_iff_right.mpr hsum))

/-- Finite algebraic form of (9.17)--(9.18) after a positive residual-block
kernel has been constructed.  The missing cycle-cutting injection is not an
assumption or conclusion of this theorem. -/
theorem finite_relaxed_matchingTraversal_enumeration
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (hM : IsBipartiteMatching M)
    (tau : ℝ≥0∞) (htau : tau < (1 / 3 : ℝ≥0∞))
    (S : A ⊕ B → A ⊕ B → ℝ≥0∞)
    (hS : ∀ v, ∑ w, S v w ≤ tau * (1 - tau)⁻¹)
    (L : ℕ) :
    let b := tau * (1 - tau)⁻¹
    b < 1 ∧
      (∑ z ∈ orientedMatchingStarts M,
          ∑ r ∈ Finset.range L,
            finiteKernelWalkMass
              (finiteKernelComp S (matchingTraversalKernel M)) (r + 1)
              (orientedMatchingStartState z)) ≤
        (((2 * M.card : ℕ) : ℝ≥0∞) * (b * (1 - b)⁻¹)) := by
  dsimp only
  exact ⟨residualWalkRatio_lt_one tau htau,
    orientedMatchingStarts_blockWalkMass_le_geometric M hM S
      (tau * (1 - tau)⁻¹) hS L⟩

#print axioms finite_relaxed_matchingTraversal_enumeration

end

end Erdos625
