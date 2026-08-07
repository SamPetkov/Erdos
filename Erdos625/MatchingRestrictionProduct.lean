import Mathlib

/-!
# Decorated skeleton weight bound (Erdős 625, Section 8)

The sum over all decorated skeletons of the product of local decoration weights
factorises as a product of one-cell sums.  Each one-cell sum is bounded by
`1 + ε ≤ exp ε`, so the whole sum is at most `exp (card ι * ε) ≤ exp (kco * ε)`.
-/

namespace Erdos625.Section8

open Finset

variable {ι : Type*} {δ : Type*}

/-- **Decorated skeleton weight bound.**  If for every cell `c` the total local
decoration weight `∑ d ∈ D c, w c d` is at most `1 + ε`, and the number of cells is at
most `kco`, then the total weight of all decorated skeletons is at most
`exp (kco * ε)`; multiplying by a nonnegative base weight `W` preserves the bound. -/
theorem matching_restriction_weighted_bound [Fintype ι] [DecidableEq ι]
    (W : ℝ) (hW : 0 ≤ W)
    (D : ι → Finset δ) (w : ι → δ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hw : ∀ c d, 0 ≤ w c d)
    (hcell : ∀ c : ι, ∑ d ∈ D c, w c d ≤ 1 + ε)
    (kco : ℕ) (hkco : Fintype.card ι ≤ kco) :
    W * ∑ S ∈ Fintype.piFinset D, ∏ c : ι, w c (S c) ≤ W * Real.exp (kco * ε) := by
  have hfac : ∑ S ∈ Fintype.piFinset D, ∏ c : ι, w c (S c)
      = ∏ c : ι, ∑ d ∈ D c, w c d := (Finset.prod_univ_sum D w).symm
  have hcell' : ∀ c : ι, ∑ d ∈ D c, w c d ≤ Real.exp ε := fun c =>
    (hcell c).trans (by simpa [add_comm] using Real.add_one_le_exp ε)
  have hnonneg : ∀ c : ι, (0:ℝ) ≤ ∑ d ∈ D c, w c d := fun c =>
    Finset.sum_nonneg fun d _ => hw c d
  have hprod : ∏ c : ι, ∑ d ∈ D c, w c d ≤ ∏ _c : ι, Real.exp ε :=
    Finset.prod_le_prod (fun c _ => hnonneg c) (fun c _ => hcell' c)
  have hcard : ∏ _c : ι, Real.exp ε = Real.exp (Fintype.card ι * ε) := by
    rw [Finset.prod_const, ← Real.exp_nat_mul, Finset.card_univ]
  have hmono : Real.exp ((Fintype.card ι : ℝ) * ε) ≤ Real.exp (kco * ε) :=
    Real.exp_le_exp.mpr (by
      have : (Fintype.card ι : ℝ) ≤ (kco : ℝ) := by exact_mod_cast hkco
      exact mul_le_mul_of_nonneg_right this hε)
  have : ∑ S ∈ Fintype.piFinset D, ∏ c : ι, w c (S c) ≤ Real.exp (kco * ε) := by
    rw [hfac]
    exact hprod.trans (hcard.le.trans hmono)
  exact mul_le_mul_of_nonneg_left this hW

end Erdos625.Section8
