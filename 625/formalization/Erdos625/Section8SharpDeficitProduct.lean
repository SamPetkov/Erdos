import Erdos625.Section8AllHighDeficitProductBound
import Mathlib.Tactic

/-!
# Section VIII: sharp cellwise product interface for all high deficits

The generic all-high product theorem previously replaced every nonzero deficit
weight by one common bound and then multiplied by the number of admissible
deficits.  That route is sufficient for the normalized second moment, but it
introduces an unnecessary factor of the phase size.

This module isolates the sharper interface actually used by the concise
manuscript proof.  First sum the complete positive-deficit fibre in each
selected physical cell; then multiply the resulting local partition functions.
The local bounds may vary from cell to cell.

No geometric-series estimate, phase asymptotic, endpoint transportation bound,
or identification with attained canonical demands is asserted here.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

set_option autoImplicit false

/-- Exact optional-deficit expansion followed by arbitrary cellwise upper
bounds on the positive-deficit sums. -/
theorem sum_nearSkeletonChoiceWeight_le_product_of_local_sums
    {Cell Deficit : Type*}
    [Fintype Cell] [Fintype Deficit] [DecidableEq Deficit]
    (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal)
    (bound : Cell → ENNReal)
    (hlocal : ∀ c, (∑ e ∈ allowed c, weight c e) ≤ bound c) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
        ∏ c, (1 + bound c) := by
  rw [sum_nearSkeletonChoiceWeight_eq_product]
  apply Finset.prod_le_prod'
  intro c _
  simpa [add_comm] using add_le_add_left (hlocal c) 1

/-- Uniform specialization of the cellwise local-sum interface. -/
theorem sum_nearSkeletonChoiceWeight_le_uniform_local_sum
    {Cell Deficit : Type*}
    [Fintype Cell] [Fintype Deficit] [DecidableEq Deficit]
    (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal)
    (sigma : ENNReal)
    (hlocal : ∀ c, (∑ e ∈ allowed c, weight c e) ≤ sigma) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
        (1 + sigma) ^ Fintype.card Cell := by
  calc
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
        nearSkeletonChoiceWeight allowed weight choice) ≤
        ∏ _c : Cell, (1 + sigma) := by
      apply sum_nearSkeletonChoiceWeight_le_product_of_local_sums
        allowed weight (fun _ => sigma)
      exact hlocal
    _ = (1 + sigma) ^ Fintype.card Cell := by simp

/-- If the complete positive-deficit fibre in cell `c` is at most `2*rho c`,
the global optional-deficit partition function retains the cellwise charges. -/
theorem sum_nearSkeletonChoiceWeight_le_cellwise_two_rho
    {Cell Deficit : Type*}
    [Fintype Cell] [Fintype Deficit] [DecidableEq Deficit]
    (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal)
    (rho : Cell → ENNReal)
    (hlocal : ∀ c, (∑ e ∈ allowed c, weight c e) ≤ 2 * rho c) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
        ∏ c, (1 + 2 * rho c) := by
  apply sum_nearSkeletonChoiceWeight_le_product_of_local_sums
    allowed weight (fun c => 2 * rho c)
  exact hlocal

/-- Uniform `2*rho` specialization.  This is the formal endpoint needed after
a finite geometric-series estimate in every selected cell. -/
theorem sum_nearSkeletonChoiceWeight_le_uniform_two_rho
    {Cell Deficit : Type*}
    [Fintype Cell] [Fintype Deficit] [DecidableEq Deficit]
    (allowed : Cell → Finset Deficit)
    (weight : Cell → Deficit → ENNReal)
    (rho : ENNReal)
    (hlocal : ∀ c, (∑ e ∈ allowed c, weight c e) ≤ 2 * rho) :
    (∑ choice : NearSkeletonChoice Cell Deficit allowed,
      nearSkeletonChoiceWeight allowed weight choice) ≤
        (1 + 2 * rho) ^ Fintype.card Cell := by
  apply sum_nearSkeletonChoiceWeight_le_uniform_local_sum
    allowed weight (2 * rho)
  exact hlocal

/-- The sharp `2*rho` local charge is never worse than the old cardinality
charge `U*rho` once every cell was allowed at least two candidate deficits. -/
theorem two_mul_ennreal_le_natCast_mul
    (U : Nat) (rho : ENNReal) (hU : 2 ≤ U) :
    2 * rho ≤ (U : ENNReal) * rho := by
  have hU' : (2 : ENNReal) ≤ (U : ENNReal) := by
    exact_mod_cast hU
  simpa [mul_comm] using mul_le_mul_right hU' rho

/-- Additive form of the comparison with the earlier uniform-cardinality
interface. -/
theorem one_add_two_mul_ennreal_le_one_add_natCast_mul
    (U : Nat) (rho : ENNReal) (hU : 2 ≤ U) :
    1 + 2 * rho ≤ 1 + (U : ENNReal) * rho := by
  simpa [add_comm] using
    add_le_add_left (two_mul_ennreal_le_natCast_mul U rho hU) 1

#print axioms sum_nearSkeletonChoiceWeight_le_product_of_local_sums
#print axioms sum_nearSkeletonChoiceWeight_le_uniform_local_sum
#print axioms sum_nearSkeletonChoiceWeight_le_cellwise_two_rho
#print axioms sum_nearSkeletonChoiceWeight_le_uniform_two_rho
#print axioms two_mul_ennreal_le_natCast_mul

end

end Erdos625
