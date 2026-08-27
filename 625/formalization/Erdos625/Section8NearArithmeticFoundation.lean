import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

/-!
# Section VIII near-window arithmetic

This module records only the transparent finite definitions used in the
near-containment part of Lemma 8.3.  It deliberately does not define a
completion law, a middle expectation, or an encoding of physical skeletons;
those require additional canonical-fibre structure.

The two finite arithmetic lemmas are proved in the pinned Lean toolchain.
-/

namespace Erdos625

open scoped ENNReal

/-- The integer cutoff equivalent to the strict inequality `e < m / 4` for
a positive natural endpoint size `m`. -/
def nearCut (m : ℕ) : ℕ :=
  (m - 1) / 4

/-- Exact natural-number form of the strict rational inequality `e < m / 4`.
The positivity hypothesis is necessary at `m = 0`. -/
theorem nearCut_le_iff_four_mul_lt (m e : ℕ) (hm : 0 < m) :
    e ≤ nearCut m ↔ 4 * e < m := by
  unfold nearCut
  omega

/-- The smaller endpoint size of a row/column cell. -/
def smallerSlotSize
    {A B : Type*} (row : A → ℕ) (col : B → ℕ) : A → B → ℕ :=
  fun a b => min (row a) (col b)

/-- A feasible multiplicity is near its smaller endpoint when its deficit is
inside the explicit quarter-window. -/
def NearEntry (m j : ℕ) : Prop :=
  j ≤ m ∧ m - j ≤ nearCut m

/-- Near-window membership is decidable by its two natural-number
inequalities. -/
instance instDecidableNearEntry (m j : ℕ) : Decidable (NearEntry m j) := by
  unfold NearEntry
  infer_instance

/-- A nonzero high entry outside the near window. -/
def MiddleEntry (m j : ℕ) : Prop :=
  j ≠ 0 ∧ ¬ NearEntry m j

/-- The exact global denominator ratio obtained when total demand is lowered
from `J₀` to `J₀ - Q`. -/
noncomputable def denominatorLoss (n J₀ Q : ℕ) : ENNReal :=
  (n.descFactorial J₀ : ENNReal) /
    (n.descFactorial (J₀ - Q) : ENNReal)

/-- The denominator loss is exactly the final `Q` falling-factorial factors
and is bounded by `n ^ Q`.  The feasibility assumptions make the cancelled
denominator positive, including the boundary case `Q = 0`. -/
theorem denominatorLoss_eq_falling_and_le_pow
    (n J₀ Q : ℕ) (hQ : Q ≤ J₀) (hJ₀ : J₀ ≤ n) :
    denominatorLoss n J₀ Q =
        ((n - J₀ + Q).descFactorial Q : ENNReal) ∧
      denominatorLoss n J₀ Q ≤ (n : ENNReal) ^ Q := by
  set d := n.descFactorial (J₀ - Q)
  set f := (n - J₀ + Q).descFactorial Q
  have hmul : (n.descFactorial J₀ : ENNReal) = (d * f : ENNReal) := by
    rw_mod_cast [← Nat.descFactorial_mul_descFactorial]
    rw [show n - (J₀ - Q) = n - J₀ + Q by omega]
    · rw [Nat.sub_sub_self hQ, mul_comm]
    · omega
  have heq : denominatorLoss n J₀ Q = f := by
    have hd0 : (d : ENNReal) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt (Nat.descFactorial_pos.mpr (by omega) : 0 < d))
    have hdtop : (d : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top d
    unfold denominatorLoss
    rw [eq_comm]
    apply (ENNReal.eq_div_iff hd0 hdtop).2
    exact hmul.symm
  refine ⟨heq, ?_⟩
  rw [heq]
  exact mod_cast Nat.descFactorial_le_pow _ _ |>.trans
    (Nat.pow_le_pow_left (by omega) _)

end Erdos625
