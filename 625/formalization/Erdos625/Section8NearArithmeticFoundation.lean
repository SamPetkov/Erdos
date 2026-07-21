import Mathlib.Data.ENNReal.BigOperators

/-!
# Section VIII near-window arithmetic

This module records only the transparent finite definitions used in the
near-containment part of Lemma 8.3.  It deliberately does not define a
completion law, a middle expectation, or an encoding of physical skeletons;
those require additional canonical-fibre structure.
-/

namespace Erdos625

open scoped ENNReal

/-- The integer cutoff equivalent to the strict inequality `e < m / 4` for
a positive natural endpoint size `m`. -/
def nearCut (m : ℕ) : ℕ :=
  (m - 1) / 4

/-- The smaller endpoint size of a row/column cell. -/
def smallerSlotSize
    {A B : Type*} (row : A → ℕ) (col : B → ℕ) : A → B → ℕ :=
  fun a b => min (row a) (col b)

/-- A feasible multiplicity is near its smaller endpoint when its deficit is
inside the explicit quarter-window. -/
def NearEntry (m j : ℕ) : Prop :=
  j ≤ m ∧ m - j ≤ nearCut m

/-- A nonzero high entry outside the near window. -/
def MiddleEntry (m j : ℕ) : Prop :=
  j ≠ 0 ∧ ¬ NearEntry m j

/-- The exact global denominator ratio obtained when total demand is lowered
from `J₀` to `J₀ - Q`. -/
noncomputable def denominatorLoss (n J₀ Q : ℕ) : ENNReal :=
  (n.descFactorial J₀ : ENNReal) /
    (n.descFactorial (J₀ - Q) : ENNReal)

end Erdos625
