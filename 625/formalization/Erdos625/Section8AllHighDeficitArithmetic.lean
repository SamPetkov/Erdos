import Erdos625.Section8NearArithmeticFoundation
import Mathlib.Tactic

/-!
# Section VIII: one deficit parametrization for the full high range

A high cell of smaller endpoint size `m` has multiplicity `j` above the global
cutoff `a / 2`.  Writing `e = m - j` parametrizes every such multiplicity by a
single endpoint deficit.  This file records the exact finite arithmetic needed
to replace the near/middle split by one all-deficit sum.

The final theorem also supplies a deliberately coarse exponent budget with
coefficient `2/3`.  It is weaker than the sharper `3/4` estimate in the review
note, but already yields a geometric all-deficit sum of the required
asymptotic scale and has a substantially simpler integer proof.
-/

namespace Erdos625

set_option autoImplicit false

/-- Largest endpoint deficit compatible with the strict high-cell cutoff. -/
def allHighDeficitCut (a m : Nat) : Nat := m - (a / 2 + 1)

/-- A multiplicity above the global cutoff is also above the half-size cutoff
of every smaller endpoint size `m <= a`. -/
theorem highMultiplicity_above_half_size
    (a m j : Nat) (hm : m <= a) (hj : a / 2 < j) :
    m / 2 < j := by
  have hhalf : m / 2 <= a / 2 := Nat.div_le_div_right hm
  exact lt_of_le_of_lt hhalf hj

/-- The endpoint deficit of a high multiplicity is strictly below half the
smaller endpoint size. -/
theorem highMultiplicity_deficit_twice_lt
    (a m j : Nat) (hm : m <= a) (hj : a / 2 < j) (hjm : j <= m) :
    2 * (m - j) < m := by
  have hjhalf := highMultiplicity_above_half_size a m j hm hj
  omega

/-- Every strict high multiplicity yields a deficit in the single finite window
`0, ..., allHighDeficitCut a m`. -/
theorem endpointDeficit_le_allHighDeficitCut
    (a m j : Nat) (hj : a / 2 < j) (hjm : j <= m) :
    m - j <= allHighDeficitCut a m := by
  unfold allHighDeficitCut
  omega

/-- Conversely, every deficit in the all-high window reconstructs a strict high
multiplicity, provided the endpoint itself lies above the cutoff. -/
theorem allHighDeficit_reconstructs_highMultiplicity
    (a m e : Nat) (hmHigh : a / 2 < m)
    (he : e <= allHighDeficitCut a m) :
    a / 2 < m - e := by
  unfold allHighDeficitCut at he
  omega

/-- Subtracting and then restoring a feasible endpoint deficit recovers the
endpoint size exactly. -/
theorem endpointDeficit_reconstruction
    (m j : Nat) (hjm : j <= m) :
    m - (m - j) = j := by
  omega

/-- For a fixed endpoint size, the deficit encoding is injective on feasible
multiplicities. -/
theorem endpointDeficit_injective
    (m j₁ j₂ : Nat) (hj₁ : j₁ <= m) (hj₂ : j₂ <= m)
    (hdef : m - j₁ = m - j₂) :
    j₁ = j₂ := by
  omega

/-- A deficit below half the endpoint pays at least two thirds of the endpoint
size in the local binary exponent:

`e * floor(2m/3) <= e*m - e*(e+1)/2`.

This weaker replacement for the sharper `floor((3m-1)/4)` budget is sufficient
for a uniform geometric all-high-deficit bound and avoids parity-sensitive
quarter arithmetic. -/
theorem highDeficit_twoThird_exponent_budget
    (m e : Nat) (hhalf : 2 * e < m) :
    e * ((2 * m) / 3) <= e * m - e * (e + 1) / 2 := by
  by_cases he : e = 0
  · simp [he]
  have hepos : 0 < e := Nat.pos_of_ne_zero he
  have hlinear : 3 * (e + 1) <= 2 * m := by
    omega
  have hmul : 3 * (e * (e + 1)) <= 2 * (e * m) := by
    nlinarith [Nat.mul_le_mul_left e hlinear]
  have hdiv := Nat.div_mul_le_self (e * (e + 1)) 2
  have hpenalty : 3 * (e * (e + 1) / 2) <= e * m := by
    nlinarith
  have hpenalty_le : e * (e + 1) / 2 <= e * m := by
    omega
  have hsub :
      (e * m - e * (e + 1) / 2) + e * (e + 1) / 2 = e * m :=
    Nat.sub_add_cancel hpenalty_le
  have hthird := Nat.div_mul_le_self (2 * m) 3
  have hbudget : 3 * (e * ((2 * m) / 3)) <= 2 * (e * m) := by
    nlinarith [Nat.mul_le_mul_left e hthird]
  have hexponent :
      2 * (e * m) <= 3 * (e * m - e * (e + 1) / 2) := by
    omega
  omega

#print axioms highMultiplicity_above_half_size
#print axioms highMultiplicity_deficit_twice_lt
#print axioms endpointDeficit_le_allHighDeficitCut
#print axioms allHighDeficit_reconstructs_highMultiplicity
#print axioms endpointDeficit_reconstruction
#print axioms endpointDeficit_injective
#print axioms highDeficit_twoThird_exponent_budget

end Erdos625
