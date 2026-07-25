import Erdos625.Section8NearArithmeticFoundation
import Mathlib.Tactic

/-!
# Section VIII: one deficit parametrization for the full high range

A high cell of smaller endpoint size `m` has multiplicity `j` above the global
cutoff `a / 2`.  Writing `e = m - j` parametrizes every such multiplicity by a
single endpoint deficit.  This file records the exact finite arithmetic needed
to replace the near/middle split by one all-deficit sum.

No weight estimate or asymptotic statement is asserted here.
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

#print axioms highMultiplicity_above_half_size
#print axioms highMultiplicity_deficit_twice_lt
#print axioms endpointDeficit_le_allHighDeficitCut
#print axioms allHighDeficit_reconstructs_highMultiplicity
#print axioms endpointDeficit_reconstruction
#print axioms endpointDeficit_injective

end Erdos625
