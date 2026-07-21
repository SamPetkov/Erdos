import Erdos625.ExtendedGaussianEntropyTransport

/-!
# Direct `S₊` entropy primal

This module states the manuscript's limiting `S₊` variational problem using
prefix limits on the deficit coordinates `{-1, 0, 1, ...}`.  Admissibility
contains only nonnegativity, unit-mass, target-moment, and entropy-limit
conditions.  In particular, it does not build a dual inequality, a selected
tilt, or an optimizer into the definition.
-/

open Filter
open scoped Topology

namespace Erdos625

noncomputable section

/-- A directly admissible limiting `S₊` profile with exceptional mass at
deficit `-1` and natural-coordinate masses `p d`. -/
structure SPlusPrimalProfile
    (target value exceptional : ℝ) (p : ℕ → ℝ) : Prop where
  exceptional_nonneg : 0 ≤ exceptional
  natural_nonneg : ∀ d, 0 ≤ p d
  mass_limit : Tendsto (extendedGaussianMassTruncation exceptional p)
    atTop (nhds 1)
  moment_limit : Tendsto (extendedGaussianMomentTruncation exceptional p)
    atTop (nhds target)
  entropy_limit : Tendsto (extendedGaussianEntropyTruncation q exceptional p)
    atTop (nhds value)

/-- Entropy values realized by direct manuscript `S₊` profiles at a fixed
target moment. -/
def sPlusPrimalCandidateSet (target : ℝ) : Set ℝ :=
  {value | ∃ exceptional p,
    SPlusPrimalProfile target value exceptional p}

/-- The direct limiting `S₊` primal entropy supremum. -/
noncomputable def sPlusPrimalEntropyValue (target : ℝ) : ℝ :=
  sSup (sPlusPrimalCandidateSet target)

end

end Erdos625
