import Erdos625.Section10CoColorablePaleyZygmundSeed

/-!
# Section X: logarithmic seed adapter

This isolated target converts the displayed logarithmic lower bound for a
strictly positive real seed probability into the exponential seed inequality
used by the uniform amplification theorem. It intentionally supplies no
probabilistic or Section IX input.
-/

namespace Erdos625

open Filter
open scoped Topology

/-- Along the full natural-number sequence, an eventual logarithmic lower
bound for a strictly positive real seed probability implies the corresponding
exponential lower bound. -/
theorem eventually_exp_neg_le_of_eventually_neg_le_log
    (Lambda p : Nat -> Real)
    (hpos : ∀ᶠ n in atTop, 0 < p n)
    (hlog : ∀ᶠ n in atTop, -Lambda n ≤ Real.log (p n)) :
    ∀ᶠ n in atTop, Real.exp (-Lambda n) ≤ p n := by
  filter_upwards [hpos, hlog] with n hn hn'
  exact (Real.exp_le_exp.mpr hn').trans_eq (Real.exp_log hn)

#print axioms Erdos625.eventually_exp_neg_le_of_eventually_neg_le_log

end Erdos625
