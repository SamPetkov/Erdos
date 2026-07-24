import Erdos625.Section9MidpointSecondMomentSeed
import Erdos625.Section6SignedPaleyZygmundSeed
import Mathlib.Tactic

namespace Erdos625

open Filter MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology

noncomputable section

theorem eventually_signedProfile_real_seed_of_midpointCanonicalPolymer_bound
    (b U : Nat → Nat)
    (k : (n : Nat) → ColoringProfile (b n))
    (row0 : (n : Nat) → OrderedProfilePartition n (k n))
    (Lambda : Nat → Real)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hpolymer : ∀ᶠ n in atTop,
      midpointCanonicalPolymerSum (row0 n) (U n) ≤
        ENNReal.ofReal (Real.exp (Lambda n))) :
    ∀ᶠ n in atTop,
      Real.exp (-Lambda n) ≤
        (randomGraphMeasure n).real
          {G | CoColorable G (ColoringProfile.partCount (k n))} := by
  filter_upwards [hpolymer] with n hn
  apply signedProfile_real_seed_of_tableSum_bound (row0 n) (Lambda n)
  rw [← normalizedSignedProfileSecondMoment_eq_tableSum (row0 n)]
  exact normalizedSignedProfileSecondMoment_le_exp_of_polymerSum
    (row0 n) (U n) (hU n) (Lambda n) (hcap n) hn

#print axioms eventually_signedProfile_real_seed_of_midpointCanonicalPolymer_bound

end

end Erdos625
