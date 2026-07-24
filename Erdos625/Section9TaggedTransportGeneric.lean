import Erdos625.Section9GlobalCanonicalResidualBridge
import Mathlib.Tactic

/-!
# Section VIII--IX: generic tagged finite-sum transport

This isolated target transports an arbitrary nonnegative observable through the
exact configuration-matching equivalence to the *dependent* tagged
`demand/witness/residual` Section IX family.  It deliberately retains both
tags.  In particular, it neither identifies a common residual PMF nor
conditions or divides by any event probability.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance fintypeResidualCapNoReturnEventTaggedTransport
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : Nat) (row : A -> Nat) (col : B -> Nat) :
    Fintype (ResidualCapNoReturnEvent M R row col) :=
  Fintype.ofFinite _

/-- Exact finite expectation/sum transport through the configuration matching
equivalence.  The observable is evaluated on the full dependent tagged state,
so demand and witness labels are never discarded. -/
theorem uniformConfigurationMatching_sum_tagged_transport
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col)
    (f : (Sigma fun demand : canonicalDemandImage row col U =>
      Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
        ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness)) -> ENNReal) :
    (Finset.univ.sum fun matching : ConfigurationMatching row col =>
      uniformConfigurationMatching row col htotal matching *
        f (configurationMatchingEquivSigmaCapNoReturn row col U matching)) =
      Finset.univ.sum fun z :
        Sigma fun demand : canonicalDemandImage row col U =>
          Sigma fun witness : PrescribedDemandWitness demand.1 row col =>
            ResidualCapNoReturnEvent (positiveDemandSupport demand.1) (U / 2)
              (residualRowDegree witness) (residualColumnDegree witness) =>
        uniformSigmaCapNoReturn row col U htotal z * f z := by
  convert Equiv.sum_comp
    (configurationMatchingEquivSigmaCapNoReturn row col U)
    (fun z => uniformSigmaCapNoReturn row col U htotal z * f z) using 1
  simp [← uniformConfigurationMatching_map_sigmaCapNoReturn]

end

end Erdos625
