import Erdos625.Section8CanonicalDemandPartition
import Erdos625.Section8CanonicalEventProbabilityNormalization
import Mathlib.Tactic

/-!
# Section VIII: exact canonical-demand mixture normalization

This module records only the finite consequence of the literal canonical-demand
partition: when the two ambient stub totals agree, the
probabilities of all attained canonical-demand fibres sum to one.  It makes
no high-demand, nonemptiness-of-an-individual-fibre, conditional-law, or
quantitative claim.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

local instance instFintypeCanonicalDemandEventMixture
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A -> B -> Nat) (row : A -> Nat) (col : B -> Nat) (U : Nat) :
    Fintype (canonicalDemandEvent demand row col U) :=
  Fintype.ofFinite _

/-- Finite ENNReal sums commute with division by a fixed denominator.  Unlike
the field lemma `Finset.sum_div`, this uses only `ENNReal.add_div`. -/
private theorem ennreal_sum_div
    {gamma : Type*} (s : Finset gamma) (f : gamma -> ENNReal) (d : ENNReal) :
    (∑ x ∈ s, f x / d) = (∑ x ∈ s, f x) / d := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hxs ih =>
      rw [Finset.sum_insert hxs, Finset.sum_insert hxs, ENNReal.add_div, ih]

/-- The literal canonical-demand fibres form a probability partition of the
ambient uniform configuration law. -/
theorem sum_uniformConfigurationMatching_canonicalDemandEvent_eq_one
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (row : A -> Nat) (col : B -> Nat) (U : Nat)
    (htotal : Finset.univ.sum row = Finset.univ.sum col) :
    (∑ demand : canonicalDemandImage row col U,
      (uniformConfigurationMatching row col htotal).toOuterMeasure
        (canonicalDemandEvent demand.1 row col U)) = 1 := by
  let m := Finset.univ.sum row
  have hfactorialZero : (m.factorial : ENNReal) ≠ 0 := by
    exact_mod_cast m.factorial_ne_zero
  have hfactorialTop : (m.factorial : ENNReal) ≠ ∞ :=
    ENNReal.natCast_ne_top _
  calc
    (∑ demand : canonicalDemandImage row col U,
        (uniformConfigurationMatching row col htotal).toOuterMeasure
          (canonicalDemandEvent demand.1 row col U)) =
        ∑ demand : canonicalDemandImage row col U,
          (Fintype.card (canonicalDemandEvent demand.1 row col U) : ENNReal) /
            (m.factorial : ENNReal) := by
      apply Finset.sum_congr rfl
      intro demand _
      simpa only [m] using
        uniformConfigurationMatching_canonicalDemandEvent_apply
          demand.1 row col U htotal
    _ =
        ((∑ demand : canonicalDemandImage row col U,
          Fintype.card (canonicalDemandEvent demand.1 row col U) : Nat) : ENNReal) /
          (m.factorial : ENNReal) := by
      rw [Nat.cast_sum]
      change
        (Finset.univ.sum fun demand : canonicalDemandImage row col U =>
          (Fintype.card (canonicalDemandEvent demand.1 row col U) : ENNReal) /
            (m.factorial : ENNReal)) =
          (Finset.univ.sum fun demand : canonicalDemandImage row col U =>
            (Fintype.card (canonicalDemandEvent demand.1 row col U) : ENNReal)) /
              (m.factorial : ENNReal)
      exact
        ennreal_sum_div
          (Finset.univ : Finset (canonicalDemandImage row col U))
          (fun demand =>
            (Fintype.card (canonicalDemandEvent demand.1 row col U) : ENNReal))
          (m.factorial : ENNReal)
    _ = (Fintype.card (ConfigurationMatching row col) : ENNReal) /
          (m.factorial : ENNReal) := by
      rw [card_configurationMatching_eq_sum_card_canonicalDemandEvent]
    _ = 1 := by
      rw [card_configurationMatching row col htotal]
      simpa only [m] using ENNReal.div_self hfactorialZero hfactorialTop

#print axioms sum_uniformConfigurationMatching_canonicalDemandEvent_eq_one

end

end Erdos625
