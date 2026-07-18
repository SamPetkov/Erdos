import Erdos625.SignedProfileWitness
import Mathlib.Tactic

/-!
# Section VI: finite Fubini bridge for the signed second moment

This module is deliberately independent of the overlap-table quotient.  It
contains only the exact finite interchange of the graph sum with the two
signed-witness sums.  Thus the later table calculation has a literal
graph-level second moment to attach to, without treating an expectation as a
formal heuristic.
-/

namespace Erdos625

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The natural-valued indicator of a set in a finite sample space. -/
noncomputable def finiteSetIndicator {α : Type*}
    (A : Set α) (x : α) : ℕ := by
  classical
  exact if x ∈ A then 1 else 0

/-- The finite atomic second moment of a natural-valued random variable. -/
noncomputable def finiteNatSecondMoment {α : Type*} [Fintype α]
    [MeasurableSpace α] (μ : Measure α) (X : α → ℕ) : ENNReal :=
  ∑ x : α, (X x : ENNReal) ^ 2 * μ {x}

/-- On a finite sample space, the singleton-mass sum of the product of two
zero-one indicators is exactly the mass of the intersection event. -/
theorem sum_finiteSetIndicator_mul_measure_eq_measure_inter
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    (μ : Measure α) (A B : Set α) :
    (∑ x : α,
      (finiteSetIndicator A x : ENNReal) *
        (finiteSetIndicator B x : ENNReal) * μ {x}) =
      μ (A ∩ B) := by
  classical
  let T := (Finset.univ : Finset α).filter fun x => x ∈ A ∩ B
  calc
    (∑ x : α,
      (finiteSetIndicator A x : ENNReal) *
        (finiteSetIndicator B x : ENNReal) * μ {x}) =
        ∑ x : α, if x ∈ A ∩ B then μ {x} else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
            simp [finiteSetIndicator, hA, hB]
    _ = ∑ x ∈ T, μ {x} := by
          simp only [T, Finset.sum_filter]
    _ = μ (T : Set α) := by
          rw [MeasureTheory.sum_measure_singleton]
    _ = μ (A ∩ B) := by
          congr 1
          ext x
          simp [T]

/-- The literal joint event of two fixed signed profile witnesses.  This
name avoids relying on the later mixed-edge-presentation layer. -/
def signedProfileWitnessPairIntersection {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    Set (LabeledGraph n) :=
  signedProfileWitnessEvent P σ ∩ signedProfileWitnessEvent Q τ

/-- A signed-witness indicator is the generic indicator of its validity
event. -/
theorem signedProfileWitnessIndicator_eq_finiteSetIndicator
    {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) :
    signedProfileWitnessIndicator G P σ =
      finiteSetIndicator (signedProfileWitnessEvent P σ) G := by
  classical
  simp [signedProfileWitnessIndicator, finiteSetIndicator,
    signedProfileWitnessEvent]

/-- Summing the product of two fixed signed-witness indicators against the
finite random-graph law recovers the mass of their joint event. -/
theorem sum_signedProfileWitnessPairIndicator_measure
    {b n : ℕ} {k : ColoringProfile b}
    (P Q : ProfilePartition n k)
    (σ : P.1.parts → Bool) (τ : Q.1.parts → Bool) :
    (∑ G : LabeledGraph n,
      (signedProfileWitnessIndicator G P σ : ENNReal) *
        (signedProfileWitnessIndicator G Q τ : ENNReal) *
          randomGraphMeasure n {G}) =
      randomGraphMeasure n (signedProfileWitnessPairIntersection P Q σ τ) := by
  rw [signedProfileWitnessPairIntersection]
  simp_rw [signedProfileWitnessIndicator_eq_finiteSetIndicator]
  exact sum_finiteSetIndicator_mul_measure_eq_measure_inter
    (randomGraphMeasure n) _ _

/-- The square of the signed count expands into the ordered pair sum of its
two fixed-witness indicators. -/
theorem signedProfileCount_sq_eq_sum_pair_indicator
    {b n : ℕ} (G : LabeledGraph n) (k : ColoringProfile b) :
    (signedProfileCount G k : ENNReal) ^ 2 =
      ∑ w : SignedProfileWitness n k, ∑ w' : SignedProfileWitness n k,
        (signedProfileWitnessIndicator G w.1 w.2 : ENNReal) *
          (signedProfileWitnessIndicator G w'.1 w'.2 : ENNReal) := by
  classical
  have hcount :
      (signedProfileCount G k : ENNReal) =
        ∑ w : SignedProfileWitness n k,
          (signedProfileWitnessIndicator G w.1 w.2 : ENNReal) := by
    calc
      (signedProfileCount G k : ENNReal) =
          ∑ P : ProfilePartition n k, ∑ σ : P.1.parts → Bool,
            (signedProfileWitnessIndicator G P σ : ENNReal) := by
              rw [signedProfileCount_eq_sum_indicator]
              simp only [Nat.cast_sum]
      _ = ∑ w : SignedProfileWitness n k,
          (signedProfileWitnessIndicator G w.1 w.2 : ENNReal) := by
              rw [Fintype.sum_sigma]
  rw [hcount, pow_two, Finset.sum_mul_sum]

/-- The graph-level second moment of the signed profile count. -/
noncomputable def signedProfileSecondMoment {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ENNReal :=
  finiteNatSecondMoment (randomGraphMeasure n) fun G => signedProfileCount G k

/-- Exact finite Fubini expansion of the signed graph-level second moment
into the joint probabilities of ordered pairs of signed witnesses. -/
theorem signedProfileSecondMoment_eq_sum_pairEvent
    {b : ℕ} (n : ℕ) (k : ColoringProfile b) :
    signedProfileSecondMoment n k =
      ∑ w : SignedProfileWitness n k, ∑ w' : SignedProfileWitness n k,
        randomGraphMeasure n
          (signedProfileWitnessPairIntersection w.1 w'.1 w.2 w'.2) := by
  classical
  unfold signedProfileSecondMoment finiteNatSecondMoment
  simp_rw [signedProfileCount_sq_eq_sum_pair_indicator]
  calc
    (∑ G : LabeledGraph n,
      (∑ w : SignedProfileWitness n k, ∑ w' : SignedProfileWitness n k,
        (signedProfileWitnessIndicator G w.1 w.2 : ENNReal) *
          (signedProfileWitnessIndicator G w'.1 w'.2 : ENNReal)) *
        randomGraphMeasure n {G}) =
      ∑ G : LabeledGraph n,
        ∑ w : SignedProfileWitness n k, ∑ w' : SignedProfileWitness n k,
          (signedProfileWitnessIndicator G w.1 w.2 : ENNReal) *
            (signedProfileWitnessIndicator G w'.1 w'.2 : ENNReal) *
              randomGraphMeasure n {G} := by
        simp_rw [Finset.sum_mul]
    _ = ∑ w : SignedProfileWitness n k, ∑ w' : SignedProfileWitness n k,
        ∑ G : LabeledGraph n,
          (signedProfileWitnessIndicator G w.1 w.2 : ENNReal) *
            (signedProfileWitnessIndicator G w'.1 w'.2 : ENNReal) *
              randomGraphMeasure n {G} := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.sum_comm]
    _ = ∑ w : SignedProfileWitness n k, ∑ w' : SignedProfileWitness n k,
        randomGraphMeasure n
          (signedProfileWitnessPairIntersection w.1 w'.1 w.2 w'.2) := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro w' hw'
        rw [sum_signedProfileWitnessPairIndicator_measure]

#print axioms sum_finiteSetIndicator_mul_measure_eq_measure_inter
#print axioms sum_signedProfileWitnessPairIndicator_measure
#print axioms signedProfileCount_sq_eq_sum_pair_indicator
#print axioms signedProfileSecondMoment_eq_sum_pairEvent

end

end Erdos625
