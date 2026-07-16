import Erdos625.Section10_11ConditionalAssembly
import Erdos625.Section10CapacityLeftoverQuantitative
import Erdos625.Section10QuarterChainLinearEvent
import Mathlib.Tactic

/-!
# Section X: uniform cochromatic amplification

This module combines the accepted induced-capacity lower tail with the
parameter-independent uniform induced-colouring event.  It is the
quantifier-correct event/probability form of manuscript Lemma 10.2:

* the same absolute constant `C` is chosen before the seed, exponent, and
  deviation-radius sequences;
* the error sequence is the fixed quarter-chain failure probability and is
  therefore independent of those later parameters;
* the two success events are combined only by a union bound, with no
  independence assumption.
-/

namespace Erdos625

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The displayed error term in the uniform amplification lemma. -/
def uniformAmplificationError
    (C : ℝ) (n : ℕ) (Lambda r : ℝ) : ℝ :=
  C * ((Real.sqrt ((n : ℝ) * Lambda) +
          Real.sqrt ((n : ℝ) * r)) / Real.log (n : ℝ) +
        (n : ℝ) ^ (1 / 3 : ℝ) + 1)

/-- Increasing the absolute constant enlarges the uniform induced-colouring
event once `log n` is positive. -/
theorem quarterChainLinearColoringEvent_mono_constant
    {C D : ℝ} {n : ℕ} (hCD : C ≤ D) (hn : 1 < n) :
    quarterChainLinearColoringEvent C n ⊆
      quarterChainLinearColoringEvent D n := by
  intro G hG U
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hfactor : 0 ≤ (U.card : ℝ) / Real.log (n : ℝ) := by
    positivity
  exact (hG U).trans (by
    gcongr)

/-- The manuscript deficit radius is bounded by the simpler displayed
square-root expression. -/
theorem cochromaticCapacityDeficitRadius_lt_displayed
    {n : ℕ} {Lambda r d : ℝ}
    (_hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hd :
      d < cochromaticCapacityDeficitRadius n Lambda r) :
    d <
      Real.sqrt ((n : ℝ) * Lambda) +
        Real.sqrt ((n : ℝ) * r) := by
  have hnSub : n - 1 ≤ n := Nat.sub_le n 1
  have hLambdaRadicand :
      ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) ≤
        (n : ℝ) * Lambda := by
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnSub
    have hmul :
        ((n - 1 : ℕ) : ℝ) * Lambda ≤ (n : ℝ) * Lambda :=
      mul_le_mul_of_nonneg_right hcast hLambda
    nlinarith [mul_nonneg (Nat.cast_nonneg (n - 1)) hLambda]
  have hrRadicand :
      ((((n - 1 : ℕ) : ℝ) * r) / 2) ≤
        (n : ℝ) * r := by
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hnSub
    have hmul :
        ((n - 1 : ℕ) : ℝ) * r ≤ (n : ℝ) * r :=
      mul_le_mul_of_nonneg_right hcast hr
    nlinarith [mul_nonneg (Nat.cast_nonneg (n - 1)) hr]
  exact hd.trans_le (add_le_add
    (Real.sqrt_le_sqrt hLambdaRadicand)
    (Real.sqrt_le_sqrt hrRadicand))

/-- Transport of the natural chromatic number across extensionally equal
inducing vertex sets. -/
private theorem chromaticNumberNat_induce_eq_of_set_eq
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Set V)
    [Fintype S] [Fintype T]
    (hST : S = T) :
    chromaticNumberNat (G.induce S) =
      chromaticNumberNat (G.induce T) := by
  subst T
  rfl

/-- Fixed-`n` deterministic amplification.  A capacity-attaining core and the
uniform induced-colouring event give the displayed cochromatic upper bound.
The exact complementary cardinality is retained throughout. -/
theorem capacityAmplification_inter_linear_subset_cochromaticUpperEvent
    (n k : ℕ) (C Lambda r : ℝ)
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hC : 1 ≤ C) :
    capacityAmplificationSuccessEvent n k Lambda r ∩
        quarterChainLinearColoringEvent C n ⊆
      cochromaticUpperEvent n k
        (uniformAmplificationError C n Lambda r) := by
  intro G hG
  obtain ⟨W, _hCore, hWcard, hComplCard, hWhole⟩ :=
    exists_capacity_witness_with_compl_bound G k
  let U : Finset (Fin n) := Finset.univ \ W
  have hUset :
      (↑U : Set (Fin n)) = ((↑W : Set (Fin n)))ᶜ := by
    ext x
    simp [U]
  have hUcard :
      U.card = n - cochromaticInducedCapacity G k := by
    calc
      U.card =
          Fintype.card (↥((↑W : Set (Fin n)))ᶜ : Type) := by
        rw [← Fintype.card_coe U]
        apply Fintype.card_congr
        exact Equiv.setCongr hUset
      _ = n - cochromaticInducedCapacity G k := hComplCard
  have hCapacityLe : cochromaticInducedCapacity G k ≤ n :=
    cochromaticInducedCapacity_le_card G k
  have hDeficit :
      ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) <
        Real.sqrt ((n : ℝ) * Lambda) +
          Real.sqrt ((n : ℝ) * r) := by
    rw [Nat.cast_sub hCapacityLe]
    exact cochromaticCapacityDeficitRadius_lt_displayed
      hn hLambda hr hG.1
  have hLinear :
      (chromaticNumberNat
          (G.induce ((↑W : Set (Fin n)))ᶜ) : ℝ) ≤
        C * ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) /
            Real.log (n : ℝ) +
          (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hAtU := hG.2 U
    rw [hUcard] at hAtU
    rw [← chromaticNumberNat_induce_eq_of_set_eq
      G (↑U : Set (Fin n)) ((↑W : Set (Fin n)))ᶜ hUset]
    exact hAtU
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn))
  have hSqrtNonneg :
      0 ≤ Real.sqrt ((n : ℝ) * Lambda) +
        Real.sqrt ((n : ℝ) * r) := by positivity
  have hDeficitQuotient :
      ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) /
          Real.log (n : ℝ) ≤
        (Real.sqrt ((n : ℝ) * Lambda) +
            Real.sqrt ((n : ℝ) * r)) /
          Real.log (n : ℝ) :=
    (div_lt_div_iff_of_pos_right hlog).2 hDeficit |>.le
  have hScaledDeficitQuotient :
      C * ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) /
          Real.log (n : ℝ) ≤
        C *
          ((Real.sqrt ((n : ℝ) * Lambda) +
              Real.sqrt ((n : ℝ) * r)) /
            Real.log (n : ℝ)) := by
    calc
      C * ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) /
            Real.log (n : ℝ) =
          C * (((n - cochromaticInducedCapacity G k : ℕ) : ℝ) /
            Real.log (n : ℝ)) := by ring
      _ ≤ C *
          ((Real.sqrt ((n : ℝ) * Lambda) +
              Real.sqrt ((n : ℝ) * r)) /
            Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hDeficitQuotient (le_trans (by norm_num) hC)
  have hWholeReal :
      (cochromaticNumber G : ℝ) ≤
        (k : ℝ) +
          (chromaticNumberNat
            (G.induce ((↑W : Set (Fin n)))ᶜ) : ℝ) := by
    exact_mod_cast hWhole
  change (cochromaticNumber G : ℝ) ≤
    (k : ℝ) + uniformAmplificationError C n Lambda r
  refine hWholeReal.trans ?_
  rw [uniformAmplificationError]
  have hCnonneg : 0 ≤ C := le_trans (by norm_num) hC
  have hCubeNonneg : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by positivity
  calc
    (k : ℝ) +
          (chromaticNumberNat
            (G.induce ((↑W : Set (Fin n)))ᶜ) : ℝ) ≤
        (k : ℝ) +
          (C * ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) /
              Real.log (n : ℝ) +
            (n : ℝ) ^ (1 / 3 : ℝ)) := by
      gcongr
    _ ≤ (k : ℝ) +
          (C *
              ((Real.sqrt ((n : ℝ) * Lambda) +
                  Real.sqrt ((n : ℝ) * r)) /
                Real.log (n : ℝ)) +
            (n : ℝ) ^ (1 / 3 : ℝ)) := by
      gcongr
    _ ≤ (k : ℝ) +
          C *
            ((Real.sqrt ((n : ℝ) * Lambda) +
                Real.sqrt ((n : ℝ) * r)) /
              Real.log (n : ℝ) +
              (n : ℝ) ^ (1 / 3 : ℝ) + 1) := by
      have hCubeScale :
          (n : ℝ) ^ (1 / 3 : ℝ) ≤
            C * (n : ℝ) ^ (1 / 3 : ℝ) :=
        le_mul_of_one_le_left hCubeNonneg hC
      nlinarith

/-- Fixed-index quantitative form of uniform amplification.  The capacity
failure and uniform-colouring failure are combined by a union bound; no
independence is assumed. -/
theorem cochromaticUpperEvent_compl_probability_le_exp_add
    (n k : ℕ) (C Lambda r epsilon : ℝ)
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hC : 1 ≤ C)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k})
    (hLinearFailure :
      (randomGraphMeasure n).real
          (quarterChainLinearColoringEvent C n)ᶜ ≤ epsilon) :
    (randomGraphMeasure n).real
        (cochromaticUpperEvent n k
          (uniformAmplificationError C n Lambda r))ᶜ ≤
      Real.exp (-r) + epsilon := by
  apply failure_probability_le_add_of_two_success_events
    (randomGraphMeasure n)
    (capacityAmplificationSuccessEvent n k Lambda r)
    (quarterChainLinearColoringEvent C n)
    (cochromaticUpperEvent n k
      (uniformAmplificationError C n Lambda r))
    (Set.toFinite _ |>.measurableSet)
    (Set.toFinite _ |>.measurableSet)
    (capacityAmplification_inter_linear_subset_cochromaticUpperEvent
      n k C Lambda r hn hLambda hr hC)
    (Real.exp (-r)) epsilon
    (capacityAmplificationSuccessEvent_compl_probability_le
      n k hn hLambda hr hSeed)
    hLinearFailure

/-- Quantifier-correct full-sequence form of manuscript Lemma 10.2.  One
fixed constant and one vanishing error sequence are chosen before all deterministic
seed, exponent, and radius sequences. -/
theorem exists_uniform_cochromatic_amplification :
    ∃ C : ℝ, ∃ epsilon : ℕ → ℝ,
      1 ≤ C ∧
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ n : ℕ, 0 ≤ epsilon n) ∧
      ∀ (k : ℕ → ℕ) (Lambda r : ℕ → ℝ),
        (∀ᶠ n in atTop, 0 ≤ Lambda n) →
        (∀ᶠ n in atTop, 0 < r n) →
        (∀ᶠ n in atTop,
          Real.exp (-Lambda n) ≤
            (randomGraphMeasure n).real
              {G | CoColorable G (k n)}) →
        ∀ᶠ n in atTop,
          (randomGraphMeasure n).real
              (cochromaticUpperEvent n (k n)
                (uniformAmplificationError C n (Lambda n) (r n)))ᶜ ≤
            Real.exp (-r n) + epsilon n := by
  obtain ⟨C₀, hC₀, hSubset₀⟩ :=
    exists_quarterChainIndependentBlockEvent_subset_linearColoringEvent_eventually
  let C : ℝ := C₀ + 1
  let epsilon : ℕ → ℝ := quarterChainIndependentBlockFailure
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith
  have hC₀C : C₀ ≤ C := by
    dsimp [C]
    linarith
  have hSubset :
      ∀ᶠ n : ℕ in atTop,
        quarterChainIndependentBlockEvent n ⊆
          quarterChainLinearColoringEvent C n := by
    filter_upwards [hSubset₀, Filter.eventually_gt_atTop 1]
      with n hSubsetN hn
    exact hSubsetN.trans
      (quarterChainLinearColoringEvent_mono_constant hC₀C hn)
  have hLinearFailure :
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            (quarterChainLinearColoringEvent C n)ᶜ ≤ epsilon n := by
    exact
      quarterChainLinearColoringEvent_compl_probability_le_failure_eventually
        C hSubset
  refine ⟨C, epsilon, hC, ?_, ?_, ?_⟩
  · exact quarterChainIndependentBlockFailure_tendsto_zero
  · exact quarterChainIndependentBlockFailure_nonneg
  · intro k Lambda r hLambda hr hSeed
    filter_upwards
        [eventually_ge_atTop (2 : ℕ), hLambda, hr, hSeed, hLinearFailure]
      with n hn hLambdaN hrN hSeedN hLinearFailureN
    exact cochromaticUpperEvent_compl_probability_le_exp_add
      n (k n) C (Lambda n) (r n) (epsilon n)
      hn hLambdaN hrN.le hC hSeedN hLinearFailureN

#print axioms quarterChainLinearColoringEvent_mono_constant
#print axioms cochromaticCapacityDeficitRadius_lt_displayed
#print axioms capacityAmplification_inter_linear_subset_cochromaticUpperEvent
#print axioms cochromaticUpperEvent_compl_probability_le_exp_add
#print axioms exists_uniform_cochromatic_amplification

end

end Erdos625
