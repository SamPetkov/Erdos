import Erdos625.Section10QuarterChainIndependentBlock
import Erdos625.Section10QuarterChainFailure
import Erdos625.Section10QuarterChainGreedyNumeric
import Erdos625.Section10_11ConditionalAssembly
import Mathlib.Tactic

/-!
# Section X: independent-block event to simultaneous leftover colouring

This module gives the finite deterministic adapter from the uniform
independent-block event to the simultaneous leftover-colouring event.  It
keeps the universal quantifier over leftover cores inside the event.
-/

namespace Erdos625

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The exact natural leftover threshold produced by the quarter-chain greedy
bound for a deficit of at most `d` vertices. -/
def quarterChainLeftoverBound (n d : ℕ) : ℕ :=
  ceilDivNat d (quarterChainSteps n) + quarterChainStart n

/-- The literal natural leftover threshold inherits the explicit real
ceiling-division bound. -/
theorem quarterChainLeftoverBound_real_upper_bound_eventually :
    ∀ᶠ n : ℕ in atTop, ∀ d : ℕ,
      (quarterChainLeftoverBound n d : ℝ) ≤
        14 * Real.log 4 * (d : ℝ) / Real.log n +
          (quarterChainStart n : ℝ) + 1 := by
  filter_upwards
      [quarterChain_greedy_count_real_upper_bound_eventually] with n hn
  intro d
  simpa only [quarterChainLeftoverBound, Nat.cast_add] using hn d

/-- Ceiling division is monotone in its numerator. -/
theorem ceilDivNat_mono_left {a b c : ℕ} (h : a ≤ b) :
    ceilDivNat a c ≤ ceilDivNat b c := by
  unfold ceilDivNat
  apply Nat.div_le_div_right
  omega

/-- The finite complement of a supplied vertex set represents the subtype
complement occurring in `simultaneousLeftoverColoringEvent`, with exactly the
same cardinality. -/
theorem univ_sdiff_card_eq_compl_fintype_card
    {n : ℕ} (W : Finset (Fin n)) :
    (Finset.univ \ W).card =
      Fintype.card (↥((↑W : Set (Fin n)))ᶜ : Type) := by
  rw [← Fintype.card_coe (Finset.univ \ W)]
  apply Fintype.card_congr
  exact Equiv.setCongr (by
    ext x
    simp)

/-- Inducing on extensionally equal vertex sets does not change the
natural-valued chromatic number.  This separate transport lemma avoids asking
`rw` to synthesize a dependent `Fintype` motive. -/
theorem chromaticNumberNat_induce_eq_of_set_eq
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Set V)
    [Fintype S] [Fintype T]
    (hST : S = T) :
    chromaticNumberNat (G.induce S) =
      chromaticNumberNat (G.induce T) := by
  subst T
  unfold chromaticNumberNat
  rfl

/-- At one fixed `n`, the uniform independent-block event implies the
simultaneous leftover-colouring event whenever the displayed deterministic
ceiling bound fits below `q`.  The event keeps the quantifier over every
`W`; no pointwise-in-`W` probability statement is used. -/
theorem quarterChainIndependentBlockEvent_subset_simultaneousLeftoverColoringEvent
    (n d q : ℕ)
    (hblock : 1 ≤ quarterChainSteps n)
    (hq :
      ceilDivNat d (quarterChainSteps n) + quarterChainStart n ≤ q) :
    quarterChainIndependentBlockEvent n ⊆
      simultaneousLeftoverColoringEvent n d q := by
  intro G hG W hW
  let U : Finset (Fin n) := Finset.univ \ W
  have hUset :
      (↑U : Set (Fin n)) = ((↑W : Set (Fin n)))ᶜ := by
    ext x
    simp [U]
  have hUcard :
      U.card = Fintype.card (↥((↑W : Set (Fin n)))ᶜ : Type) := by
    simpa only [U] using univ_sdiff_card_eq_compl_fintype_card W
  have hUle : U.card ≤ d := by
    rw [hUcard]
    exact hW
  have hChromatic :=
    chromaticNumberNat_induce_le_of_independentBlockEvent
      n G hG hblock U
  have hChromatic' :
      chromaticNumberNat (G.induce ((↑W : Set (Fin n)))ᶜ) ≤
        ceilDivNat U.card (quarterChainSteps n) + quarterChainStart n := by
    rw [← chromaticNumberNat_induce_eq_of_set_eq
      G (↑U : Set (Fin n)) ((↑W : Set (Fin n)))ᶜ hUset]
    exact hChromatic
  exact hChromatic'.trans
    ((Nat.add_le_add_right (ceilDivNat_mono_left hUle)
      (quarterChainStart n)).trans hq)

/-- Sequence-level deterministic adapter: any eventual numerical bound on the
ceiling expression turns the accepted independent-block probability limit
into the required simultaneous leftover-colouring probability limit. -/
theorem simultaneousLeftoverColoringEvent_probability_tendsto_one_of_eventually_bound
    (d q : ℕ → ℕ)
    (hq : ∀ᶠ n : ℕ in atTop,
      ceilDivNat (d n) (quarterChainSteps n) + quarterChainStart n ≤ q n) :
    Tendsto
      (fun n ↦
        randomGraphMeasure n
          (simultaneousLeftoverColoringEvent n (d n) (q n)))
      atTop (nhds 1) := by
  apply tendsto_measure_one_of_eventually_subset
    (fun n ↦ randomGraphMeasure n)
    quarterChainIndependentBlockEvent
    (fun n ↦ simultaneousLeftoverColoringEvent n (d n) (q n))
    quarterChainIndependentBlockEvent_probability_tendsto_one
  filter_upwards [one_le_quarterChainSteps_eventually, hq]
    with n hblock hqN
  exact
    quarterChainIndependentBlockEvent_subset_simultaneousLeftoverColoringEvent
      n (d n) (q n) hblock hqN

/-- With the literal greedy threshold, the simultaneous leftover event has
probability tending to one for every deterministic deficit sequence.  The
failure event remains the same independent-block failure event and therefore
does not depend on the chosen sequence. -/
theorem quarterChainLeftoverBound_probability_tendsto_one
    (d : ℕ → ℕ) :
    Tendsto
      (fun n ↦
        randomGraphMeasure n
          (simultaneousLeftoverColoringEvent n (d n)
            (quarterChainLeftoverBound n (d n))))
      atTop (nhds 1) := by
  apply simultaneousLeftoverColoringEvent_probability_tendsto_one_of_eventually_bound
  exact Filter.Eventually.of_forall fun n ↦ le_rfl

/-- Fixed-index quantitative form: the literal simultaneous-leftover failure
probability is bounded by the same parameter-independent independent-block
failure sequence. -/
theorem quarterChainLeftoverBound_compl_probability_le
    (n d : ℕ) (hblock : 1 ≤ quarterChainSteps n) :
    (randomGraphMeasure n).real
        (simultaneousLeftoverColoringEvent n d
          (quarterChainLeftoverBound n d))ᶜ ≤
      quarterChainIndependentBlockFailure n := by
  unfold quarterChainIndependentBlockFailure
  apply measureReal_mono (h₂ := by finiteness)
  exact Set.compl_subset_compl.mpr
    (quarterChainIndependentBlockEvent_subset_simultaneousLeftoverColoringEvent
      n d (quarterChainLeftoverBound n d) hblock le_rfl)

/-- The concrete quarter-chain leftover theorem discharges the leftover-tail
input of the existing Sections X--XI conditional seam. -/
theorem erdos625Statement_of_capacity_quarterChainLeftover_thresholds
    (kChi kSeed deficit kCo : ℕ → ℕ) (a : ℕ → ℝ)
    (hCapacityTail : Tendsto
      (fun n ↦ randomGraphMeasure n
        (capacityDeficitEvent n (kSeed n) (deficit n)))
      atTop (nhds 1))
    (hChromaticTail : Tendsto
      (fun n ↦ randomGraphMeasure n (chromaticLowerEvent n (kChi n)))
      atTop (nhds 1))
    (hCochromaticThreshold : ∀ᶠ n in atTop,
      (((kSeed n) + quarterChainLeftoverBound n (deficit n) : ℕ) : ℝ) ≤
        (kCo n : ℝ) + a n)
    (hGapThreshold : ∀ᶠ n in atTop,
      gapScale n ≤
        (((kChi n) + 1 : ℕ) : ℝ) - ((kCo n : ℝ) + a n)) :
    Erdos625Statement := by
  exact erdos625Statement_of_capacity_leftover_thresholds
    kChi kSeed deficit
    (fun n ↦ quarterChainLeftoverBound n (deficit n))
    kCo a hCapacityTail
    (quarterChainLeftoverBound_probability_tendsto_one deficit)
    hChromaticTail hCochromaticThreshold hGapThreshold

#print axioms ceilDivNat_mono_left
#print axioms quarterChainLeftoverBound_real_upper_bound_eventually
#print axioms univ_sdiff_card_eq_compl_fintype_card
#print axioms chromaticNumberNat_induce_eq_of_set_eq
#print axioms quarterChainIndependentBlockEvent_subset_simultaneousLeftoverColoringEvent
#print axioms simultaneousLeftoverColoringEvent_probability_tendsto_one_of_eventually_bound
#print axioms quarterChainLeftoverBound_probability_tendsto_one
#print axioms quarterChainLeftoverBound_compl_probability_le
#print axioms erdos625Statement_of_capacity_quarterChainLeftover_thresholds

end

end Erdos625
