import Erdos625.CochromaticAmplification
import Erdos625.CochromaticCapacityLowerTail
import Erdos625.Section11AsymptoticAssembly

/-!
# Conditional Sections X--XI assembly

This module connects the accepted induced-capacity tail, the deterministic
capacity-witness amplification bound, the simultaneous leftover-colouring
interface, and the Section XI event/probability infrastructure.

The final theorem is deliberately conditional.  Its hypotheses name the
five substantive inputs that are not proved here for the manuscript's concrete
sequences: the capacity tail, a simultaneous leftover-colouring tail, the
chromatic lower tail, the cochromatic threshold comparison, and the final gap
threshold separation.  No one of those hypotheses is a restatement of
`Erdos625Statement`.
-/

namespace Erdos625

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The explicit induced-capacity deficit radius in the one-sided
amplification estimate. -/
def cochromaticCapacityDeficitRadius (n : ℕ) (Lambda r : ℝ) : ℝ :=
  Real.sqrt ((((n - 1 : ℕ) : ℝ) * Lambda) / 2) +
    Real.sqrt ((((n - 1 : ℕ) : ℝ) * r) / 2)

/-- Success event for the real-valued capacity-deficit estimate.  Its
complement is exactly the non-strict failure event controlled by the accepted
one-sided lower-tail theorem. -/
def capacityAmplificationSuccessEvent
    (n k : ℕ) (Lambda r : ℝ) : Set (LabeledGraph n) :=
  {G | (n : ℝ) - (cochromaticInducedCapacity G k : ℝ) <
    cochromaticCapacityDeficitRadius n Lambda r}

/-- A natural-number version of a capacity-deficit success event. -/
def capacityDeficitEvent (n k d : ℕ) : Set (LabeledGraph n) :=
  {G | n - cochromaticInducedCapacity G k ≤ d}

/-- One event, with an internal universal quantifier, controlling the
chromatic number of every induced complement having at most `d` vertices.
This is the interface required of the still-open simultaneous leftover
colouring lemma; a pointwise-in-`W` probability statement is insufficient. -/
def simultaneousLeftoverColoringEvent
    (n d q : ℕ) : Set (LabeledGraph n) :=
  {G | ∀ W : Finset (Fin n),
    Fintype.card (↑((↑W : Set (Fin n)))ᶜ : Type) ≤ d →
      chromaticNumberNat (G.induce ((↑W : Set (Fin n)))ᶜ) ≤ q}

theorem measurableSet_capacityDeficitEvent (n k d : ℕ) :
    MeasurableSet (capacityDeficitEvent n k d) :=
  Set.toFinite (capacityDeficitEvent n k d) |>.measurableSet

theorem measurableSet_simultaneousLeftoverColoringEvent (n d q : ℕ) :
    MeasurableSet (simultaneousLeftoverColoringEvent n d q) :=
  Set.toFinite (simultaneousLeftoverColoringEvent n d q) |>.measurableSet

/-- The accepted capacity theorem controls precisely the complement of the
real-valued success event. -/
theorem capacityAmplificationSuccessEvent_compl_probability_le
    (n k : ℕ) {Lambda r : ℝ}
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k}) :
    (randomGraphMeasure n).real
        (capacityAmplificationSuccessEvent n k Lambda r)ᶜ ≤
      Real.exp (-r) := by
  have hEvent :
      (capacityAmplificationSuccessEvent n k Lambda r)ᶜ =
        {G : LabeledGraph n |
          cochromaticCapacityDeficitRadius n Lambda r ≤
            (n : ℝ) - (cochromaticInducedCapacity G k : ℝ)} := by
    ext G
    simp [capacityAmplificationSuccessEvent]
  rw [hEvent]
  simpa only [cochromaticCapacityDeficitRadius] using
    (randomGraph_cochromaticInducedCapacity_failureProbability_le
      n k hn hLambda hr hSeed)

/-- Rounding bridge from the real deficit radius to a natural leftover-size
bound.  The `d + 1` is exact: a natural number strictly below it is at most
`d`. -/
theorem capacityAmplificationSuccessEvent_subset_capacityDeficitEvent
    (n k d : ℕ) {Lambda r : ℝ}
    (hround : cochromaticCapacityDeficitRadius n Lambda r ≤
      ((d + 1 : ℕ) : ℝ)) :
    capacityAmplificationSuccessEvent n k Lambda r ⊆
      capacityDeficitEvent n k d := by
  intro G hSuccess
  have hCapacity : cochromaticInducedCapacity G k ≤ n :=
    cochromaticInducedCapacity_le_card G k
  have hReal :
      ((n - cochromaticInducedCapacity G k : ℕ) : ℝ) <
        ((d + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hCapacity]
    exact hSuccess.trans_le hround
  have hNat : n - cochromaticInducedCapacity G k < d + 1 := by
    exact_mod_cast hReal
  exact Nat.lt_succ_iff.mp hNat

/-- The accepted real capacity tail therefore controls failure of any rounded
natural deficit event whose cutoff dominates the real radius. -/
theorem capacityDeficitEvent_compl_probability_le
    (n k d : ℕ) {Lambda r : ℝ}
    (hn : 2 ≤ n) (hLambda : 0 ≤ Lambda) (hr : 0 ≤ r)
    (hSeed : Real.exp (-Lambda) ≤
      (randomGraphMeasure n).real {G | CoColorable G k})
    (hround : cochromaticCapacityDeficitRadius n Lambda r ≤
      ((d + 1 : ℕ) : ℝ)) :
    (randomGraphMeasure n).real (capacityDeficitEvent n k d)ᶜ ≤
      Real.exp (-r) := by
  calc
    (randomGraphMeasure n).real (capacityDeficitEvent n k d)ᶜ ≤
        (randomGraphMeasure n).real
          (capacityAmplificationSuccessEvent n k Lambda r)ᶜ := by
      apply measureReal_mono (h₂ := by finiteness)
      exact Set.compl_subset_compl.mpr
        (capacityAmplificationSuccessEvent_subset_capacityDeficitEvent
          n k d hround)
    _ ≤ Real.exp (-r) :=
      capacityAmplificationSuccessEvent_compl_probability_le
        n k hn hLambda hr hSeed

/-- Sequence-level use of the accepted capacity tail.  Once the seed bound,
nonnegativity, and rounding inequality hold eventually and `r n → ∞`, the
rounded natural capacity-deficit event has probability tending to one. -/
theorem capacityDeficitEvent_probability_tendsto_one
    (k d : ℕ → ℕ) (Lambda r : ℕ → ℝ)
    (hLambda : ∀ᶠ n in atTop, 0 ≤ Lambda n)
    (hr : ∀ᶠ n in atTop, 0 ≤ r n)
    (hSeed : ∀ᶠ n in atTop,
      Real.exp (-Lambda n) ≤
        (randomGraphMeasure n).real {G | CoColorable G (k n)})
    (hround : ∀ᶠ n in atTop,
      cochromaticCapacityDeficitRadius n (Lambda n) (r n) ≤
        (((d n) + 1 : ℕ) : ℝ))
    (hrTop : Tendsto r atTop atTop) :
    Tendsto
      (fun n ↦ randomGraphMeasure n (capacityDeficitEvent n (k n) (d n)))
      atTop (nhds 1) := by
  have hExp : Tendsto (fun n ↦ Real.exp (-r n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hrTop)
  have hUpper : ∀ᶠ n in atTop,
      (randomGraphMeasure n).real
          (capacityDeficitEvent n (k n) (d n))ᶜ ≤ Real.exp (-r n) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hLambda, hr, hSeed,
      hround] with n hn hLambdaN hrN hSeedN hroundN
    exact capacityDeficitEvent_compl_probability_le
      n (k n) (d n) hn hLambdaN hrN hSeedN hroundN
  have hFailureReal : Tendsto
      (fun n ↦ (randomGraphMeasure n).real
        (capacityDeficitEvent n (k n) (d n))ᶜ)
      atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hExp
      (Filter.Eventually.of_forall fun n ↦ measureReal_nonneg)
      hUpper
  have hSuccessIdentity : ∀ n,
      (randomGraphMeasure n).real (capacityDeficitEvent n (k n) (d n)) =
        1 - (randomGraphMeasure n).real
          (capacityDeficitEvent n (k n) (d n))ᶜ := by
    intro n
    have hCompl := measureReal_compl
      (μ := randomGraphMeasure n)
      (measurableSet_capacityDeficitEvent n (k n) (d n))
    rw [probReal_univ] at hCompl
    linarith
  have hSuccessReal : Tendsto
      (fun n ↦ (randomGraphMeasure n).real
        (capacityDeficitEvent n (k n) (d n)))
      atTop (nhds (1 : ℝ)) := by
    have hOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hSub := hOne.sub hFailureReal
    convert hSub using 1
    · funext n
      exact hSuccessIdentity n
    · norm_num
  exact
    (ENNReal.tendsto_toReal_iff
      (fun n ↦ measure_ne_top (randomGraphMeasure n)
        (capacityDeficitEvent n (k n) (d n)))
      ENNReal.one_ne_top).mp (by
        simpa only [Measure.real, ENNReal.toReal_one] using hSuccessReal)

/-- A capacity-attaining cocolourable core plus the simultaneous leftover
bound gives the expected whole-graph cochromatic bound. -/
theorem cochromaticNumber_le_of_capacityDeficit_and_leftover
    {n k d q : ℕ} {G : LabeledGraph n}
    (hCapacity : G ∈ capacityDeficitEvent n k d)
    (hLeftover : G ∈ simultaneousLeftoverColoringEvent n d q) :
    cochromaticNumber G ≤ k + q := by
  obtain ⟨W, _hCore, _hWcard, hComplCard, hWhole⟩ :=
    exists_capacity_witness_with_compl_bound G k
  have hSize :
      Fintype.card (↑((↑W : Set (Fin n)))ᶜ : Type) ≤ d := by
    rw [hComplCard]
    exact hCapacity
  exact hWhole.trans (Nat.add_le_add_left (hLeftover W hSize) k)

/-- Event form of the deterministic capacity/leftover interface. -/
theorem capacityDeficit_inter_leftover_subset_cochromaticUpperEvent
    {n k d q kCo : ℕ} {a : ℝ}
    (hThreshold : ((k + q : ℕ) : ℝ) ≤ (kCo : ℝ) + a) :
    capacityDeficitEvent n k d ∩
        simultaneousLeftoverColoringEvent n d q ⊆
      cochromaticUpperEvent n kCo a := by
  intro G hG
  have hNat := cochromaticNumber_le_of_capacityDeficit_and_leftover
    hG.1 hG.2
  have hReal : (cochromaticNumber G : ℝ) ≤ ((k + q : ℕ) : ℝ) := by
    exact_mod_cast hNat
  exact hReal.trans hThreshold

/-- Conditional closure of Sections X--XI.

The open inputs are exposed separately:

* `hLeftoverTail`: the one-event simultaneous leftover-colouring estimate;
* `hChromaticTail`: the upstream chromatic lower-tail theorem;
* `hCochromaticThreshold`: rounding/parameter domination after amplification;
* `hGapThreshold`: the eventual Section XI threshold separation.

The capacity tail itself can be supplied by
`capacityDeficitEvent_probability_tendsto_one`, so it is kept as a separate
named input rather than hidden inside a cochromatic-upper-tail assumption. -/
theorem erdos625Statement_of_capacity_leftover_thresholds
    (kChi kSeed deficit leftover kCo : ℕ → ℕ) (a : ℕ → ℝ)
    (hCapacityTail : Tendsto
      (fun n ↦ randomGraphMeasure n
        (capacityDeficitEvent n (kSeed n) (deficit n)))
      atTop (nhds 1))
    (hLeftoverTail : Tendsto
      (fun n ↦ randomGraphMeasure n
        (simultaneousLeftoverColoringEvent n (deficit n) (leftover n)))
      atTop (nhds 1))
    (hChromaticTail : Tendsto
      (fun n ↦ randomGraphMeasure n (chromaticLowerEvent n (kChi n)))
      atTop (nhds 1))
    (hCochromaticThreshold : ∀ᶠ n in atTop,
      (((kSeed n) + (leftover n) : ℕ) : ℝ) ≤ (kCo n : ℝ) + a n)
    (hGapThreshold : ∀ᶠ n in atTop,
      gapScale n ≤
        (((kChi n) + 1 : ℕ) : ℝ) - ((kCo n : ℝ) + a n)) :
    Erdos625Statement := by
  have hCapacityLeftover : Tendsto
      (fun n ↦ randomGraphMeasure n
        (capacityDeficitEvent n (kSeed n) (deficit n) ∩
          simultaneousLeftoverColoringEvent n (deficit n) (leftover n)))
      atTop (nhds 1) :=
    tendsto_measure_inter_one randomGraphMeasure
      (fun n ↦ capacityDeficitEvent n (kSeed n) (deficit n))
      (fun n ↦ simultaneousLeftoverColoringEvent n
        (deficit n) (leftover n))
      (fun n ↦ measurableSet_capacityDeficitEvent n (kSeed n) (deficit n))
      (fun n ↦ measurableSet_simultaneousLeftoverColoringEvent n
        (deficit n) (leftover n))
      hCapacityTail hLeftoverTail
  have hCochromaticTail : Tendsto
      (fun n ↦ randomGraphMeasure n
        (cochromaticUpperEvent n (kCo n) (a n)))
      atTop (nhds 1) := by
    apply tendsto_measure_one_of_eventually_subset randomGraphMeasure
      (fun n ↦ capacityDeficitEvent n (kSeed n) (deficit n) ∩
        simultaneousLeftoverColoringEvent n (deficit n) (leftover n))
      (fun n ↦ cochromaticUpperEvent n (kCo n) (a n))
      hCapacityLeftover
    filter_upwards [hCochromaticThreshold] with n hThreshold
    exact capacityDeficit_inter_leftover_subset_cochromaticUpperEvent
      hThreshold
  have hThresholdIntersection : Tendsto
      (fun n ↦ randomGraphMeasure n
        (chromaticLowerEvent n (kChi n) ∩
          cochromaticUpperEvent n (kCo n) (a n)))
      atTop (nhds 1) :=
    tendsto_measure_inter_one randomGraphMeasure
      (fun n ↦ chromaticLowerEvent n (kChi n))
      (fun n ↦ cochromaticUpperEvent n (kCo n) (a n))
      (fun n ↦ Set.toFinite (chromaticLowerEvent n (kChi n)) |>.measurableSet)
      (fun n ↦ Set.toFinite
        (cochromaticUpperEvent n (kCo n) (a n)) |>.measurableSet)
      hChromaticTail hCochromaticTail
  unfold Erdos625Statement
  change Tendsto (fun n ↦ randomGraphMeasure n (gapEvent n))
    atTop (nhds 1)
  apply tendsto_measure_one_of_eventually_subset randomGraphMeasure
    (fun n ↦ chromaticLowerEvent n (kChi n) ∩
      cochromaticUpperEvent n (kCo n) (a n))
    gapEvent hThresholdIntersection
  filter_upwards [hGapThreshold] with n hThreshold
  exact thresholdIntersection_subset_gapEvent hThreshold

end

end Erdos625
