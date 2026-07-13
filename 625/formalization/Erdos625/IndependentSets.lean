import Erdos625.Target
import Erdos625.Phase
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Interval

/-!
# Exact first-moment identities for independent sets

This file develops the finite combinatorics behind the standard first-moment
bound for the independence number of `G(n, 1/2)`.  All expectations are
presented as finite weighted sums on the labelled graph sample space, so no
measurable-integration infrastructure is hidden in the statement.
-/

namespace Erdos625

open MeasureTheory
open scoped BigOperators ENNReal

universe u

/-- The complete graph supported on the vertices in `S`, embedded in the
ambient vertex type. -/
def completeOn {V : Type u} (S : Finset V) : SimpleGraph V :=
  (⊤ : SimpleGraph S).map
    (Function.Embedding.subtype (fun v ↦ v ∈ S))

/-- A vertex set is independent exactly when its ambient graph is disjoint
from the complete graph supported on that set. -/
theorem isIndepSet_iff_disjoint_completeOn {V : Type u} (G : SimpleGraph V)
    (S : Finset V) :
    G.IsIndepSet (S : Set V) ↔ Disjoint G (completeOn S) := by
  rw [SimpleGraph.disjoint_left]
  constructor
  · intro h x y hxy hcomplete
    rw [completeOn, SimpleGraph.map_adj] at hcomplete
    obtain ⟨x', y', hne, rfl, rfl⟩ := hcomplete
    exact h x'.property y'.property (by simpa using hne) hxy
  · intro h x hx y hy hxy hG
    exact (h x y hG) (by
      rw [completeOn, SimpleGraph.map_adj]
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, by simpa using hxy, rfl, rfl⟩)

/-- A vertex set is independent exactly when the graph lies below the graph
of all edges not internal to that set. -/
theorem isIndepSet_iff_le_compl_completeOn {V : Type u} (G : SimpleGraph V)
    (S : Finset V) :
    G.IsIndepSet (S : Set V) ↔ G ≤ (completeOn S)ᶜ := by
  rw [le_compl_iff_disjoint_right]
  exact isIndepSet_iff_disjoint_completeOn G S

/-- The supported complete graph has one edge for each two-element subset
of its support. -/
theorem ncard_edgeSet_completeOn {V : Type u} [Fintype V] [DecidableEq V]
    (S : Finset V) :
    (completeOn S).edgeSet.ncard = S.card.choose 2 := by
  classical
  let f : S ↪ V := Function.Embedding.subtype (fun v ↦ v ∈ S)
  change (((⊤ : SimpleGraph S).map f).edgeSet).ncard = S.card.choose 2
  rw [SimpleGraph.edgeSet_map,
    Set.ncard_image_of_injective _ f.sym2Map.injective,
    SimpleGraph.edgeSet_top, Sym2.ncard_diagSet_compl]
  simp

/-- Removing the edges internal to `S` leaves
`choose |V| 2 - choose |S| 2` possible edges. -/
theorem ncard_edgeSet_compl_completeOn {V : Type u} [Fintype V]
    [DecidableEq V] (S : Finset V) :
    ((completeOn S)ᶜ).edgeSet.ncard =
      (Fintype.card V).choose 2 - S.card.choose 2 := by
  rw [← top_sdiff, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_top,
    Set.ncard_sdiff' (SimpleGraph.edgeSet_subset_compl_diagSet (completeOn S)),
    Sym2.ncard_diagSet_compl,
    ncard_edgeSet_completeOn]
  simp

/-- Graphs below `H` are in bijection with subsets of the edge set of `H`. -/
noncomputable def graphBelowEquiv {V : Type u} (H : SimpleGraph V) :
    {G : SimpleGraph V // G ≤ H} ≃ Set H.edgeSet where
  toFun G := {e | (e : Sym2 V) ∈ G.1.edgeSet}
  invFun s := ⟨SimpleGraph.fromEdgeSet (Subtype.val '' s), by
    rw [SimpleGraph.fromEdgeSet_le]
    intro e he
    obtain ⟨e', _, rfl⟩ := he.1
    exact e'.property⟩
  left_inv G := by
    apply Subtype.ext
    change SimpleGraph.fromEdgeSet
      (Subtype.val '' {e : H.edgeSet | (e : Sym2 V) ∈ G.1.edgeSet}) = G.1
    rw [show Subtype.val '' {e : H.edgeSet | (e : Sym2 V) ∈ G.1.edgeSet} =
        G.1.edgeSet by
      ext e
      constructor
      · rintro ⟨e', he', rfl⟩
        exact he'
      · intro he
        exact ⟨⟨e, (SimpleGraph.edgeSet_subset_edgeSet.mpr G.2) he⟩, he, rfl⟩]
    exact SimpleGraph.fromEdgeSet_edgeSet G.1
  right_inv s := by
    ext e
    simp only [Set.mem_setOf_eq, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, Set.mem_image]
    constructor
    · rintro ⟨⟨e', he', hval⟩, -⟩
      have heq : e' = e := Subtype.ext hval
      simpa [heq] using he'
    · intro he
      exact ⟨⟨e, he, rfl⟩, H.not_isDiag_of_mem_edgeSet e.property⟩

/-- There are `2 ^ |E(H)|` labelled graphs below a fixed graph `H`. -/
theorem card_graphBelow {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) :
    Nat.card {G : SimpleGraph V // G ≤ H} = 2 ^ H.edgeSet.ncard := by
  classical
  letI : Fintype {G : SimpleGraph V // G ≤ H} := Fintype.ofFinite _
  letI : Fintype H.edgeSet := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (graphBelowEquiv H), Fintype.card_set,
    ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

/-- The event that a fixed labelled vertex set is independent. -/
def independentEvent {n : ℕ} (S : Finset (Fin n)) : Set (LabeledGraph n) :=
  {G | G.IsIndepSet (S : Set (Fin n))}

/-- The fixed-set independence event is measurable on the finite labelled
graph sample space. -/
theorem measurableSet_independentEvent {n : ℕ} (S : Finset (Fin n)) :
    MeasurableSet (independentEvent S) :=
  Set.toFinite (independentEvent S) |>.measurableSet

/-- Exactly `2 ^ (choose n 2 - choose |S| 2)` labelled graphs make `S`
independent. -/
theorem ncard_independentEvent {n : ℕ} (S : Finset (Fin n)) :
    (independentEvent S).ncard =
      2 ^ (n.choose 2 - S.card.choose 2) := by
  change Nat.card {G : LabeledGraph n //
    G.IsIndepSet (S : Set (Fin n))} = _
  calc
    _ = Nat.card {G : LabeledGraph n // G ≤ (completeOn S)ᶜ} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun G ↦
        isIndepSet_iff_le_compl_completeOn G S)
    _ = 2 ^ ((completeOn S)ᶜ).edgeSet.ncard :=
      card_graphBelow ((completeOn S)ᶜ)
    _ = 2 ^ (n.choose 2 - S.card.choose 2) := by
      rw [ncard_edgeSet_compl_completeOn]
      simp

/-- The exact probability that a fixed `S` is independent in `G(n, 1/2)`. -/
theorem randomGraphMeasure_independentEvent {n : ℕ}
    (S : Finset (Fin n)) :
    randomGraphMeasure n (independentEvent S) =
      (1 / 2 : ENNReal) ^ S.card.choose 2 := by
  classical
  letI : Fintype (independentEvent S) := Fintype.ofFinite _
  let T := (independentEvent S).toFinset
  have hcard : T.card = 2 ^ (n.choose 2 - S.card.choose 2) := by
    simpa [T] using ncard_independentEvent S
  have hk : S.card.choose 2 ≤ n.choose 2 := by
    exact Nat.choose_le_choose 2 (by simpa using Finset.card_le_univ S)
  calc
    randomGraphMeasure n (independentEvent S) =
        randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      simp [T]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = ∑ _G ∈ T, (1 / 2 : ENNReal) ^ n.choose 2 := by
      simp_rw [randomGraphMeasure_singleton_uniform]
    _ = (2 : ENNReal) ^ (n.choose 2 - S.card.choose 2) *
        (1 / 2 : ENNReal) ^ n.choose 2 := by
      simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = (1 / 2 : ENNReal) ^ S.card.choose 2 := by
      conv_lhs =>
        rhs
        rw [show n.choose 2 =
          (n.choose 2 - S.card.choose 2) + S.card.choose 2 by
            exact (Nat.sub_add_cancel hk).symm, pow_add]
      rw [← mul_assoc, ← mul_pow]
      rw [div_eq_mul_inv, one_mul,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- The number of independent `s`-subsets of the labelled vertex set.  It is
written as a finite sum of indicators to make the first-moment calculation
transparent. -/
noncomputable def independentIndicatorNat {n : ℕ} (G : LabeledGraph n)
    (S : Finset (Fin n)) : ℕ := by
  classical
  exact if G.IsIndepSet (S : Set (Fin n)) then 1 else 0

/-- The `ENNReal` indicator of a fixed-set independence event. -/
noncomputable def independentIndicator {n : ℕ} (G : LabeledGraph n)
    (S : Finset (Fin n)) : ENNReal := by
  classical
  exact if G.IsIndepSet (S : Set (Fin n)) then 1 else 0

@[simp] theorem coe_independentIndicatorNat {n : ℕ} (G : LabeledGraph n)
    (S : Finset (Fin n)) :
    (independentIndicatorNat G S : ENNReal) = independentIndicator G S := by
  classical
  by_cases h : G.IsIndepSet (S : Set (Fin n)) <;>
    simp [independentIndicatorNat, independentIndicator, h]

noncomputable def independentSetCount {n : ℕ} (G : LabeledGraph n)
    (s : ℕ) : ℕ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
    independentIndicatorNat G S

/-- The finite weighted-sum expectation of `independentSetCount` under
`G(n, 1/2)`. -/
noncomputable def independentSetExpectation (n s : ℕ) : ENNReal :=
  ∑ G : LabeledGraph n,
    (independentSetCount G s : ENNReal) * randomGraphMeasure n {G}

/-- Summing the indicator of a fixed-set event against singleton masses
recovers the measure of that event. -/
theorem sum_independentIndicator_measure {n : ℕ}
    (S : Finset (Fin n)) :
    (∑ G : LabeledGraph n,
      independentIndicator G S * randomGraphMeasure n {G}) =
      randomGraphMeasure n (independentEvent S) := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter
    (fun G ↦ G.IsIndepSet (S : Set (Fin n)))
  calc
    _ = ∑ G : LabeledGraph n,
        if G.IsIndepSet (S : Set (Fin n))
        then randomGraphMeasure n {G} else 0 := by
      apply Finset.sum_congr rfl
      intro G _
      by_cases h : G.IsIndepSet (S : Set (Fin n)) <;>
        simp [independentIndicator, h]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      simp only [T, Finset.sum_filter]
    _ = randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = randomGraphMeasure n (independentEvent S) := by
      congr 1
      ext G
      simp [T, independentEvent]

/-- Exact first moment of the number of independent `s`-subsets in
`G(n, 1/2)`. -/
theorem independentSetExpectation_eq (n s : ℕ) :
    independentSetExpectation n s =
      (n.choose s : ENNReal) * (1 / 2 : ENNReal) ^ s.choose 2 := by
  classical
  unfold independentSetExpectation independentSetCount
  simp_rw [Nat.cast_sum, coe_independentIndicatorNat, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [sum_independentIndicator_measure]
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
        randomGraphMeasure n (independentEvent S)) =
        ∑ _S ∈ (Finset.univ : Finset (Fin n)).powersetCard s,
          (1 / 2 : ENNReal) ^ s.choose 2 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [randomGraphMeasure_independentEvent,
        (Finset.mem_powersetCard.mp hS).2]
    _ = (n.choose s : ENNReal) *
        (1 / 2 : ENNReal) ^ s.choose 2 := by
      simp [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

/-- The finite expectation is exactly the nonnegative-real lift of the real
first-moment quantity `mu` used by the phase estimates. -/
theorem independentSetExpectation_eq_ofReal_mu (n s : ℕ) :
    independentSetExpectation n s = ENNReal.ofReal (mu n s) := by
  rw [independentSetExpectation_eq]
  unfold mu
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.inv_pow]
  simp [div_eq_mul_inv]

@[simp] theorem independentIndicatorNat_pos_iff {n : ℕ}
    (G : LabeledGraph n) (S : Finset (Fin n)) :
    0 < independentIndicatorNat G S ↔
      G.IsIndepSet (S : Set (Fin n)) := by
  classical
  by_cases h : G.IsIndepSet (S : Set (Fin n)) <;>
    simp [independentIndicatorNat, h]

/-- Positivity of the count means exactly that an independent `s`-subset
exists. -/
theorem independentSetCount_pos_iff_exists {n s : ℕ}
    (G : LabeledGraph n) :
    0 < independentSetCount G s ↔
      ∃ S : Finset (Fin n), S.card = s ∧
        G.IsIndepSet (S : Set (Fin n)) := by
  classical
  unfold independentSetCount
  rw [Finset.sum_pos_iff]
  simp [Finset.mem_powersetCard, independentIndicatorNat_pos_iff]

/-- The independent-set count is positive exactly up through the graph's
independence number. -/
theorem independentSetCount_pos_iff_le_indepNum {n s : ℕ}
    (G : LabeledGraph n) :
    0 < independentSetCount G s ↔ s ≤ G.indepNum := by
  constructor
  · rw [independentSetCount_pos_iff_exists]
    rintro ⟨S, hcard, hS⟩
    simpa [hcard] using hS.card_le_indepNum
  · intro hs
    obtain ⟨T, hT⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨S, hST, hcard⟩ := Finset.exists_subset_card_eq (s := T) (n := s)
      (by simpa [hT.card_eq] using hs)
    rw [independentSetCount_pos_iff_exists]
    refine ⟨S, hcard, ?_⟩
    exact Set.Pairwise.mono (by simpa using hST) hT.isIndepSet

/-- Event that the independence number exceeds `s`. -/
def independenceNumberExceedsEvent (n s : ℕ) : Set (LabeledGraph n) :=
  {G | s < G.indepNum}

/-- Event that at least one independent `s`-set exists. -/
def independentSetCountPositiveEvent (n s : ℕ) : Set (LabeledGraph n) :=
  {G | 0 < independentSetCount G s}

/-- Exact event equivalence behind the shifted first-moment bound. -/
theorem independenceNumberExceedsEvent_eq_countPositive (n s : ℕ) :
    independenceNumberExceedsEvent n s =
      independentSetCountPositiveEvent n (s + 1) := by
  ext G
  simp only [independenceNumberExceedsEvent,
    independentSetCountPositiveEvent, Set.mem_setOf_eq,
    independentSetCount_pos_iff_le_indepNum]
  omega

theorem measurableSet_independentSetCountPositiveEvent (n s : ℕ) :
    MeasurableSet (independentSetCountPositiveEvent n s) :=
  Set.toFinite (independentSetCountPositiveEvent n s) |>.measurableSet

theorem measurableSet_independenceNumberExceedsEvent (n s : ℕ) :
    MeasurableSet (independenceNumberExceedsEvent n s) :=
  Set.toFinite (independenceNumberExceedsEvent n s) |>.measurableSet

/-- Finite-space Markov inequality at threshold one for the independent-set
count. -/
theorem randomGraphMeasure_countPositive_le_expectation (n s : ℕ) :
    randomGraphMeasure n (independentSetCountPositiveEvent n s) ≤
      independentSetExpectation n s := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter
    (fun G ↦ 0 < independentSetCount G s)
  calc
    randomGraphMeasure n (independentSetCountPositiveEvent n s) =
        randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      congr 1
      ext G
      simp [T, independentSetCountPositiveEvent]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = ∑ G : LabeledGraph n,
        if 0 < independentSetCount G s
        then randomGraphMeasure n {G} else 0 := by
      simp only [T, Finset.sum_filter]
    _ ≤ ∑ G : LabeledGraph n,
        (independentSetCount G s : ENNReal) *
          randomGraphMeasure n {G} := by
      apply Finset.sum_le_sum
      intro G _
      by_cases h : 0 < independentSetCount G s
      · rw [if_pos h]
        have hone : (1 : ENNReal) ≤
            (independentSetCount G s : ENNReal) := by
          exact_mod_cast (Nat.succ_le_iff.mpr h)
        calc
          randomGraphMeasure n {G} =
              1 * randomGraphMeasure n {G} := (one_mul _).symm
          _ ≤ (independentSetCount G s : ENNReal) *
              randomGraphMeasure n {G} := mul_le_mul_left hone _
      · simp [h]
    _ = independentSetExpectation n s := rfl

/-- The sharp shifted first-moment consequence:
`P(α(G_n) > s) ≤ μ(n,s+1)`. -/
theorem randomGraphMeasure_independenceNumberExceeds_le_mu_succ (n s : ℕ) :
    randomGraphMeasure n (independenceNumberExceedsEvent n s) ≤
      ENNReal.ofReal (mu n (s + 1)) := by
  rw [independenceNumberExceedsEvent_eq_countPositive]
  exact (randomGraphMeasure_countPositive_le_expectation n (s + 1)).trans_eq
    (independentSetExpectation_eq_ofReal_mu n (s + 1))

/-- The unshifted form used in the manuscript's coarse estimate:
`P(α(G_n) > s) ≤ μ(n,s)`.  It follows because `α > s` already
ensures the existence of an independent `s`-set. -/
theorem randomGraphMeasure_independenceNumberExceeds_le_mu (n s : ℕ) :
    randomGraphMeasure n (independenceNumberExceedsEvent n s) ≤
      ENNReal.ofReal (mu n s) := by
  calc
    randomGraphMeasure n (independenceNumberExceedsEvent n s) ≤
        randomGraphMeasure n (independentSetCountPositiveEvent n s) := by
      apply measure_mono
      intro G hG
      rw [independentSetCountPositiveEvent, Set.mem_setOf_eq,
        independentSetCount_pos_iff_le_indepNum]
      exact Nat.le_of_lt hG
    _ ≤ independentSetExpectation n s :=
      randomGraphMeasure_countPositive_le_expectation n s
    _ = ENNReal.ofReal (mu n s) :=
      independentSetExpectation_eq_ofReal_mu n s

/-- Real-valued spelling of the unshifted first-moment probability bound. -/
theorem randomGraphMeasure_independenceNumberExceeds_toReal_le_mu (n s : ℕ) :
    (randomGraphMeasure n (independenceNumberExceedsEvent n s)).toReal ≤
      mu n s := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (randomGraphMeasure_independenceNumberExceeds_le_mu n s)
  simpa [ENNReal.toReal_ofReal (mu_nonneg n s)] using h

end Erdos625
