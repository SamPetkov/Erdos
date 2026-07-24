import Erdos625.Section10BinomialEdgeCount
import Erdos625.Section10ComplementInvariance
import Erdos625.Target
import Erdos625.ProbabilityTools
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

/-!
# Fixed induced-subgraph restriction for `G(n, 1/2)`

This module proves only the fixed-set restriction law needed at the beginning
of the Section X argument.  For a fixed vertex subset `S`, inducing a graph
sampled from `G(n,1/2)` has exactly the `G(S,1/2)` law.  The consequent
lower-quarter edge-count tail is likewise fixed-set only.  No union bound over
subsets and no simultaneous high-probability event are asserted here.
-/

namespace Erdos625

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal Finset ProbabilityTheory

noncomputable section

/-- Restricting independent Bernoulli coordinates along an injection again
gives the Bernoulli set measure on the restricted coordinate set. -/
theorem setBernoulli_map_preimage_of_injective
    {α β : Type*} {u : Set β} {p : I} {e : α → β}
    (he : Function.Injective e) :
    (setBernoulli u p).map (fun A : Set β => e ⁻¹' A) =
      setBernoulli (e ⁻¹' u) p := by
  have hpre : Measurable (fun A : Set β => e ⁻¹' A) := by
    apply measurable_set_iff.mpr
    intro a
    simpa using (measurable_set_mem (e a))
  rw [setBernoulli_eq_map u p, setBernoulli_eq_map (e ⁻¹' u) p]
  rw [Measure.map_map hpre (by fun_prop)]
  change
    Measure.map ((fun A : Set β => e ⁻¹' A) ∘ fun q : β → Prop => {j | q j})
      (MeasureTheory.Measure.infinitePi fun j : β =>
        toNNReal p • Measure.dirac (j ∈ u) + toNNReal (σ p) • Measure.dirac False) =
      Measure.map (fun q : α → Prop => {i | q i})
        (MeasureTheory.Measure.infinitePi fun i : α =>
          toNNReal p • Measure.dirac (i ∈ e ⁻¹' u) +
            toNNReal (σ p) • Measure.dirac False)
  have hpi :
      Measure.map (fun ω i => ω (e i))
        (MeasureTheory.Measure.infinitePi (fun j : β =>
          toNNReal p • Measure.dirac (j ∈ u) + toNNReal (σ p) • Measure.dirac False)) =
        MeasureTheory.Measure.infinitePi (fun i : α =>
          toNNReal p • Measure.dirac (i ∈ e ⁻¹' u) +
            toNNReal (σ p) • Measure.dirac False) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj he]
    congr 1
  have hcomp :
      ((fun A : Set β => e ⁻¹' A) ∘ fun q : β → Prop => {j | q j}) =
        (fun q : α → Prop => {i | q i}) ∘ (fun ω : β → Prop => fun i => ω (e i)) := by
    funext ω
    ext i
    rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hpi]

/-- Encoding a graph by its edge set commutes with restriction to a fixed
vertex set. -/
theorem fromEdgeSet_induce_eq_preimage
    {n : ℕ} (S : Set (Fin n)) (A : Set (Sym2 (Fin n))) :
    (SimpleGraph.fromEdgeSet A).induce S =
      SimpleGraph.fromEdgeSet
        (((Function.Embedding.subtype S).sym2Map :
          Sym2 S → Sym2 (Fin n)) ⁻¹' A) := by
  have heq (u v : S) : u = v ↔ (u : Fin n) = (v : Fin n) := by
    constructor
    · exact fun h => congrArg Subtype.val h
    · exact Subtype.ext
  ext u v
  rw [SimpleGraph.induce_adj, SimpleGraph.fromEdgeSet_adj,
    SimpleGraph.fromEdgeSet_adj]
  change
    (s((u : Fin n), (v : Fin n)) ∈ A ∧ (u : Fin n) ≠ (v : Fin n)) ↔
      (s((u : Fin n), (v : Fin n)) ∈ A ∧ u ≠ v)
  constructor
  · rintro ⟨hA, huv⟩
    exact ⟨hA, fun h => huv (congrArg Subtype.val h)⟩
  · rintro ⟨hA, huv⟩
    exact ⟨hA, fun h => huv (Subtype.ext h)⟩

/-- The induced-edge embedding preserves the distinction between diagonal and
non-diagonal symmetric pairs. -/
theorem diagSet_compl_preimage_subtype_sym2Map
    {n : ℕ} (S : Set (Fin n)) :
    (((Function.Embedding.subtype S).sym2Map :
      Sym2 S → Sym2 (Fin n)) ⁻¹'
        Set.compl (Sym2.diagSet : Set (Sym2 (Fin n)))) =
      Set.compl (Sym2.diagSet : Set (Sym2 S)) := by
  ext e
  change
    (¬ (Sym2.map (fun x : S => (x : Fin n)) e).IsDiag) ↔ ¬ e.IsDiag
  exact not_congr (Sym2.isDiag_map (z := e) (Function.Embedding.subtype S).injective)

/-- For every fixed vertex set `S`, inducing a `G(n,1/2)` graph on `S` has
exactly the binomial-random-graph law on `S`. -/
theorem randomGraphMeasure_map_induce
    (n : ℕ) (S : Set (Fin n)) :
    (randomGraphMeasure n).map
        (fun G : LabeledGraph n => G.induce S) =
      SimpleGraph.binomialRandom S halfProbability := by
  classical
  have he : Function.Injective
      (((Function.Embedding.subtype S).sym2Map : Sym2 S → Sym2 (Fin n))) :=
    ((Function.Embedding.subtype S).sym2Map).injective
  rw [randomGraphMeasure, SimpleGraph.binomialRandom_eq_map,
    SimpleGraph.binomialRandom_eq_map]
  rw [Measure.map_map (measurable_of_finite _) SimpleGraph.measurable_fromEdgeSet]
  change
    Measure.map
        ((fun G : SimpleGraph (Fin n) => G.induce S) ∘
          SimpleGraph.fromEdgeSet)
        (setBernoulli (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) halfProbability) =
      Measure.map SimpleGraph.fromEdgeSet
        (setBernoulli (Sym2.diagSetᶜ : Set (Sym2 S)) halfProbability)
  have hdet :
      ((fun G : SimpleGraph (Fin n) => G.induce S) ∘
          SimpleGraph.fromEdgeSet) =
        SimpleGraph.fromEdgeSet ∘
          (fun A : Set (Sym2 (Fin n)) =>
            (((Function.Embedding.subtype S).sym2Map :
              Sym2 S → Sym2 (Fin n)) ⁻¹' A)) := by
    funext A
    exact fromEdgeSet_induce_eq_preimage S A
  have hpre : Measurable
      (fun A : Set (Sym2 (Fin n)) =>
        (((Function.Embedding.subtype S).sym2Map :
          Sym2 S → Sym2 (Fin n)) ⁻¹' A)) := by
    apply measurable_set_iff.mpr
    intro z
    simpa using
      (measurable_set_mem (((Function.Embedding.subtype S).sym2Map :
        Sym2 S → Sym2 (Fin n)) z))
  rw [hdet]
  calc
    Measure.map (SimpleGraph.fromEdgeSet ∘
      (fun A : Set (Sym2 (Fin n)) =>
        (((Function.Embedding.subtype S).sym2Map :
          Sym2 S → Sym2 (Fin n)) ⁻¹' A)))
        (setBernoulli (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) halfProbability) =
      Measure.map SimpleGraph.fromEdgeSet
        (Measure.map
          (fun A : Set (Sym2 (Fin n)) =>
            (((Function.Embedding.subtype S).sym2Map :
              Sym2 S → Sym2 (Fin n)) ⁻¹' A))
          (setBernoulli (Sym2.diagSetᶜ : Set (Sym2 (Fin n))) halfProbability)) := by
            rw [Measure.map_map SimpleGraph.measurable_fromEdgeSet hpre]
    _ = Measure.map SimpleGraph.fromEdgeSet
        (setBernoulli
          (Set.preimage
            (((Function.Embedding.subtype S).sym2Map :
              Sym2 S → Sym2 (Fin n)))
            (Sym2.diagSetᶜ : Set (Sym2 (Fin n))))
          halfProbability) := by
            rw [setBernoulli_map_preimage_of_injective
              (e := ((Function.Embedding.subtype S).sym2Map :
                Sym2 S → Sym2 (Fin n))) he]
    _ = Measure.map SimpleGraph.fromEdgeSet
        (setBernoulli (Sym2.diagSetᶜ : Set (Sym2 S)) halfProbability) := by
            congr 3
            ext z
            change
              (¬ (Sym2.map (fun x : S => (x : Fin n)) z).IsDiag) ↔ ¬ z.IsDiag
            exact not_congr
              (Sym2.isDiag_map (z := z) (Function.Embedding.subtype S).injective)

/-- The exact natural-valued edge-count distribution of a binomial random
graph on a finite vertex type. -/
theorem binomialRandom_map_edgeCount
    {V : Type*} {p : I} [Finite V] :
    (SimpleGraph.binomialRandom V p).map (fun G => G.edgeSet.ncard) =
      Bin((Nat.card V).choose 2, p) := by
  classical
  apply Measure.ext_of_singleton
  intro n
  rw [binomialRandom_map_ncard_edgeSet_singleton,
    ProbabilityTheory.binomial_singleton]
  rw [← ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)]
  simp

/-- The real threshold law obtained by casting the exact natural edge count. -/
theorem binomialRandom_real_edgeCount_lowerTail
    {V : Type*} {p : I} [Finite V] (t : ℝ) :
    (SimpleGraph.binomialRandom V p).real
        {G | (G.edgeSet.ncard : ℝ) ≤ t} =
      Bin(ℝ, (Nat.card V).choose 2, p).real {x | x ≤ t} := by
  classical
  cases nonempty_fintype V
  letI : MeasurableSingletonClass (SimpleGraph V) := by
    constructor
    intro G
    rw [← SimpleGraph.measurableEmbedding_edgeSet.measurableSet_image]
    simp
  have hmap :
      (SimpleGraph.binomialRandom V p).map (fun G => (G.edgeSet.ncard : ℝ)) =
        ((SimpleGraph.binomialRandom V p).map (fun G => G.edgeSet.ncard)).map
          (fun k : ℕ => (k : ℝ)) := by
    symm
    rw [Measure.map_map (by fun_prop) (measurable_of_finite _)]
    rfl
  calc
    (SimpleGraph.binomialRandom V p).real
        {G | (G.edgeSet.ncard : ℝ) ≤ t} =
      ((SimpleGraph.binomialRandom V p).map (fun G => (G.edgeSet.ncard : ℝ))).real
        {x | x ≤ t} := by
          rw [map_measureReal_apply (measurable_of_finite _) (by measurability)]
          rfl
    _ = Bin(ℝ, (Nat.card V).choose 2, p).real {x | x ≤ t} := by
      rw [hmap, binomialRandom_map_edgeCount]

/-- The fixed-binomial lower-quarter edge-count tail at edge probability
`1/2`. -/
theorem binomialRandom_half_edgeCount_lowerQuarter
    {V : Type*} [Finite V] :
    (SimpleGraph.binomialRandom V halfProbability).real
        {G | (G.edgeSet.ncard : ℝ) ≤ ((Nat.card V).choose 2 : ℝ) / 4} ≤
      Real.exp (-((Nat.card V).choose 2 : ℝ) / 16) := by
  rw [binomialRandom_real_edgeCount_lowerTail]
  exact binomialHalf_lowerQuarter_le_exp _

/-- The number of edges in the subgraph induced by a fixed vertex set. -/
noncomputable def inducedEdgeCount
    {n : ℕ} (S : Set (Fin n)) (G : LabeledGraph n) : ℕ :=
  (G.induce S).edgeSet.ncard

/-- The lower-quarter edge-count tail for one fixed induced subgraph. -/
theorem randomGraphMeasure_inducedEdgeCount_lowerQuarter
    (n : ℕ) (S : Set (Fin n)) :
    (randomGraphMeasure n).real
        {G | (inducedEdgeCount S G : ℝ) ≤ ((Nat.card S).choose 2 : ℝ) / 4} ≤
      Real.exp (-((Nat.card S).choose 2 : ℝ) / 16) := by
  let f : LabeledGraph n → SimpleGraph S := fun G => G.induce S
  have hf : Measurable f := measurable_of_finite _
  calc
    (randomGraphMeasure n).real
        {G | (inducedEdgeCount S G : ℝ) ≤ ((Nat.card S).choose 2 : ℝ) / 4} =
      ((randomGraphMeasure n).map f).real
        {H | (H.edgeSet.ncard : ℝ) ≤ ((Nat.card S).choose 2 : ℝ) / 4} := by
          rw [map_measureReal_apply hf (by measurability)]
          rfl
    _ = (SimpleGraph.binomialRandom S halfProbability).real
        {H | (H.edgeSet.ncard : ℝ) ≤ ((Nat.card S).choose 2 : ℝ) / 4} := by
          rw [randomGraphMeasure_map_induce]
    _ ≤ Real.exp (-((Nat.card S).choose 2 : ℝ) / 16) :=
      binomialRandom_half_edgeCount_lowerQuarter

/-- The number of edges of the complement after restriction to a fixed vertex
set. -/
noncomputable def inducedComplementEdgeCount
    {n : ℕ} (S : Set (Fin n)) (G : LabeledGraph n) : ℕ :=
  (Gᶜ.induce S).edgeSet.ncard

/-- Ambient complement invariance and the fixed induced-restriction law give
the same `G(S,1/2)` distribution for induced complement edges. -/
theorem randomGraphMeasure_map_induce_complement
    (n : ℕ) (S : Set (Fin n)) :
    (randomGraphMeasure n).map
        (fun G : LabeledGraph n => Gᶜ.induce S) =
      SimpleGraph.binomialRandom S halfProbability := by
  calc
    (randomGraphMeasure n).map
        (fun G : LabeledGraph n => Gᶜ.induce S) =
      (randomGraphMeasure n).map
        ((fun H : LabeledGraph n => H.induce S) ∘
          (fun G : LabeledGraph n => Gᶜ)) := by
            rfl
    _ = ((randomGraphMeasure n).map (fun G : LabeledGraph n => Gᶜ)).map
        (fun H : LabeledGraph n => H.induce S) := by
            rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    _ = (randomGraphMeasure n).map
        (fun H : LabeledGraph n => H.induce S) := by
            rw [randomGraphMeasure_map_compl]
    _ = SimpleGraph.binomialRandom S halfProbability :=
      randomGraphMeasure_map_induce n S

/-- The lower-quarter tail for complement edges in one fixed induced
subgraph.  This is not a simultaneous statement over vertex subsets. -/
theorem randomGraphMeasure_inducedComplementEdgeCount_lowerQuarter
    (n : ℕ) (S : Set (Fin n)) :
    (randomGraphMeasure n).real
        {G | (inducedComplementEdgeCount S G : ℝ) ≤
          ((Nat.card S).choose 2 : ℝ) / 4} ≤
      Real.exp (-((Nat.card S).choose 2 : ℝ) / 16) := by
  let f : LabeledGraph n → SimpleGraph S := fun G => Gᶜ.induce S
  have hf : Measurable f := measurable_of_finite _
  calc
    (randomGraphMeasure n).real
        {G | (inducedComplementEdgeCount S G : ℝ) ≤
          ((Nat.card S).choose 2 : ℝ) / 4} =
      ((randomGraphMeasure n).map f).real
        {H | (H.edgeSet.ncard : ℝ) ≤ ((Nat.card S).choose 2 : ℝ) / 4} := by
          rw [map_measureReal_apply hf (by measurability)]
          rfl
    _ = (SimpleGraph.binomialRandom S halfProbability).real
        {H | (H.edgeSet.ncard : ℝ) ≤ ((Nat.card S).choose 2 : ℝ) / 4} := by
          rw [randomGraphMeasure_map_induce_complement]
    _ ≤ Real.exp (-((Nat.card S).choose 2 : ℝ) / 16) :=
      binomialRandom_half_edgeCount_lowerQuarter

end

end Erdos625
