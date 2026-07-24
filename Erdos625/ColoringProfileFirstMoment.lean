import Erdos625.IndependentSets
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Exact finite first moments for bounded coloring profiles

This module develops the finite combinatorial layer behind equation (4.2) of
the manuscript.  A profile `k : Fin b → ℕ` records `k i` nonempty color
classes of size `i + 1`.  Unordered colorings are represented by
`Finpartition`s, so equal-sized classes are not silently labelled.

The probability calculation is complete: for every fixed unordered
partition with profile `k`, the probability that all its parts are
independent is exactly

`(1 / 2) ^ profileForbiddenEdges k`.

Consequently the exact first moment is the actual number of such
partitions times this probability.  This foundational module isolates the
replacement of that cardinality by the factorial quotient in (4.2) as
`ProfileEnumerationStatement`; the downstream
`ColoringProfileEnumerationInjective` module proves it by an explicit finite
bijection.  Mathlib's `Multiset.bell` supplies the arithmetic quotient, but no
unproved interpretation of it as a partition count is assumed.
-/

namespace Erdos625

open MeasureTheory
open scoped BigOperators ENNReal

universe u

private theorem sum_multiset_finset {I M : Type*} [DecidableEq I]
    [AddCommMonoid M] (s : Finset I) (f : I → Multiset M) :
    (∑ i ∈ s, f i).sum = ∑ i ∈ s, (f i).sum := by
  change Multiset.sumAddMonoidHom (∑ i ∈ s, f i) =
    ∑ i ∈ s, Multiset.sumAddMonoidHom (f i)
  exact map_sum Multiset.sumAddMonoidHom f s

private theorem map_multiset_finset {I A B : Type*} [DecidableEq I]
    (s : Finset I) (g : A → B) (f : I → Multiset A) :
    Multiset.map g (∑ i ∈ s, f i) =
      ∑ i ∈ s, Multiset.map g (f i) := by
  change (Multiset.mapAddMonoidHom g) (∑ i ∈ s, f i) =
    ∑ i ∈ s, (Multiset.mapAddMonoidHom g) (f i)
  exact map_sum (Multiset.mapAddMonoidHom g) f s

/-! ## Profiles and unordered set partitions -/

/-- A bounded coloring profile.  Index `i : Fin b` represents classes of
positive size `i + 1`; hence empty color classes never enter the profile. -/
abbrev ColoringProfile (b : ℕ) := Fin b → ℕ

namespace ColoringProfile

/-- The multiset of positive class sizes encoded by a profile. -/
def sizes {b : ℕ} (k : ColoringProfile b) : Multiset ℕ :=
  ∑ i : Fin b, Multiset.replicate (k i) (i.1 + 1)

/-- Number of nonempty parts in a profile. -/
def partCount {b : ℕ} (k : ColoringProfile b) : ℕ :=
  (sizes k).card

/-- Number of vertices covered by a profile. -/
def vertexMass {b : ℕ} (k : ColoringProfile b) : ℕ :=
  (sizes k).sum

/-- Number of within-class edges forbidden by a profile coloring. -/
def forbiddenEdges {b : ℕ} (k : ColoringProfile b) : ℕ :=
  ((sizes k).map fun s ↦ s.choose 2).sum

/-- The number of parts is the sum of the profile coordinates. -/
theorem partCount_eq_sum {b : ℕ} (k : ColoringProfile b) :
    partCount k = ∑ i : Fin b, k i := by
  simp [partCount, sizes]

/-- The vertex mass is the size-weighted sum of the coordinates. -/
theorem vertexMass_eq_sum {b : ℕ} (k : ColoringProfile b) :
    vertexMass k = ∑ i : Fin b, (i.1 + 1) * k i := by
  unfold vertexMass sizes
  rw [sum_multiset_finset]
  simp [Multiset.sum_replicate, mul_comm]

/-- The forbidden-edge count is the corresponding size-weighted sum. -/
theorem forbiddenEdges_eq_sum {b : ℕ} (k : ColoringProfile b) :
    forbiddenEdges k = ∑ i : Fin b, k i * (i.1 + 1).choose 2 := by
  unfold forbiddenEdges sizes
  rw [map_multiset_finset, sum_multiset_finset]
  simp [Multiset.map_replicate, Multiset.sum_replicate]

/-- The factorial quotient coefficient attached to the profile sizes.
`Multiset.bell` is used only as an arithmetic function here. -/
def enumerativeCoefficient {b : ℕ} (k : ColoringProfile b) : ℕ :=
  (sizes k).bell

/-- The class-size factorial product has the coordinate form appearing in
(4.2).  Coordinates with value zero contribute a factor `1`. -/
theorem prod_map_factorial_sizes {b : ℕ} (k : ColoringProfile b) :
    ((sizes k).map Nat.factorial).prod =
      ∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i := by
  unfold sizes
  rw [map_multiset_finset, Multiset.prod_sum]
  simp [Multiset.map_replicate, Multiset.prod_replicate]

/-- The multiplicity of the positive size represented by coordinate `i` is
exactly `k i`. -/
theorem count_sizes_at {b : ℕ} (k : ColoringProfile b) (i : Fin b) :
    (sizes k).count (i.1 + 1) = k i := by
  unfold sizes
  rw [Multiset.count_sum']
  simp only [Multiset.count_replicate, Nat.add_left_inj]
  have hval (x : Fin b) : x.1 = i.1 ↔ x = i := by
    constructor
    · exact Fin.ext
    · intro h
      exact congrArg Fin.val h
  simp_rw [hval]
  exact Fintype.sum_ite_eq' i k

/-- Indices of class sizes that actually occur in the profile. -/
def support {b : ℕ} (k : ColoringProfile b) : Finset (Fin b) :=
  Finset.univ.filter fun i ↦ k i ≠ 0

/-- The distinct positive sizes in a profile are the images of its active
coordinates. -/
theorem toFinset_sizes {b : ℕ} (k : ColoringProfile b) :
    (sizes k).toFinset =
      (support k).image fun i ↦ i.1 + 1 := by
  classical
  ext s
  simp [sizes, support, Multiset.mem_replicate, eq_comm]

/-- The factorials of distinct-size multiplicities give the coordinate
factor `∏_i k_i!` in (4.2); zero coordinates again contribute `1`. -/
theorem prod_factorial_count_sizes {b : ℕ} (k : ColoringProfile b) :
    (∏ s ∈ (sizes k).toFinset.erase 0,
        Nat.factorial ((sizes k).count s)) =
      ∏ i : Fin b, Nat.factorial (k i) := by
  classical
  have hinj : Function.Injective (fun i : Fin b ↦ i.1 + 1) := by
    intro i j h
    apply Fin.ext
    exact Nat.add_right_cancel h
  have hzero : 0 ∉ (support k).image (fun i ↦ i.1 + 1) := by
    simp
  rw [toFinset_sizes, Finset.erase_eq_of_notMem hzero,
    Finset.prod_image hinj.injOn]
  simp_rw [count_sizes_at]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hki : k i = 0 := by
    simpa [support] using hi
  simp [hki]

/-- Multiplication-form factorial identity for the arithmetic profile
coefficient.  Unlike a division formula, this records divisibility without
any cancellation convention. -/
theorem enumerativeCoefficient_mul_denominator_eq {b : ℕ}
    (k : ColoringProfile b) :
    enumerativeCoefficient k *
        ((sizes k).map Nat.factorial).prod *
        (∏ s ∈ (sizes k).toFinset.erase 0,
          Nat.factorial ((sizes k).count s)) =
      Nat.factorial (vertexMass k) := by
  simpa [enumerativeCoefficient, vertexMass] using
    Multiset.bell_mul_eq (sizes k)

/-- Coordinate form of the multiplication identity behind the unordered
profile count in (4.2). -/
theorem enumerativeCoefficient_mul_coordinateDenominator_eq {b : ℕ}
    (k : ColoringProfile b) :
    enumerativeCoefficient k *
        (∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) *
        (∏ i : Fin b, Nat.factorial (k i)) =
      Nat.factorial (vertexMass k) := by
  rw [← prod_map_factorial_sizes, ← prod_factorial_count_sizes]
  exact enumerativeCoefficient_mul_denominator_eq k

/-- Exact factorial quotient satisfied by the arithmetic profile
coefficient.  This theorem does not assert the separate cardinality bridge
from `Finpartition`s to `Multiset.bell`. -/
theorem enumerativeCoefficient_eq_factorialQuotient {b : ℕ}
    (k : ColoringProfile b) :
    enumerativeCoefficient k =
      Nat.factorial (vertexMass k) /
        (((sizes k).map Nat.factorial).prod *
          ∏ s ∈ (sizes k).toFinset.erase 0,
            Nat.factorial ((sizes k).count s)) := by
  simpa [enumerativeCoefficient, vertexMass] using
    Multiset.bell_eq (sizes k)

/-- Coordinate factorial-quotient form, including all zero coordinates. -/
theorem enumerativeCoefficient_eq_coordinateFactorialQuotient {b : ℕ}
    (k : ColoringProfile b) :
    enumerativeCoefficient k =
      Nat.factorial (vertexMass k) /
        ((∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) *
          ∏ i : Fin b, Nat.factorial (k i)) := by
  rw [enumerativeCoefficient_eq_factorialQuotient,
    prod_map_factorial_sizes, prod_factorial_count_sizes]

end ColoringProfile

/-- An unordered partition of the labelled vertex set. -/
abbrev VertexPartition (n : ℕ) :=
  Finpartition (Finset.univ : Finset (Fin n))

/-- The multiset of block sizes of an unordered vertex partition. -/
def partitionShape {n : ℕ} (P : VertexPartition n) : Multiset ℕ :=
  P.parts.1.map Finset.card

@[simp] theorem card_partitionShape {n : ℕ} (P : VertexPartition n) :
    (partitionShape P).card = P.parts.card := by
  simp [partitionShape]

/-- The block sizes of a partition sum to the size of the vertex set. -/
theorem sum_partitionShape {n : ℕ} (P : VertexPartition n) :
    (partitionShape P).sum = n := by
  simpa [partitionShape] using P.sum_card_parts

/-- Unordered vertex partitions having exactly the prescribed positive
block-size profile. -/
def ProfilePartition {b : ℕ} (n : ℕ) (k : ColoringProfile b) :=
  {P : VertexPartition n //
    partitionShape P = ColoringProfile.sizes k}

instance instFintypeProfilePartition {b n : ℕ} (k : ColoringProfile b) :
    Fintype (ProfilePartition n k) :=
  Subtype.fintype _

/-- Existence of a partition of profile `k` forces the mass constraint. -/
theorem ProfilePartition.vertexMass_eq {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k) :
    ColoringProfile.vertexMass k = n := by
  rw [← sum_partitionShape P.1, P.2]
  rfl

/-- A profile partition has exactly the advertised number of nonempty
parts. -/
theorem ProfilePartition.card_parts_eq {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k) :
    P.1.parts.card = ColoringProfile.partCount k := by
  rw [← card_partitionShape P.1, P.2]
  rfl

/-- If the mass constraint fails, there are no partitions of that profile. -/
theorem not_nonempty_profilePartition_of_vertexMass_ne {b n : ℕ}
    {k : ColoringProfile b}
    (h : ColoringProfile.vertexMass k ≠ n) :
    ¬ Nonempty (ProfilePartition n k) := by
  rintro ⟨P⟩
  exact h P.vertexMass_eq

/-! ## The exact probability of a fixed partition -/

/-- The graph consisting of all edges internal to parts of `P`. -/
def partitionInternalGraph {n : ℕ} (P : VertexPartition n) :
    LabeledGraph n :=
  P.parts.sup completeOn

/-- Disjoint vertex sets support edge-disjoint complete graphs. -/
theorem disjoint_completeOn_of_disjoint {V : Type u}
    {A B : Finset V} (h : Disjoint A B) :
    Disjoint (completeOn A) (completeOn B) := by
  rw [SimpleGraph.disjoint_left]
  intro x y hA hB
  rw [completeOn, SimpleGraph.map_adj] at hA hB
  obtain ⟨xA, yA, -, rfl, -⟩ := hA
  obtain ⟨xB, yB, -, hx, -⟩ := hB
  apply Finset.disjoint_left.mp h xA.property
  have hx' : (xB : V) = (xA : V) := hx
  exact hx' ▸ xB.property

/-- Pairwise disjoint graphs have an edge count additive under finite
supremum. -/
theorem ncard_edgeSet_finset_sup_of_pairwise {V : Type u} [Fintype V]
    {I : Type*} [DecidableEq I] (s : Finset I) (f : I → SimpleGraph V)
    (h : (s : Set I).PairwiseDisjoint f) :
    (s.sup f).edgeSet.ncard = ∑ i ∈ s, (f i).edgeSet.ncard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hs : (s : Set I).PairwiseDisjoint f := by
        intro i hi j hj hij
        exact h (Finset.mem_insert_of_mem hi)
          (Finset.mem_insert_of_mem hj) hij
      have hdis : Disjoint (f a) (s.sup f) := by
        apply Finset.disjoint_sup_right.2
        intro i hi
        have hai : a ≠ i := fun hai ↦ ha (hai ▸ hi)
        exact h (Finset.mem_insert_self a s)
          (Finset.mem_insert_of_mem hi) hai
      have hedge : Disjoint (f a).edgeSet (s.sup f).edgeSet :=
        SimpleGraph.disjoint_edgeSet.mpr hdis
      rw [Finset.sup_insert, SimpleGraph.edgeSet_sup,
        Set.ncard_union_eq hedge, Finset.sum_insert ha, ih hs]

/-- Internal complete graphs belonging to distinct parts are edge-disjoint. -/
theorem pairwiseDisjoint_completeOn_parts {n : ℕ}
    (P : VertexPartition n) :
    (P.parts : Set (Finset (Fin n))).PairwiseDisjoint completeOn := by
  intro A hA B hB hAB
  exact disjoint_completeOn_of_disjoint (P.disjoint hA hB hAB)

/-- The internal graph has one edge for each pair inside each block. -/
theorem ncard_partitionInternalGraph {n : ℕ}
    (P : VertexPartition n) :
    (partitionInternalGraph P).edgeSet.ncard =
      ∑ B ∈ P.parts, B.card.choose 2 := by
  rw [partitionInternalGraph,
    ncard_edgeSet_finset_sup_of_pairwise P.parts completeOn
      (pairwiseDisjoint_completeOn_parts P)]
  apply Finset.sum_congr rfl
  intro B _
  exact ncard_edgeSet_completeOn B

/-- The internal edge count of a profile partition is the profile energy. -/
theorem ProfilePartition.ncard_partitionInternalGraph {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k) :
    (partitionInternalGraph P.1).edgeSet.ncard =
      ColoringProfile.forbiddenEdges k := by
  rw [Erdos625.ncard_partitionInternalGraph]
  rw [show (∑ B ∈ P.1.parts, B.card.choose 2) =
      ((partitionShape P.1).map fun s ↦ s.choose 2).sum by
    simp [partitionShape], P.2]
  rfl

/-- Event that every part of a fixed unordered partition is independent. -/
def partitionColoringEvent {n : ℕ} (P : VertexPartition n) :
    Set (LabeledGraph n) :=
  {G | ∀ B ∈ P.parts, G.IsIndepSet (B : Set (Fin n))}

theorem measurableSet_partitionColoringEvent {n : ℕ}
    (P : VertexPartition n) :
    MeasurableSet (partitionColoringEvent P) :=
  Set.toFinite (partitionColoringEvent P) |>.measurableSet

/-- All parts are independent exactly when the graph avoids the internal
edge graph of the partition. -/
theorem mem_partitionColoringEvent_iff_le_compl {n : ℕ}
    (P : VertexPartition n) (G : LabeledGraph n) :
    G ∈ partitionColoringEvent P ↔ G ≤ (partitionInternalGraph P)ᶜ := by
  rw [partitionColoringEvent, Set.mem_setOf_eq,
    partitionInternalGraph, le_compl_iff_disjoint_right,
    Finset.disjoint_sup_right]
  constructor
  · intro h B hB
    exact (isIndepSet_iff_disjoint_completeOn G B).mp (h B hB)
  · intro h B hB
    exact (isIndepSet_iff_disjoint_completeOn G B).mpr (h hB)

/-- The complement of a graph on `n` labelled vertices has the expected
number of available edges. -/
theorem ncard_edgeSet_compl {n : ℕ} (H : LabeledGraph n) :
    Hᶜ.edgeSet.ncard = n.choose 2 - H.edgeSet.ncard := by
  rw [← top_sdiff, SimpleGraph.edgeSet_sdiff, SimpleGraph.edgeSet_top,
    Set.ncard_sdiff' H.edgeSet_subset_compl_diagSet,
    Sym2.ncard_diagSet_compl]
  simp

/-- Exact `G(n,1/2)` probability of avoiding all edges of a fixed graph. -/
theorem randomGraphMeasure_le_compl {n : ℕ} (H : LabeledGraph n) :
    randomGraphMeasure n {G | G ≤ Hᶜ} =
      (1 / 2 : ENNReal) ^ H.edgeSet.ncard := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter fun G ↦ G ≤ Hᶜ
  have hcard : T.card = 2 ^ (n.choose 2 - H.edgeSet.ncard) := by
    calc
      T.card = Fintype.card {G : LabeledGraph n // G ≤ Hᶜ} := by
        simpa [T] using
          (Fintype.card_subtype (fun G : LabeledGraph n ↦ G ≤ Hᶜ)).symm
      _ = Nat.card {G : LabeledGraph n // G ≤ Hᶜ} := by
        rw [Nat.card_eq_fintype_card]
      _ = 2 ^ (n.choose 2 - H.edgeSet.ncard) := by
        rw [card_graphBelow, ncard_edgeSet_compl]
  have hE : H.edgeSet.ncard ≤ n.choose 2 := by
    calc
      H.edgeSet.ncard ≤
          (Sym2.diagSetᶜ : Set (Sym2 (Fin n))).ncard :=
        Set.ncard_le_ncard H.edgeSet_subset_compl_diagSet
          (Set.toFinite (Sym2.diagSetᶜ : Set (Sym2 (Fin n))))
      _ = n.choose 2 := by simpa using Sym2.ncard_diagSet_compl (Fin n)
  calc
    randomGraphMeasure n {G | G ≤ Hᶜ} =
        randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      congr 1
      ext G
      simp [T]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = ∑ _G ∈ T, (1 / 2 : ENNReal) ^ n.choose 2 := by
      simp_rw [randomGraphMeasure_singleton_uniform]
    _ = (2 : ENNReal) ^ (n.choose 2 - H.edgeSet.ncard) *
        (1 / 2 : ENNReal) ^ n.choose 2 := by
      simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = (1 / 2 : ENNReal) ^ H.edgeSet.ncard := by
      conv_lhs =>
        rhs
        rw [show n.choose 2 =
          (n.choose 2 - H.edgeSet.ncard) + H.edgeSet.ncard by
            exact (Nat.sub_add_cancel hE).symm, pow_add]
      rw [← mul_assoc, ← mul_pow]
      rw [div_eq_mul_inv, one_mul,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- A fixed unordered partition with profile `k` is a proper coloring with
the exact profile energy probability. -/
theorem randomGraphMeasure_partitionColoringEvent {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k) :
    randomGraphMeasure n (partitionColoringEvent P.1) =
      (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k := by
  rw [show partitionColoringEvent P.1 =
      {G | G ≤ (partitionInternalGraph P.1)ᶜ} by
    ext G
    exact mem_partitionColoringEvent_iff_le_compl P.1 G,
    randomGraphMeasure_le_compl,
    P.ncard_partitionInternalGraph]

/-! ## Exact first moment and the isolated enumeration bridge -/

/-- Indicator that a fixed profile partition is a proper coloring. -/
noncomputable def profilePartitionIndicator {b n : ℕ}
    (G : LabeledGraph n) {k : ColoringProfile b}
    (P : ProfilePartition n k) : ℕ := by
  classical
  exact if G ∈ partitionColoringEvent P.1 then 1 else 0

/-- Number of unordered proper colorings with exactly profile `k`. -/
noncomputable def profileColoringCount {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) : ℕ := by
  classical
  exact ∑ P : ProfilePartition n k, profilePartitionIndicator G P

/-- Finite weighted-sum expectation of the exact-profile coloring count. -/
noncomputable def profileColoringExpectation {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ENNReal :=
  ∑ G : LabeledGraph n,
    (profileColoringCount G k : ENNReal) * randomGraphMeasure n {G}

/-- Summing one fixed partition indicator recovers its event probability. -/
theorem sum_profilePartitionIndicator_measure {b n : ℕ}
    {k : ColoringProfile b} (P : ProfilePartition n k) :
    (∑ G : LabeledGraph n,
      (profilePartitionIndicator G P : ENNReal) *
        randomGraphMeasure n {G}) =
      randomGraphMeasure n (partitionColoringEvent P.1) := by
  classical
  let T := (Finset.univ : Finset (LabeledGraph n)).filter
    fun G ↦ G ∈ partitionColoringEvent P.1
  calc
    _ = ∑ G : LabeledGraph n,
        if G ∈ partitionColoringEvent P.1
        then randomGraphMeasure n {G} else 0 := by
      apply Finset.sum_congr rfl
      intro G _
      by_cases h : G ∈ partitionColoringEvent P.1 <;>
        simp [profilePartitionIndicator, h]
    _ = ∑ G ∈ T, randomGraphMeasure n {G} := by
      simp only [T, Finset.sum_filter]
    _ = randomGraphMeasure n (T : Set (LabeledGraph n)) := by
      rw [MeasureTheory.sum_measure_singleton]
    _ = randomGraphMeasure n (partitionColoringEvent P.1) := by
      congr 1
      ext G
      simp [T]

/-- Exact finite first moment in terms of the actual cardinality of the
unordered profile-partition type. -/
theorem profileColoringExpectation_eq_card_mul {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) :
    profileColoringExpectation n k =
      (Nat.card (ProfilePartition n k) : ENNReal) *
        (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k := by
  classical
  unfold profileColoringExpectation profileColoringCount
  simp_rw [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [sum_profilePartitionIndicator_measure,
    randomGraphMeasure_partitionColoringEvent]
  simp [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- The combinatorial bridge isolated at this layer: `Multiset.bell` is to
equal the cardinality of unordered `Finpartition`s of the prescribed shape.
This definition is a proposition, not an axiom; the downstream enumeration
modules construct and prove an inhabitant under the necessary mass equation. -/
def ProfileEnumerationStatement {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : Prop :=
  Nat.card (ProfilePartition n k) =
    ColoringProfile.enumerativeCoefficient k

/-- Once the explicit enumeration statement is supplied, the profile first
moment has exactly the arithmetic coefficient and energy factor used in
(4.2). -/
theorem profileColoringExpectation_eq_enumerativeCoefficient_mul_of
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (h : ProfileEnumerationStatement n k) :
    profileColoringExpectation n k =
      (ColoringProfile.enumerativeCoefficient k : ENNReal) *
        (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k := by
  rw [profileColoringExpectation_eq_card_mul, h]

/-- Conditional exact spelling of (4.2), with positive sizes indexed as
`i + 1`.  The only hypothesis is the explicitly isolated set-partition
enumeration bridge. -/
theorem profileColoringExpectation_eq_coordinateFactorialQuotient_mul_of
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (h : ProfileEnumerationStatement n k) :
    profileColoringExpectation n k =
      ((Nat.factorial (ColoringProfile.vertexMass k) /
          ((∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) *
            ∏ i : Fin b, Nat.factorial (k i)) : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k := by
  rw [profileColoringExpectation_eq_enumerativeCoefficient_mul_of n k h,
    ColoringProfile.enumerativeCoefficient_eq_coordinateFactorialQuotient]

/-- Exact conditional form of (4.2) with the manuscript numerator `n!`.
The mass equation is stated explicitly rather than inferred from a possibly
empty profile-partition type. -/
theorem profileColoringExpectation_eq_formula_of_mass
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (hmass : ColoringProfile.vertexMass k = n)
    (h : ProfileEnumerationStatement n k) :
    profileColoringExpectation n k =
      ((Nat.factorial n /
          ((∏ i : Fin b, (Nat.factorial (i.1 + 1)) ^ k i) *
            ∏ i : Fin b, Nat.factorial (k i)) : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ ColoringProfile.forbiddenEdges k := by
  rw [profileColoringExpectation_eq_coordinateFactorialQuotient_mul_of
    n k h, hmass]

/-- If the mass constraint fails, the exact-profile first moment is zero. -/
theorem profileColoringExpectation_eq_zero_of_vertexMass_ne
    {b : ℕ} (n : ℕ) (k : ColoringProfile b)
    (h : ColoringProfile.vertexMass k ≠ n) :
    profileColoringExpectation n k = 0 := by
  rw [profileColoringExpectation_eq_card_mul]
  have hne : IsEmpty (ProfilePartition n k) :=
    ⟨fun P ↦ h P.vertexMass_eq⟩
  letI : IsEmpty (ProfilePartition n k) := hne
  simp

end Erdos625
