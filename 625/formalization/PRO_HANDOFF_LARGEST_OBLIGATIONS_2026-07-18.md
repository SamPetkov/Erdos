# Erdős 625: largest remaining Lean obligations

Date: 18 July 2026

This is a paste-ready handoff for a strong Lean prover.  The current source
tree has no `sorry`, `admit`, project axiom, `opaque`, `unsafe`, or
`native_decide`, but the final theorem remains conditional.  A result is not
acceptable if it merely renames one of the obligations below as a hypothesis.

## Exact final seam

The current shortest route to `Erdos625Statement` is the already proved
theorem `erdos625Statement_of_uniform_seed_and_root` in
`Erdos625/Section10_11UniformSeedRootFinal.lean`:

```lean
theorem erdos625Statement_of_uniform_seed_and_root
    (kChi kCo : Nat → Nat) (Lambda rho : Nat → Real)
    (hLambdaNonneg : ∀ᶠ n in atTop, 0 ≤ Lambda n)
    (hLambdaSmall : Lambda =o[atTop] amplificationBase)
    (hSeed : ∀ᶠ n in atTop,
      Real.exp (-Lambda n) ≤
        (randomGraphMeasure n).real {G | CoColorable G (kCo n)})
    (hChromaticAtMost : Tendsto
      (fun n => randomGraphMeasure n
        {G : LabeledGraph n | chromaticNumberNat G ≤ kChi n})
      atTop (nhds 0))
    (hrho : Tendsto rho atTop (nhds 0))
    (hroot : ∀ᶠ n in atTop,
      (((Real.log 2)^2 / 16 * Real.log (200 / 153 : Real)) - rho n) *
          baseScale n ≤
        (kChi n : Real) - (kCo n : Real)) :
    Erdos625Statement
```

Thus the three largest final groups, using the same `kChi` and `kCo`, are:

1. construct the signed cocolouring count and prove the rare seed with
   `Lambda = o(amplificationBase)`;
2. prove the concrete chromatic at-most tail;
3. construct the two concrete roots and prove their separation with
   `rho → 0`.

The most useful first assignment is the signed count and Lemma 6.1, because it
creates the random variable required by every later seed theorem.

## Paste this task into Pro

```text
Task: formalize the missing graph-level signed-profile count and the exact
first/second-moment bridge through manuscript Lemma 6.1 for Erdős Problem 625.

Repository:
C:\Users\petko\OneDrive - Université Paris Sciences et Lettres\Documents\Erdos\625\formalization

Authoritative manuscript:
625/arxiv/main.tex, Sections 5 and 6, especially Lemma 6.1.

Required imports:
import Erdos625.ColoringProfileEnumerationInjective
import Erdos625.ColoringProfileLogWeight
import Erdos625.OrderedOverlapLaw
import Erdos625.Section6CompatibleSignsComponents
import Erdos625.LocalSignReward
import Erdos625.ConfigurationModelCellMarginals
import Erdos625.ConfigurationModelProbability
import Mathlib.Tactic

namespace Erdos625
open MeasureTheory SimpleGraph
open scoped BigOperators ENNReal
noncomputable section

Do not add axioms, opaque constants, unsafe declarations, sorry, admit,
native_decide, or a renamed version of Lemma 6.1 as a hypothesis.  Do not
claim the final Erdős theorem, Lemma 9.1, or Proposition 9.2.
```

### Graph-level signed count

The following definitions have been elaboration-checked against the current
Lean project:

```lean
def profileSignValid {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (P : ProfilePartition n k)
    (σ : P.1.parts → Bool) : Prop :=
  ∀ B : P.1.parts,
    match σ B with
    | false => G.IsIndepSet (B.1 : Set (Fin n))
    | true  => G.IsClique (B.1 : Set (Fin n))

abbrev SignedProfileWitness {b : ℕ} (n : ℕ)
    (k : ColoringProfile b) :=
  Σ P : ProfilePartition n k, P.1.parts → Bool

def validSignedProfileWitness {b n : ℕ} {k : ColoringProfile b}
    (G : LabeledGraph n) (w : SignedProfileWitness n k) : Prop :=
  profileSignValid G w.1 w.2

noncomputable def signedProfileCount {b n : ℕ}
    (G : LabeledGraph n) (k : ColoringProfile b) : ℕ := by
  classical
  exact (Finset.univ.filter fun w : SignedProfileWitness n k =>
    validSignedProfileWitness G w).card

noncomputable def signedProfileExpectation {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ENNReal :=
  ∑ G : LabeledGraph n,
    (signedProfileCount G k : ENNReal) * randomGraphMeasure n {G}

noncomputable def signedProfileSecondMoment {b : ℕ}
    (n : ℕ) (k : ColoringProfile b) : ENNReal :=
  ∑ G : LabeledGraph n,
    ((signedProfileCount G k) ^ 2 : ENNReal) *
      randomGraphMeasure n {G}
```

Required theorems:

```lean
theorem signedProfileCount_pos_implies_coColorable
    {b n : ℕ} {G : LabeledGraph n} {k : ColoringProfile b} :
    0 < signedProfileCount G k →
      CoColorable G (ColoringProfile.partCount k)

theorem signedProfileExpectation_eq
    {b n : ℕ} (k : ColoringProfile b) :
    signedProfileExpectation n k =
      (2 : ENNReal) ^ ColoringProfile.partCount k *
        profileColoringExpectation n k
```

Do not replace `signedProfileCount G k` pointwise by
`2^partCount * profileColoringCount G k`: that is false.  The factor occurs
only after averaging over the random graph.

### Exact local factor from Lemma 6.1

```lean
def signedOverlapSupportGraph {A B : Type*}
    (r : A → B → ℕ) : SimpleGraph (A ⊕ B) :=
  bipartiteGraph fun a b => 2 ≤ r a b

noncomputable def overlapDuplicateEdgeCount
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → ℕ) : ℕ :=
  ∑ a, ∑ b, (r a b).choose 2

noncomputable def signedOverlapReward
    {A B : Type*} [Fintype A] [Fintype B]
    (r : A → B → ℕ) : ℕ :=
  (∏ a, ∏ b, localSignRewardNat (r a b)) *
    2 ^ cycleRank (signedOverlapSupportGraph r)

noncomputable def CompatibleOverlapSignAssignments
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) := by
  classical
  exact CompatibleBoolSignAssignments (signedOverlapSupportGraph r)

theorem signedOverlapLocalFactor_cross
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : A → B → ℕ) :
    Nat.card (CompatibleOverlapSignAssignments r) *
        2 ^ overlapDuplicateEdgeCount r =
      2 ^ (Fintype.card A + Fintype.card B) *
        signedOverlapReward r
```

This denominator-free theorem is the best bounded task to prove first.
It may add only these two local helpers:

1. exact edge cardinality of `signedOverlapSupportGraph` (the existing API has
   only a one-sided inequality);
2. the global product identity for `localSignRewardNat`.

### Mathematical proof of the local factor

For two ordered partitions let `r a b` be the intersection size,
`W = Σ a, Σ b, choose (r a b) 2`, and let `H` have edge `a-b` exactly
when `r a b ≥ 2`.

1. A row sign and a column sign are compatible precisely when they agree on
   every edge of `H`; hence signs are constant on connected components.
2. On the full vertex type `A ⊕ B`, isolated vertices already represent the
   free signs.  Therefore there are `2^c(H_full)` compatible assignments.
3. If one partition prescribes `B` internal edge bits, two compatible signed
   partitions prescribe `2B-W` distinct bits.  Their joint probability is
   therefore `2^(-(2B-W))`.
4. Dividing by the product of the two one-partition signed masses gives
   `2^(W + c(H) - |V(H)|)` in the manuscript convention omitting isolates.
5. On each support edge split
   `choose (r a b) 2 = (choose (r a b) 2 - 1) + 1`.
   The first terms give `∏ g(r a b)` and the remaining exponent is
   `|E|-|V|+c = cycleRank(H)`.

Important edge cases: a cell of size one imposes no sign compatibility;
incompatible sign pairs contribute probability zero; isolated vertices must
not be discarded without accounting for their free signs.

### Remaining bridge after the local factor

The full Lemma 6.1 assignment must additionally prove:

1. the duplicated-bit formula as an equality of actual finite edge sets;
2. an exact probability lemma for disjoint finite present/absent edge
   prescriptions;
3. the pointwise ordered/unordered multiplier
   `∏ i : Fin b, Nat.factorial (k i)`;
4. that overlap-table fibres exhaust and disjointly group all ordered pairs;
5. the fixed-margin table average

```lean
theorem signedProfile_normalizedSecondMoment_eq_overlapTableSum
    {b n : ℕ} (k : ColoringProfile b)
    (hmass : ColoringProfile.vertexMass k = n)
    (row : OrderedProfilePartition n k) :
    signedProfileSecondMoment n k /
        (signedProfileExpectation n k) ^ 2 =
      ∑ r in orderedProfileOverlapTables row,
        ((Fintype.card
            (FixedMarginOverlapEvent row.1 r (profileBlockMargin k)) :
              ENNReal) /
          (Fintype.card (OrderedProfilePartition n k) : ENNReal)) *
        (signedOverlapReward r : ENNReal)
```

The result must be proved independent of the chosen fixed row, not assumed by
an informal transitivity argument.

## Other theorem-sized obligations

After Lemma 6.1, the remaining manuscript-sized tasks are:

- **Lemma 8.3:** the full uniform quantitative skeleton-weight bound, including
  global `W(L)` comparison and the near/middle estimates;
- **Lemma 9.1:** faithful uniform instantiation of the attachment estimate for
  every feasible tagged skeleton;
- **Proposition 9.2:** assemble those estimates into the graph-level signed
  second moment and prove `Lambda = o(amplificationBase)`;
- **chromatic tail:** define the manuscript threshold and prove the complete
  profile envelope tends to `atBot` for that threshold;
- **root package:** define the concrete roots and prove the root advantage,
  slope bound, rounding control, and final shared-threshold separation.

Every accepted patch must build with `--wfail`, pass the trust scan, and show
only standard Mathlib axioms under `#print axioms`.
