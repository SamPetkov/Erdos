import Erdos625.Section9CanonicalSupportMatching
import Erdos625.Section9RewardCompatibility
import Erdos625.Section9CycleRankResidual

/-!
# Section IX: canonical reward and support decomposition

For one fixed canonical-demand witness, the full cell count is the sum of its
exposed demand and transported residual count.  On the canonical residual
event, no residual pair returns to the positive demand support.  This gives an
exact product decomposition of the local reward.  If the cutoff parameter is
at least two, every positive canonical demand is itself at least two, so the
support of cells of full multiplicity at least two is exactly the union of the
positive demand support and the residual multiplicity-two support.

The no-return hypothesis is explicit in the reward lemmas.  The graph lemmas
instead require the separate pointwise lower bound on positive demands; the
canonical specialization derives it from `2 ≤ U`.  No probability estimate,
cycle-space cardinality, or attachment bound is asserted here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- A local reward splits across an exposed demand and a residual count when
the residual count vanishes at every positive exposed demand. -/
theorem residualReward_add_eq_mul_of_noReturn
    (demand residual : ℕ)
    (hnoReturn : demand ≠ 0 → residual = 0) :
    residualReward (demand + residual) =
      localSignRewardNat demand * residualReward residual := by
  by_cases hdemand : demand = 0
  · subst demand
    simp [localSignRewardNat, residualReward]
  · rw [hnoReturn hdemand]
    simp [residualReward_eq_localSignRewardNat, localSignRewardNat]

/-- The product of full-cell rewards splits into the exposed reward on the
positive demand support and the product of all residual rewards. -/
theorem prod_residualReward_add_eq_positiveSupport_mul
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand residual : A → B → ℕ)
    (hnoReturn : ∀ a b, demand a b ≠ 0 → residual a b = 0) :
    (∏ a : A, ∏ b : B,
        residualReward (demand a b + residual a b)) =
      (∏ e ∈ positiveDemandSupport demand,
        localSignRewardNat (demand e.1 e.2)) *
        (∏ a : A, ∏ b : B, residualReward (residual a b)) := by
  classical
  have hsupport :
      (∏ e ∈ positiveDemandSupport demand,
          localSignRewardNat (demand e.1 e.2)) =
        ∏ a : A, ∏ b : B, localSignRewardNat (demand a b) := by
    rw [← Fintype.prod_ite_mem]
    calc
      (∏ e : A × B,
          if e ∈ positiveDemandSupport demand then
            localSignRewardNat (demand e.1 e.2) else 1) =
          ∏ e : A × B, localSignRewardNat (demand e.1 e.2) := by
            apply Fintype.prod_congr
            intro e
            by_cases he : demand e.1 e.2 = 0
            · simp [positiveDemandSupport, he, localSignRewardNat]
            · simp [positiveDemandSupport, he]
      _ = ∏ a : A, ∏ b : B, localSignRewardNat (demand a b) :=
        Fintype.prod_prod_type'
          (fun a : A ↦ fun b : B ↦ localSignRewardNat (demand a b))
  simp_rw [residualReward_add_eq_mul_of_noReturn _ _ (hnoReturn _ _)]
  simp_rw [Finset.prod_mul_distrib]
  rw [hsupport]

/-- Adding a table entry whose positive values are at least two creates a
multiplicity-two cell exactly when that entry is positive or the added entry
already has multiplicity at least two. -/
theorem two_le_add_iff_positive_or_two_le
    (demand residual : ℕ)
    (hpositive : demand ≠ 0 → 2 ≤ demand) :
    2 ≤ demand + residual ↔ demand ≠ 0 ∨ 2 ≤ residual := by
  by_cases hdemand : demand = 0
  · simp [hdemand]
  · have htwo := hpositive hdemand
    omega

/-- The support graph of cells of total multiplicity at least two is the
union of the positive demand support and the residual multiplicity-two
support, provided every positive demand is at least two. -/
theorem bipartiteGraph_positiveSupport_add_eq_union
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand residual : A → B → ℕ)
    (hpositive : ∀ a b, demand a b ≠ 0 → 2 ≤ demand a b) :
    bipartiteGraph (fun a b ↦ 2 ≤ demand a b + residual a b) =
      bipartiteGraph
          (fun a b ↦ (a, b) ∈ positiveDemandSupport demand) ⊔
        bipartiteGraph (fun a b ↦ 2 ≤ residual a b) := by
  rw [← bipartiteGraph_or_eq_sup]
  apply congrArg bipartiteGraph
  funext a b
  apply propext
  simpa only [positiveDemandSupport, Finset.mem_filter, Finset.mem_univ,
    true_and] using
      two_le_add_iff_positive_or_two_le
        (demand a b) (residual a b) (hpositive a b)

/-- For a fixed labelled witness of an attained canonical demand, membership
in the canonical event gives both exact deterministic decompositions needed
by the Section IX local expansion: the local-reward product split and the
multiplicity-two support-graph split.

The assumption `2 ≤ U` is used only to turn the strict canonical high-demand
bound `U / 2 < demand` into `2 ≤ demand`. -/
theorem fixedWitnessCanonical_reward_support_split
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {row : A → ℕ} {col : B → ℕ} (U : ℕ)
    (hU : 2 ≤ U)
    (demand : canonicalDemandImage row col U)
    (witness : PrescribedDemandWitness demand.1 row col)
    (extension : fixedWitnessExtensionEvent witness)
    (hevent : extension ∈ fixedWitnessCanonicalDemandEvent witness U) :
    let residual := fixedWitnessExtensionEquivResidual witness extension
    ((∏ a : A, ∏ b : B,
          residualReward (configurationCellCount extension.1 a b)) =
        (∏ e ∈ positiveDemandSupport demand.1,
          localSignRewardNat (demand.1 e.1 e.2)) *
          (∏ a : A, ∏ b : B,
            residualReward (configurationCellCount residual a b))) ∧
      (bipartiteGraph
          (fun a b ↦ 2 ≤ configurationCellCount extension.1 a b) =
        bipartiteGraph
            (fun a b ↦ (a, b) ∈ positiveDemandSupport demand.1) ⊔
          bipartiteGraph
            (fun a b ↦ 2 ≤ configurationCellCount residual a b)) := by
  dsimp only
  let residual := fixedWitnessExtensionEquivResidual witness extension
  have hhigh : ∀ a b, demand.1 a b ≠ 0 → U / 2 < demand.1 a b :=
    canonicalDemandImage_high row col U demand
  have hresidual : residual ∈ canonicalResidualCellEvent witness U := by
    exact (mem_fixedWitnessCanonicalDemandEvent_iff_residual
      witness U hhigh extension).mp hevent
  have hnoReturn : ∀ a b, demand.1 a b ≠ 0 →
      configurationCellCount residual a b = 0 := by
    intro a b hab
    exact (hresidual a b).2 hab
  have hpositive : ∀ a b, demand.1 a b ≠ 0 → 2 ≤ demand.1 a b := by
    intro a b hab
    have hcellHigh := hhigh a b hab
    omega
  have hcell : ∀ a b,
      configurationCellCount extension.1 a b =
        demand.1 a b + configurationCellCount residual a b := by
    intro a b
    exact configurationCellCount_eq_demand_add_residual
      witness extension a b
  constructor
  · simp_rw [hcell]
    exact prod_residualReward_add_eq_positiveSupport_mul
      demand.1 (configurationCellCount residual) hnoReturn
  · simp_rw [hcell]
    exact bipartiteGraph_positiveSupport_add_eq_union
      demand.1 (configurationCellCount residual) hpositive

#print axioms residualReward_add_eq_mul_of_noReturn
#print axioms prod_residualReward_add_eq_positiveSupport_mul
#print axioms two_le_add_iff_positive_or_two_le
#print axioms bipartiteGraph_positiveSupport_add_eq_union
#print axioms fixedWitnessCanonical_reward_support_split

end

end Erdos625
