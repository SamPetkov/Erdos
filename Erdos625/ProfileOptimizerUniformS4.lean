import Erdos625.ProfileOptimizerContinuityS4
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Compact-target uniformity of the four-point tilt and optimizer

The preceding continuity module proves filterwise joint continuity of the
finite four-support mean inverse.  Here that genuinely joint statement is
combined with Heine--Cantor on a compact target set.  The result is uniform
convergence in the target, first for tilts and then for all four optimizer
coordinates simultaneously.

No sequential-to-uniform inference is made: joint continuity is established
on score-target product spaces, and compactness of the target subtype is used
explicitly.  The final section also obtains a genuine compact-product positive
minimum and transfers it to an eventual uniform lower bound.
-/

open Filter Finset

namespace Erdos625.ProfileEntropyS4

noncomputable section

/-! ## Joint continuity on the interior target interval -/

/-- The tilt is jointly continuous at every score-target pair whose target is
strictly inside the support interval. -/
theorem continuousAt_tilt_joint
    (x : (Fin 4 → ℝ) × ℝ) (hx : x.2 ∈ Set.Ioo (2 : ℝ) 5) :
    ContinuousAt (fun y : (Fin 4 → ℝ) × ℝ ↦ tilt y.1 y.2) x := by
  exact tendsto_tilt_of_scores_and_target
    (h := fun y : (Fin 4 → ℝ) × ℝ ↦ y.1) x.1
    (T' := fun y ↦ y.2)
    (fun i ↦ ((continuous_apply i).comp continuous_fst).continuousAt)
    continuous_snd.continuousAt hx

/-- Each optimizer coordinate is jointly continuous at every score-target
pair whose target is strictly inside the support interval. -/
theorem continuousAt_optimizer_joint
    (i : Fin 4) (x : (Fin 4 → ℝ) × ℝ)
    (hx : x.2 ∈ Set.Ioo (2 : ℝ) 5) :
    ContinuousAt (fun y : (Fin 4 → ℝ) × ℝ ↦ optimizer y.1 y.2 i) x := by
  exact tendsto_optimizer_of_scores_and_target
    (h := fun y : (Fin 4 → ℝ) × ℝ ↦ y.1) x.1
    (T' := fun y ↦ y.2)
    (fun j ↦ ((continuous_apply j).comp continuous_fst).continuousAt)
    continuous_snd.continuousAt hx i

/-- At a fixed score, each optimizer coordinate is continuous in every
interior target. -/
theorem continuousAt_optimizer_fixed_score
    (g : Fin 4 → ℝ) (i : Fin 4) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    ContinuousAt (fun T' ↦ optimizer g T' i) T := by
  exact tendsto_optimizer_of_scores_and_target
    (h := fun _ : ℝ ↦ g) g (T' := id)
    (fun _ ↦ tendsto_const_nhds) tendsto_id hT i

/-! ## Uniform convergence over compact target sets -/

/-- As the score vector tends to `g`, its tilt function tends uniformly to the
limiting tilt on every compact subset `K` of `(2,5)`.  The target is represented
by the subtype `K`, so this is an actual `TendstoUniformly` statement. -/
theorem tendstoUniformly_tilt_on_compact
    (g : Fin 4 → ℝ) (K : Set ℝ) (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5) :
    TendstoUniformly
      (fun h : Fin 4 → ℝ ↦ fun T : K ↦ tilt h T.1)
      (fun T : K ↦ tilt g T.1) (nhds g) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  have hJoint : Continuous
      (fun x : (Fin 4 → ℝ) × K ↦ tilt x.1 x.2.1) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact tendsto_tilt_of_scores_and_target
      (h := fun y : (Fin 4 → ℝ) × K ↦ y.1) x.1
      (T' := fun y ↦ y.2.1)
      (fun i ↦ ((continuous_apply i).comp continuous_fst).continuousAt)
      ((continuous_subtype_val.comp continuous_snd).continuousAt)
      (hKinterior x.2.2)
  exact ContinuousOn.tendstoUniformly univ_mem hJoint.continuousOn

/-- For a fixed coordinate, optimizer convergence as the score tends to `g`
is uniform over every compact interior target set. -/
theorem tendstoUniformly_optimizer_on_compact
    (g : Fin 4 → ℝ) (K : Set ℝ) (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5) (i : Fin 4) :
    TendstoUniformly
      (fun h : Fin 4 → ℝ ↦ fun T : K ↦ optimizer h T.1 i)
      (fun T : K ↦ optimizer g T.1 i) (nhds g) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  have hJoint : Continuous
      (fun x : (Fin 4 → ℝ) × K ↦ optimizer x.1 x.2.1 i) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact tendsto_optimizer_of_scores_and_target
      (h := fun y : (Fin 4 → ℝ) × K ↦ y.1) x.1
      (T' := fun y ↦ y.2.1)
      (fun j ↦ ((continuous_apply j).comp continuous_fst).continuousAt)
      ((continuous_subtype_val.comp continuous_snd).continuousAt)
      (hKinterior x.2.2) i
  exact ContinuousOn.tendstoUniformly univ_mem hJoint.continuousOn

/-! ## Explicit sequential quantifiers -/

/-- A common coordinatewise error bound for the four scores implies convergence
of the score vectors in the finite product topology. -/
theorem tendsto_scores_of_uniform_coordinates
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    Tendsto h atTop (nhds g) := by
  refine tendsto_pi_nhds.2 fun i ↦ ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := huniform ε hε
  refine ⟨N, fun n hn ↦ ?_⟩
  simpa [Real.dist_eq] using hN n hn i

/-- **Compact-target tilt uniformity.**  Uniform convergence of all four score
coordinates gives one index `N` that works for every `T ∈ K`.  Compactness is
used through the preceding joint Heine--Cantor statement, not inferred from
pointwise sequential convergence. -/
theorem eventually_uniformOn_tilt_of_uniform_scores
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ) (K : Set ℝ)
    (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ K,
      |tilt (h n) T - tilt g T| < ε := by
  have hScores : Tendsto h atTop (nhds g) :=
    tendsto_scores_of_uniform_coordinates h g huniform
  have hUniformNhds :=
    tendstoUniformly_tilt_on_compact g K hKcompact hKinterior
  have hUniformTop : TendstoUniformly
      (fun n : ℕ ↦ fun T : K ↦ tilt (h n) T.1)
      (fun T : K ↦ tilt g T.1) atTop := by
    intro u hu
    exact hScores (hUniformNhds u hu)
  intro ε hε
  have hEventually := (Metric.tendstoUniformly_iff.mp hUniformTop) ε hε
  rw [eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  refine ⟨N, fun n hn T hTK ↦ ?_⟩
  have hdist := hN n hn ⟨T, hTK⟩
  simpa [Real.dist_eq, abs_sub_comm] using hdist

/-- For a fixed coordinate, optimizer convergence is uniform over a compact
interior target set, with all eventual quantifiers explicit. -/
theorem eventually_uniformOn_optimizer_coordinate_of_uniform_scores
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ) (K : Set ℝ)
    (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5) (i : Fin 4)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ j, |h n j - g j| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ K,
      |optimizer (h n) T i - optimizer g T i| < ε := by
  have hScores : Tendsto h atTop (nhds g) :=
    tendsto_scores_of_uniform_coordinates h g huniform
  have hUniformNhds :=
    tendstoUniformly_optimizer_on_compact g K hKcompact hKinterior i
  have hUniformTop : TendstoUniformly
      (fun n : ℕ ↦ fun T : K ↦ optimizer (h n) T.1 i)
      (fun T : K ↦ optimizer g T.1 i) atTop := by
    intro u hu
    exact hScores (hUniformNhds u hu)
  intro ε hε
  have hEventually := (Metric.tendstoUniformly_iff.mp hUniformTop) ε hε
  rw [eventually_atTop] at hEventually
  obtain ⟨N, hN⟩ := hEventually
  refine ⟨N, fun n hn T hTK ↦ ?_⟩
  have hdist := hN n hn ⟨T, hTK⟩
  simpa [Real.dist_eq, abs_sub_comm] using hdist

/-- **Simultaneous compact-target optimizer uniformity.**  A single index works
for every target in `K` and all four optimizer coordinates. -/
theorem eventually_uniformOn_optimizer_of_uniform_scores
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ) (K : Set ℝ)
    (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ K, ∀ i,
      |optimizer (h n) T i - optimizer g T i| < ε := by
  intro ε hε
  have hCoordinate : ∀ i : Fin 4, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ K,
      |optimizer (h n) T i - optimizer g T i| < ε := fun i ↦
    eventually_uniformOn_optimizer_coordinate_of_uniform_scores
      h g K hKcompact hKinterior i huniform ε hε
  choose N hN using hCoordinate
  refine ⟨Finset.univ.sup N, fun n hn T hTK i ↦ ?_⟩
  exact hN i n ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn) T hTK

/-! ## Genuine compact positivity -/

/-- Every limiting optimizer coordinate has one common positive lower bound
on a compact interior target set.  The proof minimizes over the compact
product `K × Fin 4`; discreteness of `Fin 4` reduces continuity to the four
fixed-coordinate continuity statements. -/
theorem exists_uniform_optimizer_lower_bound_on_compact
    (g : Fin 4 → ℝ) (K : Set ℝ) (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5) :
    ∃ c > 0, ∀ T ∈ K, ∀ i, c ≤ optimizer g T i := by
  have hContinuous : ContinuousOn
      (fun x : ℝ × Fin 4 ↦ optimizer g x.1 x.2)
      (K ×ˢ (Set.univ : Set (Fin 4))) := by
    rw [continuousOn_prod_of_discrete_right]
    intro i
    have hFixed : ContinuousOn (fun T : ℝ ↦ optimizer g T i) K := by
      intro T hTK
      exact (continuousAt_optimizer_fixed_score g i
        (hKinterior hTK)).continuousWithinAt
    simpa only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, and_true,
      Set.setOf_mem_eq] using hFixed
  have hPositive : ∀ x ∈ K ×ˢ (Set.univ : Set (Fin 4)),
      0 < optimizer g x.1 x.2 := fun x _hx ↦ optimizer_pos g x.1 x.2
  obtain ⟨c, hc, hLower⟩ :=
    (hKcompact.prod isCompact_univ).exists_forall_le' hContinuous hPositive
  exact ⟨c, hc, fun T hTK i ↦ hLower (T, i) ⟨hTK, Set.mem_univ i⟩⟩

/-- **The positivity clause of finite-four-support (3.9b).**  Uniform score
convergence gives a positive constant and one eventual index after which all
four moving optimizer coordinates are bounded below by that constant,
simultaneously for every target in `K`. -/
theorem eventually_uniform_optimizer_pos_on_compact
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ) (K : Set ℝ)
    (hKcompact : IsCompact K)
    (hKinterior : K ⊆ Set.Ioo (2 : ℝ) 5)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ K, ∀ i,
      c ≤ optimizer (h n) T i := by
  obtain ⟨c, hc, hLimitLower⟩ :=
    exists_uniform_optimizer_lower_bound_on_compact g K hKcompact hKinterior
  obtain ⟨N, hN⟩ := eventually_uniformOn_optimizer_of_uniform_scores
    h g K hKcompact hKinterior huniform (c / 2) (half_pos hc)
  refine ⟨c / 2, half_pos hc, N, fun n hn T hTK i ↦ ?_⟩
  have hClose := hN n hn T hTK i
  have hLeft := (abs_lt.mp hClose).1
  have hBase := hLimitLower T hTK i
  linarith

end

end Erdos625.ProfileEntropyS4
