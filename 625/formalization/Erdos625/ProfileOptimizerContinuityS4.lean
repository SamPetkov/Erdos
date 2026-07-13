import Erdos625.ProfileValueUniformS4

/-!
# Sequential continuity of the four-point tilt and optimizer

This module proves the finite-support parameter-continuity brick needed for
the profile analysis.  Coordinatewise convergence of the four score
coordinates and convergence of an interior target imply convergence of the
unique exponential tilt and of every optimizer coordinate.

The tilt proof is order-theoretic.  It compares the moving mean at two fixed
points on either side of the limiting tilt and uses strict monotonicity of the
mean.  Thus it does not assume boundedness of the moving tilts, invoke a
compactness subsequence, or hide such a compactness argument in a continuity
claim.  These are sequential (more generally, filterwise) statements; no
uniform-on-compact-target conclusion is asserted here.
-/

open Filter Finset

namespace Erdos625.ProfileEntropyS4

noncomputable section

/-! ## Joint continuity of the elementary finite sums -/

/-- Joint convergence of one unnormalized mass under coordinatewise score
convergence and convergence of the scalar parameter. -/
theorem tendsto_unnormalized_of_scores_and_parameter
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (t : A → ℝ) (t₀ : ℝ)
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (ht : Tendsto t l (nhds t₀)) (i : Fin 4) :
    Tendsto (fun a ↦ unnormalized (h a) (t a) i) l
      (nhds (unnormalized g t₀ i)) := by
  apply Real.continuous_exp.continuousAt.tendsto.comp
  exact (hscores i).add (ht.mul_const (support i))

/-- Joint convergence of the partition function. -/
theorem tendsto_partition_of_scores_and_parameter
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (t : A → ℝ) (t₀ : ℝ)
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (ht : Tendsto t l (nhds t₀)) :
    Tendsto (fun a ↦ partition (h a) (t a)) l
      (nhds (partition g t₀)) := by
  simp only [partition]
  simpa using tendsto_finsetSum Finset.univ
    (fun i _hi ↦
      tendsto_unnormalized_of_scores_and_parameter h g t t₀ hscores ht i)

/-- Joint convergence of the first-moment numerator. -/
theorem tendsto_firstNumerator_of_scores_and_parameter
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (t : A → ℝ) (t₀ : ℝ)
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (ht : Tendsto t l (nhds t₀)) :
    Tendsto (fun a ↦ firstNumerator (h a) (t a)) l
      (nhds (firstNumerator g t₀)) := by
  simp only [firstNumerator]
  simpa using tendsto_finsetSum Finset.univ
    (fun i _hi ↦
      (tendsto_unnormalized_of_scores_and_parameter
        h g t t₀ hscores ht i).const_mul (support i))

/-- Joint convergence of the mean.  In particular, taking `t` constant gives
fixed-parameter mean convergence from coordinatewise score convergence. -/
theorem tendsto_mean_of_scores_and_parameter
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (t : A → ℝ) (t₀ : ℝ)
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (ht : Tendsto t l (nhds t₀)) :
    Tendsto (fun a ↦ mean (h a) (t a)) l (nhds (mean g t₀)) := by
  exact (tendsto_firstNumerator_of_scores_and_parameter
      h g t t₀ hscores ht).div
    (tendsto_partition_of_scores_and_parameter h g t t₀ hscores ht)
    (ne_of_gt (partition_pos g t₀))

/-- Fixed-parameter mean convergence from convergence of each of the four
score coordinates. -/
theorem tendsto_mean_of_coordinatewise_scores
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ) (t : ℝ)
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i))) :
    Tendsto (fun a ↦ mean (h a) t) l (nhds (mean g t)) := by
  simpa using tendsto_mean_of_scores_and_parameter h g
    (fun _ ↦ t) t hscores tendsto_const_nhds

/-- Joint convergence of a normalized mass. -/
theorem tendsto_weight_of_scores_and_parameter
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (t : A → ℝ) (t₀ : ℝ)
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (ht : Tendsto t l (nhds t₀)) (i : Fin 4) :
    Tendsto (fun a ↦ weight (h a) (t a) i) l
      (nhds (weight g t₀ i)) := by
  exact (tendsto_unnormalized_of_scores_and_parameter
      h g t t₀ hscores ht i).div
    (tendsto_partition_of_scores_and_parameter h g t t₀ hscores ht)
    (ne_of_gt (partition_pos g t₀))

/-! ## Convergence of the inverse mean parameter -/

/-- Coordinatewise convergence of scores together with convergence of an
interior target implies convergence of the unique target-matching tilt.

For each fixed point strictly below (respectively above) the limiting tilt,
strict monotonicity gives a strict limiting mean inequality.  The two moving
quantities preserve this inequality eventually, which traps the moving tilt.
No a priori bound on those tilts is assumed. -/
theorem tendsto_tilt_of_scores_and_target
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (T' : A → ℝ) {T : ℝ}
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (hT' : Tendsto T' l (nhds T))
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    Tendsto (fun a ↦ tilt (h a) (T' a)) l (nhds (tilt g T)) := by
  rw [tendsto_order]
  constructor
  · intro lower hlower
    have hMeanLower : mean g lower < T := by
      calc
        mean g lower < mean g (tilt g T) := strictMono_mean g hlower
        _ = T := mean_tilt_eq g hT
    have hCompare : ∀ᶠ a in l, mean (h a) lower < T' a :=
      (tendsto_mean_of_coordinatewise_scores h g lower hscores).eventually_lt
        hT' hMeanLower
    have hInterior : ∀ᶠ a in l, T' a ∈ Set.Ioo (2 : ℝ) 5 :=
      hT' (isOpen_Ioo.mem_nhds hT)
    filter_upwards [hCompare, hInterior] with a ha hTa
    have hTiltMean := mean_tilt_eq (h a) hTa
    rw [← hTiltMean] at ha
    exact (strictMono_mean (h a)).lt_iff_lt.mp ha
  · intro upper hupper
    have hMeanUpper : T < mean g upper := by
      calc
        T = mean g (tilt g T) := (mean_tilt_eq g hT).symm
        _ < mean g upper := strictMono_mean g hupper
    have hCompare : ∀ᶠ a in l, T' a < mean (h a) upper :=
      hT'.eventually_lt
        (tendsto_mean_of_coordinatewise_scores h g upper hscores) hMeanUpper
    have hInterior : ∀ᶠ a in l, T' a ∈ Set.Ioo (2 : ℝ) 5 :=
      hT' (isOpen_Ioo.mem_nhds hT)
    filter_upwards [hCompare, hInterior] with a ha hTa
    have hTiltMean := mean_tilt_eq (h a) hTa
    rw [← hTiltMean] at ha
    exact (strictMono_mean (h a)).lt_iff_lt.mp ha

/-! ## Convergence of the optimizer -/

/-- Under the same hypotheses, every coordinate of the four-point optimizer
converges to the corresponding limiting optimizer coordinate. -/
theorem tendsto_optimizer_of_scores_and_target
    {A : Type*} {l : Filter A}
    (h : A → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (T' : A → ℝ) {T : ℝ}
    (hscores : ∀ i, Tendsto (fun a ↦ h a i) l (nhds (g i)))
    (hT' : Tendsto T' l (nhds T))
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) (i : Fin 4) :
    Tendsto (fun a ↦ optimizer (h a) (T' a) i) l
      (nhds (optimizer g T i)) := by
  exact tendsto_weight_of_scores_and_parameter h g
    (fun a ↦ tilt (h a) (T' a)) (tilt g T) hscores
    (tendsto_tilt_of_scores_and_target h g T' hscores hT' hT) i

end

end Erdos625.ProfileEntropyS4
