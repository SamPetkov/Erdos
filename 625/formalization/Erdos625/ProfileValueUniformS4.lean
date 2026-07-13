import Erdos625.ProfileValueStabilityS4

/-!
# Uniform-in-target stability of the optimized four-point profile value

The pointwise value estimate in `ProfileValueStabilityS4` has a constant
independent of the target.  Consequently, uniform convergence of the four
score coordinates implies convergence of the optimized values uniformly over
the entire interior target interval `(2,5)`, and hence uniformly over every
subset of that interval.

The conclusions below use explicit epsilon/eventual quantifiers.  In
particular, the same index `N` works for every target in the stated set.  This
module proves only value convergence; it makes no claim about convergence of
the tilt or optimizer, nor about a uniform lower bound for optimizer
coordinates.
-/

namespace Erdos625.ProfileEntropyS4

noncomputable section

/-- Uniform convergence of the four score coordinates implies eventual
uniform convergence of optimized values on any set of interior targets.  The
index `N` is independent of `T ∈ K`. -/
theorem eventually_uniformOn_optimizedValue_of_uniform_scores
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ) (K : Set ℝ)
    (hK : K ⊆ Set.Ioo (2 : ℝ) 5)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ K,
      |optimizedValue (h n) T - optimizedValue g T| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := huniform (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn T hTK ↦ ?_⟩
  exact lt_of_le_of_lt
    (abs_optimizedValue_sub_optimizedValue_le (h n) g (hK hTK)
      (half_pos hε).le (fun i ↦ (hN n hn i).le))
    (half_lt_self hε)

/-- Uniform convergence of the four score coordinates implies convergence of
the optimized values uniformly in every target `T ∈ (2,5)`.  Written with
explicit quantifiers, the conclusion says that one index `N` works
simultaneously for all such `T`. -/
theorem eventually_uniform_optimizedValue_on_Ioo_of_uniform_scores
    (h : ℕ → Fin 4 → ℝ) (g : Fin 4 → ℝ)
    (huniform : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i, |h n i - g i| < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ T ∈ Set.Ioo (2 : ℝ) 5,
      |optimizedValue (h n) T - optimizedValue g T| < ε :=
  eventually_uniformOn_optimizedValue_of_uniform_scores h g
    (Set.Ioo (2 : ℝ) 5) (fun _ hT ↦ hT) huniform

end

end Erdos625.ProfileEntropyS4
