import Erdos625.SPlusPrimalCoordinateBounds
import Erdos625.SPlusEntropySupremumDualInterior

/-!
# Representation of the limiting `S₊` entropy value

The finite dual inequality stored in the older witness structure follows
automatically from coordinatewise Gibbs inequalities and nonnegativity.  It
therefore imposes no extra admissibility condition: the older candidate set
is exactly the direct manuscript primal candidate set.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

/-- Nonnegativity alone implies the all-tilts finite truncation inequality.
No convergence, summability, target restriction, or optimizer is used. -/
theorem extendedGaussian_finite_dual_bound_of_nonneg
    {exceptional : ℝ} {p : ℕ → ℝ}
    (hexceptional : 0 ≤ exceptional)
    (hp : ∀ d, 0 ≤ p d) :
    ∀ tilt N,
      extendedGaussianEntropyTruncation q exceptional p N ≤
        extendedGaussianReferenceMassTruncation q tilt N -
          extendedGaussianMassTruncation exceptional p N +
          Real.log (extendedGaussianPartition q tilt) *
            extendedGaussianMassTruncation exceptional p N -
          tilt * extendedGaussianMomentTruncation exceptional p N := by
  intro tilt N
  have hex :=
    extendedGaussianExceptionalEntropyTerm_le_normalized
      tilt (x := exceptional) hexceptional
  have hnat :
      (∑ d ∈ Finset.range N,
        (-p d * Real.log (p d) +
          p d * extendedGaussianNaturalScore q d)) ≤
      ∑ d ∈ Finset.range N,
        (extendedGaussianNaturalTerm q tilt d /
              extendedGaussianPartition q tilt - p d +
            Real.log (extendedGaussianPartition q tilt) * p d -
            tilt * ((d : ℝ) * p d)) := by
    exact Finset.sum_le_sum fun d _ =>
      extendedGaussianNaturalEntropyTerm_le_normalized
        tilt d (hp d)
  unfold extendedGaussianEntropyTruncation
  calc
    (-exceptional * Real.log exceptional +
          exceptional * extendedGaussianExceptionalScore q) +
        ∑ d ∈ Finset.range N,
          (-p d * Real.log (p d) +
            p d * extendedGaussianNaturalScore q d)
        ≤
      (extendedGaussianExceptionalAtom q tilt /
            extendedGaussianPartition q tilt - exceptional +
          Real.log (extendedGaussianPartition q tilt) * exceptional +
          tilt * exceptional) +
        ∑ d ∈ Finset.range N,
          (extendedGaussianNaturalTerm q tilt d /
                extendedGaussianPartition q tilt - p d +
            Real.log (extendedGaussianPartition q tilt) * p d -
            tilt * ((d : ℝ) * p d)) :=
      add_le_add hex hnat
    _ =
      extendedGaussianReferenceMassTruncation q tilt N -
        extendedGaussianMassTruncation exceptional p N +
        Real.log (extendedGaussianPartition q tilt) *
          extendedGaussianMassTruncation exceptional p N -
        tilt * extendedGaussianMomentTruncation exceptional p N := by
      unfold extendedGaussianReferenceMassTruncation
        extendedGaussianMassTruncation
        extendedGaussianMomentTruncation
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      ring

/-- The all-tilts witness structure and the direct manuscript primal profile
have exactly the same inhabitants. -/
theorem extendedGaussianEntropyWitnessAllTilts_iff_sPlusPrimalProfile
    {target value exceptional : ℝ} {p : ℕ → ℝ} :
    ExtendedGaussianEntropyWitnessAllTilts
        target value exceptional p ↔
      SPlusPrimalProfile target value exceptional p := by
  constructor
  · intro h
    exact
      { exceptional_nonneg := h.exceptional_nonneg
        natural_nonneg := h.natural_nonneg
        mass_limit := h.mass_limit
        moment_limit := h.moment_limit
        entropy_limit := h.entropy_limit }
  · intro h
    exact
      { exceptional_nonneg := h.exceptional_nonneg
        natural_nonneg := h.natural_nonneg
        finite_dual_bound :=
          extendedGaussian_finite_dual_bound_of_nonneg
            h.exceptional_nonneg h.natural_nonneg
        mass_limit := h.mass_limit
        moment_limit := h.moment_limit
        entropy_limit := h.entropy_limit }

/-- The older witness-based candidate set is exactly the direct manuscript
primal candidate set. -/
theorem extendedGaussianEntropyCandidateSet_eq_sPlusPrimalCandidateSet
    (target : ℝ) :
    extendedGaussianEntropyCandidateSet target =
      sPlusPrimalCandidateSet target := by
  apply Set.ext
  intro value
  simp only [extendedGaussianEntropyCandidateSet,
    sPlusPrimalCandidateSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨exceptional, p, h⟩
    exact ⟨exceptional, p,
      extendedGaussianEntropyWitnessAllTilts_iff_sPlusPrimalProfile.mp h⟩
  · rintro ⟨exceptional, p, h⟩
    exact ⟨exceptional, p,
      extendedGaussianEntropyWitnessAllTilts_iff_sPlusPrimalProfile.mpr h⟩

/-- The entropy value used by the existing dual comparison is unconditionally
equal to the direct manuscript primal supremum. -/
theorem extendedGaussianEntropyValue_eq_sPlusPrimalEntropyValue
    (target : ℝ) :
    extendedGaussianEntropyValue target =
      sPlusPrimalEntropyValue target := by
  unfold extendedGaussianEntropyValue sPlusPrimalEntropyValue
  rw [extendedGaussianEntropyCandidateSet_eq_sPlusPrimalCandidateSet]

/-- Rewrite the existing four-point loss using the direct manuscript primal. -/
theorem fourEntropyLoss_eq_sPlusPrimalEntropyValue_sub
    (target : ℝ) :
    fourEntropyLoss target =
      sPlusPrimalEntropyValue target -
        ProfileEntropyS4.optimizedValue fourGaussianScore target := by
  simp [fourEntropyLoss,
    extendedGaussianEntropyValue_eq_sPlusPrimalEntropyValue]

end


end Erdos625
