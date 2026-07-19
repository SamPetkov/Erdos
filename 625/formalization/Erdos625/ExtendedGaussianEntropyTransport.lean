import Erdos625.SignedFourEntropyCertificate
import Erdos625.SeriesConvergenceTools
import Mathlib.Tactic

/-!
# Transport of finite extended-Gaussian entropy bounds

This module supplies the truncation-to-limit step for the entropy lane.  A
competitor consists of an explicit exceptional mass at deficit `-1` and a
natural-index mass sequence.  Nonnegativity, normalization, the first moment,
and convergence of the entropy-plus-Gaussian-score truncations are all stated
as hypotheses.  No assertion about the numerical partition ratio is made.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Erdos625

noncomputable section

/-- The limiting Gaussian score on a natural deficit coordinate. -/
def extendedGaussianNaturalScore (a : ℝ) (d : ℕ) : ℝ :=
  -a / 2 * (d : ℝ) ^ 2

/-- The Gaussian score of the exceptional deficit coordinate `-1`. -/
def extendedGaussianExceptionalScore (a : ℝ) : ℝ := -a / 2

/-- Entropy plus Gaussian score of a competitor, truncated to the exceptional
coordinate and natural deficits below `N`.  The convention `0 * log 0 = 0`
is inherited from `Real.log 0 = 0`. -/
def extendedGaussianEntropyTruncation
    (a exceptional : ℝ) (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  (-exceptional * Real.log exceptional +
      exceptional * extendedGaussianExceptionalScore a) +
    ∑ d ∈ range N,
      (-p d * Real.log (p d) + p d * extendedGaussianNaturalScore a d)

/-- Truncated total mass, including the exceptional endpoint. -/
def extendedGaussianMassTruncation
    (exceptional : ℝ) (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  exceptional + ∑ d ∈ range N, p d

/-- Truncated first moment, with the exceptional coordinate equal to `-1`. -/
def extendedGaussianMomentTruncation
    (exceptional : ℝ) (p : ℕ → ℝ) (N : ℕ) : ℝ :=
  -exceptional + ∑ d ∈ range N, (d : ℝ) * p d

/-- The normalized reference mass retained by a finite truncation. -/
def extendedGaussianReferenceMassTruncation
    (a tilt : ℝ) (N : ℕ) : ℝ :=
  extendedGaussianExceptionalAtom a tilt / extendedGaussianPartition a tilt +
    ∑ d ∈ range N,
      extendedGaussianNaturalTerm a tilt d / extendedGaussianPartition a tilt

/-- The retained normalized reference mass converges to one. -/
theorem tendsto_extendedGaussianReferenceMassTruncation
    {a tilt : ℝ} (ha : 0 < a) :
    Tendsto (extendedGaussianReferenceMassTruncation a tilt) atTop (nhds 1) := by
  have hsum : Tendsto
      (fun N ↦ ∑ d ∈ range N, extendedGaussianNaturalTerm a tilt d)
      atTop (nhds (∑' d : ℕ, extendedGaussianNaturalTerm a tilt d)) :=
    (summable_extendedGaussianNaturalTerm ha).hasSum.tendsto_sum_nat
  have hdiv := hsum.div_const (extendedGaussianPartition a tilt)
  have hadd : Tendsto
      (fun N ↦ extendedGaussianExceptionalAtom a tilt /
          extendedGaussianPartition a tilt +
        (∑ d ∈ range N, extendedGaussianNaturalTerm a tilt d) /
          extendedGaussianPartition a tilt)
      atTop (nhds (extendedGaussianExceptionalAtom a tilt /
          extendedGaussianPartition a tilt +
        (∑' d : ℕ, extendedGaussianNaturalTerm a tilt d) /
          extendedGaussianPartition a tilt)) :=
    tendsto_const_nhds.add hdiv
  have hfun : extendedGaussianReferenceMassTruncation a tilt =
      fun N ↦ extendedGaussianExceptionalAtom a tilt /
          extendedGaussianPartition a tilt +
        (∑ d ∈ range N, extendedGaussianNaturalTerm a tilt d) /
          extendedGaussianPartition a tilt := by
    funext N
    unfold extendedGaussianReferenceMassTruncation
    rw [Finset.sum_div]
  have hlimit : extendedGaussianExceptionalAtom a tilt /
          extendedGaussianPartition a tilt +
        (∑' d : ℕ, extendedGaussianNaturalTerm a tilt d) /
          extendedGaussianPartition a tilt = 1 := by
    rw [← add_div, ← extendedGaussianPartition]
    exact div_self (extendedGaussianPartition_ne_zero ha)
  rw [hfun, ← hlimit]
  exact hadd

/-- Finite truncations transport to the extended Gaussian dual bound.  This is
valid at every real target, including the endpoint value `-1`; no interiority
assumption is used.  The hypotheses explicitly require nonnegative masses,
normalization in the limit, convergence of the first moment, and convergence
of the entropy-plus-score truncations. -/
theorem extendedGaussianEntropy_le_dual_of_truncations
    {a target tilt unrestrictedEntropy exceptional : ℝ} {p : ℕ → ℝ}
    (ha : 0 < a)
    (hexceptional : 0 ≤ exceptional)
    (hp : ∀ d, 0 ≤ p d)
    (hfinite : 0 ≤ exceptional → (∀ d, 0 ≤ p d) → ∀ N,
      extendedGaussianEntropyTruncation a exceptional p N ≤
        extendedGaussianReferenceMassTruncation a tilt N -
          extendedGaussianMassTruncation exceptional p N +
          Real.log (extendedGaussianPartition a tilt) *
            extendedGaussianMassTruncation exceptional p N -
          tilt * extendedGaussianMomentTruncation exceptional p N)
    (hmass : Tendsto (extendedGaussianMassTruncation exceptional p)
      atTop (nhds 1))
    (hmoment : Tendsto (extendedGaussianMomentTruncation exceptional p)
      atTop (nhds target))
    (hentropy : Tendsto (extendedGaussianEntropyTruncation a exceptional p)
      atTop (nhds unrestrictedEntropy)) :
    unrestrictedEntropy ≤
      Real.log (extendedGaussianPartition a tilt) - tilt * target := by
  have href := tendsto_extendedGaussianReferenceMassTruncation
    (a := a) (tilt := tilt) ha
  have hlogmass : Tendsto
      (fun N ↦ Real.log (extendedGaussianPartition a tilt) *
        extendedGaussianMassTruncation exceptional p N)
      atTop (nhds (Real.log (extendedGaussianPartition a tilt) * 1)) :=
    tendsto_const_nhds.mul hmass
  have htiltmoment : Tendsto
      (fun N ↦ tilt * extendedGaussianMomentTruncation exceptional p N)
      atTop (nhds (tilt * target)) :=
    tendsto_const_nhds.mul hmoment
  have hrhs : Tendsto
      (fun N ↦ extendedGaussianReferenceMassTruncation a tilt N -
        extendedGaussianMassTruncation exceptional p N +
        Real.log (extendedGaussianPartition a tilt) *
          extendedGaussianMassTruncation exceptional p N -
        tilt * extendedGaussianMomentTruncation exceptional p N)
      atTop (nhds (Real.log (extendedGaussianPartition a tilt) -
        tilt * target)) := by
    simpa only [sub_self, zero_add, mul_one] using
      ((href.sub hmass).add hlogmass).sub htiltmoment
  exact le_of_tendsto_of_tendsto' hentropy hrhs (hfinite hexceptional hp)

/-- Specialization at the manuscript parameter `q`, in exactly the form
required by `entropy_loss_le_log_partition_ratio`. -/
theorem extendedGaussianEntropy_le_dual_of_truncations_q
    {target tilt unrestrictedEntropy exceptional : ℝ} {p : ℕ → ℝ}
    (hexceptional : 0 ≤ exceptional)
    (hp : ∀ d, 0 ≤ p d)
    (hfinite : 0 ≤ exceptional → (∀ d, 0 ≤ p d) → ∀ N,
      extendedGaussianEntropyTruncation q exceptional p N ≤
        extendedGaussianReferenceMassTruncation q tilt N -
          extendedGaussianMassTruncation exceptional p N +
          Real.log (extendedGaussianPartition q tilt) *
            extendedGaussianMassTruncation exceptional p N -
          tilt * extendedGaussianMomentTruncation exceptional p N)
    (hmass : Tendsto (extendedGaussianMassTruncation exceptional p)
      atTop (nhds 1))
    (hmoment : Tendsto (extendedGaussianMomentTruncation exceptional p)
      atTop (nhds target))
    (hentropy : Tendsto (extendedGaussianEntropyTruncation q exceptional p)
      atTop (nhds unrestrictedEntropy)) :
    unrestrictedEntropy ≤ extendedGaussianDualTestValue target tilt := by
  exact extendedGaussianEntropy_le_dual_of_truncations q_pos hexceptional hp
    hfinite hmass hmoment hentropy

/-- The truncation transport discharges the unrestricted variational input in
the conditional certificate.  The only remaining manuscript-specific input is
the displayed strict partition-ratio inequality. -/
theorem signed_margin_gt_log_200_div_153_of_truncations
    {target tilt unrestrictedEntropy exceptional : ℝ} {p : ℕ → ℝ}
    (h_mean : ProfileEntropyS4.mean fourGaussianScore tilt = target)
    (hexceptional : 0 ≤ exceptional)
    (hp : ∀ d, 0 ≤ p d)
    (hfinite : 0 ≤ exceptional → (∀ d, 0 ≤ p d) → ∀ N,
      extendedGaussianEntropyTruncation q exceptional p N ≤
        extendedGaussianReferenceMassTruncation q tilt N -
          extendedGaussianMassTruncation exceptional p N +
          Real.log (extendedGaussianPartition q tilt) *
            extendedGaussianMassTruncation exceptional p N -
          tilt * extendedGaussianMomentTruncation exceptional p N)
    (hmass : Tendsto (extendedGaussianMassTruncation exceptional p)
      atTop (nhds 1))
    (hmoment : Tendsto (extendedGaussianMomentTruncation exceptional p)
      atTop (nhds target))
    (hentropy : Tendsto (extendedGaussianEntropyTruncation q exceptional p)
      atTop (nhds unrestrictedEntropy))
    (h_partition_ratio_bound :
      extendedGaussianPartition q tilt /
          ProfileEntropyS4.partition fourGaussianScore tilt <
        (153 / 100 : ℝ)) :
    Real.log (200 / 153 : ℝ) <
      q - (unrestrictedEntropy -
        ProfileEntropyS4.optimizedValue fourGaussianScore target) := by
  apply signed_margin_gt_log_200_div_153_of_dual_ratio h_mean
  · exact extendedGaussianEntropy_le_dual_of_truncations_q
      hexceptional hp hfinite hmass hmoment hentropy
  · exact h_partition_ratio_bound

end

#print axioms tendsto_extendedGaussianReferenceMassTruncation
#print axioms extendedGaussianEntropy_le_dual_of_truncations
#print axioms extendedGaussianEntropy_le_dual_of_truncations_q
#print axioms signed_margin_gt_log_200_div_153_of_truncations

end Erdos625

