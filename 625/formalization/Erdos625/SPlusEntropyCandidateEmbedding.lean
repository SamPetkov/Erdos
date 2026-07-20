import Erdos625.ExtendedGaussianEntropyTransport
import Erdos625.ProfileOptimizerS4
import Mathlib.Tactic

/-!
# Finite `S₄` witness inside the limiting `S₊` entropy lane

This source-only module isolates the exact finite-support inclusion used by
the limiting-entropy comparison. It does not assert finite-cutoff convergence,
a moving-root theorem, any random-graph statement, or the final Erdős 625
conclusion.
-/

open Filter
open scoped Topology BigOperators

namespace Erdos625

noncomputable section

/-- A concrete admissible limiting entropy witness at a prescribed target.
The exceptional atom has deficit `-1`; the natural sequence is indexed by
nonnegative deficits. The finite inequality is the `tilt = 0` instance of the
existing truncation dual transport, written explicitly so the finite
four-point embedding is a genuine candidate rather than an assumed inclusion.
-/
structure ExtendedGaussianEntropyWitness
    (target value exceptional : ℝ) (p : ℕ → ℝ) : Prop where
  exceptional_nonneg : 0 ≤ exceptional
  natural_nonneg : ∀ d, 0 ≤ p d
  finite_dual_bound : ∀ N,
    extendedGaussianEntropyTruncation q exceptional p N ≤
      extendedGaussianReferenceMassTruncation q 0 N -
        extendedGaussianMassTruncation exceptional p N +
        Real.log (extendedGaussianPartition q 0) *
          extendedGaussianMassTruncation exceptional p N
  mass_limit : Tendsto (extendedGaussianMassTruncation exceptional p)
    atTop (nhds 1)
  moment_limit : Tendsto (extendedGaussianMomentTruncation exceptional p)
    atTop (nhds target)
  entropy_limit : Tendsto (extendedGaussianEntropyTruncation q exceptional p)
    atTop (nhds value)

/-- **Finite `S₄ ⊆ S₊` witness.** The target-matching four-point optimizer is
embedded at natural deficit coordinates `2,3,4,5`, with zero exceptional mass
and zero mass elsewhere. This establishes only the limiting candidate
inclusion; it does not identify a finite-cutoff entropy limit. -/
theorem exists_s4_embedded_extendedGaussian_witness
    {target : ℝ} (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    ∃ exceptional p,
      ExtendedGaussianEntropyWitness target
        (ProfileEntropyS4.optimizedValue fourGaussianScore target)
        exceptional p := by
  let w : Fin 4 → ℝ := ProfileEntropyS4.optimizer fourGaussianScore target
  let p : ℕ → ℝ := fun d ↦
    if d = 2 then w 0 else if d = 3 then w 1 else
    if d = 4 then w 2 else if d = 5 then w 3 else 0
  refine ⟨0, p, ?_⟩
  have hw0 : ∀ i, 0 ≤ w i := ProfileEntropyS4.optimizer_nonneg _ _
  have hwsum : ∑ i : Fin 4, w i = 1 :=
    ProfileEntropyS4.sum_optimizer _ _
  have hwmean : ∑ i : Fin 4, w i * ProfileEntropyS4.support i = target :=
    ProfileEntropyS4.sum_optimizer_mul_support _ hT
  have hwvalue :
      -(∑ i : Fin 4, w i * Real.log (w i)) +
          ∑ i : Fin 4, w i * fourGaussianScore i =
        ProfileEntropyS4.optimizedValue fourGaussianScore target := by
    exact ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target
      fourGaussianScore hT
  have hp0 (d : ℕ) : 0 ≤ p d := by
    dsimp [p]
    split_ifs <;> first | exact hw0 _ | exact le_rfl
  have hp_out (d : ℕ) (hd : 6 ≤ d) : p d = 0 := by
    have h2 : d ≠ 2 := by omega
    have h3 : d ≠ 3 := by omega
    have h4 : d ≠ 4 := by omega
    have h5 : d ≠ 5 := by omega
    simp [p, h2, h3, h4, h5]
  have hscore (i : Fin 4) :
      extendedGaussianNaturalScore q (i.1 + 2) = fourGaussianScore i := by
    simp [extendedGaussianNaturalScore, fourGaussianScore,
      ProfileEntropyS4.support]
    ring
  have hfinite (N : ℕ) :
      extendedGaussianEntropyTruncation q 0 p N ≤
        extendedGaussianReferenceMassTruncation q 0 N -
          extendedGaussianMassTruncation 0 p N +
          Real.log (extendedGaussianPartition q 0) *
            extendedGaussianMassTruncation 0 p N := by
    have hZ : 0 < extendedGaussianPartition q 0 :=
      extendedGaussianPartition_pos q_pos
    have hterm (d : ℕ) :
        -p d * Real.log (p d) + p d * extendedGaussianNaturalScore q d ≤
          extendedGaussianNaturalTerm q 0 d / extendedGaussianPartition q 0 - p d +
            Real.log (extendedGaussianPartition q 0) * p d := by
      have hy : 0 < extendedGaussianNaturalTerm q 0 d /
          extendedGaussianPartition q 0 :=
        div_pos (extendedGaussianNaturalTerm_pos q 0 d) hZ
      have hh := ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub (hp0 d) hy
      have hlog : Real.log (extendedGaussianNaturalTerm q 0 d /
            extendedGaussianPartition q 0) =
          extendedGaussianNaturalScore q d -
            Real.log (extendedGaussianPartition q 0) := by
        rw [Real.log_div (extendedGaussianNaturalTerm_pos q 0 d).ne'
          hZ.ne', extendedGaussianNaturalTerm, Real.log_exp]
        simp [extendedGaussianNaturalScore]
        ring
      rw [hlog] at hh
      linarith
    have hsum := Finset.sum_le_sum fun d (_hd : d ∈ Finset.range N) ↦ hterm d
    unfold extendedGaussianEntropyTruncation extendedGaussianReferenceMassTruncation
      extendedGaussianMassTruncation extendedGaussianExceptionalScore at *
    simp only [zero_mul, neg_zero, Real.log_zero, zero_add, Finset.sum_add_distrib,
      Finset.sum_sub_distrib] at hsum ⊢
    rw [Finset.mul_sum]
    have hex : 0 ≤ extendedGaussianExceptionalAtom q 0 /
        extendedGaussianPartition q 0 :=
      (div_pos (extendedGaussianExceptionalAtom_pos q 0) hZ).le
    linarith
  refine
    { exceptional_nonneg := le_rfl
      natural_nonneg := hp0
      finite_dual_bound := hfinite
      mass_limit := ?_
      moment_limit := ?_
      entropy_limit := ?_ }
  · have hevent : ∀ᶠ N : ℕ in atTop,
        extendedGaussianMassTruncation 0 p N = 1 := by
      filter_upwards [eventually_atTop.2 ⟨6, fun _ hN ↦ hN⟩] with N hN
      unfold extendedGaussianMassTruncation
      simp only [zero_add]
      rw [← Finset.sum_subset (show Finset.range 6 ⊆ Finset.range N by
        intro d hd
        simp only [Finset.mem_range] at hd ⊢
        omega) (fun d _hdN hd6 ↦ hp_out d (by
          simp only [Finset.mem_range] at hd6
          omega))]
      norm_num [Finset.sum_range_succ, p]
      simpa [Fin.sum_univ_four] using hwsum
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hevent)
      tendsto_const_nhds
  · have hevent : ∀ᶠ N : ℕ in atTop,
        extendedGaussianMomentTruncation 0 p N = target := by
      filter_upwards [eventually_atTop.2 ⟨6, fun _ hN ↦ hN⟩] with N hN
      rw [← hwmean]
      unfold extendedGaussianMomentTruncation
      simp only [neg_zero, zero_add]
      rw [← Finset.sum_subset (show Finset.range 6 ⊆ Finset.range N by
        intro d hd
        simp only [Finset.mem_range] at hd ⊢
        omega) (fun d _hdN hd6 ↦ by
          rw [hp_out d (by
            simp only [Finset.mem_range] at hd6
            omega), mul_zero])]
      norm_num [Finset.sum_range_succ, p]
      simp [Fin.sum_univ_four, ProfileEntropyS4.support]
      ring
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hevent)
      tendsto_const_nhds
  · have hevent : ∀ᶠ N : ℕ in atTop,
        extendedGaussianEntropyTruncation q 0 p N =
          ProfileEntropyS4.optimizedValue fourGaussianScore target := by
      filter_upwards [eventually_atTop.2 ⟨6, fun _ hN ↦ hN⟩] with N hN
      rw [← hwvalue]
      unfold extendedGaussianEntropyTruncation
      simp only [zero_mul, neg_zero, Real.log_zero, zero_add]
      rw [← Finset.sum_subset (show Finset.range 6 ⊆ Finset.range N by
        intro d hd
        simp only [Finset.mem_range] at hd ⊢
        omega) (fun d _hdN hd6 ↦ by
          rw [hp_out d (by
            simp only [Finset.mem_range] at hd6
            omega)]
          simp)]
      have hs0 := hscore (0 : Fin 4)
      have hs1 := hscore (1 : Fin 4)
      have hs2 := hscore (2 : Fin 4)
      have hs3 := hscore (3 : Fin 4)
      norm_num [Finset.sum_range_succ, p]
      norm_num at hs0 hs1 hs2 hs3
      rw [hs0, hs1, hs2, hs3]
      simp [Fin.sum_univ_four]
      ring
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hevent)
      tendsto_const_nhds

end

end Erdos625
