import Erdos625.ColoringProfileDeficitScoreBounds
import Erdos625.ColoringProfileDeficitTilt
import Erdos625.SPlusPrimalRepresentation
import Mathlib.Tactic

/-!
# Finite profile-deficit entropy comparison

This module embeds the exact finite deficit Gibbs optimizer into the limiting
extended-Gaussian primal.  The exceptional deficit `-1` coordinate is kept
separate, while the remaining finite coordinates are reversed onto natural
deficits and extended by zero.
-/

namespace Erdos625

open Filter Set
open scoped Topology BigOperators

noncomputable section

set_option autoImplicit false

/-- Reindexing the deficit support: the exceptional top coordinate plus the
reversed natural coordinates. -/
private theorem finiteProfileDeficit_sum_reindex
    (alpha : ℕ) (g : Fin (alpha + 1) → ℝ) :
    ∑ i : Fin (alpha + 1), g i =
      g (Fin.last alpha) + ∑ d : Fin alpha, g (Fin.rev d.succ) := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (alpha + 1))) g
  rw [← h, Fin.sum_univ_succ]
  congr 1

/-- A truncated sum stabilizes once the truncation covers the finite
support. -/
private theorem finiteProfileDeficit_sum_range_eq
    (alpha N : ℕ) (hN : alpha ≤ N) (f : ℕ → ℝ)
    (hf : ∀ d, alpha ≤ d → f d = 0) :
    ∑ d ∈ Finset.range N, f d = ∑ d : Fin alpha, f d.1 := by
  rw [Fin.sum_univ_eq_sum_range f alpha]
  have hsub : Finset.range alpha ⊆ Finset.range N := fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hN)
  refine (Finset.sum_subset hsub ?_).symm
  intro x _ hx
  exact hf x (by simpa [Finset.mem_range] using hx)

/-- The exact attained finite unrestricted deficit entropy is bounded by the
limiting extended-Gaussian primal entropy. -/
theorem finiteProfileDeficitEntropy_le_extendedGaussianEntropyValue
    (alpha : ℕ) (halpha : 5 < alpha)
    {target : ℝ} (htarget : target ∈ Set.Ioo (2 : ℝ) 5) :
    Real.log
          (profileDeficitPartition alpha
            (profileDeficitTilt alpha target)) -
        profileDeficitTilt alpha target * target ≤
      extendedGaussianEntropyValue target := by
  obtain ⟨ht2, ht5⟩ := htarget
  have halpha0 : 0 < alpha := by omega
  have halphaR : (6 : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast halpha
  have htargetIoo : target ∈ Set.Ioo (-1 : ℝ) ((alpha : ℝ) - 1) :=
    ⟨by linarith, by linarith⟩
  set lam : ℝ := profileDeficitTilt alpha target with hlam
  set Z : ℝ := profileDeficitPartition alpha lam with hZ
  have hZpos : 0 < Z := profileDeficitPartition_pos alpha lam
  set w : Fin (alpha + 1) → ℝ := fun i => profileDeficitWeight alpha lam i
    with hw
  have hwpos : ∀ i, 0 < w i := fun i => profileDeficitWeight_pos alpha lam i
  set exceptional : ℝ := w (Fin.last alpha) with hexc
  set p : ℕ → ℝ := fun d =>
    if h : d < alpha then w (Fin.rev (⟨d, h⟩ : Fin alpha).succ) else 0
    with hp
  have hp_nonneg : ∀ d, 0 ≤ p d := by
    intro d
    simp only [hp]
    split
    · exact (hwpos _).le
    · exact le_rfl
  have hp_fin : ∀ d : Fin alpha, p d.1 = w (Fin.rev d.succ) := by
    intro d
    simp only [hp, dif_pos d.2]
  have hp_zero : ∀ d, alpha ≤ d → p d = 0 := by
    intro d hd
    simp only [hp, dif_neg (by omega : ¬ d < alpha)]
  have hmass : ∀ N, alpha ≤ N →
      extendedGaussianMassTruncation exceptional p N = 1 := by
    intro N hN
    have h1 : ∑ d ∈ Finset.range N, p d = ∑ d : Fin alpha, w (Fin.rev d.succ) := by
      rw [finiteProfileDeficit_sum_range_eq alpha N hN p hp_zero]
      exact Finset.sum_congr rfl fun d _ => hp_fin d
    rw [extendedGaussianMassTruncation, h1, hexc,
      ← finiteProfileDeficit_sum_reindex alpha w]
    exact sum_profileDeficitWeight alpha lam
  have hmeanEq : profileDeficitMean alpha lam = target :=
    profileDeficitMean_profileDeficitTilt halpha0 htargetIoo
  have hmoment : ∀ N, alpha ≤ N →
      extendedGaussianMomentTruncation exceptional p N = target := by
    intro N hN
    have h1 : ∑ d ∈ Finset.range N, (d : ℝ) * p d =
        ∑ d : Fin alpha, (d.1 : ℝ) * w (Fin.rev d.succ) := by
      rw [finiteProfileDeficit_sum_range_eq alpha N hN
        (fun d => (d : ℝ) * p d) (by intro d hd; rw [hp_zero d hd, mul_zero])]
      exact Finset.sum_congr rfl fun d _ => by rw [hp_fin d]
    have h2 : profileDeficitMean alpha lam =
        -exceptional + ∑ d : Fin alpha, (d.1 : ℝ) * w (Fin.rev d.succ) := by
      rw [profileDeficitMean,
        finiteProfileDeficit_sum_reindex alpha
          (fun i => w i * profileDeficit alpha i)]
      rw [profileDeficit_last]
      simp only [profileDeficit_rev_succ]
      rw [hexc]
      ring_nf
      congr 1
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [extendedGaussianMomentTruncation, h1, ← h2, hmeanEq]
  set V : ℝ := ∑ i : Fin (alpha + 1),
      (-(w i) * Real.log (w i) +
        w i * (-q / 2 * (profileDeficit alpha i) ^ 2)) with hV
  have hentropy : ∀ N, alpha ≤ N →
      extendedGaussianEntropyTruncation q exceptional p N = V := by
    intro N hN
    have h1 : ∑ d ∈ Finset.range N,
          (-p d * Real.log (p d) + p d * extendedGaussianNaturalScore q d) =
        ∑ d : Fin alpha,
          (-(w (Fin.rev d.succ)) * Real.log (w (Fin.rev d.succ)) +
            w (Fin.rev d.succ) *
              (-q / 2 * (profileDeficit alpha (Fin.rev d.succ)) ^ 2)) := by
      rw [finiteProfileDeficit_sum_range_eq alpha N hN
        (fun d => -p d * Real.log (p d) +
          p d * extendedGaussianNaturalScore q d)
        (by intro d hd; rw [hp_zero d hd]; simp)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hp_fin d, profileDeficit_rev_succ, extendedGaussianNaturalScore]
    rw [extendedGaussianEntropyTruncation, h1, hV,
      finiteProfileDeficit_sum_reindex alpha
        (fun i => -(w i) * Real.log (w i) +
          w i * (-q / 2 * (profileDeficit alpha i) ^ 2))]
    rw [profileDeficit_last, hexc, extendedGaussianExceptionalScore]
    norm_num
  have hmasslim : Tendsto (extendedGaussianMassTruncation exceptional p)
      atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_atTop.2 ⟨alpha, fun _ h => h⟩] with N hN
    exact (hmass N hN).symm
  have hmomentlim : Tendsto (extendedGaussianMomentTruncation exceptional p)
      atTop (nhds target) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_atTop.2 ⟨alpha, fun _ h => h⟩] with N hN
    exact (hmoment N hN).symm
  have hentropylim : Tendsto (extendedGaussianEntropyTruncation q exceptional p)
      atTop (nhds V) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_atTop.2 ⟨alpha, fun _ h => h⟩] with N hN
    exact (hentropy N hN).symm
  have hexcnonneg : 0 ≤ exceptional := (hwpos _).le
  have hwitness : ExtendedGaussianEntropyWitnessAllTilts target V exceptional p :=
    { exceptional_nonneg := hexcnonneg
      natural_nonneg := hp_nonneg
      finite_dual_bound :=
        extendedGaussian_finite_dual_bound_of_nonneg hexcnonneg hp_nonneg
      mass_limit := hmasslim
      moment_limit := hmomentlim
      entropy_limit := hentropylim }
  have hlogw : ∀ i, Real.log (w i) =
      profileDeficitResidualScore alpha i + lam * profileDeficit alpha i -
        Real.log Z := by
    intro i
    have hnum : (0 : ℝ) < profileDeficitUnnormalized alpha lam i :=
      profileDeficitUnnormalized_pos alpha lam i
    rw [hw]
    simp only [profileDeficitWeight]
    rw [← hZ, Real.log_div hnum.ne' hZpos.ne', profileDeficitUnnormalized,
      Real.log_exp]
  have hVsplit : V = Real.log Z * (∑ i : Fin (alpha + 1), w i) -
      lam * (∑ i : Fin (alpha + 1), w i * profileDeficit alpha i) -
      ∑ i : Fin (alpha + 1),
        w i * (profileDeficitResidualScore alpha i +
          q / 2 * (profileDeficit alpha i) ^ 2) := by
    rw [hV]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlogw i]
    ring
  have hsum1 : ∑ i : Fin (alpha + 1), w i = 1 :=
    sum_profileDeficitWeight alpha lam
  have hsum2 : ∑ i : Fin (alpha + 1), w i * profileDeficit alpha i = target := by
    rw [← hmeanEq, profileDeficitMean]
  have hresid : ∑ i : Fin (alpha + 1),
      w i * (profileDeficitResidualScore alpha i +
        q / 2 * (profileDeficit alpha i) ^ 2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have hle := profileDeficitResidualScore_le_gaussian alpha halpha0 i
    nlinarith [hwpos i, hle]
  have hkey : Real.log Z - lam * target ≤ V := by
    rw [hVsplit, hsum1, hsum2]
    linarith
  have hbdd : BddAbove (extendedGaussianEntropyCandidateSet target) := by
    refine ⟨extendedGaussianDualTestValue target 0, ?_⟩
    rintro value ⟨exc, pp, hwit⟩
    exact extendedGaussianEntropy_le_dual_of_truncations_q
      hwit.exceptional_nonneg hwit.natural_nonneg
      (fun _ _ N => hwit.finite_dual_bound 0 N)
      hwit.mass_limit hwit.moment_limit hwit.entropy_limit
  have hmem : V ∈ extendedGaussianEntropyCandidateSet target :=
    ⟨exceptional, p, hwitness⟩
  calc Real.log Z - lam * target ≤ V := hkey
    _ ≤ extendedGaussianEntropyValue target := le_csSup hbdd hmem

end

end Erdos625
