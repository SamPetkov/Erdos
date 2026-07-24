import Erdos625.SPlusEntropyCandidateEmbedding

/-!
# Interior limiting `S₊` entropy supremum and dual comparison

This source-only module contains the remaining limiting-entropy variational
chain only on the domain where the four-point optimizer is defined by its
target-matching interpretation: `T ∈ (2,5)`.  It makes no assertion at an
endpoint or outside that interval, and makes no finite-cutoff, phase-root,
probabilistic, or final-problem claim.
-/

open Filter
open scoped Topology BigOperators

namespace Erdos625

noncomputable section

/-- A concrete extended-Gaussian witness.  Its finite truncation inequality
is required at every test tilt, so the already formalized pointwise transport
theorem can be applied directly to each candidate. -/
structure ExtendedGaussianEntropyWitnessAllTilts
    (target value exceptional : ℝ) (p : ℕ → ℝ) : Prop where
  exceptional_nonneg : 0 ≤ exceptional
  natural_nonneg : ∀ d, 0 ≤ p d
  finite_dual_bound : ∀ tilt N,
    extendedGaussianEntropyTruncation q exceptional p N ≤
      extendedGaussianReferenceMassTruncation q tilt N -
        extendedGaussianMassTruncation exceptional p N +
        Real.log (extendedGaussianPartition q tilt) *
          extendedGaussianMassTruncation exceptional p N -
        tilt * extendedGaussianMomentTruncation exceptional p N
  mass_limit : Tendsto (extendedGaussianMassTruncation exceptional p)
    atTop (nhds 1)
  moment_limit : Tendsto (extendedGaussianMomentTruncation exceptional p)
    atTop (nhds target)
  entropy_limit : Tendsto (extendedGaussianEntropyTruncation q exceptional p)
    atTop (nhds value)

/-- Candidate values for one fixed target. -/
def extendedGaussianEntropyCandidateSet (target : ℝ) : Set ℝ :=
  {value | ∃ exceptional p,
    ExtendedGaussianEntropyWitnessAllTilts target value exceptional p}

/-- The unrestricted limiting entropy value is the real supremum of its
concrete candidate set.  All comparison theorems below are explicitly
restricted to `target ∈ (2,5)`. -/
noncomputable def extendedGaussianEntropyValue (target : ℝ) : ℝ :=
  sSup (extendedGaussianEntropyCandidateSet target)

/-- The entropy loss of the finite four-point value against the limiting
unrestricted value. -/
noncomputable def fourEntropyLoss (target : ℝ) : ℝ :=
  extendedGaussianEntropyValue target -
    ProfileEntropyS4.optimizedValue fourGaussianScore target

/-- **Interior `S₄ ⊆ S₊` / dual / loss bundle.**  For each interior target,
the conjunction gives: a concrete all-tilts embedding of the finite
four-point optimizer; the pointwise extended dual upper bound obtained from
`extendedGaussianEntropy_le_dual_of_truncations_q` and `csSup`; the induced
four-point lower bound; and nonnegative loss. -/
theorem splusEntropySupremumDualInterior_bundle :
    (∀ {target : ℝ}, target ∈ Set.Ioo (2 : ℝ) 5 →
      ∃ exceptional p,
        ExtendedGaussianEntropyWitnessAllTilts target
          (ProfileEntropyS4.optimizedValue fourGaussianScore target)
          exceptional p) ∧
    (∀ {target tilt : ℝ}, target ∈ Set.Ioo (2 : ℝ) 5 →
      extendedGaussianEntropyValue target ≤
        extendedGaussianDualTestValue target tilt) ∧
    (∀ {target : ℝ}, target ∈ Set.Ioo (2 : ℝ) 5 →
      ProfileEntropyS4.optimizedValue fourGaussianScore target ≤
        extendedGaussianEntropyValue target) ∧
    (∀ {target : ℝ}, target ∈ Set.Ioo (2 : ℝ) 5 →
      0 ≤ fourEntropyLoss target) := by
  have hEmbed : ∀ {target : ℝ}, target ∈ Set.Ioo (2 : ℝ) 5 →
      ∃ exceptional p,
        ExtendedGaussianEntropyWitnessAllTilts target
          (ProfileEntropyS4.optimizedValue fourGaussianScore target)
          exceptional p := by
    intro target htarget
    let p : ℕ → ℝ := fun d =>
      if d = 2 then ProfileEntropyS4.optimizer fourGaussianScore target 0 else
      if d = 3 then ProfileEntropyS4.optimizer fourGaussianScore target 1 else
      if d = 4 then ProfileEntropyS4.optimizer fourGaussianScore target 2 else
      if d = 5 then ProfileEntropyS4.optimizer fourGaussianScore target 3 else 0
    have hp_nonneg : ∀ d, 0 ≤ p d := by
      intro d
      simp only [p]
      split
      · exact ProfileEntropyS4.optimizer_nonneg _ _ _
      split
      · exact ProfileEntropyS4.optimizer_nonneg _ _ _
      split
      · exact ProfileEntropyS4.optimizer_nonneg _ _ _
      split
      · exact ProfileEntropyS4.optimizer_nonneg _ _ _
      · exact le_rfl
    have hp_ge (d : ℕ) (hd : 6 ≤ d) : p d = 0 := by
      have h2 : d ≠ 2 := by omega
      have h3 : d ≠ 3 := by omega
      have h4 : d ≠ 4 := by omega
      have h5 : d ≠ 5 := by omega
      simp [p, h2, h3, h4, h5]
    have hmass_event : ∀ N ≥ 6,
        extendedGaussianMassTruncation 0 p N = 1 := by
      intro N hN
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
      unfold extendedGaussianMassTruncation
      rw [Finset.sum_range_add]
      have hz : ∑ x ∈ Finset.range k, p (6 + x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact hp_ge _ (by omega)
      rw [hz, add_zero]
      simp [p, Finset.sum_range_succ]
      have hs := ProfileEntropyS4.sum_optimizer fourGaussianScore target
      rw [Fin.sum_univ_four] at hs
      exact hs
    have hmoment_event : ∀ N ≥ 6,
        extendedGaussianMomentTruncation 0 p N = target := by
      intro N hN
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
      unfold extendedGaussianMomentTruncation
      rw [Finset.sum_range_add]
      have hz : ∑ x ∈ Finset.range k, ((6 + x : ℕ) : ℝ) * p (6 + x) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [hp_ge _ (by omega), mul_zero]
      rw [hz, add_zero]
      simp [p, Finset.sum_range_succ]
      have hs := ProfileEntropyS4.sum_optimizer_mul_support
        fourGaussianScore htarget
      rw [Fin.sum_univ_four] at hs
      rw [ProfileEntropyS4.support_zero, ProfileEntropyS4.support_one,
        ProfileEntropyS4.support_two, ProfileEntropyS4.support_three] at hs
      linarith
    have hentropy_event : ∀ N ≥ 6,
        extendedGaussianEntropyTruncation q 0 p N =
          ProfileEntropyS4.optimizedValue fourGaussianScore target := by
      intro N hN
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
      unfold extendedGaussianEntropyTruncation
      rw [Finset.sum_range_add]
      have hz : ∑ x ∈ Finset.range k,
          (-p (6 + x) * Real.log (p (6 + x)) +
            p (6 + x) * extendedGaussianNaturalScore q (6 + x)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [hp_ge _ (by omega)]
        simp
      rw [hz, add_zero]
      have hs :=
        ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target
          fourGaussianScore htarget
      rw [Fin.sum_univ_four, Fin.sum_univ_four] at hs
      unfold ProfileEntropyS4.optimizedValue
      rw [← hs]
      simp [p, Finset.sum_range_succ, extendedGaussianExceptionalScore,
        extendedGaussianNaturalScore, fourGaussianScore,
        ProfileEntropyS4.support]
      ring
    refine ⟨0, p, ?_⟩
    refine ⟨le_rfl, hp_nonneg, ?_, ?_, ?_, ?_⟩
    · intro tilt N
      have hZ : 0 < extendedGaussianPartition q tilt :=
        extendedGaussianPartition_pos q_pos
      have hterm : ∀ d, -p d * Real.log (p d) +
            p d * extendedGaussianNaturalScore q d ≤
          extendedGaussianNaturalTerm q tilt d / extendedGaussianPartition q tilt - p d +
            Real.log (extendedGaussianPartition q tilt) * p d -
              tilt * ((d : ℝ) * p d) := by
        intro d
        have href : 0 < extendedGaussianNaturalTerm q tilt d /
            extendedGaussianPartition q tilt :=
          div_pos (extendedGaussianNaturalTerm_pos q tilt d) hZ
        have hrel := ProfileEntropyS4.neg_mul_log_add_mul_log_le_sub
          (hp_nonneg d) href
        have hlog : Real.log (extendedGaussianNaturalTerm q tilt d /
              extendedGaussianPartition q tilt) =
            tilt * (d : ℝ) + extendedGaussianNaturalScore q d -
              Real.log (extendedGaussianPartition q tilt) := by
          rw [Real.log_div (extendedGaussianNaturalTerm_pos q tilt d).ne' hZ.ne',
            extendedGaussianNaturalTerm, Real.log_exp]
          unfold extendedGaussianNaturalScore
          ring
        rw [hlog] at hrel
        linarith
      have hsum := Finset.sum_le_sum fun d (_hd : d ∈ Finset.range N) => hterm d
      have hexref : 0 ≤ extendedGaussianExceptionalAtom q tilt /
          extendedGaussianPartition q tilt :=
        (div_pos (extendedGaussianExceptionalAtom_pos q tilt) hZ).le
      unfold extendedGaussianEntropyTruncation
      unfold extendedGaussianReferenceMassTruncation
      unfold extendedGaussianMassTruncation
      unfold extendedGaussianMomentTruncation
      simp only [zero_mul, neg_zero, Real.log_zero, zero_add]
      calc
        ∑ d ∈ Finset.range N,
            (-p d * Real.log (p d) + p d * extendedGaussianNaturalScore q d) ≤
          ∑ d ∈ Finset.range N,
            (extendedGaussianNaturalTerm q tilt d /
                extendedGaussianPartition q tilt - p d +
              Real.log (extendedGaussianPartition q tilt) * p d -
                tilt * ((d : ℝ) * p d)) := hsum
        _ ≤ extendedGaussianExceptionalAtom q tilt /
              extendedGaussianPartition q tilt +
            ∑ d ∈ Finset.range N,
              (extendedGaussianNaturalTerm q tilt d /
                  extendedGaussianPartition q tilt - p d +
                Real.log (extendedGaussianPartition q tilt) * p d -
                  tilt * ((d : ℝ) * p d)) := by linarith
        _ = extendedGaussianExceptionalAtom q tilt /
              extendedGaussianPartition q tilt +
            ∑ d ∈ Finset.range N, extendedGaussianNaturalTerm q tilt d /
              extendedGaussianPartition q tilt -
            ∑ d ∈ Finset.range N, p d +
            Real.log (extendedGaussianPartition q tilt) *
              ∑ d ∈ Finset.range N, p d -
            tilt * ∑ d ∈ Finset.range N, (d : ℝ) * p d := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.mul_sum]
          ring
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_atTop.2 ⟨6, fun _ h => h⟩] with N hN
      exact (hmass_event N hN).symm
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_atTop.2 ⟨6, fun _ h => h⟩] with N hN
      exact (hmoment_event N hN).symm
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_atTop.2 ⟨6, fun _ h => h⟩] with N hN
      exact (hentropy_event N hN).symm
  refine ⟨hEmbed, ?_⟩
  have hpoint : ∀ {target value : ℝ},
      value ∈ extendedGaussianEntropyCandidateSet target → ∀ tilt,
        value ≤ extendedGaussianDualTestValue target tilt := by
    intro target value hv tilt
    rcases hv with ⟨exceptional, p, hw⟩
    exact extendedGaussianEntropy_le_dual_of_truncations_q
      hw.exceptional_nonneg hw.natural_nonneg
      (fun _ _ N => hw.finite_dual_bound tilt N)
      hw.mass_limit hw.moment_limit hw.entropy_limit
  constructor
  · intro target tilt htarget
    apply csSup_le
    · rcases hEmbed htarget with ⟨exceptional, p, hw⟩
      exact ⟨_, exceptional, p, hw⟩
    · intro value hv
      exact hpoint hv tilt
  constructor
  · intro target htarget
    rcases hEmbed htarget with ⟨exceptional, p, hw⟩
    apply le_csSup
    · refine ⟨extendedGaussianDualTestValue target 0, ?_⟩
      intro value hv
      exact hpoint hv 0
    · exact ⟨exceptional, p, hw⟩
  · intro target htarget
    unfold fourEntropyLoss
    have h := (show ProfileEntropyS4.optimizedValue fourGaussianScore target ≤
      extendedGaussianEntropyValue target from by
        rcases hEmbed htarget with ⟨exceptional, p, hw⟩
        apply le_csSup
        · refine ⟨extendedGaussianDualTestValue target 0, ?_⟩
          intro value hv
          exact hpoint hv 0
        · exact ⟨exceptional, p, hw⟩)
    linarith

/-- The finite four-point optimizer is an admissible all-tilts witness for
every interior target. -/
theorem exists_s4_embedded_extendedGaussian_witness_allTilts
    {target : ℝ} (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    ∃ exceptional p,
      ExtendedGaussianEntropyWitnessAllTilts target
        (ProfileEntropyS4.optimizedValue fourGaussianScore target)
        exceptional p :=
  splusEntropySupremumDualInterior_bundle.1 hT

/-- Every interior unrestricted candidate supremum obeys the extended
Gaussian dual bound at an arbitrary test tilt. -/
theorem extendedGaussianEntropyValue_le_dual_interior
    {target tilt : ℝ} (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    extendedGaussianEntropyValue target ≤
      extendedGaussianDualTestValue target tilt :=
  splusEntropySupremumDualInterior_bundle.2.1 hT

/-- The finite four-point optimum is bounded above by the unrestricted
interior entropy supremum. -/
theorem fourGaussian_optimizedValue_le_extendedGaussianEntropyValue
    {target : ℝ} (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    ProfileEntropyS4.optimizedValue fourGaussianScore target ≤
      extendedGaussianEntropyValue target :=
  splusEntropySupremumDualInterior_bundle.2.2.1 hT

/-- The resulting interior four-point entropy loss is nonnegative. -/
theorem fourEntropyLoss_nonneg_interior
    {target : ℝ} (hT : target ∈ Set.Ioo (2 : ℝ) 5) :
    0 ≤ fourEntropyLoss target :=
  splusEntropySupremumDualInterior_bundle.2.2.2 hT

#print axioms splusEntropySupremumDualInterior_bundle
#print axioms exists_s4_embedded_extendedGaussian_witness_allTilts
#print axioms extendedGaussianEntropyValue_le_dual_interior
#print axioms fourGaussian_optimizedValue_le_extendedGaussianEntropyValue
#print axioms fourEntropyLoss_nonneg_interior

end

end Erdos625
