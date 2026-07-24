import Erdos625.Section9ActualAttachmentAggregation
import Erdos625.Section9AttachmentAsymptotics
import Erdos625.Section10AmplificationScales
import Mathlib.Tactic

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

theorem exists_midpointCanonicalAttachment_twoRegime_error
    (b U : Nat → Nat)
    (k : (n : Nat) → ColoringProfile (b n))
    (row0 : (n : Nat) → OrderedProfilePartition n (k n))
    (C : Real) (hC : 0 ≤ C)
    (hlarge : ∀ᶠ n : Nat in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (n : Real) / Real.log (n : Real) ^ 6 ≤
            (canonicalDemandResidualTotal
              (profileBlockMargin (k n)) (profileBlockMargin (k n))
              (U n) demand : Real) →
        profileHighSkeletonAttachment (row0 n) (U n) demand ≤
          ENNReal.ofReal (Real.exp (C * Real.log (n : Real) ^ 8)))
    (hsmall : ∀ᶠ n : Nat in atTop,
      ∀ demand : ProfileCanonicalHighSkeleton (k n) (U n),
        (canonicalDemandResidualTotal
          (profileBlockMargin (k n)) (profileBlockMargin (k n))
          (U n) demand : Real) <
            (n : Real) / Real.log (n : Real) ^ 6 →
        profileHighSkeletonAttachment (row0 n) (U n) demand ≤
          ENNReal.ofReal
            (Real.exp (C * (n : Real) / Real.log (n : Real) ^ 5))) :
    ∃ epsilon : Nat → Real,
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ᶠ n in atTop, 0 ≤ epsilon n) ∧
      ∀ᶠ n in atTop,
        midpointCanonicalAttachmentSum (row0 n) (U n) ≤
          canonicalBareSkeletonSum (k n) (U n) *
            ENNReal.ofReal
              (Real.exp (epsilon n * amplificationBase n)) := by
  obtain ⟨epsilon, hepsilon, hevent⟩ :=
    exists_uniform_twoRegime_error
      (fun n => ProfileCanonicalHighSkeleton (k n) (U n))
      (fun n demand =>
        (profileHighSkeletonAttachment (row0 n) (U n) demand).toReal)
      (fun n demand =>
        canonicalDemandResidualTotal
          (profileBlockMargin (k n)) (profileBlockMargin (k n))
          (U n) demand)
      C hC
      (by
        filter_upwards [hlarge] with n hn
        intro demand hmass
        have hbound := hn demand hmass
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (by
          rw [ENNReal.toReal_ofReal (Real.exp_nonneg _) ]))
      (by
        filter_upwards [hsmall] with n hn
        intro demand hmass
        have hbound := hn demand hmass
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (by
          rw [ENNReal.toReal_ofReal (Real.exp_nonneg _) ]))
  refine ⟨epsilon, hepsilon, hevent.mono fun n hn => hn.1, ?_⟩
  filter_upwards [hevent, hlarge, hsmall] with n hn hnlarge hnsmall
  apply midpointCanonicalAttachmentSum_le_bare_mul
  intro demand
  have hfinite :
      profileHighSkeletonAttachment (row0 n) (U n) demand ≠ ⊤ := by
    by_cases hmass :
        (canonicalDemandResidualTotal
          (profileBlockMargin (k n)) (profileBlockMargin (k n))
          (U n) demand : Real) <
            (n : Real) / Real.log (n : Real) ^ 6
    · have hbound := hnsmall demand hmass
      intro htop
      rw [htop] at hbound
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
    · have hbound := hnlarge demand (le_of_not_gt hmass)
      intro htop
      rw [htop] at hbound
      exact ENNReal.ofReal_ne_top (top_le_iff.mp hbound)
  rw [← ENNReal.ofReal_toReal hfinite]
  apply ENNReal.ofReal_le_ofReal
  simpa only [amplificationBase, mul_div_assoc] using hn.2 demand

#print axioms exists_midpointCanonicalAttachment_twoRegime_error

end

end Erdos625
