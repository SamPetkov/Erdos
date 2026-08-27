import Erdos625.FullCornerSumReindexing
import Mathlib.Tactic

/-!
# Filtered full-corner reindexing

This module isolates the finite, division-free bookkeeping seam for the
full-corner contribution in manuscript Section VII.  Complementation carries
the common-profile cutoff exactly to a residual-mass cutoff, and the exact
denominator-free factorization turns every summand into a full-corner weight.

No local-ratio, phase, Stirling, or asymptotic estimate is used here.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact filtered, division-free full-corner reindexing.

The filter on the left bounds the mass omitted from the common profile.  Under
the full-mass identity this is exactly the residual mass of the complementary
profile indexing the right-hand side. -/
theorem sum_partialDiagonalWeight_fullCorner_filter_mul_complete_eq
    (n massCap : Nat) (u k : I → Nat)
    (hfullMass : selectedVertexMass u k = n) :
    (∑ ell ∈ (partialSubprofileBox k).filter
        (fun ell => n - selectedVertexMass u ell ≤ massCap),
      partialDiagonalWeight n u k ell) * completeSignedFirstMoment u k =
    ∑ h ∈ (partialSubprofileBox k).filter
        (fun h => residualVertexMass u h ≤ massCap),
      fullCornerWeight u k h := by
  rw [Finset.sum_mul]
  apply Finset.sum_bij'
    (fun ell _ => complementaryProfile k ell)
    (fun h _ => complementaryProfile k h)
  · intro ell hell
    obtain ⟨hellBox, hellCap⟩ := Finset.mem_filter.mp hell
    apply Finset.mem_filter.mpr
    refine ⟨mem_partialSubprofileBox.mpr (fun i => Nat.sub_le _ _), ?_⟩
    have hsplit := selectedVertexMass_complement_add u k ell
      (mem_partialSubprofileBox.mp hellBox)
    unfold residualVertexMass
    omega
  · intro h hh
    obtain ⟨hhBox, hhCap⟩ := Finset.mem_filter.mp hh
    apply Finset.mem_filter.mpr
    refine ⟨mem_partialSubprofileBox.mpr (fun i => Nat.sub_le _ _), ?_⟩
    have hsplit := selectedVertexMass_complement_add u k h
      (mem_partialSubprofileBox.mp hhBox)
    unfold residualVertexMass at hhCap
    omega
  · intro ell hell
    funext i
    exact Nat.sub_sub_self
      (mem_partialSubprofileBox.mp (Finset.mem_filter.mp hell).1 i)
  · intro h hh
    funext i
    exact Nat.sub_sub_self
      (mem_partialSubprofileBox.mp (Finset.mem_filter.mp hh).1 i)
  · intro ell hell
    have hellBox := (Finset.mem_filter.mp hell).1
    have hinvolution :
        complementaryProfile k (complementaryProfile k ell) = ell := by
      funext i
      exact Nat.sub_sub_self (mem_partialSubprofileBox.mp hellBox i)
    simpa only [hinvolution] using
      (partialDiagonalWeight_complement_mul_complete
        n u k (complementaryProfile k ell) (fun i => Nat.sub_le _ _)
          hfullMass)

end

end Erdos625
