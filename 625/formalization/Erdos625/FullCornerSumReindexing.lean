import Erdos625.FullCornerWeights
import Erdos625.PartialDiagonalDecayReindexing
import Mathlib.Tactic

/-!
# Exact full-corner sum reindexing

The proof was returned by Aristotle project
`9f3a54c9-cd58-454e-bb37-cc7f2e3c675d`, task
`f681a971-0623-4c77-8411-e95f0e15e717`, and independently audited before
integration.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact finite reindexing of all partial-diagonal weights by complementary
residual profiles.  The full-mass hypothesis is essential: without it,
`partialDiagonalWeight n` uses a different ambient factorial expression than
the complete moment in `fullCornerWeight`. -/
theorem sum_partialDiagonalWeight_fullCorner_eq
    (n : ℕ) (u k : I → ℕ)
    (hfullMass : selectedVertexMass u k = n) :
    ∑ ell ∈ partialSubprofileBox k,
      partialDiagonalWeight n u k ell =
    ∑ h ∈ partialSubprofileBox k,
      fullCornerWeight u k h / completeSignedFirstMoment u k := by
  apply Finset.sum_bij'
    (fun ell _ ↦ complementaryProfile k ell)
    (fun h _ ↦ complementaryProfile k h)
  · intro ell _
    exact mem_partialSubprofileBox.mpr (fun i ↦ Nat.sub_le _ _)
  · intro h _
    exact mem_partialSubprofileBox.mpr (fun i ↦ Nat.sub_le _ _)
  · intro ell hell
    funext i
    exact Nat.sub_sub_self (mem_partialSubprofileBox.mp hell i)
  · intro h hh
    funext i
    exact Nat.sub_sub_self (mem_partialSubprofileBox.mp hh i)
  · intro ell hell
    have hinvolution :
        complementaryProfile k (complementaryProfile k ell) = ell := by
      funext i
      exact Nat.sub_sub_self (mem_partialSubprofileBox.mp hell i)
    simpa only [hinvolution] using
      (partialDiagonalWeight_complement_eq_fullCorner_div
        n u k (complementaryProfile k ell) (fun i ↦ Nat.sub_le _ _) hfullMass)

end

end Erdos625
