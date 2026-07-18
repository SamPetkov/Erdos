import Erdos625.PartialDiagonalDecayReindexing
import Mathlib.Tactic

/-!
# Section VII empty-corner cutoff activity

This module records the exact finite cutoff activity used by the
partial-diagonal iteration.  It is a local port of the useful part of the
Aristotle S7 activity return, with the proof written out using ordinary Lean
tactics and no automation-with-suggestions source.
-/

namespace Erdos625

open scoped BigOperators

noncomputable section

section MuMonotonicity

/-- For a fixed block size, `mu(v,s)` is nondecreasing in the number of
available vertices. -/
theorem mu_le_of_le_vertex_count {s v w : Nat}
    (_hsv : s <= v) (hvw : v <= w) :
    mu v s <= mu w s := by
  unfold mu
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.choose_le_choose s hvw

end MuMonotonicity

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact finite empty-corner activity at the worst residual vertex count. -/
def muCutoffActivity (n massCap : Nat) (u k : I -> Nat) (i : I) : Real :=
  (k i : Real) ^ 2 / (2 * mu (n - massCap) (u i))

/-- Concrete finite cutoff form of the activity hypothesis consumed by
`partialDiagonalWeight_increment_le_of_mu_lower`.

The denominator is exactly `mu (n - massCap) (u i)`, the smallest residual
first moment among last steps whose enlarged selected profile is still inside
the selected-mass cutoff. -/
theorem partialDiagonalWeight_increment_le_of_mu_cutoff_activity
    (n massCap : Nat) (u k ell : I -> Nat) (i : I)
    (hmassCap : massCap <= n)
    (hu : u i <= n - massCap)
    (hprofile : IsPartialSubprofile k ell)
    (hcut : selectedVertexMass u (incrementProfile ell i) <= massCap) :
    partialDiagonalWeight n u k (incrementProfile ell i) <=
      partialDiagonalWeight n u k ell *
        (muCutoffActivity n massCap u k i / (ell i + 1 : Real)) := by
  apply partialDiagonalWeight_increment_le_of_mu_lower n u k ell i
    (fun j => muCutoffActivity n massCap u k j) hprofile
  · rw [selectedVertexMass_increment] at hcut
    omega
  · unfold muCutoffActivity
    rw [selectedVertexMass_increment] at hcut
    have hselected : selectedVertexMass u ell <= massCap := by omega
    have hremLe :
        n - massCap <= n - selectedVertexMass u ell :=
      Nat.sub_le_sub_left hselected n
    have hmuMono :
        mu (n - massCap) (u i) <=
          mu (n - selectedVertexMass u ell) (u i) :=
      mu_le_of_le_vertex_count hu hremLe
    have hmuCut : 0 < mu (n - massCap) (u i) := mu_pos hu
    have hratio :
        1 <= mu (n - selectedVertexMass u ell) (u i) /
          mu (n - massCap) (u i) := by
      apply (le_div_iff₀ hmuCut).2
      simpa using hmuMono
    calc
      (k i : Real) ^ 2 = (k i : Real) ^ 2 * 1 := by ring
      _ <= (k i : Real) ^ 2 *
          (mu (n - selectedVertexMass u ell) (u i) /
            mu (n - massCap) (u i)) := by
        exact mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ = 2 * ((k i : Real) ^ 2 /
            (2 * mu (n - massCap) (u i))) *
          mu (n - selectedVertexMass u ell) (u i) := by
        field_simp [hmuCut.ne']

#print axioms mu_le_of_le_vertex_count
#print axioms partialDiagonalWeight_increment_le_of_mu_cutoff_activity

end

end Erdos625
