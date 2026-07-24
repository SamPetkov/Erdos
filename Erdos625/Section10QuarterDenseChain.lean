import Erdos625.Section10NeighborhoodDeletionStep
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-!
# Section 10: abstract quarter-dense neighbourhood chain

This module turns the checked one-step neighbourhood lemma into a finite
deterministic clique-and-residual chain.  Its hypotheses deliberately include
the numerical survival condition needed to make every intermediate residual
large enough for the quarter-density assumption.  It does not prove that
survival condition, derive quarter density from the random graph, perform any
rounding estimate, or invoke the later greedy-colouring argument.
-/

open Finset

namespace Erdos625

noncomputable section

/-- Repeating the deterministic quarter-dense neighbourhood step produces a
clique of the requested finite length and a common-neighbour residual set.

The shifted potential `4⁻¹^i * (|S| + 1/3) - 1/3` is used because it is
preserved exactly by the recurrence `|T| ≥ (|S| - 1) / 4`.  The hypothesis
`hSurvive` is therefore an explicit finite assumption: it is not an
asymptotic estimate hidden inside this theorem. -/
theorem exists_quarterDense_clique_chain
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) (cutoff t : ℕ)
    (hcutoff : 1 ≤ cutoff)
    (hDense : ∀ U : Finset V, U ⊆ S → cutoff ≤ U.card → QuarterDenseOn H U)
    (hSurvive : ∀ i : ℕ, i < t →
      (cutoff : ℝ) ≤ (4 : ℝ)⁻¹ ^ i * ((S.card : ℝ) + 1 / 3) - 1 / 3) :
    ∃ C R : Finset V,
      C.card = t ∧ C ⊆ S ∧ H.IsClique (C : Set V) ∧ R ⊆ S ∧
        (∀ v ∈ C, ∀ w ∈ R, H.Adj v w) ∧
        (4 : ℝ)⁻¹ ^ t * ((S.card : ℝ) + 1 / 3) - 1 / 3 ≤ (R.card : ℝ) := by
  induction t generalizing S with
  | zero =>
      refine ⟨∅, S, by simp, Finset.empty_subset _, ?_, (by intro x hx; exact hx), ?_, ?_⟩
      · simp
      · simp
      · norm_num
  | succ t ih =>
      have hcutoffSreal : (cutoff : ℝ) ≤ (S.card : ℝ) := by
        have h := hSurvive 0 (Nat.zero_lt_succ t)
        norm_num at h ⊢
        linarith
      have hcutoffS : cutoff ≤ S.card := by
        exact_mod_cast hcutoffSreal
      have hSpos : 0 < S.card :=
        lt_of_lt_of_le (Nat.zero_lt_succ 0) (hcutoff.trans hcutoffS)
      obtain ⟨v, hv, T, hTsub, hTadj, hstep⟩ :=
        quarterDense_neighbor_step H S hSpos (hDense S (by intro x hx; exact hx) hcutoffS)
      have hSone : 1 ≤ S.card := Nat.succ_le_iff.mpr hSpos
      have hstepReal : ((S.card : ℝ) - 1) / 4 ≤ (T.card : ℝ) := by
        have hstepCast : ((S.card - 1 : ℕ) : ℝ) ≤ ((4 * T.card : ℕ) : ℝ) := by
          exact_mod_cast hstep
        rw [Nat.cast_sub hSone] at hstepCast
        norm_num at hstepCast ⊢
        linarith
      have hpotentialStep : ∀ i : ℕ,
          (4 : ℝ)⁻¹ ^ (i + 1) * ((S.card : ℝ) + 1 / 3) - 1 / 3 ≤
            (4 : ℝ)⁻¹ ^ i * ((T.card : ℝ) + 1 / 3) - 1 / 3 := by
        intro i
        have hshift : ((S.card : ℝ) + 1 / 3) / 4 ≤ (T.card : ℝ) + 1 / 3 := by
          linarith
        have hpow : 0 ≤ (4 : ℝ)⁻¹ ^ i := by positivity
        have hmul := mul_le_mul_of_nonneg_left hshift hpow
        calc
          (4 : ℝ)⁻¹ ^ (i + 1) * ((S.card : ℝ) + 1 / 3) - 1 / 3 =
              (4 : ℝ)⁻¹ ^ i * (((S.card : ℝ) + 1 / 3) / 4) - 1 / 3 := by
                rw [pow_succ]
                norm_num
                ring
          _ ≤ (4 : ℝ)⁻¹ ^ i * ((T.card : ℝ) + 1 / 3) - 1 / 3 := by
                linarith
      have hDenseT : ∀ U : Finset V, U ⊆ T → cutoff ≤ U.card → QuarterDenseOn H U := by
        intro U hUT hUcard
        exact hDense U (hUT.trans hTsub) hUcard
      have hSurviveT : ∀ i : ℕ, i < t →
          (cutoff : ℝ) ≤ (4 : ℝ)⁻¹ ^ i * ((T.card : ℝ) + 1 / 3) - 1 / 3 := by
        intro i hi
        exact (hSurvive (i + 1) (Nat.succ_lt_succ hi)).trans (hpotentialStep i)
      obtain ⟨C, R, hCcard, hCsub, hClique, hRsub, hCRadj, hRcard⟩ :=
        ih (S := T) hDenseT hSurviveT
      have hvnotC : v ∉ C := by
        intro hvC
        have hvT : v ∈ T := hCsub hvC
        exact H.irrefl (hTadj v hvT)
      refine ⟨insert v C, R, ?_, ?_, ?_, hRsub.trans hTsub, ?_, ?_⟩
      · rw [card_insert_of_notMem hvnotC, hCcard]
      · intro w hw
        rw [mem_insert] at hw
        rcases hw with rfl | hw
        · exact hv
        · exact hTsub (hCsub hw)
      · push_cast
        apply hClique.insert
        intro w hw hne
        exact hTadj w (hCsub hw)
      · intro w hw z hz
        rw [mem_insert] at hw
        rcases hw with rfl | hw
        · exact hTadj z (hRsub hz)
        · exact hCRadj w hw z hz
      · exact (hpotentialStep t).trans hRcard

#print axioms exists_quarterDense_clique_chain

end

end Erdos625
