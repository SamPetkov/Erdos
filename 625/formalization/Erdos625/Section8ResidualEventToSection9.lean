import Erdos625.Section8CanonicalEventResidual
import Erdos625.Section9CappedFixedFExpansion

/-!
# Section VIII--IX: canonical residual event in Section IX form

The canonical residual half-cap/no-return event of Section VIII is exactly the
cap/no-return event used by the fixed-`F` expansion of Section IX, once the
exposed support is written as a finite set.  This is a deterministic event
identification only; it does not establish a conditioned law or any global
probability estimate.
-/

namespace Erdos625

/-- The finite support of the nonzero cells of a prescribed demand table. -/
def positiveDemandSupport
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) : Finset (A × B) :=
  Finset.univ.filter (fun e ↦ demand e.1 e.2 ≠ 0)

/-- The Section VIII canonical residual event is the Section IX cap/no-return
event for the finite support of the exposed demand table. -/
theorem canonicalResidualCellEvent_eq_residualCapNoReturnEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    canonicalResidualCellEvent witness U =
      ResidualCapNoReturnEvent (positiveDemandSupport demand) (U / 2)
        (residualRowDegree witness) (residualColumnDegree witness) := by
  ext residual
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro a b
      exact (h a b).1
    · intro e he
      exact (h e.1 e.2).2 (by
        simpa only [positiveDemandSupport, Finset.mem_filter, Finset.mem_univ,
          true_and] using he)
  · rintro ⟨hcap, hreturn⟩ a b
    refine ⟨hcap a b, ?_⟩
    intro hpositive
    exact hreturn (a, b) (by
      simp only [positiveDemandSupport, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact hpositive)

/-- The fixed-witness canonical event transports to the Section IX
cap/no-return event under the existing residual matching equivalence. -/
theorem mem_fixedWitnessCanonicalDemandEvent_iff_residualCapNoReturn
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (extension : fixedWitnessExtensionEvent witness) :
    extension ∈ fixedWitnessCanonicalDemandEvent witness U ↔
      fixedWitnessExtensionEquivResidual witness extension ∈
        ResidualCapNoReturnEvent (positiveDemandSupport demand) (U / 2)
          (residualRowDegree witness) (residualColumnDegree witness) := by
  rw [mem_fixedWitnessCanonicalDemandEvent_iff_residual witness U hhigh extension,
    canonicalResidualCellEvent_eq_residualCapNoReturnEvent witness U]

#print axioms canonicalResidualCellEvent_eq_residualCapNoReturnEvent
#print axioms mem_fixedWitnessCanonicalDemandEvent_iff_residualCapNoReturn

end Erdos625
