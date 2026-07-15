import Erdos625.Section8CanonicalLabelledWitness
import Erdos625.Section8FixedWitnessAssembly

/-!
# Section 8: canonical event under the residual equivalence

For one fixed labelled prescribed-demand exposure, this module identifies the
event that the full matching has exactly the canonical high-cell table with
the residual event imposing the half-cap off that table and no return to its
nonzero support.  This is a deterministic event equivalence; counting the
global event and identifying its conditioned probability law remain separate.
-/

namespace Erdos625

noncomputable section

/-- Full configurations whose literal canonical high-cell demand is the fixed
table `demand`. -/
def canonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (demand : A → B → ℕ) (row : A → ℕ) (col : B → ℕ) (U : ℕ) :
    Set (ConfigurationMatching row col) :=
  {matching | canonicalDemandOfMatching matching U = demand}

/-- Inside the extension subtype of one labelled witness, require the ambient
matching to have exactly the prescribed canonical high-cell table. -/
def fixedWitnessCanonicalDemandEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Set (fixedWitnessExtensionEvent witness) :=
  {extension | canonicalDemandOfMatching extension.1 U = demand}

/-- The canonical residual cap/no-return event: every residual cell is at most
`U / 2`, and cells in the nonzero exposed support receive no further pair. -/
def canonicalResidualCellEvent
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ) :
    Set (ConfigurationMatching (residualRowDegree witness)
      (residualColumnDegree witness)) :=
  {residual | ∀ a b,
    configurationCellCount residual a b ≤ U / 2 ∧
      (demand a b ≠ 0 → configurationCellCount residual a b = 0)}

/-- For one fixed labelled exposure, the canonical full event transports
exactly to the residual half-cap/no-return event. -/
theorem mem_fixedWitnessCanonicalDemandEvent_iff_residual
    {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {demand : A → B → ℕ} {row : A → ℕ} {col : B → ℕ}
    (witness : PrescribedDemandWitness demand row col) (U : ℕ)
    (hhigh : ∀ a b, demand a b ≠ 0 → U / 2 < demand a b)
    (extension : fixedWitnessExtensionEvent witness) :
    extension ∈ fixedWitnessCanonicalDemandEvent witness U ↔
      fixedWitnessExtensionEquivResidual witness extension ∈
        canonicalResidualCellEvent witness U := by
  change canonicalHighDemand (configurationCellCount extension.1) U = demand ↔ _
  rw [canonicalHighDemand_eq_iff_exact_support_and_capped_off
    (configurationCellCount extension.1) demand U hhigh]
  constructor
  · rintro ⟨hsupport, hcapped⟩ a b
    have hsplit := configurationCellCount_eq_demand_add_residual
      witness extension a b
    change configurationCellCount extension.1 a b = demand a b +
      configurationCellCount
        (fixedWitnessExtensionEquivResidual witness extension) a b at hsplit
    by_cases hab : demand a b = 0
    · constructor
      · calc
          configurationCellCount
              (fixedWitnessExtensionEquivResidual witness extension) a b =
              configurationCellCount extension.1 a b := by
                simpa [hab] using hsplit.symm
          _ ≤ U / 2 := hcapped a b hab
      · exact fun h ↦ (h hab).elim
    · have hzero : configurationCellCount
          (fixedWitnessExtensionEquivResidual witness extension) a b = 0 := by
        have heq := hsupport a b hab
        apply Nat.add_left_cancel (n := demand a b)
        simpa using hsplit.symm.trans heq
      exact ⟨by simp [hzero], fun _ ↦ hzero⟩
  · intro h
    constructor
    · intro a b hab
      have hsplit := configurationCellCount_eq_demand_add_residual
        witness extension a b
      change configurationCellCount extension.1 a b = demand a b +
        configurationCellCount
          (fixedWitnessExtensionEquivResidual witness extension) a b at hsplit
      have hzero := (h a b).2 hab
      calc
        configurationCellCount extension.1 a b = demand a b +
            configurationCellCount
              (fixedWitnessExtensionEquivResidual witness extension) a b := hsplit
        _ = demand a b := by simp [hzero]
    · intro a b hab
      have hsplit := configurationCellCount_eq_demand_add_residual
        witness extension a b
      change configurationCellCount extension.1 a b = demand a b +
        configurationCellCount
          (fixedWitnessExtensionEquivResidual witness extension) a b at hsplit
      have hcap := (h a b).1
      calc
        configurationCellCount extension.1 a b = demand a b +
            configurationCellCount
              (fixedWitnessExtensionEquivResidual witness extension) a b := hsplit
        _ = configurationCellCount
              (fixedWitnessExtensionEquivResidual witness extension) a b := by
            simp [hab]
        _ ≤ U / 2 := hcap

#print axioms mem_fixedWitnessCanonicalDemandEvent_iff_residual

end

end Erdos625
