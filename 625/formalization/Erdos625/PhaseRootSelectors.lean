import Erdos625.PhaseSignedFourSizeLogLogCorridorRootExistence
import Erdos625.PhaseUnrestrictedLogLogCorridorRootExistence

/-!
# Canonical selectors for the two phase roots

The signed and unrestricted root-existence modules provide eventual unique
roots in fixed logarithmic-logarithmic corridors.  This module chooses the two
corridor coefficients once and turns those existential roots into named
sequences.  It proves only selection and uniqueness; it does not compare the
two roots or claim a quantitative separation.
-/

namespace Erdos625

open Filter Set

noncomputable section

set_option autoImplicit false

/-- A fixed corridor coefficient witnessing eventual existence and uniqueness
of the signed finite-four phase root. -/
noncomputable def phaseSignedFourSizeRootCorridorCoefficient : Real :=
  Classical.choose
    exists_pos_eventually_existsUnique_phaseSignedFourSizeRoot_logLogCorridor

theorem phaseSignedFourSizeRootCorridorCoefficient_pos :
    0 < phaseSignedFourSizeRootCorridorCoefficient :=
  (Classical.choose_spec
    exists_pos_eventually_existsUnique_phaseSignedFourSizeRoot_logLogCorridor).1

theorem eventually_existsUnique_phaseSignedFourSizeRoot_selectedCorridor :
    ∀ᶠ n : Nat in atTop,
      ∃! r : Real,
        r ∈ Ioo
            (phaseRootCenter n -
              phaseSignedFourSizeRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              phaseSignedFourSizeRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n) ∧
          IsPhaseSignedFourSizeRoot n r :=
  (Classical.choose_spec
    exists_pos_eventually_existsUnique_phaseSignedFourSizeRoot_logLogCorridor).2

/-- The unique signed finite-four phase root in the chosen corridor when it
exists, and the reference center otherwise. -/
noncomputable def phaseSignedFourSizeRootSelected (n : Nat) : Real := by
  classical
  exact if h : ∃ r : Real,
      r ∈ Ioo
          (phaseRootCenter n -
            phaseSignedFourSizeRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            phaseSignedFourSizeRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        IsPhaseSignedFourSizeRoot n r then
    Classical.choose h
  else
    phaseRootCenter n

theorem phaseSignedFourSizeRootSelected_spec_of_exists
    (n : Nat)
    (h : ∃ r : Real,
      r ∈ Ioo
          (phaseRootCenter n -
            phaseSignedFourSizeRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            phaseSignedFourSizeRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        IsPhaseSignedFourSizeRoot n r) :
    phaseSignedFourSizeRootSelected n ∈ Ioo
        (phaseRootCenter n -
          phaseSignedFourSizeRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          phaseSignedFourSizeRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n) ∧
      IsPhaseSignedFourSizeRoot n (phaseSignedFourSizeRootSelected n) := by
  classical
  rw [phaseSignedFourSizeRootSelected, dif_pos h]
  exact Classical.choose_spec h

theorem eventually_phaseSignedFourSizeRootSelected_spec_unique :
    ∀ᶠ n : Nat in atTop,
      (phaseSignedFourSizeRootSelected n ∈ Ioo
          (phaseRootCenter n -
            phaseSignedFourSizeRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            phaseSignedFourSizeRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        IsPhaseSignedFourSizeRoot n (phaseSignedFourSizeRootSelected n)) ∧
      ∀ r : Real,
        r ∈ Ioo
            (phaseRootCenter n -
              phaseSignedFourSizeRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              phaseSignedFourSizeRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n) ∧
          IsPhaseSignedFourSizeRoot n r →
        r = phaseSignedFourSizeRootSelected n := by
  filter_upwards
    [eventually_existsUnique_phaseSignedFourSizeRoot_selectedCorridor] with n hn
  have hSelected :=
    phaseSignedFourSizeRootSelected_spec_of_exists n hn.exists
  exact ⟨hSelected, fun r hr ↦ hn.unique hr hSelected⟩

/-- A fixed corridor coefficient witnessing eventual existence and uniqueness
of the unrestricted phase-objective zero. -/
noncomputable def unrestrictedPhaseRootCorridorCoefficient : Real :=
  Classical.choose
    exists_pos_eventually_existsUnique_unrestrictedPhaseObjective_zero_logLogCorridor

theorem unrestrictedPhaseRootCorridorCoefficient_pos :
    0 < unrestrictedPhaseRootCorridorCoefficient :=
  (Classical.choose_spec
    exists_pos_eventually_existsUnique_unrestrictedPhaseObjective_zero_logLogCorridor).1

theorem eventually_existsUnique_unrestrictedPhaseRoot_selectedCorridor :
    ∀ᶠ n : Nat in atTop,
      ∃! r : Real,
        r ∈ Ioo
            (phaseRootCenter n -
              unrestrictedPhaseRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              unrestrictedPhaseRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n) ∧
          unrestrictedPhaseObjective n r = 0 :=
  (Classical.choose_spec
    exists_pos_eventually_existsUnique_unrestrictedPhaseObjective_zero_logLogCorridor).2

/-- The unique unrestricted phase-objective zero in the chosen corridor when
it exists, and the reference center otherwise. -/
noncomputable def unrestrictedPhaseRootSelected (n : Nat) : Real := by
  classical
  exact if h : ∃ r : Real,
      r ∈ Ioo
          (phaseRootCenter n -
            unrestrictedPhaseRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            unrestrictedPhaseRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        unrestrictedPhaseObjective n r = 0 then
    Classical.choose h
  else
    phaseRootCenter n

theorem unrestrictedPhaseRootSelected_spec_of_exists
    (n : Nat)
    (h : ∃ r : Real,
      r ∈ Ioo
          (phaseRootCenter n -
            unrestrictedPhaseRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            unrestrictedPhaseRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        unrestrictedPhaseObjective n r = 0) :
    unrestrictedPhaseRootSelected n ∈ Ioo
        (phaseRootCenter n -
          unrestrictedPhaseRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n)
        (phaseRootCenter n +
          unrestrictedPhaseRootCorridorCoefficient *
            logLogOrder n * phaseRootGapRadius n) ∧
      unrestrictedPhaseObjective n (unrestrictedPhaseRootSelected n) = 0 := by
  classical
  rw [unrestrictedPhaseRootSelected, dif_pos h]
  exact Classical.choose_spec h

theorem eventually_unrestrictedPhaseRootSelected_spec_unique :
    ∀ᶠ n : Nat in atTop,
      (unrestrictedPhaseRootSelected n ∈ Ioo
          (phaseRootCenter n -
            unrestrictedPhaseRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n)
          (phaseRootCenter n +
            unrestrictedPhaseRootCorridorCoefficient *
              logLogOrder n * phaseRootGapRadius n) ∧
        unrestrictedPhaseObjective n (unrestrictedPhaseRootSelected n) = 0) ∧
      ∀ r : Real,
        r ∈ Ioo
            (phaseRootCenter n -
              unrestrictedPhaseRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n)
            (phaseRootCenter n +
              unrestrictedPhaseRootCorridorCoefficient *
                logLogOrder n * phaseRootGapRadius n) ∧
          unrestrictedPhaseObjective n r = 0 →
        r = unrestrictedPhaseRootSelected n := by
  filter_upwards
    [eventually_existsUnique_unrestrictedPhaseRoot_selectedCorridor] with n hn
  have hSelected := unrestrictedPhaseRootSelected_spec_of_exists n hn.exists
  exact ⟨hSelected, fun r hr ↦ hn.unique hr hSelected⟩

#print axioms eventually_phaseSignedFourSizeRootSelected_spec_unique
#print axioms eventually_unrestrictedPhaseRootSelected_spec_unique

end

end Erdos625
