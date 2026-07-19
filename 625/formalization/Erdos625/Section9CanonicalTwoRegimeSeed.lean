import Erdos625.Section9CanonicalLambda
import Erdos625.Section9AttachmentAsymptotics
import Mathlib.Tactic

/-!
# Section IX: canonical two-regime seed assembly

This module feeds the existing Section IX two-regime asymptotic mechanism into
the literal attained-demand polymer sum.  It does not assume Proposition 9.2.
The two displayed finite estimates are the remaining analytic inputs, stated
directly for the canonical polymer sum after conversion to its finite real
value.
-/

namespace Erdos625

open Filter
open scoped ENNReal Topology

noncomputable section

/-- The real value of the finite attained-demand polymer sum. -/
noncomputable def canonicalPolymerReal
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) : ℝ :=
  (midpointCanonicalPolymerSum row₀ U).toReal

/-- The finite `ENNReal` polymer sum is recovered exactly from its real value. -/
theorem ofReal_canonicalPolymerReal
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) :
    ENNReal.ofReal (canonicalPolymerReal row₀ U) =
      midpointCanonicalPolymerSum row₀ U := by
  exact ENNReal.ofReal_toReal (midpointCanonicalPolymerSum_ne_top row₀ U)

/-- Two-regime bounds for the literal canonical polymer sum produce a
nonnegative vanishing coefficient in the Section X scale. -/
theorem exists_canonicalPolymer_twoRegime_error
    (b U m₀ : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ n : ℝ) →
      canonicalPolymerReal (row₀ n) (U n) ≤
        Real.exp (C * Real.log (n : ℝ) ^ 8))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      (m₀ n : ℝ) < (n : ℝ) / Real.log (n : ℝ) ^ 6 →
      canonicalPolymerReal (row₀ n) (U n) ≤
        Real.exp (C * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    ∃ epsilon : ℕ → ℝ,
      Tendsto epsilon atTop (nhds 0) ∧
      (∀ᶠ n in atTop, 0 ≤ epsilon n) ∧
      ∀ᶠ n in atTop,
        midpointCanonicalPolymerSum (row₀ n) (U n) ≤
          ENNReal.ofReal (Real.exp (epsilon n * amplificationBase n)) := by
  obtain ⟨epsilon, hepsilon, hevent⟩ :=
    exists_uniform_twoRegime_error
      (fun _ => Unit)
      (fun n (_ : Unit) => canonicalPolymerReal (row₀ n) (U n))
      (fun n (_ : Unit) => m₀ n) C hC
      (by
        filter_upwards [hlarge] with n hn
        intro _ hm
        exact hn hm)
      (by
        filter_upwards [hsmall] with n hn
        intro _ hm
        exact hn hm)
  refine ⟨epsilon, hepsilon, hevent.mono fun n hn => hn.1, ?_⟩
  filter_upwards [hevent] with n hn
  rw [← ofReal_canonicalPolymerReal (row₀ n) (U n)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [amplificationBase, mul_div_assoc] using (hn.2 ())

/-- Complete conditional theorem-level seed assembly from the concrete two-regime
canonical-polymer estimates.  The exponent is the explicit
`canonicalMidpointLambda`; its nonnegativity is unconditional and its Little-o
property is derived here. -/
theorem canonicalMidpoint_secondMoment_seed_of_twoRegime
    (b U m₀ : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (C : ℝ) (hC : 0 ≤ C)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hlarge : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ^ 6 ≤ (m₀ n : ℝ) →
      canonicalPolymerReal (row₀ n) (U n) ≤
        Real.exp (C * Real.log (n : ℝ) ^ 8))
    (hsmall : ∀ᶠ n : ℕ in atTop,
      (m₀ n : ℝ) < (n : ℝ) / Real.log (n : ℝ) ^ 6 →
      canonicalPolymerReal (row₀ n) (U n) ≤
        Real.exp (C * (n : ℝ) / Real.log (n : ℝ) ^ 5)) :
    (∀ n, signedProfileSecondMoment n (k n) /
        signedProfileExpectation n (k n) ^ 2 ≤
      ENNReal.ofReal
        (Real.exp (canonicalMidpointLambda (row₀ n) (U n)))) ∧
    (∀ n, 0 ≤ canonicalMidpointLambda (row₀ n) (U n)) ∧
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  obtain ⟨epsilon, hepsilon, hepsilonNonneg, hpolymer⟩ :=
    exists_canonicalPolymer_twoRegime_error
      b U m₀ k row₀ C hC hlarge hsmall
  exact canonicalMidpoint_secondMoment_seed_of_polymer_bound
    b U k row₀ epsilon hU hcap hepsilonNonneg hepsilon hpolymer

#print axioms exists_canonicalPolymer_twoRegime_error
#print axioms canonicalMidpoint_secondMoment_seed_of_twoRegime

end

end Erdos625
