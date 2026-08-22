import Erdos625.SignedFourFirstMomentPositiveRate
import Erdos625.ProfileOptimizerUniformS4
import Mathlib.Tactic

/-!
# Eventual admissibility of the tangent-rounded midpoint profile

`MidpointRoundingAdmissible` contains five finite obligations:

* `5 < alpha`;
* `0 < K`;
* `n <= alpha * K`;
* the deficit target lies in `(2,5)`;
* every scaled optimizer coordinate is at least `14`.

For the phase sequence `alpha = phaseNat n`, the first obligation follows
from the established phase asymptotics.  The normalized part-count limit
`K_n / (n/log n) -> q/2` gives positivity and sufficient growth.  A compact
interior target corridor gives a uniform positive lower bound for all four
optimizer coordinates via the existing joint-continuity/Heine--Cantor
certificate.

This module assembles those ingredients and removes eventual midpoint
admissibility as an independent E625-10 hypothesis.  The only new analytic
input is that the actual midpoint targets remain in one fixed compact subset
of `(2,5)`.

No first-moment estimate, root-gap estimate, derivative estimate, chromatic
lower tail, partial diagonal, second moment, or final Erdős statement is
assumed or proved here.
-/

namespace Erdos625

open Filter Set Asymptotics
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- The natural-number phase tends to infinity. -/
theorem tendsto_phaseNat_atTop_nat : Tendsto phaseNat atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro A
  have hLog : ∀ᶠ n : ℕ in atTop, (A : ℝ) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually (eventually_ge_atTop (A : ℝ))
  filter_upwards
    [hLog, eventually_logOrder_le_phaseNat_and_phaseNat_le_four_logOrder]
      with n hnLog hnPhase
  exact_mod_cast hnLog.trans hnPhase.1

/-- The four finite deficit scores converge uniformly along the actual phase
sequence, with explicit sequential quantifiers. -/
theorem uniform_fourDeficitScore_along_phaseNat :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i : Fin 4,
      |fourDeficitScore (phaseNat n) i - fourGaussianScore i| < ε := by
  intro ε hε
  obtain ⟨A, hA⟩ := eventually_uniform_fourDeficitScore ε hε
  have hPhase : ∀ᶠ n : ℕ in atTop, A ≤ phaseNat n :=
    tendsto_phaseNat_atTop_nat.eventually (eventually_ge_atTop A)
  rw [eventually_atTop] at hPhase
  obtain ⟨N, hN⟩ := hPhase
  exact ⟨N, fun n hn i ↦ hA (phaseNat n) (hN n hn) i⟩

/-- Compact target containment supplies one eventual positive lower bound for
all four moving midpoint optimizer coordinates. -/
theorem exists_eventually_midpointOptimizer_lower_on_compact
    (K : ℕ → ℕ) (C : Set ℝ)
    (hCcompact : IsCompact C)
    (hCinterior : C ⊆ Ioo (2 : ℝ) 5)
    (hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (K n : ℝ) ∈ C) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∀ i : Fin 4,
      c ≤ midpointOptimizer n (phaseNat n) (K n) i := by
  obtain ⟨c, hc, N, hN⟩ :=
    ProfileEntropyS4.eventually_uniform_optimizer_pos_on_compact
      (fun n : ℕ ↦ fourDeficitScore (phaseNat n))
      fourGaussianScore C hCcompact hCinterior
      uniform_fourDeficitScore_along_phaseNat
  refine ⟨c, hc, ?_⟩
  filter_upwards [hTarget, eventually_ge_atTop N] with n hnTarget hnN
  intro i
  simpa only [midpointOptimizer] using
    hN n hnN (fourSizeTarget n (phaseNat n) (K n : ℝ)) hnTarget i

/-- Finite assembly of `MidpointRoundingAdmissible` from a positive optimizer
floor and a sufficiently large part count.  The vertex-mass inequality is not
assumed: it follows from the positive target condition. -/
theorem midpointRoundingAdmissible_of_optimizer_lower
    (n alpha K : ℕ) (c : ℝ)
    (hAlpha : 5 < alpha)
    (hK : 0 < K)
    (hTarget : fourSizeTarget n alpha (K : ℝ) ∈ Ioo (2 : ℝ) 5)
    (hc : 0 < c)
    (hOptimizer : ∀ i : Fin 4, c ≤ midpointOptimizer n alpha K i)
    (hKLarge : 14 / c ≤ (K : ℝ)) :
    MidpointRoundingAdmissible n alpha K := by
  have hKReal : (0 : ℝ) < K := by exact_mod_cast hK
  have hTargetLower := hTarget.1
  simp only [fourSizeTarget] at hTargetLower
  have hnDivLtAlpha : (n : ℝ) / (K : ℝ) < (alpha : ℝ) := by
    linarith
  have hnLtMul : (n : ℝ) < (alpha : ℝ) * (K : ℝ) :=
    (div_lt_iff₀ hKReal).mp hnDivLtAlpha
  have hnLeCast : (n : ℝ) ≤ ((alpha * K : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact hnLtMul.le
  have hnLe : n ≤ alpha * K := by exact_mod_cast hnLeCast
  have hFourteen : (14 : ℝ) ≤ (K : ℝ) * c :=
    (div_le_iff₀ hc).mp hKLarge
  refine ⟨hAlpha, hK, hnLe, hTarget, ?_⟩
  intro i
  exact hFourteen.trans
    (mul_le_mul_of_nonneg_left (hOptimizer i) (Nat.cast_nonneg K))

/-- A normalized part-count limit makes `K_n` eventually large enough for any
fixed positive optimizer floor. -/
theorem eventually_fourteen_div_le_parts_of_normalized_tendsto
    (K : ℕ → ℕ) (c : ℝ) (_hc : 0 < c)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop, 14 / c ≤ (K n : ℝ) := by
  have hLogThreshold : ∀ᶠ n : ℕ in atTop,
      max 1 (14 / c) ≤ logOrder n :=
    tendsto_logOrder_atTop.eventually
      (eventually_ge_atTop (max 1 (14 / c)))
  have hLogSquare : ∀ᶠ n : ℕ in atTop,
      14 / c ≤ (logOrder n) ^ 2 := by
    filter_upwards [hLogThreshold] with n hn
    have hOne : (1 : ℝ) ≤ logOrder n :=
      (le_max_left 1 (14 / c)).trans hn
    have hThreshold : 14 / c ≤ logOrder n :=
      (le_max_right 1 (14 / c)).trans hn
    have hNonneg : 0 ≤ logOrder n := zero_le_one.trans hOne
    have hMul := mul_le_mul_of_nonneg_right hOne hNonneg
    have hSelfLeSquare : logOrder n ≤ (logOrder n) ^ 2 := by
      simpa only [one_mul, pow_two] using hMul
    exact hThreshold.trans hSelfLeSquare
  have hSquareLeParts :=
    eventually_logOrder_sq_le_parts_of_normalized_tendsto K hParts
  filter_upwards [hLogSquare, hSquareLeParts] with n hnLog hnParts
  exact hnLog.trans hnParts

/-- **Eventual midpoint admissibility.**  Compact containment of the actual
phase targets and the ordinary manuscript part-count asymptotic discharge all
five finite rounding obligations. -/
theorem eventually_midpointRoundingAdmissible_of_compactTarget
    (K : ℕ → ℕ) (C : Set ℝ)
    (hCcompact : IsCompact C)
    (hCinterior : C ⊆ Ioo (2 : ℝ) 5)
    (hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n) (K n : ℝ) ∈ C)
    (hParts : Tendsto (signedFourNormalizedPartCount K)
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n) (K n) := by
  obtain ⟨c, hc, hOptimizer⟩ :=
    exists_eventually_midpointOptimizer_lower_on_compact
      K C hCcompact hCinterior hTarget
  have hKPos :=
    eventually_signedFourPartCount_pos_of_normalized_tendsto K hParts
  have hKLarge :=
    eventually_fourteen_div_le_parts_of_normalized_tendsto K c hc hParts
  filter_upwards [eventually_five_lt_phaseNat, hKPos, hTarget,
    hOptimizer, hKLarge] with n hnAlpha hnK hnTarget hnOptimizer hnLarge
  exact midpointRoundingAdmissible_of_optimizer_lower
    n (phaseNat n) (K n) c hnAlpha hnK
    (hCinterior hnTarget) hc hnOptimizer hnLarge

/-- Root-midpoint specialization of the compact-target admissibility theorem. -/
theorem eventually_rootMidpointRoundingAdmissible_of_compactTarget
    (rCo rPlus : ℕ → ℝ) (C : Set ℝ)
    (hCcompact : IsCompact C)
    (hCinterior : C ⊆ Ioo (2 : ℝ) 5)
    (hTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∈ C)
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop,
      MidpointRoundingAdmissible n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n) :=
  eventually_midpointRoundingAdmissible_of_compactTarget
    (signedFourRootMidpointPartCount rCo rPlus)
    C hCcompact hCinterior hTarget hParts

/-- Manuscript-facing exponential first-moment endpoint with midpoint
admissibility derived internally from compact target containment. -/
theorem
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_compactTarget
    (rCo rPlus slopeLower slopeUpper : ℕ → ℝ) (C : Set ℝ)
    (hCcompact : IsCompact C)
    (hCinterior : C ⊆ Ioo (2 : ℝ) 5)
    (hCompactTarget : ∀ᶠ n : ℕ in atTop,
      fourSizeTarget n (phaseNat n)
        (signedFourRootMidpointPartCount rCo rPlus n : ℝ) ∈ C)
    (hCo : ∀ᶠ n : ℕ in atTop, 0 ≤ rCo n)
    (hGap : ∀ᶠ n : ℕ in atTop, 2 ≤ rPlus n - rCo n)
    (hSlopeLowerNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeLower n)
    (hSlopeUpperNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ slopeUpper n)
    (hFeasible : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (rCo n) (rPlus n),
        0 < s ∧ fourSizeTarget n (phaseNat n) s ∈ Ioo (2 : ℝ) 5)
    (hDerivLower : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        slopeLower n ≤ signedFourSizeObjectiveDerivative n (phaseNat n) s)
    (hDerivUpper : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Ioo (rCo n) (rPlus n),
        signedFourSizeObjectiveDerivative n (phaseNat n) s ≤ slopeUpper n)
    (hRoot : ∀ᶠ n : ℕ in atTop,
      phaseSignedFourSizeObjective n (rCo n) = 0)
    (hSlopeLower : Tendsto (signedFourNormalizedSlope slopeLower)
      atTop (𝓝 (2 / q)))
    (hSlopeUpper : Tendsto (signedFourNormalizedSlope slopeUpper)
      atTop (𝓝 (2 / q)))
    (hRootGap : Tendsto
      (fun n : ℕ ↦
        signedFourNormalizedRootGap rCo rPlus n -
          q ^ 2 / 4 * signedFourPhaseMargin n)
      atTop (𝓝 0))
    (hParts : Tendsto
      (signedFourNormalizedPartCount
        (signedFourRootMidpointPartCount rCo rPlus))
      atTop (𝓝 (q / 2))) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          (signedFourCertifiedFirstMomentRate *
            (signedFourRootMidpointPartCount rCo rPlus n : ℝ)) <
        signedFourRootMidpointFirstMoment rCo rPlus n := by
  have hAdmissible :=
    eventually_rootMidpointRoundingAdmissible_of_compactTarget
      rCo rPlus C hCcompact hCinterior hCompactTarget hParts
  exact
    eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor
      rCo rPlus slopeLower slopeUpper hCo hGap
      hSlopeLowerNonneg hSlopeUpperNonneg hFeasible
      hDerivLower hDerivUpper hRoot hSlopeLower hSlopeUpper
      hRootGap hParts hAdmissible

#print axioms tendsto_phaseNat_atTop_nat
#print axioms uniform_fourDeficitScore_along_phaseNat
#print axioms exists_eventually_midpointOptimizer_lower_on_compact
#print axioms midpointRoundingAdmissible_of_optimizer_lower
#print axioms eventually_fourteen_div_le_parts_of_normalized_tendsto
#print axioms eventually_midpointRoundingAdmissible_of_compactTarget
#print axioms eventually_rootMidpointRoundingAdmissible_of_compactTarget
#print axioms eventually_exp_certifiedRate_mul_parts_lt_signedFourRootMidpointFirstMoment_of_rootCorridor_and_compactTarget

end

end Erdos625
