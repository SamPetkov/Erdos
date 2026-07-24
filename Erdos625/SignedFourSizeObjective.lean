import Erdos625.FourDeficitScoreConvergence
import Erdos625.ProfileOptimizerContinuityS4
import Erdos625.SignedProfileWitness
import Mathlib.Tactic

/-!
# The signed four-size finite objective

This module isolates the actual Section V root function.  It is deliberately
different from `profilePhaseObjective`: the latter is an unrestricted
size-coordinate upper envelope used for the chromatic lower tail, whereas the
function below is the four-deficit (`S4 = {2,3,4,5}`) entropy optimum together
with the exact signed first-moment bonus `log 2` per part.

The module proves the finite algebraic and calculus leaves only.  In
particular, it does not claim the entropy certificate, a root corridor, a
root exists, or the numerical `log (200 / 153)` margin.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Erdos625

noncomputable section

/-! ## The exact four-deficit score -/

/-- The finite coordinate in the full deficit support corresponding to one of
the four allowed deficits.  The hypothesis is exactly what makes the class
sizes `alpha - 2, ..., alpha - 5` positive. -/
def fourDeficitCoordinate (alpha : Nat) (halpha : 5 < alpha)
    (i : Fin 4) : Fin (alpha + 1) :=
  Fin.rev ((⟨fourDeficit i, by
    have hle : fourDeficit i ≤ 5 := by
      fin_cases i <;> norm_num [fourDeficit]
    omega⟩ : Fin alpha).succ)

/-- The reindexed finite coordinate really has the advertised deficit. -/
theorem profileDeficit_fourDeficitCoordinate
    (alpha : Nat) (halpha : 5 < alpha) (i : Fin 4) :
    profileDeficit alpha (fourDeficitCoordinate alpha halpha i) =
      (fourDeficit i : Real) := by
  unfold fourDeficitCoordinate profileDeficit profileClassSize
  rw [Fin.val_rev, Fin.val_succ]
  push_cast
  have hle : fourDeficit i ≤ 5 := by
    fin_cases i <;> norm_num [fourDeficit]
  have hlt : fourDeficit i < alpha := lt_of_le_of_lt hle halpha
  have hnat : alpha - (fourDeficit i + 1) + 1 = alpha - fourDeficit i := by
    omega
  have hcast :
      ((alpha - (fourDeficit i + 1) : Nat) : Real) + 1 =
        ((alpha - fourDeficit i : Nat) : Real) := by
    norm_cast
  rw [hcast, Nat.cast_sub (Nat.le_of_lt hlt)]
  ring

/-- The exact centered residual score at a permitted four-deficit coordinate
is `fourDeficitScore`.  This is the finite, rather than limiting-Gaussian,
score used by the Section V objective. -/
theorem profileDeficitResidualScore_fourDeficitCoordinate
    (alpha : Nat) (halpha : 5 < alpha) (i : Fin 4) :
    profileDeficitResidualScore alpha (fourDeficitCoordinate alpha halpha i) =
      fourDeficitScore alpha i := by
  unfold fourDeficitCoordinate
  apply profileDeficitResidualScore_rev_succ_eq_fourDeficitScore

/-- A concrete coloring profile uses only the four allowed deficit
coordinates when every occupied class has deficit in `{2,3,4,5}`.  This
semantic predicate is intentionally separate from the real four-point
optimizer below: integer rounding is a later proof obligation. -/
def IsFourDeficitSupported (alpha : Nat) (k : ColoringProfile (alpha + 1)) : Prop :=
  ∀ j, k j ≠ 0 → ∃ i : Fin 4, profileDeficit alpha j = (fourDeficit i : Real)

/-- The signed first-moment factor is exact for every concrete profile, hence
also for each four-deficit-supported profile.  This is the bridge from the
analytic sign bonus in the objective to the graph-theoretic signed witness
count. -/
theorem signedFourDeficitProfileExpectation_eq
    (n alpha : Nat) (k : ColoringProfile (alpha + 1))
    (_hk : IsFourDeficitSupported alpha k) :
    signedProfileExpectation n k =
      (2 : ENNReal) ^ ColoringProfile.partCount k *
        profileColoringExpectation n k :=
  signedProfileExpectation_eq n k

/-! ## Finite entropy value and the signed objective -/

/-- The target deficit mean attached to a real part count.  In the manuscript
notation this is `T = alpha - n / k`. -/
def fourSizeTarget (n alpha : Nat) (parts : Real) : Real :=
  (alpha : Real) - (n : Real) / parts

/-- The attained finite four-size entropy value at prescribed deficit mean.
Unlike the limiting Gaussian value, this uses the exact descending-factorial
scores `fourDeficitScore alpha`. -/
noncomputable def fourSizeFiniteEntropy (alpha : Nat) (target : Real) : Real :=
  ProfileEntropyS4.optimizedValue (fourDeficitScore alpha) target

/-- The entropy-plus-score expression evaluated at the exact finite Gibbs
optimizer.  It is written separately so the exact variational rewrite is
visible in the formalization. -/
noncomputable def fourSizeGibbsEntropy (alpha : Nat) (target : Real) : Real :=
  -(∑ i : Fin 4,
      ProfileEntropyS4.optimizer (fourDeficitScore alpha) target i *
        Real.log (ProfileEntropyS4.optimizer (fourDeficitScore alpha) target i)) +
    ∑ i : Fin 4,
      ProfileEntropyS4.optimizer (fourDeficitScore alpha) target i *
        fourDeficitScore alpha i

/-- The exact Gibbs optimizer attains the finite entropy value at every
interior target. -/
theorem fourSizeFiniteEntropy_eq_gibbs
    (alpha : Nat) {target : Real}
    (htarget : target ∈ Set.Ioo (2 : Real) 5) :
    fourSizeFiniteEntropy alpha target = fourSizeGibbsEntropy alpha target := by
  unfold fourSizeFiniteEntropy fourSizeGibbsEntropy
  simpa only [ProfileEntropyS4.optimizedValue] using
    (ProfileEntropyS4.optimizer_entropy_score_eq_log_partition_sub_tilt_mul_target
      (fourDeficitScore alpha) htarget).symm

/-- The signed `S4` objective at an explicit target mean.  Its three pieces
are the finite Stirling/part-count term, the exact affine-plus-residual
deficit entropy, and the signed first-moment bonus `q * parts`. -/
noncomputable def signedFourSizeObjectiveAtTarget
    (n alpha : Nat) (parts target : Real) : Real :=
  (n : Real) * Real.log (n : Real) - (n : Real) +
    parts - parts * Real.log parts +
    parts *
      (profileDeficitAffineA alpha +
        profileDeficitAffineB alpha * target +
        fourSizeFiniteEntropy alpha target + q)

/-- The same signed objective with the entropy term displayed at its Gibbs
optimizer. -/
noncomputable def signedFourSizeGibbsObjectiveAtTarget
    (n alpha : Nat) (parts target : Real) : Real :=
  (n : Real) * Real.log (n : Real) - (n : Real) +
    parts - parts * Real.log parts +
    parts *
      (profileDeficitAffineA alpha +
        profileDeficitAffineB alpha * target +
        fourSizeGibbsEntropy alpha target + q)

/-- Exact finite deficit/entropy rewrite of the signed `S4` objective. -/
theorem signedFourSizeObjectiveAtTarget_eq_gibbs
    (n alpha : Nat) (parts : Real) {target : Real}
    (htarget : target ∈ Set.Ioo (2 : Real) 5) :
    signedFourSizeObjectiveAtTarget n alpha parts target =
      signedFourSizeGibbsObjectiveAtTarget n alpha parts target := by
  rw [signedFourSizeObjectiveAtTarget, signedFourSizeGibbsObjectiveAtTarget,
    fourSizeFiniteEntropy_eq_gibbs alpha htarget]

/-- The actual one-variable signed four-size root function from Section V:
substitute `T = alpha - n / parts` into the exact finite objective. -/
noncomputable def signedFourSizeObjective (n alpha : Nat) (parts : Real) : Real :=
  signedFourSizeObjectiveAtTarget n alpha parts (fourSizeTarget n alpha parts)

/-- The phase-specialized signed root function used in Sections V and XI.
It is not definitionally or mathematically identified with the ordinary
`profilePhaseObjective`, which has a different support and no sign bonus. -/
noncomputable def phaseSignedFourSizeObjective (n : Nat) (parts : Real) : Real :=
  signedFourSizeObjective n (phaseNat n) parts

/-- A root of the actual signed four-size objective is required to have a
positive part count and an interior deficit target.  No existence or
uniqueness assertion is built into this definition. -/
def IsSignedFourSizeRoot (n alpha : Nat) (root : Real) : Prop :=
  0 < root ∧
    fourSizeTarget n alpha root ∈ Set.Ioo (2 : Real) 5 ∧
      signedFourSizeObjective n alpha root = 0

/-- Phase-specialized root predicate used by the final Section XI assembly. -/
def IsPhaseSignedFourSizeRoot (n : Nat) (root : Real) : Prop :=
  IsSignedFourSizeRoot n (phaseNat n) root

/-- Unfolding the root predicate exposes exactly the signed root equation. -/
theorem isSignedFourSizeRoot_iff
    (n alpha : Nat) (root : Real) :
    IsSignedFourSizeRoot n alpha root ↔
      0 < root ∧
        fourSizeTarget n alpha root ∈ Set.Ioo (2 : Real) 5 ∧
          signedFourSizeObjective n alpha root = 0 :=
  Iff.rfl

/-! ## Finite derivative and continuity leaves -/

/-- The selected exact four-point tilt is differentiable in its target. -/
theorem hasDerivAt_fourSizeTilt
    (alpha : Nat) {target : Real}
    (htarget : target ∈ Set.Ioo (2 : Real) 5) :
    HasDerivAt (ProfileEntropyS4.tilt (fourDeficitScore alpha))
      (ProfileEntropyS4.variance (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha) target))⁻¹ target := by
  have hContinuous : ContinuousAt
      (ProfileEntropyS4.tilt (fourDeficitScore alpha)) target := by
    exact ProfileEntropyS4.tendsto_tilt_of_scores_and_target
      (h := fun _ : Real => fourDeficitScore alpha)
      (fourDeficitScore alpha) (T' := id)
      (fun _ => tendsto_const_nhds) tendsto_id htarget
  have hLeftInverse : ∀ᶠ y in nhds target,
      ProfileEntropyS4.mean (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha) y) = y := by
    filter_upwards [isOpen_Ioo.mem_nhds htarget] with y hy
    exact ProfileEntropyS4.mean_tilt_eq (fourDeficitScore alpha) hy
  exact
    (ProfileEntropyS4.hasDerivAt_mean (fourDeficitScore alpha)
      (ProfileEntropyS4.tilt (fourDeficitScore alpha) target)).of_local_left_inverse
      hContinuous
      (ProfileEntropyS4.variance_pos (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha) target)).ne'
      hLeftInverse

/-- Envelope derivative of the exact finite four-size entropy value. -/
theorem hasDerivAt_fourSizeFiniteEntropy
    (alpha : Nat) {target : Real}
    (htarget : target ∈ Set.Ioo (2 : Real) 5) :
    HasDerivAt (fourSizeFiniteEntropy alpha)
      (-ProfileEntropyS4.tilt (fourDeficitScore alpha) target) target := by
  have hTilt := hasDerivAt_fourSizeTilt alpha htarget
  have hLog : HasDerivAt
      (fun t => Real.log (ProfileEntropyS4.partition (fourDeficitScore alpha) t))
      (ProfileEntropyS4.mean (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha) target))
      (ProfileEntropyS4.tilt (fourDeficitScore alpha) target) := by
    simpa only [ProfileEntropyS4.mean] using
      (ProfileEntropyS4.hasDerivAt_partition (fourDeficitScore alpha)
        (ProfileEntropyS4.tilt (fourDeficitScore alpha) target)).log
        (ProfileEntropyS4.partition_pos (fourDeficitScore alpha)
          (ProfileEntropyS4.tilt (fourDeficitScore alpha) target)).ne'
  have hLogComp := hLog.comp target hTilt
  have hProduct := hTilt.mul (hasDerivAt_id target)
  have hMean := ProfileEntropyS4.mean_tilt_eq (fourDeficitScore alpha) htarget
  have hSub := (hLogComp.sub hProduct).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)
  change HasDerivAt
    (fun t => Real.log (ProfileEntropyS4.partition (fourDeficitScore alpha)
      (ProfileEntropyS4.tilt (fourDeficitScore alpha) t)) -
        ProfileEntropyS4.tilt (fourDeficitScore alpha) t * t)
      (-ProfileEntropyS4.tilt (fourDeficitScore alpha) target) target
  apply hSub.congr_deriv
  rw [hMean]
  simp only [id_eq]
  ring

/-- The target map `alpha - n / parts` has its exact finite derivative. -/
theorem hasDerivAt_fourSizeTarget
    (n alpha : Nat) {parts : Real} (hparts : 0 < parts) :
    HasDerivAt (fun x => fourSizeTarget n alpha x)
      ((n : Real) / parts ^ 2) parts := by
  have hQuotient : HasDerivAt (fun x : Real => (n : Real) / x)
      (-(n : Real) / parts ^ 2) parts := by
    change HasDerivAt ((fun _ : Real => (n : Real)) / id)
      (-(n : Real) / parts ^ 2) parts
    apply ((hasDerivAt_const parts (n : Real)).div
      (hasDerivAt_id parts) hparts.ne').congr_deriv
    simp only [id_eq, zero_mul, mul_one, zero_sub]
  have h := (hasDerivAt_const parts (alpha : Real)).sub hQuotient
  change HasDerivAt ((fun _ : Real => (alpha : Real)) -
    fun x => (n : Real) / x)
    ((n : Real) / parts ^ 2) parts
  exact h.congr_deriv (by ring)

/-- The exact derivative which must be controlled on a later root corridor.
This statement is finite and contains no asymptotic or numerical bound. -/
noncomputable def signedFourSizeObjectiveDerivative
    (n alpha : Nat) (parts : Real) : Real :=
  -Real.log parts +
    (profileDeficitAffineA alpha +
      profileDeficitAffineB alpha * fourSizeTarget n alpha parts +
      fourSizeFiniteEntropy alpha (fourSizeTarget n alpha parts) + q) +
    (profileDeficitAffineB alpha -
      ProfileEntropyS4.tilt (fourDeficitScore alpha)
        (fourSizeTarget n alpha parts)) *
      (n : Real) / parts

/-- Finite envelope derivative of the actual signed four-size root function.
The only analytic hypothesis is that the induced deficit target is interior. -/
theorem hasDerivAt_signedFourSizeObjective
    (n alpha : Nat) {parts : Real} (hparts : 0 < parts)
    (htarget : fourSizeTarget n alpha parts ∈ Set.Ioo (2 : Real) 5) :
    HasDerivAt (signedFourSizeObjective n alpha)
      (signedFourSizeObjectiveDerivative n alpha parts) parts := by
  let target : Real := fourSizeTarget n alpha parts
  have hTarget := hasDerivAt_fourSizeTarget n alpha hparts
  have hEntropy := hasDerivAt_fourSizeFiniteEntropy alpha htarget
  have hEntropyComp := hEntropy.comp parts hTarget
  have hAffine : HasDerivAt
      (fun x => profileDeficitAffineA alpha +
        profileDeficitAffineB alpha * fourSizeTarget n alpha x +
        fourSizeFiniteEntropy alpha (fourSizeTarget n alpha x) + q)
      (profileDeficitAffineB alpha * ((n : Real) / parts ^ 2) +
        (-ProfileEntropyS4.tilt (fourDeficitScore alpha) target) *
          ((n : Real) / parts ^ 2)) parts := by
    have h :=
      (((hasDerivAt_const parts (profileDeficitAffineA alpha)).add
        (hTarget.const_mul (profileDeficitAffineB alpha))).add hEntropyComp).add
        (hasDerivAt_const parts q)
    have hFunction :
        (fun x : Real => profileDeficitAffineA alpha +
          profileDeficitAffineB alpha * fourSizeTarget n alpha x +
          fourSizeFiniteEntropy alpha (fourSizeTarget n alpha x) + q) =
        (((fun _ : Real => profileDeficitAffineA alpha) +
          fun x : Real => profileDeficitAffineB alpha * fourSizeTarget n alpha x) +
          fourSizeFiniteEntropy alpha ∘ fourSizeTarget n alpha +
          fun _ : Real => q) := by
      funext x
      simp only [Function.comp_apply, Pi.add_apply]
    rw [hFunction]
    apply h.congr_deriv
    dsimp [target]
    ring
  have hLog := Real.hasDerivAt_log hparts.ne'
  have hPartEntropy := (hasDerivAt_id parts).sub
    ((hasDerivAt_id parts).mul hLog)
  have hProduct := (hasDerivAt_id parts).mul hAffine
  have hTotal := ((hasDerivAt_const parts
      ((n : Real) * Real.log (n : Real) - (n : Real))).add hPartEntropy).add hProduct
  have hObjective := hTotal.congr_of_eventuallyEq
    (f₁ := signedFourSizeObjective n alpha)
    (Filter.Eventually.of_forall fun x => by
      unfold signedFourSizeObjective signedFourSizeObjectiveAtTarget
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq]
      ring)
  apply hObjective.congr_deriv
  dsimp [signedFourSizeObjectiveDerivative, target]
  field_simp [hparts.ne']
  ring

/-- The signed four-size root function is continuous at every admissible
interior point. -/
theorem continuousAt_signedFourSizeObjective
    (n alpha : Nat) {parts : Real} (hparts : 0 < parts)
    (htarget : fourSizeTarget n alpha parts ∈ Set.Ioo (2 : Real) 5) :
    ContinuousAt (signedFourSizeObjective n alpha) parts :=
  (hasDerivAt_signedFourSizeObjective n alpha hparts htarget).continuousAt

/-- The phase-specialized root function inherits the exact finite derivative
without identifying it with the ordinary chromatic phase objective. -/
theorem hasDerivAt_phaseSignedFourSizeObjective
    (n : Nat) {parts : Real} (hparts : 0 < parts)
    (htarget : fourSizeTarget n (phaseNat n) parts ∈ Set.Ioo (2 : Real) 5) :
    HasDerivAt (phaseSignedFourSizeObjective n)
      (signedFourSizeObjectiveDerivative n (phaseNat n) parts) parts := by
  change HasDerivAt (signedFourSizeObjective n (phaseNat n))
    (signedFourSizeObjectiveDerivative n (phaseNat n) parts) parts
  exact hasDerivAt_signedFourSizeObjective n (phaseNat n) hparts htarget

/-- Continuity of the Section V/XI phase-specialized signed root function at
every admissible interior point. -/
theorem continuousAt_phaseSignedFourSizeObjective
    (n : Nat) {parts : Real} (hparts : 0 < parts)
    (htarget : fourSizeTarget n (phaseNat n) parts ∈ Set.Ioo (2 : Real) 5) :
    ContinuousAt (phaseSignedFourSizeObjective n) parts :=
  (hasDerivAt_phaseSignedFourSizeObjective n hparts htarget).continuousAt

end

#print axioms profileDeficitResidualScore_fourDeficitCoordinate
#print axioms profileDeficit_fourDeficitCoordinate
#print axioms signedFourDeficitProfileExpectation_eq
#print axioms fourSizeFiniteEntropy_eq_gibbs
#print axioms signedFourSizeObjectiveAtTarget_eq_gibbs
#print axioms hasDerivAt_fourSizeTilt
#print axioms hasDerivAt_fourSizeFiniteEntropy
#print axioms hasDerivAt_fourSizeTarget
#print axioms hasDerivAt_signedFourSizeObjective
#print axioms continuousAt_signedFourSizeObjective
#print axioms hasDerivAt_phaseSignedFourSizeObjective
#print axioms continuousAt_phaseSignedFourSizeObjective

end Erdos625
