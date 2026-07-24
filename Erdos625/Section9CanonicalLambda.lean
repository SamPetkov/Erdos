import Erdos625.Section9MidpointSecondMomentSeed
import Mathlib.Tactic

/-!
# Section IX: canonical finite exponent

This module packages the literal attained-demand polymer sum into an explicit
canonical exponent. Its pointwise self-envelope is finite algebra, not the
missing asymptotic estimate. The central analytic obligation remains to prove
that this concrete exponent is little-o on the intended midpoint profile
sequence, for example through the direct polymer bound stated below.
-/

namespace Erdos625

open Filter
open scoped BigOperators ENNReal Topology

noncomputable section

lemma configurationCellTheta_ne_top
    {A B : Type*} [Fintype A] [Fintype B]
    (row : A → ℕ) (col : B → ℕ) (a : A) (b : B) :
    configurationCellTheta row col (Finset.univ.sum row) a b ≠ ∞ := by
  unfold configurationCellTheta
  by_cases hm : Finset.univ.sum row = 0
  · have hrow : row a = 0 :=
      (Finset.sum_eq_zero_iff.mp hm) a (Finset.mem_univ a)
    simp [hrow]
  · exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
        (ENNReal.natCast_ne_top _))
      (by exact_mod_cast hm)

lemma residualLambda_ne_top
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (a : A) (b : B) :
    residualLambda M R row col a b ≠ ∞ := by
  unfold residualLambda
  split_ifs
  · simp
  · rw [ENNReal.sum_ne_top]
    intro x hx
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.pow_ne_top (configurationCellTheta_ne_top row col a b)))
      (by exact_mod_cast Nat.factorial_ne_zero x)

lemma residualQ_ne_top
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (M : Finset (A × B)) (R : ℕ) (row : A → ℕ) (col : B → ℕ)
    (a : A) (b : B) :
    residualQ M R row col a b ≠ ∞ := by
  unfold residualQ
  split_ifs
  · simp
  · rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.div_ne_top
      (ENNReal.pow_ne_top (configurationCellTheta_ne_top row col a b))
      (by norm_num), residualLambda_ne_top M R row col a b⟩

lemma edgeWeightOutsideENN_ne_top
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (q : A → B → ENNReal) (hq : ∀ a b, q a b ≠ ∞)
    (M F : Finset (A × B)) :
    edgeWeightOutsideENN q M F ≠ ∞ := by
  unfold edgeWeightOutsideENN
  exact ENNReal.prod_ne_top fun e he => hq e.1 e.2

lemma canonicalDemandPolymerMajorant_ne_top
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (row : A → ℕ) (col : B → ℕ) (U : ℕ)
    (demand : canonicalDemandImage row col U) :
    canonicalDemandPolymerMajorant row col U demand ≠ ∞ := by
  unfold canonicalDemandPolymerMajorant
  apply ENNReal.mul_ne_top
  · apply ENNReal.prod_ne_top
    intro a ha
    apply ENNReal.prod_ne_top
    intro b hb
    rw [ENNReal.add_ne_top]
    exact ⟨by simp, residualLambda_ne_top _ _ _ _ _ _⟩
  · apply ENNReal.prod_ne_top
    intro C hC
    rw [ENNReal.add_ne_top]
    refine ⟨by simp, edgeWeightOutsideENN_ne_top _ ?_ _ _⟩
    intro a b
    exact residualQ_ne_top _ _ _ _ _ _

lemma midpointCanonicalPolymerSum_ne_top
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) :
    midpointCanonicalPolymerSum row₀ U ≠ ∞ := by
  unfold midpointCanonicalPolymerSum
  rw [ENNReal.sum_ne_top]
  intro demand hdemand
  apply ENNReal.mul_ne_top
  · exact ENNReal.natCast_ne_top _
  · apply ENNReal.mul_ne_top
    · unfold labelledWitnessIncidence
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by
        exact_mod_cast (Nat.descFactorial_pos.mpr
          (profileHighSkeleton_totalDemand_le k U demand)).ne')
    · exact canonicalDemandPolymerMajorant_ne_top
        (profileBlockMargin k) (profileBlockMargin k) U demand

/-- Explicit finite exponent attached to the literal canonical polymer sum. -/
noncomputable def canonicalMidpointLambda
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) : ℝ :=
  max 0 (Real.log (midpointCanonicalPolymerSum row₀ U).toReal)

/-- The canonical exponent is nonnegative, without an additional estimate. -/
theorem canonicalMidpointLambda_nonneg
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) :
    0 ≤ canonicalMidpointLambda row₀ U := by
  exact le_max_left _ _

/-- The literal polymer sum is bounded by the exponential of its canonical
nonnegative exponent. -/
theorem midpointCanonicalPolymerSum_le_exp_canonicalMidpointLambda
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) :
    midpointCanonicalPolymerSum row₀ U ≤
      ENNReal.ofReal (Real.exp (canonicalMidpointLambda row₀ U)) := by
  have htop := midpointCanonicalPolymerSum_ne_top row₀ U
  by_cases hzero : midpointCanonicalPolymerSum row₀ U = 0
  · simp [hzero]
  · have hreal : 0 < (midpointCanonicalPolymerSum row₀ U).toReal :=
      ENNReal.toReal_pos hzero htop
    rw [← ENNReal.ofReal_toReal htop]
    apply ENNReal.ofReal_le_ofReal
    calc
      (midpointCanonicalPolymerSum row₀ U).toReal =
          Real.exp (Real.log (midpointCanonicalPolymerSum row₀ U).toReal) :=
        (Real.exp_log hreal).symm
      _ ≤ Real.exp (canonicalMidpointLambda row₀ U) := by
        apply Real.exp_le_exp.mpr
        exact le_max_right _ _

/-- Concrete finite second-moment bound with an explicit nonnegative exponent. -/
theorem normalizedSignedProfileSecondMoment_le_exp_canonicalMidpointLambda
    {b n : ℕ} {k : ColoringProfile b}
    (row₀ : OrderedProfilePartition n k) (U : ℕ) (hU : 2 ≤ U)
    (hcap : ∀ a : ProfileBlockIndex k, profileBlockMargin k a ≤ U) :
    signedProfileSecondMoment n k / signedProfileExpectation n k ^ 2 ≤
      ENNReal.ofReal (Real.exp (canonicalMidpointLambda row₀ U)) := by
  exact (normalizedSignedProfileSecondMoment_le_midpointCanonicalPolymerSum
    row₀ U hU hcap).trans
      (midpointCanonicalPolymerSum_le_exp_canonicalMidpointLambda row₀ U)

/-- A direct eventual bound on the concrete polymer sum implies the required
Little-o estimate for the canonical logarithmic exponent.  This is the exact
analytic input shape needed from the Section VII--IX near/middle and two-regime
estimates; no exponent or demand law is hidden in the premise. -/
theorem canonicalMidpointLambda_isLittleO_of_polymer_bound
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ᶠ n in atTop, 0 ≤ epsilon n)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hpolymer : ∀ᶠ n in atTop,
      midpointCanonicalPolymerSum (row₀ n) (U n) ≤
        ENNReal.ofReal (Real.exp
          (epsilon n * amplificationBase n))) :
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hepsilonBound : ∀ᶠ n in atTop, |epsilon n| < c := by
    simpa [Real.dist_eq] using
      hepsilon.eventually (Metric.ball_mem_nhds (0 : ℝ) hc)
  have hbasePos : ∀ᶠ n : ℕ in atTop, 0 < amplificationBase n := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    unfold amplificationBase
    exact div_pos (Nat.cast_pos.mpr (by omega))
      (pow_pos (Real.log_pos (by exact_mod_cast hn)) 4)
  filter_upwards [hepsilonNonneg, hepsilonBound, hpolymer, hbasePos] with
      n hεnonneg hεbound hpoly hbase
  have hexpPos : 0 < Real.exp (epsilon n * amplificationBase n) := Real.exp_pos _
  have htoReal :
      (midpointCanonicalPolymerSum (row₀ n) (U n)).toReal ≤
        Real.exp (epsilon n * amplificationBase n) := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpoly
    simpa [ENNReal.toReal_ofReal hexpPos.le] using h
  have hlog :
      Real.log (midpointCanonicalPolymerSum (row₀ n) (U n)).toReal ≤
        epsilon n * amplificationBase n := by
    by_cases hz : midpointCanonicalPolymerSum (row₀ n) (U n) = 0
    · simp [hz, mul_nonneg hεnonneg hbase.le]
    · apply (Real.log_le_iff_le_exp
        (ENNReal.toReal_pos hz
          (midpointCanonicalPolymerSum_ne_top (row₀ n) (U n)))).2
      exact htoReal
  have hlambda :
      canonicalMidpointLambda (row₀ n) (U n) ≤
        epsilon n * amplificationBase n := by
    unfold canonicalMidpointLambda
    exact max_le (mul_nonneg hεnonneg hbase.le) hlog
  rw [Real.norm_eq_abs,
    abs_of_nonneg (canonicalMidpointLambda_nonneg (row₀ n) (U n)),
    Real.norm_eq_abs, abs_of_pos hbase]
  calc
    canonicalMidpointLambda (row₀ n) (U n) ≤
        epsilon n * amplificationBase n := hlambda
    _ ≤ c * amplificationBase n := by
      apply mul_le_mul_of_nonneg_right
      have hεlt : epsilon n < c := by
        simpa [abs_of_nonneg hεnonneg] using hεbound
      exact hεlt.le
      exact hbase.le

/-- For a concrete profile sequence, only the direct polymer bound above
remains analytic; nonnegativity and the finite second-moment estimate are
unconditional consequences. -/
theorem canonicalMidpoint_secondMoment_seed
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hsmall : (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase) :
    (∀ n, signedProfileSecondMoment n (k n) /
        signedProfileExpectation n (k n) ^ 2 ≤
      ENNReal.ofReal
        (Real.exp (canonicalMidpointLambda (row₀ n) (U n)))) ∧
    (∀ n, 0 ≤ canonicalMidpointLambda (row₀ n) (U n)) ∧
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  exact ⟨fun n => normalizedSignedProfileSecondMoment_le_exp_canonicalMidpointLambda
    (row₀ n) (U n) (hU n) (hcap n),
    fun n => canonicalMidpointLambda_nonneg (row₀ n) (U n), hsmall⟩

/-- The direct polymer estimate can be consumed immediately: it supplies the
Little-o property, while the finite second-moment bound and nonnegativity are
already unconditional. -/
theorem canonicalMidpoint_secondMoment_seed_of_polymer_bound
    (b U : ℕ → ℕ)
    (k : (n : ℕ) → ColoringProfile (b n))
    (row₀ : (n : ℕ) → OrderedProfilePartition n (k n))
    (epsilon : ℕ → ℝ)
    (hU : ∀ n, 2 ≤ U n)
    (hcap : ∀ n (a : ProfileBlockIndex (k n)),
      profileBlockMargin (k n) a ≤ U n)
    (hepsilonNonneg : ∀ᶠ n in atTop, 0 ≤ epsilon n)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hpolymer : ∀ᶠ n in atTop,
      midpointCanonicalPolymerSum (row₀ n) (U n) ≤
        ENNReal.ofReal (Real.exp
          (epsilon n * amplificationBase n))) :
    (∀ n, signedProfileSecondMoment n (k n) /
        signedProfileExpectation n (k n) ^ 2 ≤
      ENNReal.ofReal
        (Real.exp (canonicalMidpointLambda (row₀ n) (U n)))) ∧
    (∀ n, 0 ≤ canonicalMidpointLambda (row₀ n) (U n)) ∧
    (fun n => canonicalMidpointLambda (row₀ n) (U n)) =o[atTop]
      amplificationBase := by
  apply canonicalMidpoint_secondMoment_seed b U k row₀ hU hcap
  exact canonicalMidpointLambda_isLittleO_of_polymer_bound
    b U k row₀ epsilon hepsilonNonneg hepsilon hpolymer


#print axioms canonicalMidpointLambda_isLittleO_of_polymer_bound
#print axioms canonicalMidpoint_secondMoment_seed
#print axioms canonicalMidpoint_secondMoment_seed_of_polymer_bound

end

end Erdos625
