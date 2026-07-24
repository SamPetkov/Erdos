import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.UniformOn
import Erdos625.ProbabilityTools

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open ProbabilityTheory

namespace Erdos625

/-!
# Bounded differences on the finite Boolean cube

This file supplies the independent-coordinate bridge needed for the
bounded-differences estimate in the manuscript.  We work on the uniform
Boolean cube, which is exactly the probability space used for the edge
indicators of `G(n, 1/2)`.  The proof is a finite induction (the usual Doob
exposure argument written as repeated two-point averaging), so it does not
assume a conditional moment-generating-function hypothesis.
-/

/-- Repeated uniform averaging over a Boolean cube.  Defining this
recursively makes the independent-coordinate step computationally visible. -/
noncomputable def cubeMean : {n : ℕ} → ((Fin n → Bool) → ℝ) → ℝ
  | 0, f => f (fun i => Fin.elim0 i)
  | n + 1, f =>
      (cubeMean (fun x : Fin n → Bool => f (Fin.cons false x)) +
        cubeMean (fun x : Fin n → Bool => f (Fin.cons true x))) / 2

@[simp]
theorem cubeMean_zero (f : (Fin 0 → Bool) → ℝ) :
    cubeMean f = f (fun i => Fin.elim0 i) := rfl

@[simp]
theorem cubeMean_succ {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    cubeMean f =
      (cubeMean (fun x => f (Fin.cons false x)) +
        cubeMean (fun x => f (Fin.cons true x))) / 2 := rfl

theorem cubeMean_congr {n : ℕ} {f g : (Fin n → Bool) → ℝ}
    (h : ∀ x, f x = g x) : cubeMean f = cubeMean g := by
  induction n with
  | zero => simp [h]
  | succ n ih =>
      simp only [cubeMean_succ]
      congr 2
      · exact ih (fun x => h (Fin.cons false x))
      · exact ih (fun x => h (Fin.cons true x))

@[simp]
theorem cubeMean_const {n : ℕ} (a : ℝ) :
    cubeMean (fun _ : Fin n → Bool => a) = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cubeMean_succ, ih]

theorem cubeMean_add {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    cubeMean (fun x => f x + g x) = cubeMean f + cubeMean g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cubeMean_succ, ih]
      ring

theorem cubeMean_neg {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    cubeMean (fun x => -f x) = -cubeMean f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cubeMean_succ, ih]
      ring

theorem cubeMean_sub {n : ℕ} (f g : (Fin n → Bool) → ℝ) :
    cubeMean (fun x => f x - g x) = cubeMean f - cubeMean g := by
  change cubeMean (fun x => f x + -g x) = cubeMean f - cubeMean g
  rw [cubeMean_add, cubeMean_neg]
  rfl

theorem cubeMean_const_mul {n : ℕ} (a : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeMean (fun x => a * f x) = a * cubeMean f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cubeMean_succ, ih]
      ring

theorem cubeMean_mono {n : ℕ} {f g : (Fin n → Bool) → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeMean f ≤ cubeMean g := by
  induction n with
  | zero => exact h _
  | succ n ih =>
      simp only [cubeMean_succ]
      gcongr
      · exact ih (fun x => h (Fin.cons false x))
      · exact ih (fun x => h (Fin.cons true x))

/-- Coordinatewise oscillation bounds.  The two inputs may differ only at
the displayed coordinate. -/
def HasCoordinateOscillation {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (c : Fin n → ℝ≥0) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ)

namespace HasCoordinateOscillation

theorem tail {n : ℕ} {f : (Fin (n + 1) → Bool) → ℝ}
    {c : Fin (n + 1) → ℝ≥0} (h : HasCoordinateOscillation f c) (b : Bool) :
    HasCoordinateOscillation (fun x => f (Fin.cons b x)) (fun i => c i.succ) := by
  intro i x y hxy
  apply h i.succ (Fin.cons b x) (Fin.cons b y)
  intro j hj
  cases j using Fin.cases with
  | zero => simp
  | succ k =>
      simp only [Fin.cons_succ]
      apply hxy k
      exact fun hki => hj (congrArg Fin.succ hki)

theorem head {n : ℕ} {f : (Fin (n + 1) → Bool) → ℝ}
    {c : Fin (n + 1) → ℝ≥0} (h : HasCoordinateOscillation f c)
    (x : Fin n → Bool) :
    |f (Fin.cons false x) - f (Fin.cons true x)| ≤ (c 0 : ℝ) := by
  apply h 0 (Fin.cons false x) (Fin.cons true x)
  intro j hj
  cases j using Fin.cases with
  | zero => exact (hj rfl).elim
  | succ k => simp

end HasCoordinateOscillation

private theorem twoPoint_exp_center_le {a b c t : ℝ} (hc : 0 ≤ c)
    (hab : |a - b| ≤ c) :
    (Real.exp (t * (a - (a + b) / 2)) +
        Real.exp (t * (b - (a + b) / 2))) / 2 ≤
      Real.exp ((c / 2) ^ 2 * t ^ 2 / 2) := by
  have habsq : (a - b) ^ 2 ≤ c ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hc] using hab
  have hleft : t * (a - (a + b) / 2) = t * (a - b) / 2 := by ring
  have hright : t * (b - (a + b) / 2) = -(t * (a - b) / 2) := by ring
  calc
    (Real.exp (t * (a - (a + b) / 2)) +
        Real.exp (t * (b - (a + b) / 2))) / 2 =
        Real.cosh (t * (a - b) / 2) := by
          rw [hleft, hright, Real.cosh_eq]
    _ ≤ Real.exp ((t * (a - b) / 2) ^ 2 / 2) :=
      Real.cosh_le_exp_half_sq _
    _ ≤ Real.exp ((c / 2) ^ 2 * t ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t]

private theorem abs_cubeMean_head_sub_le {n : ℕ}
    {f : (Fin (n + 1) → Bool) → ℝ} {c : Fin (n + 1) → ℝ≥0}
    (h : HasCoordinateOscillation f c) :
    |cubeMean (fun x => f (Fin.cons false x)) -
        cubeMean (fun x => f (Fin.cons true x))| ≤ (c 0 : ℝ) := by
  have hu : cubeMean (fun x =>
      f (Fin.cons false x) - f (Fin.cons true x)) ≤ (c 0 : ℝ) := by
    calc
      cubeMean (fun x => f (Fin.cons false x) - f (Fin.cons true x)) ≤
          cubeMean (fun _ : Fin n → Bool => (c 0 : ℝ)) := by
            apply cubeMean_mono
            intro x
            exact (le_abs_self _).trans (h.head x)
      _ = (c 0 : ℝ) := cubeMean_const _
  have hl : -(c 0 : ℝ) ≤ cubeMean (fun x =>
      f (Fin.cons false x) - f (Fin.cons true x)) := by
    calc
      -(c 0 : ℝ) = cubeMean (fun _ : Fin n → Bool => -(c 0 : ℝ)) :=
        (cubeMean_const _).symm
      _ ≤ cubeMean (fun x => f (Fin.cons false x) - f (Fin.cons true x)) := by
        apply cubeMean_mono
        intro x
        exact (neg_le_of_abs_le (h.head x))
  rw [cubeMean_sub] at hu hl
  exact abs_le.mpr ⟨hl, hu⟩

/-- The variance proxy in bounded differences: `Σ i, c i² / 4`, represented
as a nonnegative real. -/
noncomputable def coordinateVariance {n : ℕ} (c : Fin n → ℝ≥0) : ℝ≥0 :=
  ∑ i, (c i / 2) ^ 2

private theorem coordinateVariance_succ {n : ℕ} (c : Fin (n + 1) → ℝ≥0) :
    coordinateVariance c = (c 0 / 2) ^ 2 + coordinateVariance (fun i => c i.succ) := by
  simp [coordinateVariance, Fin.sum_univ_succ]

/-- Finite bounded differences in moment-generating-function form.  This is
the analytic heart of McDiarmid's inequality on the uniform Boolean cube. -/
theorem cubeMean_exp_center_le (n : ℕ) :
    ∀ (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ≥0),
      HasCoordinateOscillation f c → ∀ t : ℝ,
        cubeMean (fun x => Real.exp (t * (f x - cubeMean f))) ≤
          Real.exp ((coordinateVariance c : ℝ) * t ^ 2 / 2) := by
  induction n with
  | zero =>
      intro f c h t
      change Real.exp (t * (f (fun i => Fin.elim0 i) - f (fun i => Fin.elim0 i))) ≤
        Real.exp ((coordinateVariance c : ℝ) * t ^ 2 / 2)
      simp [coordinateVariance]
  | succ n ih =>
      intro f c h t
      let f₀ : (Fin n → Bool) → ℝ := fun x => f (Fin.cons false x)
      let f₁ : (Fin n → Bool) → ℝ := fun x => f (Fin.cons true x)
      let c' : Fin n → ℝ≥0 := fun i => c i.succ
      let m₀ : ℝ := cubeMean f₀
      let m₁ : ℝ := cubeMean f₁
      let R : ℝ := Real.exp ((coordinateVariance c' : ℝ) * t ^ 2 / 2)
      have hfmean : cubeMean f = (m₀ + m₁) / 2 := by
        rfl
      have h₀ := ih f₀ c' (h.tail false) t
      have h₁ := ih f₁ c' (h.tail true) t
      have hb₀ :
          cubeMean (fun x => Real.exp (t * (f₀ x - (m₀ + m₁) / 2))) ≤
            Real.exp (t * (m₀ - (m₀ + m₁) / 2)) * R := by
        calc
          cubeMean (fun x => Real.exp (t * (f₀ x - (m₀ + m₁) / 2))) =
              cubeMean (fun x =>
                Real.exp (t * (m₀ - (m₀ + m₁) / 2)) *
                  Real.exp (t * (f₀ x - m₀))) := by
                    apply cubeMean_congr
                    intro x
                    rw [← Real.exp_add]
                    congr 1
                    ring
          _ = Real.exp (t * (m₀ - (m₀ + m₁) / 2)) *
                cubeMean (fun x => Real.exp (t * (f₀ x - m₀))) :=
              cubeMean_const_mul _ _
          _ ≤ Real.exp (t * (m₀ - (m₀ + m₁) / 2)) * R := by
              apply mul_le_mul_of_nonneg_left
              · simpa [m₀, R] using h₀
              · exact Real.exp_nonneg _
      have hb₁ :
          cubeMean (fun x => Real.exp (t * (f₁ x - (m₀ + m₁) / 2))) ≤
            Real.exp (t * (m₁ - (m₀ + m₁) / 2)) * R := by
        calc
          cubeMean (fun x => Real.exp (t * (f₁ x - (m₀ + m₁) / 2))) =
              cubeMean (fun x =>
                Real.exp (t * (m₁ - (m₀ + m₁) / 2)) *
                  Real.exp (t * (f₁ x - m₁))) := by
                    apply cubeMean_congr
                    intro x
                    rw [← Real.exp_add]
                    congr 1
                    ring
          _ = Real.exp (t * (m₁ - (m₀ + m₁) / 2)) *
                cubeMean (fun x => Real.exp (t * (f₁ x - m₁))) :=
              cubeMean_const_mul _ _
          _ ≤ Real.exp (t * (m₁ - (m₀ + m₁) / 2)) * R := by
              apply mul_le_mul_of_nonneg_left
              · simpa [m₁, R] using h₁
              · exact Real.exp_nonneg _
      have hm : |m₀ - m₁| ≤ (c 0 : ℝ) := by
        simpa [m₀, m₁, f₀, f₁] using abs_cubeMean_head_sub_le h
      have htwo := twoPoint_exp_center_le (t := t) (by positivity : 0 ≤ (c 0 : ℝ)) hm
      rw [cubeMean_succ, hfmean]
      change
        (cubeMean (fun x => Real.exp (t * (f₀ x - (m₀ + m₁) / 2))) +
          cubeMean (fun x => Real.exp (t * (f₁ x - (m₀ + m₁) / 2)))) / 2 ≤ _
      calc
        (cubeMean (fun x => Real.exp (t * (f₀ x - (m₀ + m₁) / 2))) +
            cubeMean (fun x => Real.exp (t * (f₁ x - (m₀ + m₁) / 2)))) / 2 ≤
            (Real.exp (t * (m₀ - (m₀ + m₁) / 2)) * R +
              Real.exp (t * (m₁ - (m₀ + m₁) / 2)) * R) / 2 := by
                gcongr
        _ = R * ((Real.exp (t * (m₀ - (m₀ + m₁) / 2)) +
              Real.exp (t * (m₁ - (m₀ + m₁) / 2))) / 2) := by ring
        _ ≤ R * Real.exp (((c 0 : ℝ) / 2) ^ 2 * t ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left htwo
          exact Real.exp_nonneg _
        _ = Real.exp ((coordinateVariance c : ℝ) * t ^ 2 / 2) := by
          rw [coordinateVariance_succ]
          push_cast
          rw [← Real.exp_add]
          congr 1
          dsimp [R, c']
          ring

theorem cubeMean_eq_sum_div_pow {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    cubeMean f = (∑ x, f x) / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      rw [cubeMean_zero]
      rw [pow_zero, div_one]
      calc
        f (fun i => Fin.elim0 i) = f default := by
          congr
          exact Subsingleton.elim _ _
        _ = ∑ x, f x := by
          convert (Fintype.sum_unique f).symm using 1
          exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
      have hsum :
          (∑ x : Fin (n + 1) → Bool, f x) =
            (∑ x : Fin n → Bool, f (Fin.cons false x)) +
              ∑ x : Fin n → Bool, f (Fin.cons true x) := by
        rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp f, Fintype.sum_prod_type]
        simp
        rw [add_comm]
        simp [Fin.consEquiv]
      rw [cubeMean_succ, ih, ih, hsum, pow_succ]
      ring

theorem coordinateVariance_eq_sum_sq_div_four {n : ℕ} (c : Fin n → ℝ≥0) :
    (coordinateVariance c : ℝ) = ∑ i, (c i : ℝ) ^ 2 / 4 := by
  rw [coordinateVariance]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The uniform probability mass function on the `n`-dimensional Boolean
cube. -/
noncomputable def boolCubePMF (n : ℕ) : PMF (Fin n → Bool) :=
  PMF.uniformOfFintype (Fin n → Bool)

/-- `cubeMean` is the actual measure-theoretic expectation under the uniform
Boolean-cube law. -/
theorem integral_boolCubePMF_eq_cubeMean {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∫ x, f x ∂(boolCubePMF n).toMeasure = cubeMean f := by
  rw [PMF.integral_eq_sum, cubeMean_eq_sum_div_pow]
  simp only [boolCubePMF, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [show Fintype.card (Fin n → Bool) = 2 ^ n by simp]
  rw [← Finset.mul_sum]
  simp [div_eq_mul_inv]
  ring

/-- McDiarmid's bounded-differences bridge on independent fair bits.  The
center is the genuine expectation, and the variance proxy is exactly
`(∑ i, c i²) / 4`; no conditional-MGF premise is assumed. -/
theorem boundedDifferences_hasSubgaussianMGF {n : ℕ}
    {f : (Fin n → Bool) → ℝ} {c : Fin n → ℝ≥0}
    (h : HasCoordinateOscillation f c) :
    HasSubgaussianMGF
      (fun x => f x - ∫ y, f y ∂(boolCubePMF n).toMeasure)
      (coordinateVariance c) (boolCubePMF n).toMeasure := by
  have hmean : ∫ y, f y ∂(boolCubePMF n).toMeasure = cubeMean f :=
    integral_boolCubePMF_eq_cubeMean f
  constructor
  · intro t
    have hi : IntegrableOn
        (fun x => Real.exp (t * (f x - ∫ y, f y ∂(boolCubePMF n).toMeasure)))
        Set.univ (boolCubePMF n).toMeasure :=
      IntegrableOn.of_finite Set.finite_univ
    change Integrable
      (fun x => Real.exp (t * (f x - ∫ y, f y ∂(boolCubePMF n).toMeasure)))
      ((boolCubePMF n).toMeasure.restrict Set.univ) at hi
    rw [Measure.restrict_univ] at hi
    exact hi
  · intro t
    rw [ProbabilityTheory.mgf, integral_boolCubePMF_eq_cubeMean, hmean]
    exact cubeMean_exp_center_le n f c h t

/-- The one-sided McDiarmid tail on the uniform Boolean cube. -/
theorem boundedDifferences_upperTail {n : ℕ}
    {f : (Fin n → Bool) → ℝ} {c : Fin n → ℝ≥0}
    (h : HasCoordinateOscillation f c) {t : ℝ} (ht : 0 ≤ t) :
    (boolCubePMF n).toMeasure.real
        {x | t ≤ f x - ∫ y, f y ∂(boolCubePMF n).toMeasure} ≤
      Real.exp (-t ^ 2 / (2 * coordinateVariance c)) :=
  (boundedDifferences_hasSubgaussianMGF h).measure_ge_le ht

/-- The two-sided McDiarmid tail on the uniform Boolean cube. -/
theorem boundedDifferences_twoSidedTail {n : ℕ}
    {f : (Fin n → Bool) → ℝ} {c : Fin n → ℝ≥0}
    (h : HasCoordinateOscillation f c) {t : ℝ} (ht : 0 ≤ t) :
    (boolCubePMF n).toMeasure.real
        {x | t ≤ |f x - ∫ y, f y ∂(boolCubePMF n).toMeasure|} ≤
      2 * Real.exp (-t ^ 2 / (2 * coordinateVariance c)) :=
  subgaussian_two_sided (boundedDifferences_hasSubgaussianMGF h) ht

end Erdos625
