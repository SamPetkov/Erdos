import Erdos625.ProfileAsymptoticTools
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Uniform convergence tools for growing-support profiles

This module records three analytic interfaces used to upgrade fixed-coordinate
profile limits to convergence uniform in a bounded tilt parameter.  The first
uses the multiplicative separation of a fixed-coordinate exponential.  The
second is a uniform dominated-convergence theorem for real series.  The third
passes uniform numerator and denominator convergence through a quotient when
the denominators stay uniformly positive.

These statements are generic.  They do not provide a profile-specific
majorant, a bounded optimizer tilt, or the fixed-coordinate convergence needed
to invoke them.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

/-- Convergence of one scalar residual gives uniform convergence of its
exponentially tilted fixed coordinate on every bounded tilt interval. -/
theorem tendstoUniformlyOn_exp_affine_add_of_tendsto
    {r : ℕ → ℝ} {R M : ℝ}
    (hr : Tendsto r atTop (𝓝 R)) (d : ℕ) :
    TendstoUniformlyOn
      (fun n lambda ↦ Real.exp (lambda * (d : ℝ) + r n))
      (fun lambda ↦ Real.exp (lambda * (d : ℝ) + R))
      atTop (Icc (-M) M) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let C : ℝ := Real.exp (M * (d : ℝ))
  have hC : 0 < C := Real.exp_pos _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hr.rexp
    (eps / C) (div_pos heps hC)
  filter_upwards [eventually_ge_atTop N] with n hn
  intro lambda hlambda
  have hscalar := hN n hn
  have hscalar' :
      |Real.exp R - Real.exp (r n)| < eps / C := by
    simpa only [Real.dist_eq, abs_sub_comm] using hscalar
  have hlambdaC : Real.exp (lambda * (d : ℝ)) ≤ C := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hlambda.2 (Nat.cast_nonneg d)
  rw [Real.dist_eq, Real.exp_add, Real.exp_add, ← mul_sub, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (lambda * (d : ℝ)) *
          |Real.exp R - Real.exp (r n)| ≤
        C * |Real.exp R - Real.exp (r n)| :=
      mul_le_mul_of_nonneg_right hlambdaC (abs_nonneg _)
    _ < C * (eps / C) := mul_lt_mul_of_pos_left hscalar' hC
    _ = eps := by field_simp

/-- Uniform coordinate convergence passes through an infinite real series
under one summable majorant, uniformly on the same parameter set. -/
theorem tendstoUniformlyOn_tsum_of_uniform_coordinate_limits
    {X : Type*} {K : Set X}
    {f : ℕ → ℕ → X → ℝ} {F : ℕ → X → ℝ}
    {g : ℕ → ℝ}
    (hg : Summable g)
    (hg0 : ∀ d, 0 ≤ g d)
    (hdom : ∀ n d x, x ∈ K → ‖f n d x‖ ≤ g d)
    (hdomF : ∀ d x, x ∈ K → ‖F d x‖ ≤ g d)
    (hcoord : ∀ d,
      TendstoUniformlyOn (fun n x ↦ f n d x) (F d) atTop K) :
    TendstoUniformlyOn
      (fun n x ↦ ∑' d : ℕ, f n d x)
      (fun x ↦ ∑' d : ℕ, F d x)
      atTop K := by
  have _hg0 : ∀ d, 0 ≤ g d := hg0
  have hfinite : ∀ s : Finset ℕ,
      TendstoUniformlyOn
        (fun n x ↦ ∑ d ∈ s, f n d x)
        (fun x ↦ ∑ d ∈ s, F d x)
        atTop K := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa using
          (tendsto_const_nhds.tendstoUniformlyOn_const K :
            TendstoUniformlyOn
              (fun _ : ℕ ↦ fun _ : X ↦ (0 : ℝ))
              (fun _ : X ↦ (0 : ℝ)) atTop K)
    | @insert d s hd ih =>
        simp only [Finset.sum_insert hd]
        change TendstoUniformlyOn
          ((fun n x ↦ f n d x) + (fun n x ↦ ∑ e ∈ s, f n e x))
          (F d + (fun x ↦ ∑ e ∈ s, F e x)) atTop K
        exact (hcoord d).add ih
  have hfPartial :
      TendstoUniformlyOn
        (fun N (p : ℕ × X) ↦
          ∑ d ∈ Finset.range N, f p.1 d p.2)
        (fun p : ℕ × X ↦ ∑' d : ℕ, f p.1 d p.2)
        atTop (Set.univ ×ˢ K) := by
    exact tendstoUniformlyOn_tsum_nat hg
      (fun d p hp ↦ hdom p.1 d p.2 hp.2)
  have hFPartial :
      TendstoUniformlyOn
        (fun N x ↦ ∑ d ∈ Finset.range N, F d x)
        (fun x ↦ ∑' d : ℕ, F d x)
        atTop K := by
    exact tendstoUniformlyOn_tsum_nat hg hdomF
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  have heps3 : 0 < eps / 3 := by positivity
  have hfEventually :=
    (Metric.tendstoUniformlyOn_iff.mp hfPartial) (eps / 3) heps3
  have hFEventually :=
    (Metric.tendstoUniformlyOn_iff.mp hFPartial) (eps / 3) heps3
  rcases (hfEventually.and hFEventually).exists with ⟨N, hfN, hFN⟩
  have hheadEventually :=
    (Metric.tendstoUniformlyOn_iff.mp (hfinite (Finset.range N)))
      (eps / 3) heps3
  filter_upwards [hheadEventually] with n hn
  intro x hx
  have hleft := hFN x hx
  have hmiddle := hn x hx
  have hright := hfN (n, x) ⟨Set.mem_univ n, hx⟩
  calc
    dist (∑' d : ℕ, F d x) (∑' d : ℕ, f n d x) ≤
        dist (∑' d : ℕ, F d x)
            (∑ d ∈ Finset.range N, F d x) +
          dist (∑ d ∈ Finset.range N, F d x)
            (∑' d : ℕ, f n d x) :=
      dist_triangle _ _ _
    _ ≤ dist (∑' d : ℕ, F d x)
            (∑ d ∈ Finset.range N, F d x) +
          (dist (∑ d ∈ Finset.range N, F d x)
              (∑ d ∈ Finset.range N, f n d x) +
            dist (∑ d ∈ Finset.range N, f n d x)
              (∑' d : ℕ, f n d x)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < eps := by rw [dist_comm] at hright; linarith

/-- Uniform convergence is stable under normalized quotients when both
denominators have a common positive lower bound and the limiting numerator is
uniformly bounded. -/
theorem tendstoUniformlyOn_div_of_denominator_ge
    {X : Type*} {K : Set X}
    {A B : ℕ → X → ℝ} {a b : X → ℝ}
    {z M : ℝ}
    (hz : 0 < z) (hM : 0 ≤ M)
    (hA : TendstoUniformlyOn A a atTop K)
    (hB : TendstoUniformlyOn B b atTop K)
    (hden : ∀ n x, x ∈ K → z ≤ B n x)
    (hdenlim : ∀ x, x ∈ K → z ≤ b x)
    (ha : ∀ x, x ∈ K → |a x| ≤ M) :
    TendstoUniformlyOn
      (fun n x ↦ A n x / B n x)
      (fun x ↦ a x / b x)
      atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro eps heps
  let epsA : ℝ := eps * z / 2
  let epsB : ℝ := eps * z ^ 2 / (2 * (M + 1))
  have hepsA : 0 < epsA := by
    dsimp [epsA]
    positivity
  have hepsB : 0 < epsB := by
    dsimp [epsB]
    positivity
  have hAE := (Metric.tendstoUniformlyOn_iff.mp hA) epsA hepsA
  have hBE := (Metric.tendstoUniformlyOn_iff.mp hB) epsB hepsB
  filter_upwards [hAE, hBE] with n hAn hBn
  intro x hx
  have hAerr : |A n x - a x| ≤ epsA := by
    have := hAn x hx
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hBerr : |B n x - b x| ≤ epsB := by
    have := hBn x hx
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hquot := abs_div_sub_div_le_of_denominator_ge
    hz hepsA.le hepsB.le hM
    (hden n x hx) (hdenlim x hx) hAerr hBerr (ha x hx)
  rw [Real.dist_eq, abs_sub_comm]
  apply lt_of_le_of_lt hquot
  dsimp [epsA, epsB]
  have hMone : 0 < M + 1 := by linarith
  calc
    eps * z / 2 / z + M * (eps * z ^ 2 / (2 * (M + 1))) / z ^ 2 =
        eps / 2 + eps / 2 * (M / (M + 1)) := by
      field_simp
    _ < eps := by
      have hratio : M / (M + 1) < 1 := by
        exact (div_lt_one hMone).mpr (by linarith)
      nlinarith [mul_lt_mul_of_pos_left hratio (by positivity : 0 < eps / 2)]

end

end Erdos625
