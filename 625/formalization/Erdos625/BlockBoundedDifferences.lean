import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Erdos625.ProbabilityTools

/-!
# Bounded differences for finite uniformly distributed blocks

This module proves the finite-product bounded-differences inequality for a
dependent family of nonempty finite block spaces.  The proof is an explicit
induction over the blocks.  At each step, mathlib's Hoeffding lemma is applied
to the uniformly distributed head-block conditional means.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory
open ProbabilityTheory

namespace Erdos625

universe u

/-! ## Uniform finite means -/

/-- The normalized sum of a real-valued function on a nonempty finite type. -/
noncomputable def finiteMean {A : Type u} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

theorem finiteMean_congr {A : Type u} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a = g a) : finiteMean f = finiteMean g := by
  unfold finiteMean
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ h a

@[simp]
theorem finiteMean_const {A : Type u} [Fintype A] [Nonempty A] (r : ℝ) :
    finiteMean (fun _ : A ↦ r) = r := by
  unfold finiteMean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem finiteMean_add {A : Type u} [Fintype A] (f g : A → ℝ) :
    finiteMean (fun a ↦ f a + g a) = finiteMean f + finiteMean g := by
  unfold finiteMean
  rw [Finset.sum_add_distrib]
  ring

theorem finiteMean_sub {A : Type u} [Fintype A] (f g : A → ℝ) :
    finiteMean (fun a ↦ f a - g a) = finiteMean f - finiteMean g := by
  unfold finiteMean
  rw [Finset.sum_sub_distrib]
  ring

theorem finiteMean_const_mul {A : Type u} [Fintype A] (r : ℝ) (f : A → ℝ) :
    finiteMean (fun a ↦ r * f a) = r * finiteMean f := by
  unfold finiteMean
  rw [← Finset.mul_sum]
  ring

theorem finiteMean_mono {A : Type u} [Fintype A] [Nonempty A]
    {f g : A → ℝ} (h : ∀ a, f a ≤ g a) : finiteMean f ≤ finiteMean g := by
  unfold finiteMean
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun a _ ↦ h a
  · exact_mod_cast (Nat.zero_le (Fintype.card A))

/-- The uniform PMF on a nonempty finite type. -/
noncomputable def finiteUniformPMF (A : Type u) [Fintype A] [Nonempty A] : PMF A :=
  PMF.uniformOfFintype A

/-- The uniform PMF viewed as a measure on the canonical discrete
measurable space. -/
noncomputable def finiteUniformMeasure (A : Type u) [Fintype A] [Nonempty A] :
    @MeasureTheory.Measure A ⊤ :=
  @PMF.toMeasure A ⊤ (finiteUniformPMF A)

/-- Integration against the uniform PMF is exactly normalized finite
averaging. -/
theorem integral_finiteUniformPMF_eq_finiteMean
    {A : Type u} [Fintype A] [Nonempty A] (f : A → ℝ) :
    @MeasureTheory.integral A ℝ _ _ ⊤ (finiteUniformMeasure A) f = finiteMean f := by
  letI : MeasurableSpace A := ⊤
  unfold finiteUniformMeasure
  rw [PMF.integral_eq_sum]
  simp only [finiteUniformPMF, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, finiteMean]
  rw [← Finset.mul_sum]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-! ## Dependent finite products -/

/-- Uniform averaging on a dependent finite product. -/
noncomputable def blockMean {n : ℕ} (Omega : Fin n → Type u)
    [∀ i, Fintype (Omega i)] (f : (∀ i, Omega i) → ℝ) : ℝ :=
  finiteMean f

/-- Uniform PMF on a dependent finite product. -/
noncomputable def blockUniformPMF {n : ℕ} (Omega : Fin n → Type u)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)] : PMF (∀ i, Omega i) :=
  finiteUniformPMF (∀ i, Omega i)

/-- The product-uniform PMF as a measure on the canonical discrete product
space. -/
noncomputable def blockUniformMeasure {n : ℕ} (Omega : Fin n → Type u)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)] :
    @MeasureTheory.Measure (∀ i, Omega i) ⊤ :=
  @PMF.toMeasure (∀ i, Omega i) ⊤ (blockUniformPMF Omega)

@[simp]
theorem blockMean_zero (Omega : Fin 0 → Type u) [∀ i, Fintype (Omega i)]
    (f : (∀ i, Omega i) → ℝ) :
    blockMean Omega f = f (fun i ↦ Fin.elim0 i) := by
  unfold blockMean finiteMean
  rw [show Fintype.card (∀ i, Omega i) = 1 by simp, Nat.cast_one, div_one]
  calc
    ∑ x, f x = f (fun i ↦ Fin.elim0 i) := by
      convert Fintype.sum_unique f using 1
      exact congrArg f (Subsingleton.elim _ _)

/-- Decomposition of the product mean into the head-block mean of the tail
means. -/
theorem blockMean_succ {n : ℕ} (Omega : Fin (n + 1) → Type u)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    (f : (∀ i, Omega i) → ℝ) :
    blockMean Omega f =
      finiteMean (fun a : Omega 0 ↦
        blockMean (fun i : Fin n ↦ Omega i.succ) (fun x ↦ f (Fin.cons a x))) := by
  unfold blockMean finiteMean
  have hsum :
      (∑ x : ∀ i, Omega i, f x) =
        ∑ a : Omega 0, ∑ x : ∀ i : Fin n, Omega i.succ, f (Fin.cons a x) := by
    rw [← (Fin.consEquiv Omega).sum_comp f, Fintype.sum_prod_type]
    simp [Fin.consEquiv]
  have hcard : Fintype.card (∀ i, Omega i) =
      Fintype.card (Omega 0) * Fintype.card (∀ i : Fin n, Omega i.succ) := by
    calc
      Fintype.card (∀ i, Omega i) =
          Fintype.card (Omega 0 × (∀ i : Fin n, Omega i.succ)) :=
        Fintype.card_congr (Fin.consEquiv Omega).symm
      _ = _ := Fintype.card_prod _ _
  rw [hsum, hcard]
  have hHead : (Fintype.card (Omega 0) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hTail : (Fintype.card (∀ i : Fin n, Omega i.succ) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  push_cast
  rw [← Finset.sum_div]
  field_simp [hHead, hTail]

/-- Product-space expectation agrees with the normalized product mean. -/
theorem integral_blockUniformPMF_eq_blockMean {n : ℕ}
    (Omega : Fin n → Type u) [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)] (f : (∀ i, Omega i) → ℝ) :
    @MeasureTheory.integral (∀ i, Omega i) ℝ _ _ ⊤
        (blockUniformMeasure Omega) f = blockMean Omega f := by
  exact integral_finiteUniformPMF_eq_finiteMean f

/-- Coordinatewise oscillation for dependent blocks. -/
def HasBlockOscillation {n : ℕ} {Omega : Fin n → Type u}
    (f : (∀ i, Omega i) → ℝ) (c : Fin n → ℝ≥0) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ (c i : ℝ)

namespace HasBlockOscillation

theorem tail {n : ℕ} {Omega : Fin (n + 1) → Type u}
    {f : (∀ i, Omega i) → ℝ} {c : Fin (n + 1) → ℝ≥0}
    (h : HasBlockOscillation f c) (a : Omega 0) :
    HasBlockOscillation (fun x ↦ f (Fin.cons a x)) (fun i ↦ c i.succ) := by
  intro i x y hxy
  apply h i.succ (Fin.cons a x) (Fin.cons a y)
  intro j hj
  cases j using Fin.cases with
  | zero => simp
  | succ k =>
      simp only [Fin.cons_succ]
      apply hxy k
      exact fun hki ↦ hj (congrArg Fin.succ hki)

theorem head {n : ℕ} {Omega : Fin (n + 1) → Type u}
    {f : (∀ i, Omega i) → ℝ} {c : Fin (n + 1) → ℝ≥0}
    (h : HasBlockOscillation f c) (a b : Omega 0)
    (x : ∀ i : Fin n, Omega i.succ) :
    |f (Fin.cons a x) - f (Fin.cons b x)| ≤ (c 0 : ℝ) := by
  apply h 0 (Fin.cons a x) (Fin.cons b x)
  intro j hj
  cases j using Fin.cases with
  | zero => exact (hj rfl).elim
  | succ k => simp

end HasBlockOscillation

/-! ## Variance proxy and the finite head-block estimate -/

/-- The bounded-differences variance proxy `∑ i, c i² / 4`. -/
noncomputable def blockVariance {n : ℕ} (c : Fin n → ℝ≥0) : ℝ≥0 :=
  ∑ i, (c i / 2) ^ 2

private theorem blockVariance_succ {n : ℕ} (c : Fin (n + 1) → ℝ≥0) :
    blockVariance c = (c 0 / 2) ^ 2 + blockVariance (fun i ↦ c i.succ) := by
  simp [blockVariance, Fin.sum_univ_succ]

theorem blockVariance_eq_sum_sq_div_four {n : ℕ} (c : Fin n → ℝ≥0) :
    (blockVariance c : ℝ) = ∑ i, (c i : ℝ) ^ 2 / 4 := by
  rw [blockVariance]
  push_cast
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Hoeffding's lemma specialized to a uniformly distributed finite type,
with the interval length obtained from a pairwise oscillation bound. -/
private theorem finiteMean_exp_center_le_of_pairwise
    {A : Type u} [Fintype A] [Nonempty A]
    (m : A → ℝ) (c : ℝ≥0)
    (hpair : ∀ a b, |m a - m b| ≤ (c : ℝ)) (t : ℝ) :
    finiteMean (fun a ↦ Real.exp (t * (m a - finiteMean m))) ≤
      Real.exp (((c : ℝ) / 2) ^ 2 * t ^ 2 / 2) := by
  classical
  let values : Finset ℝ := Finset.univ.image m
  have hvalues : values.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty A)
    exact ⟨m a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  let lo : ℝ := values.min' hvalues
  have hloMem : lo ∈ values := Finset.min'_mem values hvalues
  obtain ⟨a₀, _ha₀, ha₀⟩ := Finset.mem_image.mp hloMem
  have hbounds (a : A) : m a ∈ Set.Icc lo (lo + (c : ℝ)) := by
    constructor
    · exact Finset.min'_le values (m a)
        (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    · have hdiff : m a - m a₀ ≤ (c : ℝ) :=
        (le_abs_self (m a - m a₀)).trans (hpair a a₀)
      rw [ha₀] at hdiff
      linarith
  letI : MeasurableSpace A := ⊤
  let mu : Measure A := finiteUniformMeasure A
  letI : IsProbabilityMeasure mu := by
    dsimp only [mu, finiteUniformMeasure]
    infer_instance
  have hm : AEMeasurable m mu := (measurable_of_finite m).aemeasurable
  have hb : ∀ᵐ a ∂mu, m a ∈ Set.Icc lo (lo + (c : ℝ)) :=
    Filter.Eventually.of_forall hbounds
  have hsub := hasSubgaussianMGF_of_mem_Icc hm hb
  have hmgf := hsub.mgf_le t
  dsimp only [mu] at hmgf
  rw [ProbabilityTheory.mgf, integral_finiteUniformPMF_eq_finiteMean,
    integral_finiteUniformPMF_eq_finiteMean] at hmgf
  simpa using hmgf

private theorem abs_blockMean_head_sub_le {n : ℕ}
    {Omega : Fin (n + 1) → Type u} [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)]
    {f : (∀ i, Omega i) → ℝ} {c : Fin (n + 1) → ℝ≥0}
    (h : HasBlockOscillation f c) (a b : Omega 0) :
    |blockMean (fun i : Fin n ↦ Omega i.succ) (fun x ↦ f (Fin.cons a x)) -
        blockMean (fun i : Fin n ↦ Omega i.succ) (fun x ↦ f (Fin.cons b x))| ≤
      (c 0 : ℝ) := by
  let Omega' : Fin n → Type u := fun i ↦ Omega i.succ
  let fₐ : (∀ i, Omega' i) → ℝ := fun x ↦ f (Fin.cons a x)
  let fB : (∀ i, Omega' i) → ℝ := fun x ↦ f (Fin.cons b x)
  change |finiteMean fₐ - finiteMean fB| ≤ (c 0 : ℝ)
  rw [← finiteMean_sub]
  apply abs_le.mpr
  constructor
  · calc
      -(c 0 : ℝ) = finiteMean (fun _ : ∀ i, Omega' i ↦ -(c 0 : ℝ)) :=
        (finiteMean_const _).symm
      _ ≤ finiteMean (fun x ↦ fₐ x - fB x) := by
        apply finiteMean_mono
        intro x
        exact neg_le_of_abs_le (h.head a b x)
  · calc
      finiteMean (fun x ↦ fₐ x - fB x) ≤
          finiteMean (fun _ : ∀ i, Omega' i ↦ (c 0 : ℝ)) := by
        apply finiteMean_mono
        intro x
        exact (le_abs_self _).trans (h.head a b x)
      _ = (c 0 : ℝ) := finiteMean_const _

/-! ## Product bounded differences -/

/-- Finite bounded differences in MGF form for arbitrary nonempty finite
uniform blocks. -/
theorem blockMean_exp_center_le (n : ℕ) :
    ∀ (Omega : Fin n → Type u) [∀ i, Fintype (Omega i)]
      [∀ i, Nonempty (Omega i)]
      (f : (∀ i, Omega i) → ℝ) (c : Fin n → ℝ≥0),
      HasBlockOscillation f c → ∀ t : ℝ,
        blockMean Omega (fun x ↦ Real.exp (t * (f x - blockMean Omega f))) ≤
          Real.exp ((blockVariance c : ℝ) * t ^ 2 / 2) := by
  induction n with
  | zero =>
      intro Omega instF instN f c h t
      simp only [blockMean_zero]
      simp [blockVariance]
  | succ n ih =>
      intro Omega instF instN f c h t
      let Omega' : Fin n → Type u := fun i ↦ Omega i.succ
      let c' : Fin n → ℝ≥0 := fun i ↦ c i.succ
      let fₐ : Omega 0 → (∀ i, Omega' i) → ℝ :=
        fun a x ↦ f (Fin.cons a x)
      let m : Omega 0 → ℝ := fun a ↦ blockMean Omega' (fₐ a)
      let R : ℝ := Real.exp ((blockVariance c' : ℝ) * t ^ 2 / 2)
      have hfmean : blockMean Omega f = finiteMean m := by
        simpa only [m, fₐ, Omega'] using blockMean_succ Omega f
      have htail (a : Omega 0) :
          blockMean Omega' (fun x ↦ Real.exp (t * (fₐ a x - m a))) ≤ R := by
        simpa only [m, R] using ih Omega' (fₐ a) c' (h.tail a) t
      have hbranch (a : Omega 0) :
          blockMean Omega'
              (fun x ↦ Real.exp (t * (fₐ a x - finiteMean m))) ≤
            R * Real.exp (t * (m a - finiteMean m)) := by
        calc
          blockMean Omega'
              (fun x ↦ Real.exp (t * (fₐ a x - finiteMean m))) =
            blockMean Omega' (fun x ↦
              Real.exp (t * (m a - finiteMean m)) *
                Real.exp (t * (fₐ a x - m a))) := by
              unfold blockMean
              apply finiteMean_congr
              intro x
              rw [← Real.exp_add]
              congr 1
              ring
          _ = Real.exp (t * (m a - finiteMean m)) *
              blockMean Omega' (fun x ↦ Real.exp (t * (fₐ a x - m a))) := by
                exact finiteMean_const_mul _ _
          _ ≤ Real.exp (t * (m a - finiteMean m)) * R := by
                apply mul_le_mul_of_nonneg_left (htail a) (Real.exp_nonneg _)
          _ = R * Real.exp (t * (m a - finiteMean m)) := by ring
      have hmPair : ∀ a b, |m a - m b| ≤ (c 0 : ℝ) := by
        intro a b
        simpa only [m, fₐ, Omega'] using abs_blockMean_head_sub_le h a b
      have hhead := finiteMean_exp_center_le_of_pairwise m (c 0) hmPair t
      rw [blockMean_succ, hfmean]
      change finiteMean (fun a ↦
          blockMean Omega' (fun x ↦ Real.exp (t * (fₐ a x - finiteMean m)))) ≤ _
      calc
        finiteMean (fun a ↦
            blockMean Omega' (fun x ↦ Real.exp (t * (fₐ a x - finiteMean m)))) ≤
          finiteMean (fun a ↦ R * Real.exp (t * (m a - finiteMean m))) := by
            exact finiteMean_mono hbranch
        _ = R * finiteMean (fun a ↦ Real.exp (t * (m a - finiteMean m))) :=
          finiteMean_const_mul _ _
        _ ≤ R * Real.exp (((c 0 : ℝ) / 2) ^ 2 * t ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left hhead (Real.exp_nonneg _)
        _ = Real.exp ((blockVariance c : ℝ) * t ^ 2 / 2) := by
          rw [blockVariance_succ]
          push_cast
          rw [← Real.exp_add]
          congr 1
          dsimp only [R, c']
          ring

/-! ## Measure-theoretic bridge and tails -/

/-- Expectation under the canonical discrete uniform product measure. -/
noncomputable def blockExpectation {n : ℕ} (Omega : Fin n → Type u)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    (f : (∀ i, Omega i) → ℝ) : ℝ :=
  @MeasureTheory.integral (∀ i, Omega i) ℝ _ _ ⊤ (blockUniformMeasure Omega) f

theorem blockExpectation_eq_blockMean {n : ℕ} (Omega : Fin n → Type u)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    (f : (∀ i, Omega i) → ℝ) :
    blockExpectation Omega f = blockMean Omega f := by
  exact integral_blockUniformPMF_eq_blockMean Omega f

/-- Bounded differences on arbitrary finite uniform blocks, with no MGF
premise.  The centering is the genuine expectation under the product-uniform
PMF. -/
theorem blockBoundedDifferences_hasSubgaussianMGF {n : ℕ}
    {Omega : Fin n → Type u} [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)]
    {f : (∀ i, Omega i) → ℝ} {c : Fin n → ℝ≥0}
    (h : HasBlockOscillation f c) :
    @HasSubgaussianMGF (∀ i, Omega i) ⊤
      (fun x ↦ f x - blockExpectation Omega f)
      (blockVariance c) (blockUniformMeasure Omega) := by
  letI : MeasurableSpace (∀ i, Omega i) := ⊤
  letI : IsProbabilityMeasure (blockUniformMeasure Omega) := by
    dsimp only [blockUniformMeasure]
    infer_instance
  have hmean : blockExpectation Omega f = blockMean Omega f :=
    blockExpectation_eq_blockMean Omega f
  constructor
  · intro t
    have hi : IntegrableOn
        (fun x ↦ Real.exp (t * (f x - blockExpectation Omega f)))
        Set.univ (blockUniformMeasure Omega) :=
      IntegrableOn.of_finite Set.finite_univ
    change Integrable
      (fun x ↦ Real.exp (t * (f x - blockExpectation Omega f)))
      ((blockUniformMeasure Omega).restrict Set.univ) at hi
    rw [Measure.restrict_univ] at hi
    exact hi
  · intro t
    rw [ProbabilityTheory.mgf, integral_blockUniformPMF_eq_blockMean, hmean]
    exact blockMean_exp_center_le n Omega f c h t

/-- One-sided bounded-differences tail for finite uniform blocks. -/
theorem blockBoundedDifferences_upperTail {n : ℕ}
    {Omega : Fin n → Type u} [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)]
    {f : (∀ i, Omega i) → ℝ} {c : Fin n → ℝ≥0}
    (h : HasBlockOscillation f c) {t : ℝ} (ht : 0 ≤ t) :
    (blockUniformMeasure Omega).real
        {x | t ≤ f x - blockExpectation Omega f} ≤
      Real.exp (-t ^ 2 / (2 * blockVariance c)) :=
  by
    letI : MeasurableSpace (∀ i, Omega i) := ⊤
    exact (blockBoundedDifferences_hasSubgaussianMGF h).measure_ge_le ht

/-- Two-sided bounded-differences tail for finite uniform blocks. -/
theorem blockBoundedDifferences_twoSidedTail {n : ℕ}
    {Omega : Fin n → Type u} [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)]
    {f : (∀ i, Omega i) → ℝ} {c : Fin n → ℝ≥0}
    (h : HasBlockOscillation f c) {t : ℝ} (ht : 0 ≤ t) :
    (blockUniformMeasure Omega).real
        {x | t ≤ |f x - blockExpectation Omega f|} ≤
      2 * Real.exp (-t ^ 2 / (2 * blockVariance c)) :=
  by
    letI : MeasurableSpace (∀ i, Omega i) := ⊤
    exact subgaussian_two_sided (blockBoundedDifferences_hasSubgaussianMGF h) ht

@[simp]
theorem blockVariance_zero {n : ℕ} :
    blockVariance (fun _ : Fin n ↦ (0 : ℝ≥0)) = 0 := by
  simp [blockVariance]

/-- On a product of singleton blocks, every function has zero coordinate
oscillation. -/
theorem hasBlockOscillation_zero_of_subsingleton {n : ℕ}
    {Omega : Fin n → Type u} [∀ i, Subsingleton (Omega i)]
    (f : (∀ i, Omega i) → ℝ) :
    HasBlockOscillation f (fun _ ↦ 0) := by
  intro i x y _hxy
  have hxy : x = y := by
    funext j
    exact Subsingleton.elim _ _
  simp [hxy]

/-- Explicit zero-variance specialization whenever every coordinate
oscillation bound is zero. -/
theorem blockBoundedDifferences_hasSubgaussianMGF_zero {n : ℕ}
    {Omega : Fin n → Type u} [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)]
    {f : (∀ i, Omega i) → ℝ}
    (h : HasBlockOscillation f (fun _ ↦ 0)) :
    @HasSubgaussianMGF (∀ i, Omega i) ⊤
      (fun x ↦ f x - blockExpectation Omega f) 0 (blockUniformMeasure Omega) := by
  simpa using blockBoundedDifferences_hasSubgaussianMGF h

/-- Explicit zero-variance specialization for products of singleton blocks. -/
theorem blockBoundedDifferences_hasSubgaussianMGF_of_subsingleton {n : ℕ}
    {Omega : Fin n → Type u} [∀ i, Fintype (Omega i)]
    [∀ i, Nonempty (Omega i)] [∀ i, Subsingleton (Omega i)]
    (f : (∀ i, Omega i) → ℝ) :
    @HasSubgaussianMGF (∀ i, Omega i) ⊤
      (fun x ↦ f x - blockExpectation Omega f) 0 (blockUniformMeasure Omega) := by
  exact blockBoundedDifferences_hasSubgaussianMGF_zero
    (hasBlockOscillation_zero_of_subsingleton f)

end Erdos625
