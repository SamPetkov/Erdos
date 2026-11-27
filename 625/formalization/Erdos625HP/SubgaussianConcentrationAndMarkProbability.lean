import Erdos625.HPRouteMarkBound
import Erdos625HP.UnconditionalSplittingAndQuasiExpTail

/-!
# v8 Sub-Gaussian gap concentration, conditional Popoviciu variance, and Section 7 mark measures

This module formalizes the v8 manuscript upgrades across Sections 1, 7, 8, and 9 using only
the standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`):

1. **Section 1 (`eq:t1-3`) — Conditional Popoviciu variance, Hoeffding MGF, and two-sided
   bounded-differences tails for general oscillation bounds:**
   - `blockMean_sq_center_le`: for any coordinatewise oscillation vector `c : Fin n → ℝ≥0`,
     `Var(f) ≤ ∑ i, (c i)² / 4 = blockVariance c` under the uniform product law.
   - `blockUniform_variance_mgf_and_tails_of_const_oscillation`: for uniform oscillation `c > 0`
     across `r ≥ 1` independent blocks, proves `Var(Y) ≤ c² r / 4`,
     `E[exp(λ(Y - E[Y]))] ≤ exp(c² r λ² / 8)`, and one- and two-sided `exp(-2 t² / (c² r))`
     concentration bounds.
   - `randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation`: transports the
     variance, MGF, and tail bounds to `G(n, 1/2)` across the `n - 1` active vertex-star blocks
     (`v = 2, ..., n`), yielding `Var(ζ(G_n)) ≤ (n - 1) / 4` and `Var(χ(G_n)) ≤ (n - 1) / 4`.

2. **Section 8 (Corollary 8.1) — Non-asymptotic oscillation-`2` bounds for `Δ = χ - ζ` and `Y_n`:**
   - `chromaticSubCochromatic_hasVertexDeletionOscillation`: deleting a vertex changes
     `Δ(G) = χ(G) - ζ(G)` by at most `2` (`Δ(G) ∈ [Δ(G - v) - 1, Δ(G - v) + 1]`).
   - `variance_chromaticSubCochromatic_le` (`Var(χ(G_n) - ζ(G_n)) ≤ n - 1`),
     `variance_normalizedGap_le` (`Var(Y_n) ≤ (log₂ n)⁶ / n`),
     `mgf_chromaticSubCochromatic_center_le` (`E[exp(λ(Δ - E[Δ]))] ≤ exp((n - 1) λ² / 2)`),
     `mgf_normalizedGap_bounds` (`exp(λ E[Y_n]) ≤ E[exp(λ Y_n)] ≤ exp(λ E[Y_n]) exp(λ² (log₂ n)⁶ / (2 n))`),
     `randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le` (`≤ 2 exp(-t² / (2(n - 1)))`), and
     `randomGraph_abs_normalizedGap_sub_mean_ge_le` (`≤ 2 exp(-u² n / (2 (log₂ n)⁶))`).

3. **Section 7 (`eq:hp-marks` & Lemma 7.2) — `G(n, 1/2)` mark-measure equations and scrambled overlaps:**
   - `randomGraphMeasure_partitionCocoloringEvent_eq_two_pow_mul`: when every part of `P` has size
     `≥ 2`, `P(A_P^co) = 2 ^ |P| * P(A_P)` (`ENNReal` and `.real` forms).
   - `randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_common` and
     `randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_inter`: connects
     `CompatiblePairSignAssignments` to `G(n, 1/2)` via simultaneous clique/independent-set edge
     flips, proving `P(A_P^co ∩ A_Q^co) ≤ 2 ^ (|P| + |Q| - |P ∩ Q|) * P(A_P ∩ A_Q)` whenever every
     shared part in `P ∩ Q` has size `≥ 2`.
   - `scrambledPart_heavyOverlap_card_and_vertex_sum_le`: in any partition of a size-`u` scrambled
     class (`u ≤ α`, `α - u ≤ M + 1`) into `z` nonempty overlap blocks with
     `u ≤ z + 2(α - u) + 1`, every block has size `≤ 2(α - u) + 2 ≤ 2M + 4` and the total number
     of vertices in blocks of size `≥ 2` is `≤ 2(u - z) ≤ 4M + 6`.

4. **Section 9 — Summability and sub-Gaussian Main Theorem + Phase Refinement assemblies:**
   - `summable_subgaussianGapTail` (`∑ exp(-c n / (log₂ n)⁶) < ∞` for every `c > 0`) and
     `summable_phaseRefinementSubgaussianTail` (`∑ exp(-n (log log n)² / (2 (log n)⁸)) < ∞`).
   - `mainTheorem_subgaussian_tail_ae_lp_expectation_and_mgf`: upgrades the single-`n` deviation
     tail from `O_ε(exp(-2 n / (log n)^10))` by four powers of `log n` to the explicit bound
     `P(|Y_n - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))` eventually for every `ε > 0` and
     `ϑ ∈ (0, 1)`, alongside `Var(χ - ζ) ≤ n - 1`, non-asymptotic mean concentration, arbitrary-
     coupling a.s. convergence, `L^p` (`1 ≤ p < ∞`) convergence, and MGF convergence via the CGF
     squeeze.
   - `phaseRefinement_subgaussian_tail_expectation_and_ae`: upgrades the Phase Refinement exit
     probability to `P(W_n ∉ I_n) ≤ 2 exp(-n (log log n)² / (2 (log n)⁸))` eventually.
-/

namespace Erdos625HP

open Erdos625 Filter Asymptotics MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal

noncomputable section

set_option autoImplicit false

/-!
## 1. Conditional Popoviciu variance, Hoeffding MGF, and oscillation-`c` block concentration
-/

private theorem finiteMean_const {A : Type*} [Fintype A] [Nonempty A] (r : ℝ) :
    finiteMean (fun _ : A ↦ r) = r := by
  unfold finiteMean
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ r hcard]

private theorem finiteMean_sq_center_le_of_pairwise
    {A : Type*} [Fintype A] [Nonempty A]
    (m : A → ℝ) (c : ℝ≥0)
    (hpair : ∀ a b : A, |m a - m b| ≤ (c : ℝ)) :
    finiteMean (fun a ↦ (m a - finiteMean m) ^ 2) ≤ ((c : ℝ) / 2) ^ 2 := by
  classical
  let values : Finset ℝ := Finset.univ.image m
  have hvalues : values.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty A)
    exact ⟨m a, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩
  let lo : ℝ := values.min' hvalues
  let hi : ℝ := values.max' hvalues
  let mid : ℝ := (lo + hi) / 2
  obtain ⟨a₀, -, ha₀⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
  obtain ⟨a₁, -, ha₁⟩ := Finset.mem_image.mp (Finset.max'_mem values hvalues)
  have hwidth : hi - lo ≤ (c : ℝ) := by
    have hdiff : m a₁ - m a₀ ≤ (c : ℝ) :=
      (le_abs_self (m a₁ - m a₀)).trans (hpair a₁ a₀)
    dsimp [hi, lo]
    linarith
  have hpt (a : A) : (m a - mid) ^ 2 ≤ ((c : ℝ) / 2) ^ 2 := by
    have hmem : m a ∈ values := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have hlo : lo ≤ m a := Finset.min'_le values (m a) hmem
    have hhi : m a ≤ hi := Finset.le_max' values (m a) hmem
    have habs : |m a - mid| ≤ (c : ℝ) / 2 := by
      rw [abs_le]
      dsimp [mid]
      constructor <;> linarith
    have hc2 : 0 ≤ (c : ℝ) / 2 := by positivity
    nlinarith [abs_le.mp habs]
  let μ : ℝ := finiteMean m
  have hident : (fun a : A ↦ (m a - mid) ^ 2) =
      (fun a : A ↦ ((m a - μ) ^ 2 + 2 * (μ - mid) * (m a - μ)) + (μ - mid) ^ 2) := by
    funext a
    ring
  have hcenter_zero : finiteMean (fun a : A ↦ m a - μ) = 0 := by
    have hsub : finiteMean (fun a : A ↦ m a - μ) = finiteMean m - finiteMean (fun _ : A ↦ μ) :=
      finiteMean_sub m (fun _ ↦ μ)
    rw [hsub, finiteMean_const]
    dsimp [μ]
    ring
  have hbias :
      finiteMean (fun a : A ↦ (m a - mid) ^ 2) =
        finiteMean (fun a : A ↦ (m a - μ) ^ 2) + (μ - mid) ^ 2 := by
    rw [hident, finiteMean_add, finiteMean_add, finiteMean_const_mul,
      hcenter_zero, finiteMean_const]
    ring
  have hsq_nn : 0 ≤ (μ - mid) ^ 2 := sq_nonneg _
  have hmid_le : finiteMean (fun a : A ↦ (m a - mid) ^ 2) ≤ ((c : ℝ) / 2) ^ 2 := by
    calc
      finiteMean (fun a : A ↦ (m a - mid) ^ 2) ≤
          finiteMean (fun _ : A ↦ ((c : ℝ) / 2) ^ 2) := finiteMean_mono hpt
      _ = ((c : ℝ) / 2) ^ 2 := finiteMean_const _
  dsimp [μ] at hbias
  linarith

private theorem blockMean_const {n : ℕ} (Omega : Fin n → Type*)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)] (r : ℝ) :
    blockMean Omega (fun _ ↦ r) = r :=
  finiteMean_const r

private theorem blockMean_add {n : ℕ} (Omega : Fin n → Type*)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    (f g : (∀ i, Omega i) → ℝ) :
    blockMean Omega (fun x ↦ f x + g x) = blockMean Omega f + blockMean Omega g :=
  finiteMean_add f g

private theorem blockMean_sub {n : ℕ} (Omega : Fin n → Type*)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    (f g : (∀ i, Omega i) → ℝ) :
    blockMean Omega (fun x ↦ f x - g x) = blockMean Omega f - blockMean Omega g :=
  finiteMean_sub f g

private theorem blockMean_const_mul {n : ℕ} (Omega : Fin n → Type*)
    [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    (r : ℝ) (f : (∀ i, Omega i) → ℝ) :
    blockMean Omega (fun x ↦ r * f x) = r * blockMean Omega f :=
  finiteMean_const_mul r f

/-- **Conditional Popoviciu bounded-differences variance bound (Section 1, eq. `(1.2)`):**
for any coordinatewise oscillation vector `c : Fin n → ℝ≥0` on a finite uniform product space,
`E[(f - E[f])²] ≤ ∑ i, (c i)² / 4 = blockVariance c`. -/
theorem blockMean_sq_center_le {n : ℕ}
    {Omega : Fin n → Type*} [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    {f : (∀ i, Omega i) → ℝ} {c : Fin n → ℝ≥0}
    (hf : HasBlockOscillation f c) :
    blockMean Omega (fun x ↦ (f x - blockMean Omega f) ^ 2) ≤ (blockVariance c : ℝ) := by
  induction n with
  | zero =>
    have huniq : ∀ x y : ∀ i : Fin 0, Omega i, x = y := fun x y ↦ Subsingleton.elim x y
    obtain ⟨x₀⟩ := (inferInstance : Nonempty (∀ i : Fin 0, Omega i))
    have hconst : f = fun _ ↦ f x₀ := by
      funext x; exact congrArg f (huniq x x₀)
    have hmean : blockMean Omega f = f x₀ := by
      rw [hconst, blockMean_const]
    have hzero : (fun x : ∀ i : Fin 0, Omega i ↦ (f x - blockMean Omega f) ^ 2) = fun _ ↦ 0 := by
      funext x
      rw [hmean, congrArg f (huniq x x₀)]
      ring
    rw [hzero, blockMean_const]
    simp [blockVariance]
  | succ n ih =>
    let Omega' : Fin n → Type _ := fun i ↦ Omega i.succ
    let c' : Fin n → ℝ≥0 := fun i ↦ c i.succ
    let m : Omega 0 → ℝ := fun a ↦ blockMean Omega' (fun x ↦ f (Fin.cons a x))
    have hmean : blockMean Omega f = finiteMean m := blockMean_succ Omega f
    rw [hmean, blockMean_succ]
    have hdecomp (a : Omega 0) :
        blockMean Omega' (fun x ↦ (f (Fin.cons a x) - finiteMean m) ^ 2) =
          blockMean Omega' (fun x ↦ (f (Fin.cons a x) - m a) ^ 2) +
            (m a - finiteMean m) ^ 2 := by
      have hexp :
          (fun x : ∀ i, Omega' i ↦ (f (Fin.cons a x) - finiteMean m) ^ 2) =
            (fun x : ∀ i, Omega' i ↦
              ((f (Fin.cons a x) - m a) ^ 2 +
                2 * (m a - finiteMean m) * (f (Fin.cons a x) - m a)) +
                (m a - finiteMean m) ^ 2) := by
        funext x; ring
      have hsub0 : blockMean Omega' (fun x ↦ f (Fin.cons a x) - m a) = 0 := by
        rw [blockMean_sub, blockMean_const]
        dsimp [m]
        ring
      rw [hexp, blockMean_add, blockMean_add, blockMean_const_mul, hsub0, blockMean_const]
      ring
    have hstep (a : Omega 0) :
        blockMean Omega' (fun x ↦ (f (Fin.cons a x) - finiteMean m) ^ 2) ≤
          (blockVariance c' : ℝ) + (m a - finiteMean m) ^ 2 := by
      rw [hdecomp a]
      have htail :
          blockMean Omega' (fun x ↦ (f (Fin.cons a x) - m a) ^ 2) ≤ (blockVariance c' : ℝ) :=
        ih (Omega := Omega') (f := fun x ↦ f (Fin.cons a x)) (c := c') (hf.tail a)
      linarith
    have hpair (a b : Omega 0) : |m a - m b| ≤ (c 0 : ℝ) := by
      have hdiff : m a - m b =
          blockMean Omega' (fun x ↦ f (Fin.cons a x) - f (Fin.cons b x)) :=
        (blockMean_sub Omega' _ _).symm
      have hle1 : m a - m b ≤ (c 0 : ℝ) := by
        rw [hdiff]
        calc
          blockMean Omega' (fun x ↦ f (Fin.cons a x) - f (Fin.cons b x)) ≤
              blockMean Omega' (fun _ ↦ (c 0 : ℝ)) :=
            finiteMean_mono fun x ↦ (le_abs_self _).trans (hf.head a b x)
          _ = (c 0 : ℝ) := blockMean_const Omega' _
      have hle2 : m b - m a ≤ (c 0 : ℝ) := by
        have hdiff' : m b - m a =
            blockMean Omega' (fun x ↦ f (Fin.cons b x) - f (Fin.cons a x)) :=
          (blockMean_sub Omega' _ _).symm
        rw [hdiff']
        calc
          blockMean Omega' (fun x ↦ f (Fin.cons b x) - f (Fin.cons a x)) ≤
              blockMean Omega' (fun _ ↦ (c 0 : ℝ)) :=
            finiteMean_mono fun x ↦ (le_abs_self _).trans (hf.head b a x)
          _ = (c 0 : ℝ) := blockMean_const Omega' _
      exact abs_sub_le_iff.mpr ⟨hle1, hle2⟩
    have hhead : finiteMean (fun a ↦ (m a - finiteMean m) ^ 2) ≤ ((c 0 : ℝ) / 2) ^ 2 :=
      finiteMean_sq_center_le_of_pairwise m (c 0) hpair
    have hsum_var : (blockVariance c : ℝ) = ((c 0 : ℝ) / 2) ^ 2 + (blockVariance c' : ℝ) := by
      unfold blockVariance
      rw [Fin.sum_univ_succ]
      push_cast
      ring
    calc
      finiteMean (fun a ↦ blockMean Omega' (fun x ↦ (f (Fin.cons a x) - finiteMean m) ^ 2)) ≤
          finiteMean (fun a ↦ (blockVariance c' : ℝ) + (m a - finiteMean m) ^ 2) :=
        finiteMean_mono hstep
      _ = (blockVariance c' : ℝ) + finiteMean (fun a ↦ (m a - finiteMean m) ^ 2) := by
        rw [finiteMean_add, finiteMean_const]
      _ ≤ (blockVariance c' : ℝ) + ((c 0 : ℝ) / 2) ^ 2 := by linarith
      _ = (blockVariance c : ℝ) := by linarith [hsum_var]

private theorem hasBlockOscillation_neg {n : ℕ}
    {Omega : Fin n → Type*} {f : (∀ i, Omega i) → ℝ} {c : Fin n → ℝ≥0}
    (hf : HasBlockOscillation f c) :
    HasBlockOscillation (fun x ↦ -f x) c := by
  intro i x y hxy
  have h := hf i x y hxy
  rwa [show -f x - -f y = -(f x - f y) by ring, abs_neg]

private theorem blockVariance_const {r : ℕ} (c : ℝ≥0) :
    (blockVariance (fun _ : Fin r ↦ c) : ℝ) = (c : ℝ) ^ 2 * (r : ℝ) / 4 := by
  rw [blockVariance_eq_sum_sq_div_four]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Section 1, eq. `(1.2)` (`eq:t1-3`) in full:**
for a real-valued function `Y` of coordinatewise oscillation `≤ c` (`c > 0`) across `r ≥ 1`
independent uniform blocks, simultaneously establishes:
1. `Var(Y) ≤ c² r / 4`,
2. `E[exp(λ(Y - E[Y]))] ≤ exp(c² r λ² / 8)` for every `λ ∈ ℝ`,
3. `P(Y - E[Y] ≥ t) ≤ exp(-2 t² / (c² r))`, `P(E[Y] - Y ≥ t) ≤ exp(-2 t² / (c² r))`,
   and `P(|Y - E[Y]| ≥ t) ≤ 2 exp(-2 t² / (c² r))` for every `t ≥ 0`. -/
theorem blockUniform_variance_mgf_and_tails_of_const_oscillation
    {r : ℕ} (hr : 1 ≤ r)
    {Omega : Fin r → Type*} [∀ i, Fintype (Omega i)] [∀ i, Nonempty (Omega i)]
    {Y : (∀ i, Omega i) → ℝ} {c : ℝ≥0} (hc : 0 < c)
    (hY : HasBlockOscillation Y (fun _ ↦ c)) :
    blockExpectation Omega (fun x ↦ (Y x - blockExpectation Omega Y) ^ 2) ≤
        (c : ℝ) ^ 2 * (r : ℝ) / 4 ∧
      (∀ lam : ℝ,
        blockExpectation Omega
            (fun x ↦ Real.exp (lam * (Y x - blockExpectation Omega Y))) ≤
          Real.exp ((c : ℝ) ^ 2 * (r : ℝ) * lam ^ 2 / 8)) ∧
      (∀ {t : ℝ}, 0 ≤ t →
        (blockUniformMeasure Omega).real {x | t ≤ Y x - blockExpectation Omega Y} ≤
            Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ))) ∧
          (blockUniformMeasure Omega).real {x | t ≤ blockExpectation Omega Y - Y x} ≤
            Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ))) ∧
          (blockUniformMeasure Omega).real {x | t ≤ |Y x - blockExpectation Omega Y|} ≤
            2 * Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ)))) := by
  have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hvar :
      blockExpectation Omega (fun x ↦ (Y x - blockExpectation Omega Y) ^ 2) ≤
        (c : ℝ) ^ 2 * (r : ℝ) / 4 := by
    rw [blockExpectation_eq_blockMean, blockExpectation_eq_blockMean, ← blockVariance_const]
    exact blockMean_sq_center_le hY
  have hmgf (lam : ℝ) :
      blockExpectation Omega
          (fun x ↦ Real.exp (lam * (Y x - blockExpectation Omega Y))) ≤
        Real.exp ((c : ℝ) ^ 2 * (r : ℝ) * lam ^ 2 / 8) := by
    letI : MeasurableSpace (∀ i, Omega i) := ⊤
    have hsub := (blockBoundedDifferences_hasSubgaussianMGF hY).mgf_le lam
    rw [ProbabilityTheory.mgf] at hsub
    have hval :
        (blockVariance (fun _ : Fin r ↦ c) : ℝ) * lam ^ 2 / 2 =
          (c : ℝ) ^ 2 * (r : ℝ) * lam ^ 2 / 8 := by
      rw [blockVariance_const]; ring
    simpa [blockExpectation, hval] using hsub
  refine ⟨hvar, hmgf, ?_⟩
  intro t ht
  have hexp_eq :
      -t ^ 2 / (2 * (blockVariance (fun _ : Fin r ↦ c) : ℝ)) =
        -2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ)) := by
    rw [blockVariance_const]
    field_simp [hc_pos.ne', hr_pos.ne']
    ring
  have hup :
      (blockUniformMeasure Omega).real {x | t ≤ Y x - blockExpectation Omega Y} ≤
        Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ))) := by
    simpa only [hexp_eq] using blockBoundedDifferences_upperTail hY ht
  have hneg_mean : blockExpectation Omega (fun x ↦ -Y x) = -blockExpectation Omega Y := by
    rw [blockExpectation_eq_blockMean, blockExpectation_eq_blockMean]
    have h0 : (fun x : ∀ i, Omega i ↦ -Y x) = (fun x ↦ (-1 : ℝ) * Y x) := by funext x; ring
    rw [h0, blockMean_const_mul]
    ring
  have hlo :
      (blockUniformMeasure Omega).real {x | t ≤ blockExpectation Omega Y - Y x} ≤
        Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ))) := by
    have h1 := blockBoundedDifferences_upperTail (hasBlockOscillation_neg hY) ht
    rw [hneg_mean, hexp_eq] at h1
    have hset :
        {x : ∀ i, Omega i | t ≤ blockExpectation Omega Y - Y x} =
          {x : ∀ i, Omega i | t ≤ -Y x - -blockExpectation Omega Y} := by
      ext x; simp [add_comm, sub_eq_add_neg]
    rwa [hset]
  have htwo :
      (blockUniformMeasure Omega).real {x | t ≤ |Y x - blockExpectation Omega Y|} ≤
        2 * Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * (r : ℝ))) := by
    simpa only [hexp_eq] using blockBoundedDifferences_twoSidedTail hY ht
  exact ⟨hup, hlo, htwo⟩

/-!
## 2. Vertex-star `G(n, 1/2)` variance/MGF/tails and oscillation-`2` bounds for `Δ = χ - ζ`
-/

private def noninitialConstOscillation {n : ℕ} (c : ℝ≥0) : Fin n → ℝ≥0 :=
  fun i ↦ if i.val = 0 then 0 else c

private theorem blockVariance_noninitialConstOscillation {n : ℕ} (c : ℝ≥0) :
    (blockVariance (noninitialConstOscillation (n := n) c) : ℝ) =
      (c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) / 4 := by
  rw [blockVariance_eq_sum_sq_div_four]
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.sum_univ_succ]
    simp [noninitialConstOscillation, Finset.sum_const, nsmul_eq_mul]
    ring

private theorem hasBlockOscillation_noninitialConst_of_vertexDeletion {n : ℕ}
    {F : LabeledGraph n → ℝ} {c : ℝ≥0}
    (hF : HasVertexDeletionOscillation F (fun _ ↦ c)) :
    HasBlockOscillation (fun x : VertexBlocks n ↦ F (blocksToGraph x))
      (noninitialConstOscillation c) := by
  intro i x y hxy
  by_cases hi : i.val = 0
  · have hxi : x i = y i := by
      funext u
      have hu : u.val < 0 := by simpa [hi] using u.isLt
      omega
    have hAll : x = y := by
      funext j
      by_cases hji : j = i
      · subst j; exact hxi
      · exact hxy j hji
    subst y
    simp [noninitialConstOscillation, hi]
  · have h := hF.hasBlockOscillation i x y hxy
    simpa [noninitialConstOscillation, hi] using h

private theorem hasVertexDeletionOscillation_neg {n : ℕ}
    {F : LabeledGraph n → ℝ} {c : Fin n → ℝ≥0}
    (hF : HasVertexDeletionOscillation F c) :
    HasVertexDeletionOscillation (fun G ↦ -F G) c := by
  intro i G H hGH
  have h := hF i G H hGH
  rwa [show -F G - -F H = -(F G - F H) by ring, abs_neg]

/-- **General vertex-star `G(n, 1/2)` concentration package:**
for any graph statistic `F : LabeledGraph n → ℝ` with vertex-deletion oscillation `≤ c`,
exposing `G_n` in `n - 1` active vertex-star blocks (`v = 2, ..., n`) yields:
1. `Var(F(G_n)) ≤ c² (n - 1) / 4` (for all `n : ℕ`),
2. `E[exp(λ(F(G_n) - E[F(G_n)]))] ≤ exp(c² (n - 1) λ² / 8)` (for all `n : ℕ`, `λ ∈ ℝ`),
3. when `2 ≤ n` and `0 < c`, one- and two-sided `exp(-2 t² / (c² (n - 1)))` tail bounds. -/
theorem randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation
    {n : ℕ} {F : LabeledGraph n → ℝ} {c : ℝ≥0}
    (hF : HasVertexDeletionOscillation F (fun _ ↦ c)) :
    (∫ G : LabeledGraph n,
        (F G - ∫ H : LabeledGraph n, F H ∂randomGraphMeasure n) ^ 2
        ∂randomGraphMeasure n) ≤
      (c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) / 4 ∧
    (∀ lam : ℝ,
      (∫ G : LabeledGraph n,
          Real.exp (lam * (F G - ∫ H : LabeledGraph n, F H ∂randomGraphMeasure n))
          ∂randomGraphMeasure n) ≤
        Real.exp ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) * lam ^ 2 / 8)) ∧
    (2 ≤ n → 0 < c → ∀ {t : ℝ}, 0 ≤ t →
      (randomGraphMeasure n).real
          {G : LabeledGraph n | t ≤ F G - ∫ H, F H ∂randomGraphMeasure n} ≤
        Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))) ∧
      (randomGraphMeasure n).real
          {G : LabeledGraph n | t ≤ (∫ H, F H ∂randomGraphMeasure n) - F G} ≤
        Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))) ∧
      (randomGraphMeasure n).real
          {G : LabeledGraph n | t ≤ |F G - ∫ H, F H ∂randomGraphMeasure n|} ≤
        2 * Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ)))) := by
  let Omega : Fin n → Type := fun v ↦ VertexBlock v
  have hbOsc := hasBlockOscillation_noninitialConst_of_vertexDeletion hF
  have hmean_eq :
      (∫ H : LabeledGraph n, F H ∂randomGraphMeasure n) =
        blockMean Omega (fun x : VertexBlocks n ↦ F (blocksToGraph x)) := by
    rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
    exact blockExpectation_eq_blockMean Omega _
  have hvar :
      (∫ G : LabeledGraph n,
          (F G - ∫ H : LabeledGraph n, F H ∂randomGraphMeasure n) ^ 2
          ∂randomGraphMeasure n) ≤
        (c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) / 4 := by
    rw [hmean_eq, integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
    unfold randomGraphBlockExpectation
    rw [blockExpectation_eq_blockMean, ← blockVariance_noninitialConstOscillation]
    exact blockMean_sq_center_le hbOsc
  have hmgf (lam : ℝ) :
      (∫ G : LabeledGraph n,
          Real.exp (lam * (F G - ∫ H : LabeledGraph n, F H ∂randomGraphMeasure n))
          ∂randomGraphMeasure n) ≤
        Real.exp ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) * lam ^ 2 / 8) := by
    rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
    rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
    unfold randomGraphBlockExpectation
    letI : MeasurableSpace (VertexBlocks n) := ⊤
    have hsub := (blockBoundedDifferences_hasSubgaussianMGF hbOsc).mgf_le lam
    rw [ProbabilityTheory.mgf] at hsub
    have hval :
        (blockVariance (noninitialConstOscillation (n := n) c) : ℝ) * lam ^ 2 / 2 =
          (c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) * lam ^ 2 / 8 := by
      rw [blockVariance_noninitialConstOscillation]; ring
    simpa [blockExpectation, Omega, hval] using hsub
  refine ⟨hvar, hmgf, ?_⟩
  intro hn hc t ht
  have hc_pos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hexp_eq :
      -t ^ 2 / (2 * (blockVariance (noninitialConstOscillation (n := n) c) : ℝ)) =
        -2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ)) := by
    rw [blockVariance_noninitialConstOscillation]
    field_simp [hc_pos.ne', hn1_pos.ne']
    ring
  have hup :
      (randomGraphMeasure n).real
          {G : LabeledGraph n | t ≤ F G - ∫ H, F H ∂randomGraphMeasure n} ≤
        Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))) := by
    rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
    have hb := blockBoundedDifferences_upperTail (Omega := Omega) hbOsc ht
    rw [hexp_eq] at hb
    change (randomGraphMeasure n
      {G | t ≤ F G - randomGraphBlockExpectation F}).toReal ≤ _
    rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
    simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
      vertexBlockMeasure, Measure.real, Omega] using hb
  have hlo :
      (randomGraphMeasure n).real
          {G : LabeledGraph n | t ≤ (∫ H, F H ∂randomGraphMeasure n) - F G} ≤
        Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))) := by
    have hbOscNeg := hasBlockOscillation_noninitialConst_of_vertexDeletion
      (hasVertexDeletionOscillation_neg hF)
    have hb := blockBoundedDifferences_upperTail (Omega := Omega) hbOscNeg ht
    rw [hexp_eq] at hb
    have hint_neg :
        (∫ H : LabeledGraph n, -F H ∂randomGraphMeasure n) =
          -∫ H : LabeledGraph n, F H ∂randomGraphMeasure n := integral_neg F
    have hset :
        {G : LabeledGraph n | t ≤ (∫ H, F H ∂randomGraphMeasure n) - F G} =
          {G : LabeledGraph n | t ≤ -F G - randomGraphBlockExpectation (fun H ↦ -F H)} := by
      rw [randomGraphBlockExpectation_eq_integral_randomGraphMeasure, hint_neg]
      ext G; simp [add_comm, sub_eq_add_neg]
    rw [hset]
    change (randomGraphMeasure n
      {G | t ≤ -F G - randomGraphBlockExpectation (fun H ↦ -F H)}).toReal ≤ _
    rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
    simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
      vertexBlockMeasure, Measure.real, Omega] using hb
  have htwo :
      (randomGraphMeasure n).real
          {G : LabeledGraph n | t ≤ |F G - ∫ H, F H ∂randomGraphMeasure n|} ≤
        2 * Real.exp (-2 * t ^ 2 / ((c : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ))) := by
    rw [integral_randomGraphMeasure_eq_randomGraphBlockExpectation]
    have hb := blockBoundedDifferences_twoSidedTail (Omega := Omega) hbOsc ht
    rw [hexp_eq] at hb
    change (randomGraphMeasure n
      {G | t ≤ |F G - randomGraphBlockExpectation F|}).toReal ≤ _
    rw [← vertexBlockMeasure_preimage_eq_randomGraphMeasure]
    simpa only [Set.preimage_setOf_eq, randomGraphBlockExpectation,
      vertexBlockMeasure, Measure.real, Omega] using hb
  exact ⟨hup, hlo, htwo⟩

/-- **Oscillation-`1` variance bounds for `ζ(G_n)` and `χ(G_n)`:**
`Var(ζ(G_n)) ≤ (n - 1) / 4` and `Var(χ(G_n)) ≤ (n - 1) / 4` for every `n : ℕ`. -/
theorem variance_cochromatic_and_chromatic_le (n : ℕ) :
    (∫ G : LabeledGraph n,
        ((cochromaticNumber G : ℝ) -
          ∫ H : LabeledGraph n, (cochromaticNumber H : ℝ) ∂randomGraphMeasure n) ^ 2
        ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ) / 4 ∧
    (∫ G : LabeledGraph n,
        ((chromaticNumberNat G : ℝ) -
          ∫ H : LabeledGraph n, (chromaticNumberNat H : ℝ) ∂randomGraphMeasure n) ^ 2
        ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ) / 4 := by
  have hco := (randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation
    (cochromaticNumber_hasVertexDeletionOscillation n)).1
  have hch := (randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation
    (chromaticNumberNat_hasVertexDeletionOscillation n)).1
  exact ⟨by simpa using hco, by simpa using hch⟩

/-- **Corollary 8.1 vertex-deletion oscillation of `Δ = χ - ζ`:**
when `G - i = H - i`, both `χ` and `ζ` differ by at most `1`, so `Δ(G) = χ(G) - ζ(G)`
has vertex-deletion oscillation `≤ 2`. -/
theorem chromaticSubCochromatic_hasVertexDeletionOscillation {n : ℕ} :
    HasVertexDeletionOscillation
      (fun G : LabeledGraph n ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
      (fun _ ↦ (2 : ℝ≥0)) := by
  intro i G H hGH
  have hchi := chromaticNumberNat_hasVertexDeletionOscillation (n := n) i G H hGH
  have hzeta := cochromaticNumber_hasVertexDeletionOscillation (n := n) i G H hGH
  dsimp at hchi hzeta ⊢
  have heq :
      ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
        ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ)) =
      ((chromaticNumberNat G : ℝ) - (chromaticNumberNat H : ℝ)) -
        ((cochromaticNumber G : ℝ) - (cochromaticNumber H : ℝ)) := by ring
  rw [heq]
  have htri := abs_sub ((chromaticNumberNat G : ℝ) - (chromaticNumberNat H : ℝ))
    ((cochromaticNumber G : ℝ) - (cochromaticNumber H : ℝ))
  linarith

/-- **Main Theorem & Corollary 8.1 variance bound:**
`Var(χ(G_n) - ζ(G_n)) ≤ n - 1` for every `n : ℕ`. -/
theorem variance_chromaticSubCochromatic_le (n : ℕ) :
    (∫ G : LabeledGraph n,
        (((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
          ∫ H : LabeledGraph n,
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
            ∂randomGraphMeasure n) ^ 2
        ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ) := by
  have h := (randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation
    (n := n) chromaticSubCochromatic_hasVertexDeletionOscillation).1
  have h2 : ((2 : ℝ≥0) : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) / 4 = ((n - 1 : ℕ) : ℝ) := by
    push_cast; ring
  rwa [h2] at h

/-- **Normalized gap variance bound:**
for `Y_n := ((log₂ n)³ / n) (χ(G_n) - ζ(G_n))` and `n ≥ 2`,
`Var(Y_n) ≤ (log₂ n)⁶ / n`. -/
theorem variance_normalizedGap_le {n : ℕ} (hn : 2 ≤ n) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    (∫ G : LabeledGraph n, (Y G - ∫ H, Y H ∂randomGraphMeasure n) ^ 2 ∂randomGraphMeasure n) ≤
      (Real.logb 2 (n : ℝ)) ^ 6 / (n : ℝ) := by
  intro Y
  set s : ℝ := (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)
  set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
  have hmean : (∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n) =
      s * ∫ H : LabeledGraph n, D H ∂randomGraphMeasure n :=
    integral_const_mul s D
  have hsq :
      (fun G : LabeledGraph n ↦ (Y G - ∫ H, Y H ∂randomGraphMeasure n) ^ 2) =
        (fun G : LabeledGraph n ↦
          s ^ 2 * (D G - ∫ H, D H ∂randomGraphMeasure n) ^ 2) := by
    funext G
    rw [hmean]
    dsimp [Y, s, D]
    ring
  rw [hsq, integral_const_mul]
  have hvarD := variance_chromaticSubCochromatic_le n
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  calc
    s ^ 2 * (∫ G : LabeledGraph n, (D G - ∫ H, D H ∂randomGraphMeasure n) ^ 2
        ∂randomGraphMeasure n) ≤ s ^ 2 * ((n - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hvarD (sq_nonneg s)
    _ ≤ s ^ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left hn1_le (sq_nonneg s)
    _ = (Real.logb 2 (n : ℝ)) ^ 6 / (n : ℝ) := by
      dsimp [s]
      field_simp [hn_pos.ne']

/-- **Corollary 8.1 centered MGF bound for `Δ(G_n) = χ(G_n) - ζ(G_n)`:**
for every `n : ℕ` and `lam ∈ ℝ`,
`E[exp(lam * (Δ(G_n) - E[Δ(G_n)]))] ≤ exp((n - 1) * lam² / 2)`. -/
theorem mgf_chromaticSubCochromatic_center_le (n : ℕ) (lam : ℝ) :
    (∫ G : LabeledGraph n,
        Real.exp (lam * (((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
          ∫ H : LabeledGraph n,
            ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
            ∂randomGraphMeasure n))
        ∂randomGraphMeasure n) ≤
      Real.exp (((n - 1 : ℕ) : ℝ) * lam ^ 2 / 2) := by
  have h := (randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation
    (n := n) chromaticSubCochromatic_hasVertexDeletionOscillation).2.1 lam
  have h2 : ((2 : ℝ≥0) : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) * lam ^ 2 / 8 =
      ((n - 1 : ℕ) : ℝ) * lam ^ 2 / 2 := by
    push_cast; ring
  rwa [h2] at h

/-- **Corollary 8.1 two-sided tail for `Δ(G_n) = χ(G_n) - ζ(G_n)`:**
for every `n ≥ 2` and `t ≥ 0`,
`P(|Δ(G_n) - E[Δ(G_n)]| ≥ t) ≤ 2 exp(-t² / (2(n - 1)))`. -/
theorem randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    (randomGraphMeasure n).real
        {G : LabeledGraph n |
          t ≤ |((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
            ∫ H : LabeledGraph n,
              ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
              ∂randomGraphMeasure n|} ≤
      2 * Real.exp (-t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) := by
  have h := ((randomGraph_variance_mgf_and_tails_of_const_vertexDeletionOscillation
    (n := n) chromaticSubCochromatic_hasVertexDeletionOscillation).2.2 hn (by norm_num) ht).2.2
  have hexp :
      -2 * t ^ 2 / (((2 : ℝ≥0) : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ)) =
        -t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ)) := by
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    push_cast
    field_simp [hn1_pos.ne']
  rwa [hexp] at h

/-- **Corollary 8.1 two-sided MGF squeeze for `Y_n`:**
for every `n ≥ 2` and `lam ∈ ℝ`,
`exp(lam * E[Y_n]) ≤ E[exp(lam * Y_n)] ≤ exp(lam * E[Y_n]) * exp(lam² (log₂ n)⁶ / (2 n))`. -/
theorem mgf_normalizedGap_bounds {n : ℕ} (hn : 2 ≤ n) (lam : ℝ) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    let μ : ℝ := ∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n
    Real.exp (lam * μ) ≤
        (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) ∧
      (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) ≤
        Real.exp (lam * μ) *
          Real.exp (lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))) := by
  intro Y μ
  have hsplit :
      (∫ G : LabeledGraph n, Real.exp (lam * Y G) ∂randomGraphMeasure n) =
        Real.exp (lam * μ) *
          ∫ G : LabeledGraph n, Real.exp (lam * (Y G - μ)) ∂randomGraphMeasure n := by
    have hfun :
        (fun G : LabeledGraph n ↦ Real.exp (lam * Y G)) =
          (fun G : LabeledGraph n ↦ Real.exp (lam * μ) * Real.exp (lam * (Y G - μ))) := by
      funext G
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfun, integral_const_mul]
  rw [hsplit]
  have hexp_pos : 0 ≤ Real.exp (lam * μ) := (Real.exp_pos _).le
  refine ⟨?_, ?_⟩
  · have hone_le :
        (1 : ℝ) ≤ ∫ G : LabeledGraph n, Real.exp (lam * (Y G - μ)) ∂randomGraphMeasure n := by
      have hpt : ∀ G : LabeledGraph n,
          (lam * (Y G - μ) + 1) ≤ Real.exp (lam * (Y G - μ)) := fun G ↦
        Real.add_one_le_exp (lam * (Y G - μ))
      have hint := integral_mono (μ := randomGraphMeasure n)
        (Integrable.of_finite) (Integrable.of_finite) hpt
      have hlhs :
          (∫ G : LabeledGraph n, (lam * (Y G - μ) + 1) ∂randomGraphMeasure n) = 1 := by
        rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
          integral_const_mul, integral_sub (Integrable.of_finite) (Integrable.of_finite)]
        simp only [integral_const, probReal_univ, one_smul]
        dsimp [μ]
        ring
      linarith
    calc
      Real.exp (lam * μ) = Real.exp (lam * μ) * 1 := (mul_one _).symm
      _ ≤ Real.exp (lam * μ) *
            ∫ G : LabeledGraph n, Real.exp (lam * (Y G - μ)) ∂randomGraphMeasure n :=
        mul_le_mul_of_nonneg_left hone_le hexp_pos
  · set s : ℝ := lam * ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ))
    set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    have hμ : μ = ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)) *
        ∫ H : LabeledGraph n, D H ∂randomGraphMeasure n :=
      integral_const_mul _ D
    have hcenter :
        (fun G : LabeledGraph n ↦ Real.exp (lam * (Y G - μ))) =
          (fun G : LabeledGraph n ↦
            Real.exp (s * (D G - ∫ H, D H ∂randomGraphMeasure n))) := by
      funext G
      congr 1
      rw [hμ]
      dsimp [Y, s, D]
      ring
    rw [hcenter]
    have hD := mgf_chromaticSubCochromatic_center_le n s
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hexp_le :
        Real.exp (((n - 1 : ℕ) : ℝ) * s ^ 2 / 2) ≤
          Real.exp (lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      calc
        ((n - 1 : ℕ) : ℝ) * s ^ 2 / 2 ≤ (n : ℝ) * s ^ 2 / 2 := by
          nlinarith [sq_nonneg s]
        _ = lam ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)) := by
          dsimp [s]
          field_simp [hn_pos.ne']
    exact mul_le_mul_of_nonneg_left (hD.trans hexp_le) hexp_pos

/-- **Main Theorem & Corollary 8.1 non-asymptotic mean concentration for `Y_n`:**
for every `n ≥ 2` and `u ≥ 0`,
`P(|Y_n - E[Y_n]| ≥ u) ≤ 2 exp(-u² n / (2 (log₂ n)⁶))`. -/
theorem randomGraph_abs_normalizedGap_sub_mean_ge_le
    {n : ℕ} (hn : 2 ≤ n) {u : ℝ} (hu : 0 ≤ u) :
    let Y : LabeledGraph n → ℝ := fun G ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
    (randomGraphMeasure n).real
        {G : LabeledGraph n | u ≤ |Y G - ∫ H, Y H ∂randomGraphMeasure n|} ≤
      2 * Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6)) := by
  intro Y
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hlog2_pos : 0 < Real.logb 2 (n : ℝ) := Real.logb_pos one_lt_two hn1
  set scale : ℝ := (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ)
  have hscale_pos : 0 < scale := by positivity
  set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
  have hmean : (∫ H : LabeledGraph n, Y H ∂randomGraphMeasure n) =
      scale * ∫ H : LabeledGraph n, D H ∂randomGraphMeasure n :=
    integral_const_mul scale D
  have hset :
      {G : LabeledGraph n | u ≤ |Y G - ∫ H, Y H ∂randomGraphMeasure n|} =
        {G : LabeledGraph n | u / scale ≤ |D G - ∫ H, D H ∂randomGraphMeasure n|} := by
    ext G
    simp only [Set.mem_setOf_eq, hmean]
    have hfactor : Y G - scale * (∫ H, D H ∂randomGraphMeasure n) =
        scale * (D G - ∫ H, D H ∂randomGraphMeasure n) := by
      dsimp [Y, D]; ring
    rw [hfactor, abs_mul, abs_of_pos hscale_pos, div_le_iff₀ hscale_pos, mul_comm]
  rw [hset]
  have hraw := randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le hn
    (div_nonneg hu hscale_pos.le)
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hexp_le :
      Real.exp (-(u / scale) ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) ≤
        Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6)) := by
    apply Real.exp_le_exp.mpr
    have hden :
        (u / scale) ^ 2 / (2 * (n : ℝ)) ≤
          (u / scale) ^ 2 / (2 * ((n - 1 : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    have hident :
        (u / scale) ^ 2 / (2 * (n : ℝ)) =
          u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) := by
      dsimp [scale]
      field_simp [hn_pos.ne', hlog2_pos.ne']
    calc
      -(u / scale) ^ 2 / (2 * ((n - 1 : ℕ) : ℝ)) =
          -((u / scale) ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) := by ring
      _ ≤ -((u / scale) ^ 2 / (2 * (n : ℝ))) := neg_le_neg hden
      _ = -(u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6)) := by rw [hident]
      _ = -u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) := by ring
  linarith

/-!
## 3. Section 7 mark-measure equations (`eq:hp-marks`) and scrambled-part overlap bounds
-/

private theorem flipMarkedInternal_mem_partitionMarkedEvent {n : ℕ}
    {P : VertexPartition n} {σ : P.parts → Bool} {G : LabeledGraph n}
    (hG : G ∈ partitionColoringEvent P) :
    flipMarkedInternal P σ G ∈ partitionMarkedEvent P σ := by
  classical
  intro B
  have hB_eq : ∀ D : P.parts, ∀ u ∈ B.1, u ∈ D.1 → D = B := by
    intro D u huB huD
    apply Subtype.ext
    by_contra hne
    exact (Finset.disjoint_left.mp (P.disjoint D.2 B.2 hne) huD) huB
  have hBind := hG B.1 B.2
  cases hσB : σ B
  · simp only [Bool.false_eq_true, ↓reduceIte]
    intro u hu v hv huv hadj
    change flipMarkedAdj P σ G u v at hadj
    unfold flipMarkedAdj at hadj
    have huB : u ∈ B.1 := by simpa using hu
    have hnot : ¬ markedPair P σ u v := by
      rintro ⟨D, hσD, huD, -⟩
      rw [hB_eq D u huB huD, hσB] at hσD
      exact Bool.false_ne_true hσD
    have hadj_ite := hadj.2
    rw [if_neg hnot] at hadj_ite
    exact hBind hu hv huv hadj_ite
  · simp only [↓reduceIte]
    intro u hu v hv huv
    change flipMarkedAdj P σ G u v
    unfold flipMarkedAdj
    have huB : u ∈ B.1 := by simpa using hu
    have hvB : v ∈ B.1 := by simpa using hv
    have hex : markedPair P σ u v := ⟨B, hσB, huB, hvB⟩
    refine ⟨huv, ?_⟩
    rw [if_pos hex]
    exact hBind hu hv huv

/-- For any partition `P` and marking `σ : P.parts → Bool`, flipping the internal edges of the
`true`-marked parts is a measure-preserving bijection between `partitionMarkedEvent P σ` and
`partitionColoringEvent P` in `G(n, 1/2)`. -/
theorem randomGraphMeasure_partitionMarkedEvent_eq {n : ℕ}
    (P : VertexPartition n) (σ : P.parts → Bool) :
    randomGraphMeasure n (partitionMarkedEvent P σ) =
      randomGraphMeasure n (partitionColoringEvent P) := by
  apply le_antisymm (randomGraphMeasure_partitionMarkedEvent_le P σ)
  exact randomGraphMeasure_image_le_of_involutive (flipMarkedInternal P σ)
    (flipMarkedInternal_involutive P σ)
    (fun _ hG ↦ flipMarkedInternal_mem_partitionMarkedEvent hG)

/-- **Section 7, eq. `(7.1)` (`eq:hp-marks`, first identity):**
when every part of `P : VertexPartition n` has size `≥ 2`, the `2 ^ |P.parts|` marked events
partition `partitionCocoloringEvent P`, yielding the exact equalities
`P(A_P^co) = 2 ^ |P.parts| * P(A_P)` in both `ENNReal` and `.real` forms. -/
theorem randomGraphMeasure_partitionCocoloringEvent_eq_two_pow_mul {n : ℕ}
    (P : VertexPartition n) (hP : ∀ B ∈ P.parts, 2 ≤ B.card) :
    randomGraphMeasure n (partitionCocoloringEvent P) =
        (2 : ENNReal) ^ P.parts.card * randomGraphMeasure n (partitionColoringEvent P) ∧
      (randomGraphMeasure n).real (partitionCocoloringEvent P) =
        (2 : ℝ) ^ P.parts.card * (randomGraphMeasure n).real (partitionColoringEvent P) := by
  classical
  have hunion :
      partitionCocoloringEvent P = ⋃ σ : P.parts → Bool, partitionMarkedEvent P σ := by
    apply Set.Subset.antisymm
    · intro G hG
      rw [Set.mem_iUnion]
      refine ⟨fun B ↦ decide (G.IsClique (B.1 : Set (Fin n))), ?_⟩
      intro B
      by_cases hcl : G.IsClique (B.1 : Set (Fin n))
      · simp [hcl]
      · simp only [hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
        rcases hG B.1 B.2 with hind | hcl'
        · exact hind
        · exact (hcl hcl').elim
    · intro G hG B hB
      rw [Set.mem_iUnion] at hG
      obtain ⟨σ, hσ⟩ := hG
      have hBσ := hσ ⟨B, hB⟩
      cases hval : σ ⟨B, hB⟩
      · simp only [hval, Bool.false_eq_true, ↓reduceIte] at hBσ
        exact Or.inl hBσ
      · simp only [hval, ↓reduceIte] at hBσ
        exact Or.inr hBσ
  have hdisj : Pairwise (fun σ τ ↦ Disjoint (partitionMarkedEvent P σ) (partitionMarkedEvent P τ)) := by
    intro σ τ hne
    rw [Set.disjoint_left]
    intro G hGσ hGτ
    obtain ⟨B, hBne⟩ := Function.ne_iff.mp hne
    have hcard : 1 < B.1.card := Nat.lt_of_lt_of_le Nat.one_lt_two (hP B.1 B.2)
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
    have hσB := hGσ B
    have hτB := hGτ B
    cases hs : σ B <;> cases ht : τ B
    · exact hBne (hs.trans ht.symm)
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hσB
      simp only [ht, ↓reduceIte] at hτB
      exact hσB hu hv huv (hτB hu hv huv)
    · simp only [hs, ↓reduceIte] at hσB
      simp only [ht, Bool.false_eq_true, ↓reduceIte] at hτB
      exact hτB hu hv huv (hσB hu hv huv)
    · exact hBne (hs.trans ht.symm)
  have henn :
      randomGraphMeasure n (partitionCocoloringEvent P) =
        (2 : ENNReal) ^ P.parts.card * randomGraphMeasure n (partitionColoringEvent P) := by
    rw [hunion, measure_iUnion hdisj (fun σ ↦ (Set.toFinite _).measurableSet),
      tsum_fintype]
    calc
      ∑ σ : P.parts → Bool, randomGraphMeasure n (partitionMarkedEvent P σ) =
          ∑ _σ : P.parts → Bool, randomGraphMeasure n (partitionColoringEvent P) :=
        Finset.sum_congr rfl fun σ _ ↦ randomGraphMeasure_partitionMarkedEvent_eq P σ
      _ = (Fintype.card (P.parts → Bool) : ENNReal) *
            randomGraphMeasure n (partitionColoringEvent P) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = (2 : ENNReal) ^ P.parts.card * randomGraphMeasure n (partitionColoringEvent P) := by
        rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
        norm_cast
  refine ⟨henn, ?_⟩
  simp only [Measure.real, henn, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

private def pairMarkedPair {n : ℕ} (P Q : VertexPartition n)
    (σ : P.parts → Bool) (τ : Q.parts → Bool) (u v : Fin n) : Prop :=
  markedPair P σ u v ∨ markedPair Q τ u v

private theorem pairMarkedPair_comm {n : ℕ} (P Q : VertexPartition n)
    (σ : P.parts → Bool) (τ : Q.parts → Bool) (u v : Fin n) :
    pairMarkedPair P Q σ τ u v ↔ pairMarkedPair P Q σ τ v u := by
  unfold pairMarkedPair
  rw [markedPair_comm P σ u v, markedPair_comm Q τ u v]

private def flipPairMarkedAdj {n : ℕ} (P Q : VertexPartition n)
    (σ : P.parts → Bool) (τ : Q.parts → Bool)
    (G : LabeledGraph n) (u v : Fin n) : Prop := by
  classical
  exact u ≠ v ∧ if pairMarkedPair P Q σ τ u v then ¬ G.Adj u v else G.Adj u v

private def flipPairMarkedInternal {n : ℕ} (P Q : VertexPartition n)
    (σ : P.parts → Bool) (τ : Q.parts → Bool) (G : LabeledGraph n) : LabeledGraph n where
  Adj := flipPairMarkedAdj P Q σ τ G
  symm := ⟨by
    classical
    intro u v huv
    unfold flipPairMarkedAdj at huv ⊢
    refine ⟨huv.1.symm, ?_⟩
    by_cases hm : pairMarkedPair P Q σ τ u v
    · have hmv : pairMarkedPair P Q σ τ v u := (pairMarkedPair_comm P Q σ τ u v).mp hm
      rw [if_pos hm] at huv
      rw [if_pos hmv]
      exact fun hadj ↦ huv.2 (G.adj_symm hadj)
    · have hmv : ¬ pairMarkedPair P Q σ τ v u :=
        fun hc ↦ hm ((pairMarkedPair_comm P Q σ τ u v).mpr hc)
      rw [if_neg hm] at huv
      rw [if_neg hmv]
      exact G.adj_symm huv.2⟩
  loopless := ⟨fun u hu ↦ hu.1 rfl⟩

private theorem flipPairMarkedInternal_involutive {n : ℕ} (P Q : VertexPartition n)
    (σ : P.parts → Bool) (τ : Q.parts → Bool) :
    Function.Involutive (flipPairMarkedInternal P Q σ τ) := by
  classical
  intro G
  ext u v
  change flipPairMarkedAdj P Q σ τ (flipPairMarkedInternal P Q σ τ G) u v ↔ G.Adj u v
  unfold flipPairMarkedAdj
  change (u ≠ v ∧
    if pairMarkedPair P Q σ τ u v then ¬ flipPairMarkedAdj P Q σ τ G u v
    else flipPairMarkedAdj P Q σ τ G u v) ↔ G.Adj u v
  unfold flipPairMarkedAdj
  by_cases huv : u = v
  · subst v
    constructor
    · intro h; exact (h.1 rfl).elim
    · intro h; exact (G.ne_of_adj h rfl).elim
  · by_cases hm : pairMarkedPair P Q σ τ u v
    · simp [huv, hm]
    · simp [huv, hm]

private theorem flipPairMarkedInternal_mem_inter_coloring {n : ℕ}
    {P Q : VertexPartition n} {σ : P.parts → Bool} {τ : Q.parts → Bool}
    (hcompat : ∀ (A : P.parts) (B : Q.parts), 2 ≤ (A.1 ∩ B.1).card → σ A = τ B)
    {G : LabeledGraph n}
    (hGP : G ∈ partitionMarkedEvent P σ) (hGQ : G ∈ partitionMarkedEvent Q τ) :
    flipPairMarkedInternal P Q σ τ G ∈
      partitionColoringEvent P ∩ partitionColoringEvent Q := by
  classical
  have hUnique {R : VertexPartition n} {D : Finset (Fin n)} (hD : D ∈ R.parts)
      {u : Fin n} (huD : u ∈ D) (B : R.parts) (huB : u ∈ B.1) : B = ⟨D, hD⟩ := by
    apply Subtype.ext
    by_contra hne
    exact (Finset.disjoint_left.mp (R.disjoint B.2 hD hne) huB) huD
  refine ⟨?_, ?_⟩
  · intro D hD u hu v hv huv hadj
    change flipPairMarkedAdj P Q σ τ G u v at hadj
    unfold flipPairMarkedAdj at hadj
    have huD : u ∈ D := by simpa using hu
    have hvD : v ∈ D := by simpa using hv
    let A : P.parts := ⟨D, hD⟩
    have hAspec := hGP A
    cases hσA : σ A
    · simp only [hσA, Bool.false_eq_true, ↓reduceIte] at hAspec
      have hnot : ¬ pairMarkedPair P Q σ τ u v := by
        rintro (⟨A', hσA', huA', -⟩ | ⟨B, hτB, huB, hvB⟩)
        · rw [hUnique hD huD A' huA', hσA] at hσA'
          exact Bool.false_ne_true hσA'
        · have h2 : 2 ≤ (A.1 ∩ B.1).card :=
            Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨huD, huB⟩,
              v, Finset.mem_inter.mpr ⟨hvD, hvB⟩, huv⟩
          have heq := hcompat A B h2
          rw [hσA, hτB] at heq
          exact Bool.false_ne_true heq
      have hadj_ite := hadj.2
      rw [if_neg hnot] at hadj_ite
      exact hAspec hu hv huv hadj_ite
    · simp only [hσA, ↓reduceIte] at hAspec
      have hex : pairMarkedPair P Q σ τ u v := Or.inl ⟨A, hσA, huD, hvD⟩
      have hadj_ite := hadj.2
      rw [if_pos hex] at hadj_ite
      exact hadj_ite (hAspec hu hv huv)
  · intro D hD u hu v hv huv hadj
    change flipPairMarkedAdj P Q σ τ G u v at hadj
    unfold flipPairMarkedAdj at hadj
    have huD : u ∈ D := by simpa using hu
    have hvD : v ∈ D := by simpa using hv
    let B : Q.parts := ⟨D, hD⟩
    have hBspec := hGQ B
    cases hτB : τ B
    · simp only [hτB, Bool.false_eq_true, ↓reduceIte] at hBspec
      have hnot : ¬ pairMarkedPair P Q σ τ u v := by
        rintro (⟨A, hσA, huA, hvA⟩ | ⟨B', hτB', huB', -⟩)
        · have h2 : 2 ≤ (A.1 ∩ B.1).card :=
            Finset.one_lt_card.mpr ⟨u, Finset.mem_inter.mpr ⟨huA, huD⟩,
              v, Finset.mem_inter.mpr ⟨hvA, hvD⟩, huv⟩
          have heq := hcompat A B h2
          rw [hσA, hτB] at heq
          exact Bool.false_ne_true (heq.symm)
        · rw [hUnique hD huD B' huB', hτB] at hτB'
          exact Bool.false_ne_true hτB'
      have hadj_ite := hadj.2
      rw [if_neg hnot] at hadj_ite
      exact hBspec hu hv huv hadj_ite
    · simp only [hτB, ↓reduceIte] at hBspec
      have hex : pairMarkedPair P Q σ τ u v := Or.inr ⟨B, hτB, huD, hvD⟩
      have hadj_ite := hadj.2
      rw [if_pos hex] at hadj_ite
      exact hadj_ite (hBspec hu hv huv)

/-- **General `G(n, 1/2)` compatible-marking pair bound (Heckel Proposition 6 / eq. `(7.1)`):**
if every `c`-selected part of `Q` meets its partner in `P` in at least `2` vertices, then
`P(A_P^co ∩ A_Q^co) ≤ 2 ^ (|P| + |Q| - #{B ∈ Q : c B}) * P(A_P ∩ A_Q)`. -/
theorem randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_common
    {n : ℕ} (P Q : VertexPartition n)
    (c : Q.parts → Prop) [DecidablePred c]
    (g : {B : Q.parts // c B} → P.parts)
    (hg : ∀ b : {B : Q.parts // c B}, 2 ≤ ((g b).1 ∩ b.1.1).card) :
    randomGraphMeasure n (partitionCocoloringEvent P ∩ partitionCocoloringEvent Q) ≤
        (2 : ENNReal) ^ (P.parts.card + Q.parts.card - Fintype.card {B : Q.parts // c B}) *
          randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) ∧
      (randomGraphMeasure n).real (partitionCocoloringEvent P ∩ partitionCocoloringEvent Q) ≤
        (2 : ℝ) ^ (P.parts.card + Q.parts.card - Fintype.card {B : Q.parts // c B}) *
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) := by
  classical
  let r : P.parts → Q.parts → ℕ := fun A B ↦ (A.1 ∩ B.1).card
  letI : Fintype (CompatiblePairSignAssignments r) := by
    unfold CompatiblePairSignAssignments; infer_instance
  have hcov :
      partitionCocoloringEvent P ∩ partitionCocoloringEvent Q ⊆
        ⋃ s : CompatiblePairSignAssignments r,
          (partitionMarkedEvent P s.1.1 ∩ partitionMarkedEvent Q s.1.2) := by
    intro G ⟨hGP, hGQ⟩
    let σ : P.parts → Bool := fun A ↦ decide (G.IsClique (A.1 : Set (Fin n)))
    let τ : Q.parts → Bool := fun B ↦ decide (G.IsClique (B.1 : Set (Fin n)))
    have hGPσ : G ∈ partitionMarkedEvent P σ := by
      intro A
      by_cases hcl : G.IsClique (A.1 : Set (Fin n))
      · simp [σ, hcl]
      · simp only [σ, hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
        rcases hGP A.1 A.2 with hind | hcl'
        · exact hind
        · exact (hcl hcl').elim
    have hGQτ : G ∈ partitionMarkedEvent Q τ := by
      intro B
      by_cases hcl : G.IsClique (B.1 : Set (Fin n))
      · simp [τ, hcl]
      · simp only [τ, hcl, decide_false, Bool.false_eq_true, ↓reduceIte]
        rcases hGQ B.1 B.2 with hind | hcl'
        · exact hind
        · exact (hcl hcl').elim
    have hcompat : ∀ A B, 2 ≤ r A B → σ A = τ B := by
      intro A B hab
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp
        (Nat.lt_of_lt_of_le Nat.one_lt_two hab)
      have huA : u ∈ A.1 := (Finset.mem_inter.mp hu).1
      have huB : u ∈ B.1 := (Finset.mem_inter.mp hu).2
      have hvA : v ∈ A.1 := (Finset.mem_inter.mp hv).1
      have hvB : v ∈ B.1 := (Finset.mem_inter.mp hv).2
      have hA := hGPσ A
      have hB := hGQτ B
      cases hs : σ A <;> cases ht : τ B
      · rfl
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hA
        simp only [ht, ↓reduceIte] at hB
        exact (hA huA hvA huv (hB huB hvB huv)).elim
      · simp only [hs, ↓reduceIte] at hA
        simp only [ht, Bool.false_eq_true, ↓reduceIte] at hB
        exact (hB huB hvB huv (hA huA hvA huv)).elim
      · rfl
    rw [Set.mem_iUnion]
    exact ⟨⟨(σ, τ), hcompat⟩, hGPσ, hGQτ⟩
  have hcell (s : CompatiblePairSignAssignments r) :
      randomGraphMeasure n (partitionMarkedEvent P s.1.1 ∩ partitionMarkedEvent Q s.1.2) ≤
        randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) :=
    randomGraphMeasure_image_le_of_involutive
      (flipPairMarkedInternal P Q s.1.1 s.1.2)
      (flipPairMarkedInternal_involutive P Q s.1.1 s.1.2)
      (fun _ hG ↦ flipPairMarkedInternal_mem_inter_coloring s.2 hG.1 hG.2)
  have hcard :
      Fintype.card (CompatiblePairSignAssignments r) ≤
        2 ^ (P.parts.card + Q.parts.card - Fintype.card {B : Q.parts // c B}) := by
    have hnat := natCard_compatiblePairSignAssignments_le_two_pow_sub_common r c g hg
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hnat
  have henn :
      randomGraphMeasure n (partitionCocoloringEvent P ∩ partitionCocoloringEvent Q) ≤
        (2 : ENNReal) ^ (P.parts.card + Q.parts.card - Fintype.card {B : Q.parts // c B}) *
          randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) := by
    calc
      randomGraphMeasure n (partitionCocoloringEvent P ∩ partitionCocoloringEvent Q) ≤
          randomGraphMeasure n
            (⋃ s : CompatiblePairSignAssignments r,
              (partitionMarkedEvent P s.1.1 ∩ partitionMarkedEvent Q s.1.2)) :=
        measure_mono hcov
      _ ≤ ∑ s : CompatiblePairSignAssignments r,
            randomGraphMeasure n (partitionMarkedEvent P s.1.1 ∩ partitionMarkedEvent Q s.1.2) :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _s : CompatiblePairSignAssignments r,
            randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) :=
        Finset.sum_le_sum fun s _ ↦ hcell s
      _ = (Fintype.card (CompatiblePairSignAssignments r) : ENNReal) *
            randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ENNReal) ^ (P.parts.card + Q.parts.card - Fintype.card {B : Q.parts // c B}) *
            randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) := by
        gcongr
        exact_mod_cast hcard
  refine ⟨henn, ?_⟩
  have hfin :
      (2 : ENNReal) ^ (P.parts.card + Q.parts.card - Fintype.card {B : Q.parts // c B}) *
        randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (measure_ne_top _ _)
  have htr := ENNReal.toReal_mono hfin henn
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using htr

/-- **Section 7, eq. `(7.1)` (`eq:hp-marks`, shared-class specialization):**
if every shared part in `P.parts ∩ Q.parts` has size `≥ 2`, then
`P(A_P^co ∩ A_Q^co) ≤ 2 ^ (|P.parts| + |Q.parts| - |P.parts ∩ Q.parts|) * P(A_P ∩ A_Q)`
(at `|P.parts| = |Q.parts| = k` and `|P.parts ∩ Q.parts| = ν_•`, this is `2 ^ (2 k - ν_•)`). -/
theorem randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_inter
    {n : ℕ} (P Q : VertexPartition n)
    (hshared : ∀ B ∈ P.parts ∩ Q.parts, 2 ≤ B.card) :
    randomGraphMeasure n (partitionCocoloringEvent P ∩ partitionCocoloringEvent Q) ≤
        (2 : ENNReal) ^ (P.parts.card + Q.parts.card - (P.parts ∩ Q.parts).card) *
          randomGraphMeasure n (partitionColoringEvent P ∩ partitionColoringEvent Q) ∧
      (randomGraphMeasure n).real (partitionCocoloringEvent P ∩ partitionCocoloringEvent Q) ≤
        (2 : ℝ) ^ (P.parts.card + Q.parts.card - (P.parts ∩ Q.parts).card) *
          (randomGraphMeasure n).real (partitionColoringEvent P ∩ partitionColoringEvent Q) := by
  classical
  let c : Q.parts → Prop := fun B ↦ B.1 ∈ P.parts
  let g : {B : Q.parts // c B} → P.parts := fun b ↦ ⟨b.1.1, b.2⟩
  have hg : ∀ b : {B : Q.parts // c B}, 2 ≤ ((g b).1 ∩ b.1.1).card := by
    intro b
    have hmem : b.1.1 ∈ P.parts ∩ Q.parts := Finset.mem_inter.mpr ⟨b.2, b.1.2⟩
    simpa [g] using hshared b.1.1 hmem
  have hcard_eq : Fintype.card {B : Q.parts // c B} = (P.parts ∩ Q.parts).card := by
    have h1 : Fintype.card {B : Q.parts // c B} =
        (Finset.univ.filter (fun B : Q.parts ↦ B.1 ∈ P.parts)).card :=
      Fintype.card_of_subtype _ (fun _ ↦ by simp [c])
    rw [h1]
    have hbij :
        (Finset.univ.filter (fun B : Q.parts ↦ B.1 ∈ P.parts)).card =
          (P.parts ∩ Q.parts).card := by
      refine Finset.card_bij (fun B _ ↦ B.1) ?_ ?_ ?_
      · intro B hB
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
        exact Finset.mem_inter.mpr ⟨hB, B.2⟩
      · intro B₁ _ B₂ _ h; exact Subtype.ext h
      · intro D hD
        obtain ⟨hDP, hDQ⟩ := Finset.mem_inter.mp hD
        exact ⟨⟨D, hDQ⟩, by simp [hDP], rfl⟩
    exact hbij
  simpa only [hcard_eq] using
    randomGraphMeasure_partitionCocoloringEvent_inter_le_two_pow_sub_common P Q c g hg

/-- **Lemma 7.2 scrambled-part heavy-overlap bounds (`main.tex` lines 1043–1050):**
for any partition `P : Finpartition V` of a scrambled class `V` of size `u = V.card` into
`z = P.parts.card` nonempty overlap blocks satisfying `u ≤ α`, `α - u ≤ M + 1`, and
`u ≤ z + 2 * (α - u) + 1` (i.e. `z ≥ u - 2(α - u) - 1`):
1. every overlap block `B ∈ P.parts` satisfies `B.card ≤ 2 * (α - u) + 2` and `≤ 2 * M + 4`;
2. the total vertex mass in blocks of size `≥ 2` satisfies
   `∑ B ∈ P.parts with 2 ≤ B.card, B.card ≤ 2 * (u - z)` and `≤ 4 * M + 6`. -/
theorem scrambledPart_heavyOverlap_card_and_vertex_sum_le
    {α_type : Type*} [DecidableEq α_type]
    {V : Finset α_type} (P : Finpartition V)
    {u α M : ℕ} (hu : V.card = u) (_hu_le : u ≤ α) (hdef : α - u ≤ M + 1)
    (hscr : u ≤ P.parts.card + 2 * (α - u) + 1) :
    (∀ B ∈ P.parts, B.card ≤ 2 * (α - u) + 2 ∧ B.card ≤ 2 * M + 4) ∧
      ((P.parts.filter (fun B ↦ 2 ≤ B.card)).sum Finset.card ≤ 2 * (u - P.parts.card) ∧
        (P.parts.filter (fun B ↦ 2 ≤ B.card)).sum Finset.card ≤ 4 * M + 6) := by
  have hsum_all : P.parts.sum Finset.card = u := by
    rw [← hu]
    exact P.sum_card_parts
  refine ⟨?_, ?_⟩
  · intro B hB
    have hrest_ge : (P.parts.erase B).card ≤ (P.parts.erase B).sum Finset.card := by
      calc
        (P.parts.erase B).card = ∑ _D ∈ P.parts.erase B, 1 := by simp
        _ ≤ ∑ D ∈ P.parts.erase B, D.card := by
          apply Finset.sum_le_sum
          intro D hD
          exact (P.nonempty_of_mem_parts (Finset.mem_of_mem_erase hD)).card_pos
    have hsplit : B.card + (P.parts.erase B).sum Finset.card = u := by
      rw [← hsum_all, Finset.add_sum_erase _ _ hB]
    have herase_card : (P.parts.erase B).card = P.parts.card - 1 := Finset.card_erase_of_mem hB
    have hz_pos : 1 ≤ P.parts.card := Finset.card_pos.mpr ⟨B, hB⟩
    omega
  · let heavy := P.parts.filter (fun B ↦ 2 ≤ B.card)
    let single := P.parts.filter (fun B ↦ ¬ 2 ≤ B.card)
    have hcard_split : heavy.card + single.card = P.parts.card :=
      Finset.card_filter_add_card_filter_not _
    have hsum_split :
        heavy.sum Finset.card + single.sum Finset.card = P.parts.sum Finset.card :=
      Finset.sum_filter_add_sum_filter_not P.parts (fun B ↦ 2 ≤ B.card) Finset.card
    have hsingle_eq : single.sum Finset.card = single.card := by
      calc
        single.sum Finset.card = ∑ B ∈ single, 1 := by
          apply Finset.sum_congr rfl
          intro B hB
          simp only [single, Finset.mem_filter] at hB
          have hpos : 1 ≤ B.card := (P.nonempty_of_mem_parts hB.1).card_pos
          omega
        _ = single.card := by simp
    have hheavy_ge : 2 * heavy.card ≤ heavy.sum Finset.card := by
      calc
        2 * heavy.card = ∑ _B ∈ heavy, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ B ∈ heavy, B.card := by
          apply Finset.sum_le_sum
          intro B hB
          exact (Finset.mem_filter.mp hB).2
    change heavy.sum Finset.card ≤ 2 * (u - P.parts.card) ∧ heavy.sum Finset.card ≤ 4 * M + 6
    omega

/-!
## 4. Section 9 summability and sub-Gaussian Main Theorem + Phase Refinement assemblies
-/

/-- **Main Theorem Borel–Cantelli summability:**
for every `c > 0`, `∑_{n ≥ 0} exp(-c * n / (log₂ n)⁶) < ∞`. -/
theorem summable_subgaussianGapTail {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ ↦ Real.exp (-c * (n : ℝ) / (Real.logb 2 (n : ℝ)) ^ 6)) := by
  have hq_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hq6_pos : 0 < (Real.log 2) ^ 6 := pow_pos hq_pos 6
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.exp (-c * (n : ℝ) / (Real.logb 2 (n : ℝ)) ^ 6) ≤ quasiExpTail n := by
    filter_upwards [eventually_ge_atTop 3,
      hlog.eventually_ge_atTop (max 1 (2 / (c * (Real.log 2) ^ 6)))] with n hn3 hLm
    have hL1 : 1 ≤ Real.log (n : ℝ) := le_trans (le_max_left _ _) hLm
    have hL_ge : 2 / (c * (Real.log 2) ^ 6) ≤ Real.log (n : ℝ) :=
      le_trans (le_max_right _ _) hLm
    have hL4 : 2 / (c * (Real.log 2) ^ 6) ≤ (Real.log (n : ℝ)) ^ 4 := by
      have hpow : Real.log (n : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
        nlinarith [sq_nonneg (Real.log (n : ℝ)), sq_nonneg ((Real.log (n : ℝ)) ^ 2 - 1)]
      linarith
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    unfold quasiExpTail
    apply Real.exp_le_exp.mpr
    have hlogb : (Real.logb 2 (n : ℝ)) ^ 6 = (Real.log (n : ℝ)) ^ 6 / (Real.log 2) ^ 6 := by
      rw [Real.logb, div_pow]
    rw [hlogb]
    have hineq :
        2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 ≤
          c * (n : ℝ) / ((Real.log (n : ℝ)) ^ 6 / (Real.log 2) ^ 6) := by
      rw [div_le_div_iff₀ (pow_pos hL_pos 10) (div_pos (pow_pos hL_pos 6) hq6_pos)]
      have hmul : 2 ≤ c * (Real.log 2) ^ 6 * (Real.log (n : ℝ)) ^ 4 := by
        rwa [div_le_iff₀ (mul_pos hc hq6_pos), mul_comm] at hL4
      have hpow10 : (Real.log (n : ℝ)) ^ 10 =
          (Real.log (n : ℝ)) ^ 4 * (Real.log (n : ℝ)) ^ 6 := by ring
      calc
        2 * (n : ℝ) * ((Real.log (n : ℝ)) ^ 6 / (Real.log 2) ^ 6) =
            (2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 6) / (Real.log 2) ^ 6 := by ring
        _ ≤ (c * (Real.log 2) ^ 6 * (Real.log (n : ℝ)) ^ 4 *
              (n : ℝ) * (Real.log (n : ℝ)) ^ 6) / (Real.log 2) ^ 6 := by
          apply div_le_div_of_nonneg_right _ hq6_pos.le
          nlinarith [mul_pos hn_pos (pow_pos hL_pos 6)]
        _ = c * (n : ℝ) * (Real.log (n : ℝ)) ^ 10 := by
          rw [hpow10]
          field_simp [hq6_pos.ne']
    calc
      -c * (n : ℝ) / ((Real.log (n : ℝ)) ^ 6 / (Real.log 2) ^ 6) =
          -(c * (n : ℝ) / ((Real.log (n : ℝ)) ^ 6 / (Real.log 2) ^ 6)) := by ring
      _ ≤ -(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := neg_le_neg hineq
      _ = -2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by ring
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have hshift :
      Summable (fun k : ℕ ↦
        Real.exp (-c * ((k + N₀ : ℕ) : ℝ) / (Real.logb 2 ((k + N₀ : ℕ) : ℝ)) ^ 6)) :=
    Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
      (fun k ↦ hN₀ (k + N₀) (Nat.le_add_left N₀ k))
      (summable_quasiExpTail.comp_injective (add_left_injective N₀))
  exact (summable_nat_add_iff N₀).mp hshift

/-- **Phase Refinement Borel–Cantelli summability:**
`∑_{n ≥ 0} exp(-n (log log n)² / (2 (log n)⁸)) < ∞`. -/
theorem summable_phaseRefinementSubgaussianTail :
    Summable (fun n : ℕ ↦
      Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (2 * (Real.log (n : ℝ)) ^ 8))) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hev : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (2 * (Real.log (n : ℝ)) ^ 8)) ≤
        quasiExpTail n := by
    filter_upwards [eventually_ge_atTop 3,
      hloglog.eventually_ge_atTop 1, hlog.eventually_ge_atTop 2] with n hn3 hll1 hL_ge2
    have hL2 : 4 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn1
    unfold quasiExpTail
    apply Real.exp_le_exp.mpr
    have hll_sq : 1 ≤ (Real.log (Real.log (n : ℝ))) ^ 2 := by nlinarith
    have hineq :
        2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 ≤
          (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (2 * (Real.log (n : ℝ)) ^ 8) := by
      rw [div_le_div_iff₀ (pow_pos hL_pos 10) (by positivity)]
      have hpow10 : (Real.log (n : ℝ)) ^ 10 =
          (Real.log (n : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 8 := by ring
      rw [hpow10]
      calc
        2 * (n : ℝ) * (2 * (Real.log (n : ℝ)) ^ 8) =
            4 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 8) := by ring
        _ ≤ (Real.log (n : ℝ)) ^ 2 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 8) :=
          mul_le_mul_of_nonneg_right hL2 (by positivity)
        _ = 1 * ((Real.log (n : ℝ)) ^ 2 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 8)) := by ring
        _ ≤ (Real.log (Real.log (n : ℝ))) ^ 2 *
              ((Real.log (n : ℝ)) ^ 2 * ((n : ℝ) * (Real.log (n : ℝ)) ^ 8)) :=
          mul_le_mul_of_nonneg_right hll_sq (by positivity)
        _ = (n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 *
              ((Real.log (n : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 8) := by ring
    calc
      -(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (2 * (Real.log (n : ℝ)) ^ 8) =
          -((n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 / (2 * (Real.log (n : ℝ)) ^ 8)) := by ring
      _ ≤ -(2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10) := neg_le_neg hineq
      _ = -2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 10 := by ring
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
  have hshift :
      Summable (fun k : ℕ ↦
        Real.exp (-((k + N₀ : ℕ) : ℝ) * (Real.log (Real.log ((k + N₀ : ℕ) : ℝ))) ^ 2 /
          (2 * (Real.log ((k + N₀ : ℕ) : ℝ)) ^ 8))) :=
    Summable.of_nonneg_of_le (fun _ ↦ (Real.exp_pos _).le)
      (fun k ↦ hN₀ (k + N₀) (Nat.le_add_left N₀ k))
      (summable_quasiExpTail.comp_injective (add_left_injective N₀))
  exact (summable_nat_add_iff N₀).mp hshift

/-- **Section 9 sub-Gaussian bootstrap from `E[Y_n] → 1 / 4`:**
once `E[Y_n] → 1 / 4` is known, Corollary 8.1's oscillation-`2` sub-Gaussian bounds immediately
yield:
1. for every `ε > 0` and `ϑ ∈ (0, 1)`, eventually
   `P(|Y_n - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))`;
2. `E[exp(t Y_n)] → exp(t / 4)` for every `t ∈ ℝ` via the two-sided CGF squeeze. -/
theorem subgaussian_tail_and_mgf_of_tendsto_expected_normalizedGap
    (hexp : Tendsto (fun n : ℕ ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n)
      atTop (nhds (1 / 4 : ℝ))) :
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            {G : LabeledGraph n |
              eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    (∀ t : ℝ,
      Tendsto (fun n : ℕ ↦
        ∫ G : LabeledGraph n,
          Real.exp (t * ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))))
          ∂randomGraphMeasure n)
        atTop (nhds (Real.exp (t / 4)))) := by
  let Y : ∀ n : ℕ, LabeledGraph n → ℝ := fun n G ↦
    (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
      ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
  have hμ : (fun n : ℕ ↦ ∫ G : LabeledGraph n, Y n G ∂randomGraphMeasure n) =
      (fun n : ℕ ↦ (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n) := by
    funext n
    exact integral_const_mul _ _
  have hμ_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ G : LabeledGraph n, Y n G ∂randomGraphMeasure n)
        atTop (nhds (1 / 4 : ℝ)) := by
    rwa [hμ]
  refine ⟨?_, ?_⟩
  · intro eps theta heps htheta
    have hgap_pos : 0 < (1 - theta) * eps := mul_pos (by linarith [htheta.2]) heps
    have hclose : ∀ᶠ n : ℕ in atTop,
        |(∫ G : LabeledGraph n, Y n G ∂randomGraphMeasure n) - 1 / 4| ≤ (1 - theta) * eps := by
      filter_upwards [(Metric.tendsto_nhds.mp hμ_tendsto ((1 - theta) * eps) hgap_pos)] with n hn
      rw [Real.dist_eq] at hn
      exact hn.le
    filter_upwards [eventually_ge_atTop 2, hclose] with n hn2 hnclose
    have hsub :
        {G : LabeledGraph n | eps < |Y n G - 1 / 4|} ⊆
          {G : LabeledGraph n |
            theta * eps ≤ |Y n G - ∫ H, Y n H ∂randomGraphMeasure n|} := by
      intro G hG
      simp only [Set.mem_setOf_eq] at hG ⊢
      have htri : |Y n G - 1 / 4| ≤
          |Y n G - ∫ H, Y n H ∂randomGraphMeasure n| +
            |(∫ H, Y n H ∂randomGraphMeasure n) - 1 / 4| := by
        have h1 : Y n G - 1 / 4 =
            (Y n G - ∫ H, Y n H ∂randomGraphMeasure n) +
              ((∫ H, Y n H ∂randomGraphMeasure n) - 1 / 4) := by ring
        rw [h1]
        exact abs_add_le _ _
      linarith
    have htail := randomGraph_abs_normalizedGap_sub_mean_ge_le hn2
      (mul_nonneg htheta.1.le heps.le)
    have hrew : -(theta * eps) ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) =
        -theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6) := by ring
    rw [hrew] at htail
    exact (measureReal_mono hsub).trans htail
  · intro t
    have hlo_lim :
        Tendsto (fun n : ℕ ↦ Real.exp (t * ∫ G, Y n G ∂randomGraphMeasure n))
          atTop (nhds (Real.exp (t / 4))) := by
      have hmul_lim :
          Tendsto (fun n : ℕ ↦ t * ∫ G, Y n G ∂randomGraphMeasure n)
            atTop (nhds (t / 4)) := by
        have h0 := hμ_tendsto.const_mul t
        rwa [show t * (1 / 4 : ℝ) = t / 4 by ring] at h0
      exact (Real.continuous_exp.tendsto (t / 4)).comp hmul_lim
    have herr_zero :
        Tendsto (fun n : ℕ ↦ t ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ)))
          atTop (nhds 0) := by
      have hq6_pos : 0 < (Real.log 2) ^ 6 := pow_pos (Real.log_pos one_lt_two) 6
      have hlittle := Real.isLittleO_pow_log_id_atTop (n := 6)
      have hdiv0 : Tendsto (fun x : ℝ ↦ (Real.log x) ^ 6 / x) atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hlittle.tendsto_div_nhds_zero
      have hnat : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ 6 / (n : ℝ)) atTop (nhds 0) :=
        hdiv0.comp tendsto_natCast_atTop_atTop
      have hmul := hnat.const_mul (t ^ 2 / (2 * (Real.log 2) ^ 6))
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      rw [Real.logb, div_pow]
      field_simp [hn_pos.ne', hq6_pos.ne']
    have hhi_lim :
        Tendsto (fun n : ℕ ↦
          Real.exp (t * ∫ G, Y n G ∂randomGraphMeasure n) *
            Real.exp (t ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))))
          atTop (nhds (Real.exp (t / 4))) := by
      have hexp0 :
          Tendsto (fun n : ℕ ↦ Real.exp (t ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))))
            atTop (nhds 1) := by
        have h0 : Tendsto
            (fun n : ℕ ↦ Real.exp (t ^ 2 * (Real.logb 2 (n : ℝ)) ^ 6 / (2 * (n : ℝ))))
            atTop (nhds (Real.exp 0)) :=
          (Real.continuous_exp.tendsto 0).comp herr_zero
        rwa [Real.exp_zero] at h0
      have h0 := hlo_lim.mul hexp0
      rwa [mul_one] at h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hhi_lim ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn2
      exact (mgf_normalizedGap_bounds hn2 t).1
    · filter_upwards [eventually_ge_atTop 2] with n hn2
      exact (mgf_normalizedGap_bounds hn2 t).2

/-- **Complete v8 Main Theorem assembly (variance, non-asymptotic mean tail, sharp sub-Gaussian
`1/4` tail, arbitrary-coupling a.s., `L^p`, expectation, and MGF convergence):**
from the `O_ε(exp(-2 n / (log n)^10))` finite-phase-cover bound, proves simultaneously:
1. `Var(χ(G_n) - ζ(G_n)) ≤ n - 1` for all `n : ℕ`;
2. `P(|Y_n - E[Y_n]| ≥ u) ≤ 2 exp(-u² n / (2 (log₂ n)⁶))` for all `n ≥ 2`, `u ≥ 0`;
3. for every `ε > 0` and `ϑ ∈ (0, 1)`, eventually
   `P(|Y_n - 1/4| > ε) ≤ 2 exp(-ϑ² ε² n / (2 (log₂ n)⁶))`;
4. arbitrary-coupling almost-sure convergence in natural and base-`2` logarithms;
5. `L^p` convergence `E[|Y_n - 1/4|^p] → 0` for every `1 ≤ p < ∞` and `E[Y_n] → 1 / 4`;
6. MGF convergence `E[exp(t Y_n)] → exp(t / 4)` for every `t ∈ ℝ`. -/
theorem mainTheorem_subgaussian_tail_ae_lp_expectation_and_mgf
    (htail : ∀ eps : ℝ, 0 < eps →
      (fun n : ℕ ↦ (randomGraphMeasure n).real
        {G : LabeledGraph n |
          eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|})
        =O[atTop] quasiExpTail) :
    (∀ n : ℕ,
      (∫ G : LabeledGraph n,
          (((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
            ∫ H : LabeledGraph n,
              ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
              ∂randomGraphMeasure n) ^ 2
          ∂randomGraphMeasure n) ≤ ((n - 1 : ℕ) : ℝ)) ∧
    (∀ {n : ℕ}, 2 ≤ n → ∀ {u : ℝ}, 0 ≤ u →
      (randomGraphMeasure n).real
          {G : LabeledGraph n |
            u ≤ |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                  ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) -
                ∫ H : LabeledGraph n,
                  (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                    ((chromaticNumberNat H : ℝ) - (cochromaticNumber H : ℝ))
                  ∂randomGraphMeasure n|} ≤
        2 * Real.exp (-u ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    (∀ {eps theta : ℝ}, 0 < eps → theta ∈ Ioo 0 1 →
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            {G : LabeledGraph n |
              eps < |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4|} ≤
          2 * Real.exp (-theta ^ 2 * eps ^ 2 * (n : ℝ) / (2 * (Real.logb 2 (n : ℝ)) ^ 6))) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
      (G : ∀ n : ℕ, Ω → LabeledGraph n),
      (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
      ∀ᵐ ω ∂ℙ,
        Tendsto (fun n : ℕ ↦
          (Real.log n) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
          atTop (nhds sharpGapConstant) ∧
        Tendsto (fun n : ℕ ↦
          (Real.logb 2 n) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ)))
          atTop (nhds (1 / 4 : ℝ))) ∧
    (∀ {p : ℝ}, 1 ≤ p →
      Tendsto (fun n : ℕ ↦
        ∫ G : LabeledGraph n,
          |(Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)) - 1 / 4| ^ p
          ∂randomGraphMeasure n)
        atTop (nhds 0)) ∧
    Tendsto (fun n : ℕ ↦
      (Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
        ∫ G : LabeledGraph n,
          ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
          ∂randomGraphMeasure n)
      atTop (nhds (1 / 4 : ℝ)) ∧
    (∀ t : ℝ,
      Tendsto (fun n : ℕ ↦
        ∫ G : LabeledGraph n,
          Real.exp (t * ((Real.logb 2 (n : ℝ)) ^ 3 / (n : ℝ) *
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))))
          ∂randomGraphMeasure n)
        atTop (nhds (Real.exp (t / 4)))) := by
  obtain ⟨hae, hlp, hexp, -⟩ := mainTheorem_ae_lp_expectation_and_mgf_of_quasiExp_tail htail
  obtain ⟨hsubg, hmgf⟩ := subgaussian_tail_and_mgf_of_tendsto_expected_normalizedGap hexp
  exact ⟨variance_chromaticSubCochromatic_le,
    fun {_} hn {_} hu ↦ randomGraph_abs_normalizedGap_sub_mean_ge_le hn hu,
    hsubg, hae, hlp, hexp, hmgf⟩

/-- **Complete v8 Phase Refinement assembly (explicit `2 exp(-n (log log n)² / (2 (log n)⁸))`
sub-Gaussian exit bound + expectation sandwich + `[0.080, 0.086]` a.s.):**
under an `O(exp(-2 n / (log n)^10))` exit tail from the `tildeEps = O(log log n / log n)`
phase interval, setting `ε_n := tildeEps n + (1 + log log n) / log n` (`n ≥ 3`, `0` otherwise)
yields:
1. `0 ≤ ε_n` for all `n` and `ε_n ≤ C₁ log log n / log n` for all `n ≥ 3`;
2. eventually `P(G_n ∉ twoSidedGapEvent (lower - ε_n) (upper + ε_n) n) ≤
   2 exp(-n (log log n)² / (2 (log n)⁸))`;
3. `((log n)³ / n) E[χ(G_n) - ζ(G_n)] ∈ [lower - ε_n, upper + ε_n]` eventually;
4. for every `c' ≤ 0.080` and `C' ≥ 0.086`, `[c', C'] · n / (log n)³` holds eventually
   both in expectation and almost surely under every `G(n, 1/2)` coupling. -/
theorem phaseRefinement_subgaussian_tail_expectation_and_ae
    (tildeEps : ℕ → ℝ)
    (htilde_nn : ∀ n, 0 ≤ tildeEps n)
    (htilde_O : tildeEps =O[atTop]
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)))
    (htail : (fun n : ℕ ↦ (randomGraphMeasure n).real
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - tildeEps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + tildeEps n) n)ᶜ)
      =O[atTop] quasiExpTail) :
    let eps : ℕ → ℝ := fun n ↦
      if 3 ≤ n then tildeEps n + (1 + Real.log (Real.log (n : ℝ))) / Real.log (n : ℝ) else 0
    (∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n, 0 ≤ eps n) ∧
      ∀ n ≥ 3, eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) ∧
    (∀ᶠ n : ℕ in atTop,
      (randomGraphMeasure n).real
          (twoSidedGapEvent
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ≤
        2 * Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 /
          (2 * (Real.log (n : ℝ)) ^ 8))) ∧
    (∀ᶠ n : ℕ in atTop,
      lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n ≤
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
        (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
          upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) ∧
    (∀ c' C' : ℝ, c' ≤ 80 / 1000 → 86 / 1000 ≤ C' →
      (∀ᶠ n : ℕ in atTop,
        c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ∧
          (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) ≤
            C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3)) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
        (G : ∀ n : ℕ, Ω → LabeledGraph n),
        (∀ n : ℕ, Measure.map (G n) ℙ = randomGraphMeasure n) →
        ∀ᵐ ω ∂ℙ, ∀ᶠ n : ℕ in atTop,
          c' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3) ≤
              (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ∧
            (chromaticNumberNat (G n ω) : ℝ) - (cochromaticNumber (G n ω) : ℝ) ≤
              C' * ((n : ℝ) / (Real.log (n : ℝ)) ^ 3))) := by
  intro eps
  obtain ⟨⟨C₀, hC₀_pos, h1_nn, h1_O⟩, -, h3_eps1, h4⟩ :=
    phaseRefinement_expectation_and_ae_of_quasiExp_tail tildeEps htilde_nn htilde_O htail
  let eps₁ : ℕ → ℝ := fun n ↦ if 3 ≤ n then tildeEps n + 1 / Real.log (n : ℝ) else 0
  have heps_rel : ∀ n ≥ 3,
      eps n = eps₁ n + Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    intro n hn3
    dsimp [eps, eps₁]
    rw [if_pos hn3, if_pos hn3]
    ring
  have hll_pos : ∀ n : ℕ, 3 ≤ n → 0 < Real.log (Real.log (n : ℝ)) := by
    intro n hn3
    have hexp1_lt_3 : Real.exp 1 < (3 : ℝ) :=
      lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hexp1_lt_n : Real.exp 1 < (n : ℝ) :=
      lt_of_lt_of_le hexp1_lt_3 (by exact_mod_cast hn3)
    have h1_lt_log : 1 < Real.log (n : ℝ) := by
      have := Real.log_lt_log (Real.exp_pos 1) hexp1_lt_n
      rwa [Real.log_exp] at this
    exact Real.log_pos h1_lt_log
  have h1_upgrade :
      ∃ C₁ : ℝ, 0 < C₁ ∧ (∀ n, 0 ≤ eps n) ∧
        ∀ n ≥ 3, eps n ≤ C₁ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
    refine ⟨C₀ + 1, by linarith, ?_, ?_⟩
    · intro n
      by_cases hn3 : 3 ≤ n
      · rw [heps_rel n hn3]
        have hL_pos : 0 < Real.log (n : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        exact add_nonneg (h1_nn n) (div_nonneg (hll_pos n hn3).le hL_pos.le)
      · dsimp [eps]; rw [if_neg hn3]
    · intro n hn3
      rw [heps_rel n hn3]
      have hb : eps₁ n ≤ C₀ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := h1_O n hn3
      have hsplit_c :
          (C₀ + 1) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) =
            C₀ * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) +
              Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by ring
      linarith
  have h3_upgrade :
      ∀ᶠ n : ℕ in atTop,
        lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n ≤
            (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              (∫ G : LabeledGraph n,
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
                ∂randomGraphMeasure n) ∧
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
              (∫ G : LabeledGraph n,
                ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
                ∂randomGraphMeasure n) ≤
            upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n := by
    filter_upwards [eventually_ge_atTop 3, h3_eps1] with n hn3 ⟨hlo, hhi⟩
    have hL_pos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hpos_add : 0 ≤ Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) :=
      div_nonneg (hll_pos n hn3).le hL_pos.le
    have hlo' :
        lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps₁ n ≤
          (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
            (∫ G : LabeledGraph n,
              ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
              ∂randomGraphMeasure n) := hlo
    have hhi' :
        (Real.log (n : ℝ)) ^ 3 / (n : ℝ) *
          (∫ G : LabeledGraph n,
            ((chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ))
            ∂randomGraphMeasure n) ≤
        upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps₁ n := hhi
    rw [heps_rel n hn3]
    exact ⟨by linarith, by linarith⟩
  have h2_subg :
      ∀ᶠ n : ℕ in atTop,
        (randomGraphMeasure n).real
            (twoSidedGapEvent
              (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
              (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ≤
          2 * Real.exp (-(n : ℝ) * (Real.log (Real.log (n : ℝ))) ^ 2 /
            (2 * (Real.log (n : ℝ)) ^ 8)) := by
    filter_upwards [eventually_ge_atTop 3, h3_eps1] with n hn3 ⟨hlo, hhi⟩
    have hn2 : 2 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have hL_pos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hll_n_pos : 0 < Real.log (Real.log (n : ℝ)) := hll_pos n hn3
    set L : ℝ := Real.log (n : ℝ)
    set ell : ℝ := Real.log (Real.log (n : ℝ))
    set D : LabeledGraph n → ℝ := fun G ↦ (chromaticNumberNat G : ℝ) - (cochromaticNumber G : ℝ)
    set meanD : ℝ := ∫ G : LabeledGraph n, D G ∂randomGraphMeasure n
    set t : ℝ := (n : ℝ) * ell / L ^ 4
    have ht_nn : 0 ≤ t := by positivity
    have hsub :
        (twoSidedGapEvent
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps n)
          (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps n) n)ᶜ ⊆
        {G : LabeledGraph n | t ≤ |D G - meanD|} := by
      intro G hGnot
      rw [Set.mem_setOf_eq]
      by_contra hlt_not
      have habs : |D G - meanD| < t := not_le.mp hlt_not
      obtain ⟨hD_lo, hD_hi⟩ := abs_lt.mp habs
      apply hGnot
      unfold twoSidedGapEvent
      rw [Set.mem_setOf_eq]
      rw [heps_rel n hn3]
      have hfac_pos : 0 < (n : ℝ) / L ^ 3 := by positivity
      have hmean_lo :
          (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps₁ n) * ((n : ℝ) / L ^ 3) ≤
            meanD := by
        have hm := mul_le_mul_of_nonneg_right hlo hfac_pos.le
        have hrhs : L ^ 3 / (n : ℝ) * meanD * ((n : ℝ) / L ^ 3) = meanD := by
          field_simp [hn_pos.ne', hL_pos.ne']
        dsimp [eps₁, L, meanD, D] at hm hrhs ⊢
        linarith
      have hmean_hi :
          meanD ≤
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps₁ n) * ((n : ℝ) / L ^ 3) := by
        have hm := mul_le_mul_of_nonneg_right hhi hfac_pos.le
        have hlhs : L ^ 3 / (n : ℝ) * meanD * ((n : ℝ) / L ^ 3) = meanD := by
          field_simp [hn_pos.ne', hL_pos.ne']
        dsimp [eps₁, L, meanD, D] at hm hlhs ⊢
        linarith
      have ht_eq : (ell / L) * ((n : ℝ) / L ^ 3) = t := by
        dsimp [t]
        field_simp [hL_pos.ne']
      refine ⟨?_, ?_⟩
      · have hexpand :
            (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - (eps₁ n + ell / L)) *
                ((n : ℝ) / L ^ 3) =
              (lowerPhaseCoeff7 (shiftedPhase (phaseDelta n)) - eps₁ n) * ((n : ℝ) / L ^ 3) - t := by
          rw [← ht_eq]; ring
        dsimp [L, ell, D] at hexpand ⊢
        linarith
      · have hexpand :
            (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + (eps₁ n + ell / L)) *
                ((n : ℝ) / L ^ 3) =
              (upperPhaseCoeff7 (shiftedPhase (phaseDelta n)) + eps₁ n) * ((n : ℝ) / L ^ 3) + t := by
          rw [← ht_eq]; ring
        dsimp [L, ell, D] at hexpand ⊢
        linarith
    have hconc := randomGraph_abs_chromaticSubCochromatic_sub_mean_ge_le hn2 ht_nn
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    have hexp_le :
        Real.exp (-t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) ≤
          Real.exp (-(n : ℝ) * ell ^ 2 / (2 * L ^ 8)) := by
      apply Real.exp_le_exp.mpr
      have hden :
          t ^ 2 / (2 * (n : ℝ)) ≤ t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      have hident : t ^ 2 / (2 * (n : ℝ)) = (n : ℝ) * ell ^ 2 / (2 * L ^ 8) := by
        dsimp [t]
        field_simp [hn_pos.ne', hL_pos.ne']
      calc
        -t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ)) =
            -(t ^ 2 / (2 * ((n - 1 : ℕ) : ℝ))) := by ring
        _ ≤ -(t ^ 2 / (2 * (n : ℝ))) := neg_le_neg hden
        _ = -((n : ℝ) * ell ^ 2 / (2 * L ^ 8)) := by rw [hident]
        _ = -(n : ℝ) * ell ^ 2 / (2 * L ^ 8) := by ring
    exact (measureReal_mono hsub).trans (hconc.trans (by linarith))
  exact ⟨h1_upgrade, h2_subg, h3_upgrade, h4⟩

end

end Erdos625HP
