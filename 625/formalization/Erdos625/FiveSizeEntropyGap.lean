import Erdos625.UniformExplicitPartitionRatio

/-!
# The five-size entropy gap (v2 manuscript, Lemma `lem:entropy-gap`)

This standalone module states, with the manuscript's own definitions, the
five-size entropy bound of the v2 Erdős 625 manuscript and proves it.  It is
**not** imported by `Erdos625.lean`; the released theorem `Erdos625.erdos625`
still carries the v1 constant `log (200 / 153)`.

## Source-facing definitions (main theorem and Section 5 of the v2 manuscript)

* `gaussWeight lambda i = exp (lambda * i - (log 2 / 2) * i ^ 2)`  (`w_i(λ)`),
* `Splus = {i : ℤ | -1 ≤ i}`, `S5 = {2,3,4,5,6}`, `S4 = {2,3,4,5}`,
* `partitionFn S lambda = ∑' i : S, gaussWeight lambda i`  (`Z_S(λ)`),
* `dualValue S T = ⨅ lambda : ℝ, (log (partitionFn S lambda) - lambda * T)`
  (`𝓕_S(T)`),
* `phaseTarget delta = 1 + 2 / log 2 - delta`  (`T_δ`),
* `phaseGain5 delta = log 2 - 𝓕_{S₊}(T_δ) + 𝓕_{S₅}(T_δ)`  (`A₅(δ)`), and the
  comparison quantities `phaseGain4` (`A₄`), `entropyLoss5` (`D₅`),
  `entropyLoss4` (`D₄`), `gamma5 = log (8750 / 6681)` (`γ₅`).

Because `tsum` returns `0` on non-summable families and `⨅` over `ℝ` returns
`0` on sets that are not bounded below, the module also proves that these
junk values never occur on the source domain:
`hasSum_partitionFn` (every `Z_S(λ)` is a genuine convergent sum) and
`isGLB_dualValue` (for `S ∈ {S₄, S₅, S₊}` and `T ∈ (2,5)`, `dualValue S T`
is the genuine greatest lower bound of the dual objective).

## Main results

* `entropy_gap` — the full statement (5.3) of Lemma `lem:entropy-gap`:
  for `0 ≤ δ ≤ 1`,
  `A₅(δ) - A₄(δ) > log (525/524)`, `0 ≤ D₅(δ) < log (6681/4375)` and
  `A₅(δ) > γ₅ = log (8750/6681)`;
* `four_size_entropy_certificate` — Lemma `lem:four-size-entropy-certificate`
  with the manuscript's literal infimum definitions;
* `log_8750_div_6681_lt_phaseGain5` — the bound `A₅(δ) > log (8750/6681)`
  asserted in the main theorem;
* `phaseGain5_uniform_margin` — the explicit uniform margin
  `A₅(δ) > log (8750/6681) + log (273004/273000)` on `[0,1]`.

## Proof route

The four-size input is the repository's verified uniform partition-ratio
estimate `uniform_four_size_partition_ratio_for_delta`
(`Z_{S₊}(λ₄)/Z_{S₄}(λ₄) < 153/100` at the four-size tilt `λ₄ = λ_{S₄}(T_δ)`).
The five-size step replaces the manuscript's argument through the five-size
optimizer by an equivalent elementary one that needs no five-point tilt:
for every finite support the inequality `exp x ≥ 1 + x` gives the tangent
bound `Z(λ) e^{-λT} ≥ Z(μ) e^{-μT} (1 + (λ-μ)(M(μ) - T))`; with
`Z_{S₅}(λ) ≥ (521/520) Z_{S₄}(λ)` for `λ ≥ 2 log 2` and
`M_{S₅}(2 log 2) < 14/5 ≤ T_δ` this yields
`𝓕_{S₅}(T_δ) ≥ 𝓕_{S₄}(T_δ) + log (521/520)` uniformly in `δ`.
-/

namespace Erdos625

namespace FiveSizeEntropyGap

open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section

/-! ## Source-facing definitions -/

/-- The limiting weight `w_i(λ) = exp (λ i - (log 2 / 2) i²)` of the
manuscript, at an integer deficit `i`. -/
def gaussWeight (lambda : ℝ) (i : ℤ) : ℝ :=
  Real.exp (lambda * (i : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2)

/-- The unrestricted support `S₊ = {i ∈ ℤ : i ≥ -1}`. -/
def Splus : Set ℤ := {i : ℤ | -1 ≤ i}

/-- The five-size support `S₅ = {2,3,4,5,6}`. -/
def S5 : Set ℤ := {2, 3, 4, 5, 6}

/-- The four-size comparison support `S₄ = {2,3,4,5}` of Section 5. -/
def S4 : Set ℤ := {2, 3, 4, 5}

/-- The partition function `Z_S(λ) = ∑_{i ∈ S} w_i(λ)`. -/
def partitionFn (S : Set ℤ) (lambda : ℝ) : ℝ :=
  ∑' i : S, gaussWeight lambda i

/-- The dual value `𝓕_S(T) = inf_{λ ∈ ℝ} { log Z_S(λ) - λ T }`. -/
def dualValue (S : Set ℤ) (T : ℝ) : ℝ :=
  ⨅ lambda : ℝ, (Real.log (partitionFn S lambda) - lambda * T)

/-- The phase target `T_δ = 1 + 2 / log 2 - δ`. -/
def phaseTarget (delta : ℝ) : ℝ :=
  1 + 2 / Real.log 2 - delta

/-- The five-size phase gain `A₅(δ) = log 2 - 𝓕_{S₊}(T_δ) + 𝓕_{S₅}(T_δ)`. -/
def phaseGain5 (delta : ℝ) : ℝ :=
  Real.log 2 - dualValue Splus (phaseTarget delta) +
    dualValue S5 (phaseTarget delta)

/-- The four-size comparison gain `A₄(δ) = q - 𝓕_{S₊}(T_δ) + 𝓕_{S₄}(T_δ)`,
with `q = log 2`. -/
def phaseGain4 (delta : ℝ) : ℝ :=
  Real.log 2 - dualValue Splus (phaseTarget delta) +
    dualValue S4 (phaseTarget delta)

/-- The five-size entropy loss `D₅(δ) = 𝓕_{S₊}(T_δ) - 𝓕_{S₅}(T_δ)`. -/
def entropyLoss5 (delta : ℝ) : ℝ :=
  dualValue Splus (phaseTarget delta) - dualValue S5 (phaseTarget delta)

/-- The four-size entropy loss `D₄(δ) = q - A₄(δ)`. -/
def entropyLoss4 (delta : ℝ) : ℝ :=
  dualValue Splus (phaseTarget delta) - dualValue S4 (phaseTarget delta)

/-- The uniform constant `γ₅ = log (8750 / 6681)` of (5.2). -/
def gamma5 : ℝ :=
  Real.log (8750 / 6681)

/-! ## Elementary facts about the weights -/

theorem gaussWeight_pos (lambda : ℝ) (i : ℤ) : 0 < gaussWeight lambda i :=
  Real.exp_pos _

theorem gaussWeight_eq_exp (lambda : ℝ) (i : ℤ) (c : ℝ)
    (h : lambda * (i : ℝ) - Real.log 2 / 2 * (i : ℝ) ^ 2 = c) :
    gaussWeight lambda i = Real.exp c := by
  unfold gaussWeight
  rw [h]

/-- Changing the tilt multiplies each weight by an exponential factor. -/
theorem gaussWeight_shift (lambda mu : ℝ) (i : ℤ) :
    gaussWeight lambda i = gaussWeight mu i * Real.exp ((lambda - mu) * (i : ℝ)) := by
  unfold gaussWeight
  rw [← Real.exp_add]
  congr 1
  ring

/-- The weights are summable over all of `ℤ`. -/
theorem summable_gaussWeight (lambda : ℝ) : Summable (gaussWeight lambda) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · refine (summable_extendedGaussianNaturalTerm (a := q) (lambda := lambda)
      q_pos).congr (fun n => ?_)
    unfold gaussWeight extendedGaussianNaturalTerm q
    simp
  · refine (summable_extendedGaussianNaturalTerm (a := q) (lambda := -lambda)
      q_pos).congr (fun n => ?_)
    unfold gaussWeight extendedGaussianNaturalTerm q
    congr 1
    push_cast
    ring

/-- **Fidelity of `Z_S`.** For every `S ⊆ ℤ` and every real tilt, the `tsum`
defining `partitionFn S lambda` is a genuine convergent sum. -/
theorem hasSum_partitionFn (S : Set ℤ) (lambda : ℝ) :
    HasSum (fun i : S => gaussWeight lambda i) (partitionFn S lambda) :=
  ((summable_gaussWeight lambda).subtype (· ∈ S)).hasSum

/-- Enlarging the support enlarges the partition function. -/
theorem partitionFn_mono {S S' : Set ℤ} (h : S ⊆ S') (lambda : ℝ) :
    partitionFn S lambda ≤ partitionFn S' lambda := by
  unfold partitionFn
  rw [tsum_subtype S (gaussWeight lambda), tsum_subtype S' (gaussWeight lambda)]
  refine Summable.tsum_le_tsum (fun i => ?_)
    ((summable_gaussWeight lambda).indicator S)
    ((summable_gaussWeight lambda).indicator S')
  by_cases hi : i ∈ S
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem (h hi)]
  · rw [Set.indicator_of_notMem hi]
    exact Set.indicator_nonneg (fun j _ => (gaussWeight_pos lambda j).le) i

/-- On a finite support the partition function is the finite sum. -/
theorem partitionFn_coe_finset (F : Finset ℤ) (lambda : ℝ) :
    partitionFn (F : Set ℤ) lambda = ∑ i ∈ F, gaussWeight lambda i := by
  unfold partitionFn
  exact Finset.tsum_subtype' F (gaussWeight lambda)

/-! ## The finite supports as finsets -/

/-- `S₄` as a finset. -/
def F4 : Finset ℤ := {2, 3, 4, 5}

/-- `S₅` as a finset. -/
def F5 : Finset ℤ := {2, 3, 4, 5, 6}

theorem coe_F4 : (F4 : Set ℤ) = S4 := by
  ext i
  simp [F4, S4]

theorem coe_F5 : (F5 : Set ℤ) = S5 := by
  ext i
  simp [F5, S5]

theorem F4_nonempty : F4.Nonempty := ⟨2, by simp [F4]⟩

theorem F5_nonempty : F5.Nonempty := ⟨2, by simp [F5]⟩

theorem sum_F4 (f : ℤ → ℝ) : ∑ i ∈ F4, f i = f 2 + f 3 + f 4 + f 5 := by
  have h : F4 = insert 2 (insert 3 (insert 4 {5})) := rfl
  rw [h, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_singleton]
  ring

theorem sum_F5 (f : ℤ → ℝ) :
    ∑ i ∈ F5, f i = f 2 + f 3 + f 4 + f 5 + f 6 := by
  have h : F5 = insert 2 (insert 3 (insert 4 (insert 5 {6}))) := rfl
  rw [h, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  ring

theorem partitionFn_S4 (lambda : ℝ) :
    partitionFn S4 lambda = ∑ i ∈ F4, gaussWeight lambda i := by
  rw [← coe_F4]
  exact partitionFn_coe_finset F4 lambda

theorem partitionFn_S5 (lambda : ℝ) :
    partitionFn S5 lambda = ∑ i ∈ F5, gaussWeight lambda i := by
  rw [← coe_F5]
  exact partitionFn_coe_finset F5 lambda

theorem sum_gaussWeight_pos (F : Finset ℤ) (hF : F.Nonempty) (lambda : ℝ) :
    0 < ∑ i ∈ F, gaussWeight lambda i :=
  Finset.sum_pos (fun i _ => gaussWeight_pos lambda i) hF

theorem S4_subset_S5 : S4 ⊆ S5 := by
  intro i hi
  simp only [S4, S5, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  omega

theorem S5_subset_Splus : S5 ⊆ Splus := by
  intro i hi
  simp only [S5, Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  show (-1 : ℤ) ≤ i
  omega

theorem S4_subset_Splus : S4 ⊆ Splus :=
  Set.Subset.trans S4_subset_S5 S5_subset_Splus

/-! ## The unrestricted support and the repository's extended profile -/

/-- `Z_{S₊}(λ)` is the repository's `extendedGaussianPartition q λ`
(exceptional atom at `-1` plus the natural-deficit `tsum`). -/
theorem hasSum_gaussWeight_Splus (lambda : ℝ) :
    HasSum (fun i : Splus => gaussWeight lambda i)
      (extendedGaussianPartition q lambda) := by
  refine (hasSum_subtype_iff_indicator (f := gaussWeight lambda) (s := Splus)).mpr ?_
  have h1 : HasSum (fun n : ℕ => Splus.indicator (gaussWeight lambda) (n : ℤ))
      (∑' n : ℕ, extendedGaussianNaturalTerm q lambda n) := by
    have hs := (summable_extendedGaussianNaturalTerm (a := q) (lambda := lambda)
      q_pos).hasSum
    convert hs using 1
    funext n
    have hmem : (n : ℤ) ∈ Splus := by
      show (-1 : ℤ) ≤ (n : ℤ)
      omega
    rw [Set.indicator_of_mem hmem]
    unfold gaussWeight extendedGaussianNaturalTerm q
    simp
  have h2 : HasSum (fun n : ℕ => Splus.indicator (gaussWeight lambda) (-((n : ℤ) + 1)))
      (extendedGaussianExceptionalAtom q lambda) := by
    have hfun : (fun n : ℕ => Splus.indicator (gaussWeight lambda) (-((n : ℤ) + 1))) =
        fun n : ℕ => if n = 0 then extendedGaussianExceptionalAtom q lambda else 0 := by
      funext n
      by_cases hn : n = 0
      · subst hn
        have hmem : (-(((0 : ℕ) : ℤ) + 1)) ∈ Splus := by
          show (-1 : ℤ) ≤ -(((0 : ℕ) : ℤ) + 1)
          omega
        rw [Set.indicator_of_mem hmem, if_pos rfl]
        unfold gaussWeight extendedGaussianExceptionalAtom q
        congr 1
        push_cast
        ring
      · have hnot : (-((n : ℤ) + 1)) ∉ Splus := by
          intro h
          have h' : (-1 : ℤ) ≤ -((n : ℤ) + 1) := h
          omega
        rw [Set.indicator_of_notMem hnot, if_neg hn]
    rw [hfun]
    exact hasSum_ite_eq 0 _
  have h := h1.of_nat_of_neg_add_one h2
  convert h using 1
  rw [extendedGaussianPartition]
  ring

theorem partitionFn_Splus (lambda : ℝ) :
    partitionFn Splus lambda = extendedGaussianPartition q lambda :=
  (hasSum_gaussWeight_Splus lambda).tsum_eq

/-! ## The four-size support and the repository's `ProfileEntropyS4` -/

theorem unnormalized_eq_gaussWeight (lambda : ℝ) (i : Fin 4) (k : ℤ)
    (hk : ProfileEntropyS4.support i = (k : ℝ)) :
    ProfileEntropyS4.unnormalized fourGaussianScore lambda i = gaussWeight lambda k := by
  unfold ProfileEntropyS4.unnormalized fourGaussianScore gaussWeight q
  rw [hk]
  congr 1
  ring

theorem partition_four_eq (lambda : ℝ) :
    ProfileEntropyS4.partition fourGaussianScore lambda =
      gaussWeight lambda 2 + gaussWeight lambda 3 + gaussWeight lambda 4 +
        gaussWeight lambda 5 := by
  unfold ProfileEntropyS4.partition
  rw [Fin.sum_univ_four, unnormalized_eq_gaussWeight lambda 0 2 (by norm_num),
    unnormalized_eq_gaussWeight lambda 1 3 (by norm_num),
    unnormalized_eq_gaussWeight lambda 2 4 (by norm_num),
    unnormalized_eq_gaussWeight lambda 3 5 (by norm_num)]

theorem firstNumerator_four_eq (lambda : ℝ) :
    ProfileEntropyS4.firstNumerator fourGaussianScore lambda =
      2 * gaussWeight lambda 2 + 3 * gaussWeight lambda 3 +
        4 * gaussWeight lambda 4 + 5 * gaussWeight lambda 5 := by
  unfold ProfileEntropyS4.firstNumerator
  rw [Fin.sum_univ_four, unnormalized_eq_gaussWeight lambda 0 2 (by norm_num),
    unnormalized_eq_gaussWeight lambda 1 3 (by norm_num),
    unnormalized_eq_gaussWeight lambda 2 4 (by norm_num),
    unnormalized_eq_gaussWeight lambda 3 5 (by norm_num)]
  simp only [ProfileEntropyS4.support_zero, ProfileEntropyS4.support_one,
    ProfileEntropyS4.support_two, ProfileEntropyS4.support_three]

/-- A four-size tilt with mean `T` balances the centred first moment. -/
theorem mean_condition {T lambda : ℝ}
    (h : ProfileEntropyS4.mean fourGaussianScore lambda = T) :
    ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight lambda i = 0 := by
  have hpos := ProfileEntropyS4.partition_pos fourGaussianScore lambda
  unfold ProfileEntropyS4.mean at h
  rw [div_eq_iff hpos.ne', firstNumerator_four_eq, partition_four_eq] at h
  rw [sum_F4]
  push_cast
  linear_combination h

/-! ## The tangent bound for finite exponential sums -/

theorem log_sub_mul_eq {Z : ℝ} (hZ : 0 < Z) (lambda T : ℝ) :
    Real.log Z - lambda * T = Real.log (Z * Real.exp (-(lambda * T))) := by
  rw [Real.log_mul hZ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- Supporting-line inequality for `λ ↦ Z_F(λ) e^{-λT}` on a finite support,
from `exp x ≥ 1 + x`. -/
theorem tangent_finset (F : Finset ℤ) (T mu lambda : ℝ) :
    (∑ i ∈ F, gaussWeight mu i) * Real.exp (-(mu * T)) +
        (lambda - mu) * Real.exp (-(mu * T)) *
          ∑ i ∈ F, ((i : ℝ) - T) * gaussWeight mu i ≤
      (∑ i ∈ F, gaussWeight lambda i) * Real.exp (-(lambda * T)) := by
  calc
    (∑ i ∈ F, gaussWeight mu i) * Real.exp (-(mu * T)) +
        (lambda - mu) * Real.exp (-(mu * T)) *
          ∑ i ∈ F, ((i : ℝ) - T) * gaussWeight mu i =
        ∑ i ∈ F, (gaussWeight mu i * Real.exp (-(mu * T)) +
          (lambda - mu) * Real.exp (-(mu * T)) *
            (((i : ℝ) - T) * gaussWeight mu i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ ∑ i ∈ F, gaussWeight lambda i * Real.exp (-(lambda * T)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hshift : gaussWeight lambda i * Real.exp (-(lambda * T)) =
          gaussWeight mu i * Real.exp (-(mu * T)) *
            Real.exp ((lambda - mu) * ((i : ℝ) - T)) := by
        unfold gaussWeight
        simp only [← Real.exp_add]
        congr 1
        ring
      have ha : 0 ≤ gaussWeight mu i * Real.exp (-(mu * T)) :=
        (mul_pos (gaussWeight_pos mu i) (Real.exp_pos _)).le
      rw [hshift]
      calc
        gaussWeight mu i * Real.exp (-(mu * T)) +
            (lambda - mu) * Real.exp (-(mu * T)) *
              (((i : ℝ) - T) * gaussWeight mu i) =
            gaussWeight mu i * Real.exp (-(mu * T)) *
              ((lambda - mu) * ((i : ℝ) - T) + 1) := by
          ring
        _ ≤ gaussWeight mu i * Real.exp (-(mu * T)) *
              Real.exp ((lambda - mu) * ((i : ℝ) - T)) :=
          mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) ha
    _ = (∑ i ∈ F, gaussWeight lambda i) * Real.exp (-(lambda * T)) := by
      rw [Finset.sum_mul]

/-- At a four-size tilt with mean `T`, the four-size dual objective is
minimized. -/
theorem four_dual_tangent {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) (lambda : ℝ) :
    (∑ i ∈ F4, gaussWeight l4 i) * Real.exp (-(l4 * T)) ≤
      (∑ i ∈ F4, gaussWeight lambda i) * Real.exp (-(lambda * T)) := by
  have h := tangent_finset F4 T l4 lambda
  rw [hmean, mul_zero, add_zero] at h
  exact h

/-! ## Explicit weights at the tilt `2 log 2` -/

theorem sqrt_two_facts :
    0 < Real.exp (Real.log 2 / 2) ∧ Real.exp (Real.log 2 / 2) ^ 2 = 2 ∧
      (7 / 5 : ℝ) ≤ Real.exp (Real.log 2 / 2) ∧
        Real.exp (Real.log 2 / 2) ≤ 71 / 50 := by
  have hpos := Real.exp_pos (Real.log 2 / 2)
  have hsq : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [sq, ← Real.exp_add,
      show Real.log 2 / 2 + Real.log 2 / 2 = Real.log 2 by ring,
      Real.exp_log (by norm_num)]
  refine ⟨hpos, hsq, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- With `u = exp (log 2 / 2) = √2`, the five weights at tilt `2 log 2` are
`4, 2u, 1, 1/(4u), 1/64`. -/
theorem weights_at_two_log_two :
    gaussWeight (2 * Real.log 2) 2 = 4 ∧
      gaussWeight (2 * Real.log 2) 3 = 2 * Real.exp (Real.log 2 / 2) ∧
      gaussWeight (2 * Real.log 2) 4 = 1 ∧
      gaussWeight (2 * Real.log 2) 5 * (4 * Real.exp (Real.log 2 / 2)) = 1 ∧
      gaussWeight (2 * Real.log 2) 6 = 1 / 64 := by
  obtain ⟨-, hsq, -, -⟩ := sqrt_two_facts
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gaussWeight_eq_exp (2 * Real.log 2) 2 (((2 : ℕ) : ℝ) * Real.log 2)
        (by push_cast; ring),
      Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  · rw [gaussWeight_eq_exp (2 * Real.log 2) 3 (((3 : ℕ) : ℝ) * (Real.log 2 / 2))
        (by push_cast; ring),
      Real.exp_nat_mul]
    have h3 : Real.exp (Real.log 2 / 2) ^ 3 =
        Real.exp (Real.log 2 / 2) ^ 2 * Real.exp (Real.log 2 / 2) := by ring
    rw [h3, hsq]
  · rw [gaussWeight_eq_exp (2 * Real.log 2) 4 0 (by push_cast; ring), Real.exp_zero]
  · rw [gaussWeight_eq_exp (2 * Real.log 2) 5 (-(((5 : ℕ) : ℝ) * (Real.log 2 / 2)))
        (by push_cast; ring)]
    have h5 : 4 * Real.exp (Real.log 2 / 2) = Real.exp (Real.log 2 / 2) ^ 5 := by
      have : Real.exp (Real.log 2 / 2) ^ 5 =
          (Real.exp (Real.log 2 / 2) ^ 2) ^ 2 * Real.exp (Real.log 2 / 2) := by ring
      rw [this, hsq]
      norm_num
    rw [h5, ← Real.exp_nat_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  · rw [gaussWeight_eq_exp (2 * Real.log 2) 6 (-(((6 : ℕ) : ℝ) * Real.log 2))
        (by push_cast; ring),
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num

theorem weight5_at_two_log_two_le :
    gaussWeight (2 * Real.log 2) 5 ≤ 5 / 28 := by
  obtain ⟨-, -, -, h5, -⟩ := weights_at_two_log_two
  obtain ⟨-, -, hu_lo, -⟩ := sqrt_two_facts
  have hw5 := gaussWeight_pos (2 * Real.log 2) 5
  nlinarith [mul_le_mul_of_nonneg_left hu_lo hw5.le]

/-- The five-size mean at tilt `2 log 2` is below `14/5`, hence below every
target `T ≥ 14/5`. -/
theorem five_mean_at_two_log_two_le {T : ℝ} (hT : 14 / 5 ≤ T) :
    ∑ i ∈ F5, ((i : ℝ) - T) * gaussWeight (2 * Real.log 2) i ≤ 0 := by
  obtain ⟨h2, h3, h4, -, h6⟩ := weights_at_two_log_two
  obtain ⟨hu, -, -, hu_hi⟩ := sqrt_two_facts
  have hw5 := gaussWeight_pos (2 * Real.log 2) 5
  have hw5le := weight5_at_two_log_two_le
  rw [sum_F5, h2, h3, h4, h6]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr hT) hu.le,
    mul_nonneg (sub_nonneg.mpr hT) hw5.le]

/-- The scalar inequality behind `five_ge_four_of_ge`, with the exponential
factors abstracted: `4 + 2u + 1 + w₅ ≤ 8.019 < 520/64` for
`u ≤ 71/50`, `w₅ ≤ 5/28`. -/
theorem five_four_scalar {E2 E3 E4 E5 E6 u w5 : ℝ}
    (e2 : E2 ≤ E6) (e3 : E3 ≤ E6) (e4 : E4 ≤ E6) (e5 : E5 ≤ E6) (hE6 : 0 < E6)
    (hu0 : 0 ≤ u) (hu : u ≤ 71 / 50) (hw0 : 0 ≤ w5) (hw : w5 ≤ 5 / 28) :
    (521 / 520 : ℝ) * (4 * E2 + 2 * u * E3 + 1 * E4 + w5 * E5) ≤
      4 * E2 + 2 * u * E3 + 1 * E4 + w5 * E5 + 1 / 64 * E6 := by
  have h3 : 2 * u * E3 ≤ 2 * u * E6 :=
    mul_le_mul_of_nonneg_left e3 (by linarith)
  have h5 : w5 * E5 ≤ w5 * E6 := mul_le_mul_of_nonneg_left e5 hw0
  have hu6 : 2 * u * E6 ≤ 2 * (71 / 50) * E6 :=
    mul_le_mul_of_nonneg_right (by linarith) hE6.le
  have hw6 : w5 * E6 ≤ 5 / 28 * E6 := mul_le_mul_of_nonneg_right hw hE6.le
  linarith

/-- For `λ ≥ 2 log 2`, the sixth weight is at least `1/520` of the four-size
partition function. -/
theorem five_ge_four_of_ge (lambda : ℝ) (hl : 2 * Real.log 2 ≤ lambda) :
    (521 / 520 : ℝ) * ∑ i ∈ F4, gaussWeight lambda i ≤
      ∑ i ∈ F5, gaussWeight lambda i := by
  obtain ⟨h2, h3, h4, -, h6⟩ := weights_at_two_log_two
  obtain ⟨hu, -, -, hu_hi⟩ := sqrt_two_facts
  have hw5 := gaussWeight_pos (2 * Real.log 2) 5
  have hw5le := weight5_at_two_log_two_le
  have hs : 0 ≤ lambda - 2 * Real.log 2 := by linarith
  have hE : ∀ k : ℤ, k ≤ 6 →
      Real.exp ((lambda - 2 * Real.log 2) * (k : ℝ)) ≤
        Real.exp ((lambda - 2 * Real.log 2) * ((6 : ℤ) : ℝ)) := by
    intro k hk
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hs
    exact_mod_cast hk
  have e2 := hE 2 (by norm_num)
  have e3 := hE 3 (by norm_num)
  have e4 := hE 4 (by norm_num)
  have e5 := hE 5 (by norm_num)
  have hE6 := Real.exp_pos ((lambda - 2 * Real.log 2) * ((6 : ℤ) : ℝ))
  rw [sum_F4, sum_F5, gaussWeight_shift lambda (2 * Real.log 2) 2,
    gaussWeight_shift lambda (2 * Real.log 2) 3,
    gaussWeight_shift lambda (2 * Real.log 2) 4,
    gaussWeight_shift lambda (2 * Real.log 2) 5,
    gaussWeight_shift lambda (2 * Real.log 2) 6, h2, h3, h4, h6]
  exact five_four_scalar e2 e3 e4 e5 hE6 hu.le hu_hi hw5.le hw5le

/-- Uniform five-size lower bound: for every tilt `λ`,
`Z_{S₅}(λ) e^{-λT} ≥ (521/520) Z_{S₄}(λ₄) e^{-λ₄T}`. -/
theorem five_tangent_lower {T l4 : ℝ} (hT : 14 / 5 ≤ T)
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) (lambda : ℝ) :
    (521 / 520 : ℝ) * ((∑ i ∈ F4, gaussWeight l4 i) * Real.exp (-(l4 * T))) ≤
      (∑ i ∈ F5, gaussWeight lambda i) * Real.exp (-(lambda * T)) := by
  have hhigh : ∀ l : ℝ, 2 * Real.log 2 ≤ l →
      (521 / 520 : ℝ) * ((∑ i ∈ F4, gaussWeight l4 i) * Real.exp (-(l4 * T))) ≤
        (∑ i ∈ F5, gaussWeight l i) * Real.exp (-(l * T)) := by
    intro l hl
    have h1 := four_dual_tangent hmean l
    have h2 := five_ge_four_of_ge l hl
    have hE := Real.exp_pos (-(l * T))
    calc
      (521 / 520 : ℝ) * ((∑ i ∈ F4, gaussWeight l4 i) * Real.exp (-(l4 * T))) ≤
          (521 / 520 : ℝ) * ((∑ i ∈ F4, gaussWeight l i) * Real.exp (-(l * T))) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = ((521 / 520 : ℝ) * ∑ i ∈ F4, gaussWeight l i) * Real.exp (-(l * T)) := by
        ring
      _ ≤ (∑ i ∈ F5, gaussWeight l i) * Real.exp (-(l * T)) :=
        mul_le_mul_of_nonneg_right h2 hE.le
  by_cases hl : 2 * Real.log 2 ≤ lambda
  · exact hhigh lambda hl
  · have hl' : lambda < 2 * Real.log 2 := not_le.mp hl
    refine (hhigh (2 * Real.log 2) le_rfl).trans ?_
    have h := tangent_finset F5 T (2 * Real.log 2) lambda
    have hS := five_mean_at_two_log_two_le hT
    have hE := Real.exp_pos (-(2 * Real.log 2 * T))
    have ha : (lambda - 2 * Real.log 2) * Real.exp (-(2 * Real.log 2 * T)) ≤ 0 := by
      nlinarith
    have hnonneg : 0 ≤ (lambda - 2 * Real.log 2) * Real.exp (-(2 * Real.log 2 * T)) *
        ∑ i ∈ F5, ((i : ℝ) - T) * gaussWeight (2 * Real.log 2) i := by
      nlinarith [mul_nonneg (neg_nonneg.mpr ha) (neg_nonneg.mpr hS)]
    linarith

/-! ## Dual values -/

/-- The four-size dual value is a lower bound for the dual objective of any
support containing `S₄`. -/
theorem dual_lower_of_superset {S : Set ℤ} (hS : S4 ⊆ S) {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) (l : ℝ) :
    Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T ≤
      Real.log (partitionFn S l) - l * T := by
  have hZ4pos : 0 < ∑ i ∈ F4, gaussWeight l i := sum_gaussWeight_pos F4 F4_nonempty l
  have hZ4l4pos : 0 < ∑ i ∈ F4, gaussWeight l4 i :=
    sum_gaussWeight_pos F4 F4_nonempty l4
  have hZ4 : ∑ i ∈ F4, gaussWeight l i ≤ partitionFn S l := by
    rw [← partitionFn_S4]
    exact partitionFn_mono hS l
  have htan := four_dual_tangent hmean l
  have h1 : Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T ≤
      Real.log (∑ i ∈ F4, gaussWeight l i) - l * T := by
    rw [log_sub_mul_eq hZ4l4pos, log_sub_mul_eq hZ4pos]
    exact Real.log_le_log (mul_pos hZ4l4pos (Real.exp_pos _)) htan
  have h2 := Real.log_le_log hZ4pos hZ4
  linarith

theorem bddBelow_dual {S : Set ℤ} (hS : S4 ⊆ S) {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) :
    BddBelow (Set.range fun l : ℝ => Real.log (partitionFn S l) - l * T) :=
  ⟨Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T, by
    rintro _ ⟨l, rfl⟩
    exact dual_lower_of_superset hS hmean l⟩

theorem dualValue_le_at {S : Set ℤ} (hS : S4 ⊆ S) {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) (l : ℝ) :
    dualValue S T ≤ Real.log (partitionFn S l) - l * T :=
  ciInf_le (bddBelow_dual hS hmean) l

theorem le_dualValue_of_superset {S : Set ℤ} (hS : S4 ⊆ S) {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) :
    Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T ≤ dualValue S T :=
  le_ciInf (dual_lower_of_superset hS hmean)

/-- The four-size infimum is attained at the four-size tilt. -/
theorem dualValue_S4_eq {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) :
    dualValue S4 T = Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T := by
  apply le_antisymm
  · calc
      dualValue S4 T ≤ Real.log (partitionFn S4 l4) - l4 * T :=
        dualValue_le_at subset_rfl hmean l4
      _ = Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T := by
        rw [partitionFn_S4]
  · exact le_dualValue_of_superset subset_rfl hmean

/-- The dual value is monotone in the support (for supports containing
`S₄`). -/
theorem dualValue_mono {S S' : Set ℤ} (hS : S4 ⊆ S) (hSS' : S ⊆ S') {T l4 : ℝ}
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) :
    dualValue S T ≤ dualValue S' T := by
  refine le_ciInf (fun l => ?_)
  have hpos : 0 < partitionFn S l := by
    refine lt_of_lt_of_le (sum_gaussWeight_pos F4 F4_nonempty l) ?_
    rw [← partitionFn_S4]
    exact partitionFn_mono hS l
  have h1 := dualValue_le_at hS hmean l
  have h2 := Real.log_le_log hpos (partitionFn_mono hSS' l)
  show dualValue S T ≤ Real.log (partitionFn S' l) - l * T
  linarith

/-- **Five-versus-four comparison.**  Uniformly in the tilt,
`𝓕_{S₅}(T) ≥ 𝓕_{S₄}(T) + log (521/520)` for `T ≥ 14/5`. -/
theorem le_dualValue_S5 {T l4 : ℝ} (hT : 14 / 5 ≤ T)
    (hmean : ∑ i ∈ F4, ((i : ℝ) - T) * gaussWeight l4 i = 0) :
    Real.log (521 / 520) + (Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T) ≤
      dualValue S5 T := by
  refine le_ciInf (fun l => ?_)
  have hZ4pos := sum_gaussWeight_pos F4 F4_nonempty l4
  have hZ5pos := sum_gaussWeight_pos F5 F5_nonempty l
  have hX : 0 < (∑ i ∈ F4, gaussWeight l4 i) * Real.exp (-(l4 * T)) :=
    mul_pos hZ4pos (Real.exp_pos _)
  have key := five_tangent_lower hT hmean l
  show Real.log (521 / 520) + (Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * T) ≤
    Real.log (partitionFn S5 l) - l * T
  rw [partitionFn_S5, log_sub_mul_eq hZ5pos, log_sub_mul_eq hZ4pos,
    ← Real.log_mul (by norm_num) hX.ne']
  exact Real.log_le_log (mul_pos (by norm_num) hX) key

/-! ## The phase interval -/

theorem phaseTarget_bounds (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    phaseTarget delta ∈ Set.Ioo (2 : ℝ) 5 ∧ (14 / 5 : ℝ) ≤ phaseTarget delta := by
  obtain ⟨h0, h1⟩ := hdelta
  have hq57 : Real.log 2 < 5 / 7 := by linarith [Real.log_two_lt_d9]
  have hq12 : 1 / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hpos : 0 < Real.log 2 := by linarith
  have hA : (14 / 5 : ℝ) < 2 / Real.log 2 := by
    rw [lt_div_iff₀ hpos]
    linarith
  have hB : 2 / Real.log 2 < 4 := by
    rw [div_lt_iff₀ hpos]
    linarith
  unfold phaseTarget
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- **Fidelity of `𝓕_S`.**  For `S ∈ {S₄, S₅, S₊}` (any `S ⊇ S₄`) and every
`T ∈ (2,5)`, the dual objective is bounded below, so the Lean infimum
`dualValue S T` is its genuine greatest lower bound (no junk value). -/
theorem isGLB_dualValue {S : Set ℤ} (hS : S4 ⊆ S) {T : ℝ}
    (hT : T ∈ Set.Ioo (2 : ℝ) 5) :
    IsGLB (Set.range fun l : ℝ => Real.log (partitionFn S l) - l * T)
      (dualValue S T) :=
  isGLB_ciInf (bddBelow_dual hS
    (mean_condition (ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT)))

/-! ## Assembly -/

/-- The four comparison inequalities at the phase target, with the four-size
dual value `v = 𝓕_{S₄}(T_δ)`. -/
theorem core_at_delta (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    ∃ v : ℝ,
      dualValue S4 (phaseTarget delta) = v ∧
      Real.log (521 / 520) + v ≤ dualValue S5 (phaseTarget delta) ∧
      dualValue Splus (phaseTarget delta) < Real.log (153 / 100) + v ∧
      dualValue S5 (phaseTarget delta) ≤ dualValue Splus (phaseTarget delta) ∧
      v ≤ dualValue Splus (phaseTarget delta) := by
  obtain ⟨hT25, hT⟩ := phaseTarget_bounds delta hdelta
  obtain ⟨l4, hmeanT⟩ : ∃ l4 : ℝ,
      ProfileEntropyS4.mean fourGaussianScore l4 = phaseTarget delta :=
    ⟨_, ProfileEntropyS4.mean_tilt_eq fourGaussianScore hT25⟩
  have hmean := mean_condition hmeanT
  refine ⟨Real.log (∑ i ∈ F4, gaussWeight l4 i) - l4 * phaseTarget delta,
    dualValue_S4_eq hmean, le_dualValue_S5 hT hmean, ?_,
    dualValue_mono S4_subset_S5 S5_subset_Splus hmean,
    le_dualValue_of_superset S4_subset_Splus hmean⟩
  have hratio := uniform_four_size_partition_ratio_for_delta delta l4
    hdelta.1 hdelta.2 hmeanT
  have hle := dualValue_le_at S4_subset_Splus hmean l4
  rw [partitionFn_Splus] at hle
  have hZ4 : ProfileEntropyS4.partition fourGaussianScore l4 =
      ∑ i ∈ F4, gaussWeight l4 i := by
    rw [partition_four_eq, sum_F4]
  rw [hZ4] at hratio
  have hZ4pos := sum_gaussWeight_pos F4 F4_nonempty l4
  have hZpos := extendedGaussianPartition_pos (a := q) (lambda := l4) q_pos
  have hlog : Real.log (extendedGaussianPartition q l4) -
      Real.log (∑ i ∈ F4, gaussWeight l4 i) < Real.log (153 / 100) := by
    rw [← Real.log_div hZpos.ne' hZ4pos.ne']
    exact Real.log_lt_log (div_pos hZpos hZ4pos) hratio
  linarith

theorem log_200_div_153_eq : Real.log (200 / 153) = Real.log 2 - Real.log (153 / 100) := by
  rw [show (200 / 153 : ℝ) = 2 / (153 / 100) by norm_num]
  exact Real.log_div (by norm_num) (by norm_num)

theorem log_8750_div_6681_eq :
    Real.log (8750 / 6681) = Real.log (200 / 153) + Real.log (525 / 524) := by
  rw [show (8750 / 6681 : ℝ) = 200 / 153 * (525 / 524) by norm_num]
  exact Real.log_mul (by norm_num) (by norm_num)

theorem log_6681_div_4375_eq :
    Real.log (6681 / 4375) = Real.log (153 / 100) - Real.log (525 / 524) := by
  rw [show (6681 / 4375 : ℝ) = (153 / 100) / (525 / 524) by norm_num]
  exact Real.log_div (by norm_num) (by norm_num)

theorem log_margin_eq :
    Real.log (273004 / 273000) = Real.log (521 / 520) - Real.log (525 / 524) := by
  rw [show (273004 / 273000 : ℝ) = (521 / 520) / (525 / 524) by norm_num]
  exact Real.log_div (by norm_num) (by norm_num)

theorem log_525_div_524_lt_log_521_div_520 :
    Real.log (525 / 524) < Real.log (521 / 520) :=
  Real.log_lt_log (by norm_num) (by norm_num)

/-- **Lemma `lem:four-size-entropy-certificate`** with the manuscript's
literal infimum definitions: for `0 ≤ δ ≤ 1`,
`0 ≤ D₄(δ) < log (153/100)` and `A₄(δ) > log (200/153)`. -/
theorem four_size_entropy_certificate (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    (0 ≤ entropyLoss4 delta ∧ entropyLoss4 delta < Real.log (153 / 100)) ∧
      Real.log (200 / 153) < phaseGain4 delta := by
  obtain ⟨v, h4, -, hplus, -, hv⟩ := core_at_delta delta hdelta
  have L1 := log_200_div_153_eq
  unfold entropyLoss4 phaseGain4
  rw [h4]
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- **Lemma `lem:entropy-gap`, statement (5.3).**  For every `0 ≤ δ ≤ 1`,
`A₅(δ) - A₄(δ) > log (525/524)`, `0 ≤ D₅(δ) < log (6681/4375)`, and
`A₅(δ) > γ₅ = log (8750/6681)`. -/
theorem entropy_gap (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (525 / 524) < phaseGain5 delta - phaseGain4 delta ∧
      (0 ≤ entropyLoss5 delta ∧ entropyLoss5 delta < Real.log (6681 / 4375)) ∧
      gamma5 < phaseGain5 delta := by
  obtain ⟨v, h4, h5, hplus, h5plus, -⟩ := core_at_delta delta hdelta
  have L1 := log_200_div_153_eq
  have L2 := log_8750_div_6681_eq
  have L3 := log_6681_div_4375_eq
  have L4 := log_525_div_524_lt_log_521_div_520
  unfold phaseGain5 phaseGain4 entropyLoss5 gamma5
  rw [h4]
  exact ⟨by linarith, ⟨by linarith, by linarith⟩, by linarith⟩

/-- The bound `A₅(δ) > log (8750/6681)` for every `δ ∈ [0,1]`, as asserted in
the v2 main theorem. -/
theorem log_8750_div_6681_lt_phaseGain5 (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (8750 / 6681) < phaseGain5 delta :=
  (entropy_gap delta hdelta).2.2

/-- An explicit positive uniform margin above `γ₅` on the whole phase
interval: `A₅(δ) > log (8750/6681) + log (273004/273000)`. -/
theorem phaseGain5_uniform_margin (delta : ℝ)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) 1) :
    Real.log (8750 / 6681) + Real.log (273004 / 273000) < phaseGain5 delta := by
  obtain ⟨v, -, h5, hplus, -, -⟩ := core_at_delta delta hdelta
  have L1 := log_200_div_153_eq
  have L2 := log_8750_div_6681_eq
  have L5 := log_margin_eq
  unfold phaseGain5
  linarith

theorem log_273004_div_273000_pos : 0 < Real.log (273004 / 273000) :=
  Real.log_pos (by norm_num)

end

end FiveSizeEntropyGap

end Erdos625

#print axioms Erdos625.FiveSizeEntropyGap.hasSum_partitionFn
#print axioms Erdos625.FiveSizeEntropyGap.isGLB_dualValue
#print axioms Erdos625.FiveSizeEntropyGap.four_size_entropy_certificate
#print axioms Erdos625.FiveSizeEntropyGap.entropy_gap
#print axioms Erdos625.FiveSizeEntropyGap.log_8750_div_6681_lt_phaseGain5
#print axioms Erdos625.FiveSizeEntropyGap.phaseGain5_uniform_margin
