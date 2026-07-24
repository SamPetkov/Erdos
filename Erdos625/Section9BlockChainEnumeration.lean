import Erdos625.Section9KernelPathEnumeration
import Erdos625.Section9MatchingTraversalBridge

/-!
# Section 9: exact finite enumeration of relaxed block chains

A relaxed block consists of a positive `K`-path of length at most `L`,
followed by one transition of a second kernel `P`.  This module records every
internal positive-path code, its endpoint before the `P` transition, and the
state after that transition.  Iterating the construction therefore preserves
all path multiplicities and all intermediate transition states.

The main theorem identifies the sum of the resulting code weights exactly
with the endpoint mass of the composed kernel
`finiteKernelComp (finitePositiveWalkKernel K L) P`.
-/

namespace Erdos625

open scoped BigOperators ENNReal

noncomputable section

/-! ## One relaxed block -/

/-- A positive `K`-path from `v` to some state `u`, ready to be followed by
a `P` transition.

The sigma coordinate stores `u`, while the second coordinate stores the full
positive path code, including all of its internal vertices. -/
abbrev PositiveKernelThenTransitionCode
    (V : Type*) (L : ℕ) (v : V) : Type _ :=
  Σ u : V, PositiveKernelPathCode V L v u

namespace PositiveKernelThenTransitionCode

/-- Exact weight of one relaxed block. -/
def weight {V : Type*}
    (K P : V → V → ℝ≥0∞) (x : V) {L : ℕ} {v : V}
    (code : PositiveKernelThenTransitionCode V L v) : ℝ≥0∞ :=
  code.2.weight K * P code.1 x

@[simp]
theorem weight_mk {V : Type*}
    (K P : V → V → ℝ≥0∞) {L : ℕ} {v u x : V}
    (path : PositiveKernelPathCode V L v u) :
    weight K P x (Sigma.mk u path :
      PositiveKernelThenTransitionCode V L v) =
      path.weight K * P u x := rfl

end PositiveKernelThenTransitionCode

/-- Summing all one-block codes gives exactly one entry of the composed
positive-walk-then-transition kernel. -/
theorem sum_positiveKernelThenTransitionCode_weight_eq_finiteKernelComp
    {V : Type*} [Fintype V] [DecidableEq V]
    (K P : V → V → ℝ≥0∞) (L : ℕ) (v x : V) :
    (∑ code : PositiveKernelThenTransitionCode V L v,
        code.weight K P x) =
      finiteKernelComp (finitePositiveWalkKernel K L) P v x := by
  rw [Fintype.sum_sigma]
  unfold finiteKernelComp
  apply Finset.sum_congr rfl
  intro u hu
  change
    (∑ path : PositiveKernelPathCode V L v u,
        path.weight K * P u x) =
      finitePositiveWalkKernel K L v u * P u x
  rw [← Finset.sum_mul]
  rw [sum_positiveKernelPathCode_weight_eq_finitePositiveWalkKernel]

/-! ## Finite chains of relaxed blocks -/

/-- Codes for exactly `r` relaxed blocks from `v` to `w`.

At positive length, `x` is the state after the first `P` transition, the
first component records the entire positive path and its pre-transition
endpoint, and the last component records the remaining chain from `x` to
`w`.  At length zero the code type is inhabited exactly when `v = w`, in
agreement with the zero-step endpoint kernel. -/
def RelaxedBlockChainCode (V : Type*) (L : ℕ) : ℕ → V → V → Type _
  | 0, v, w => KernelPathCode V 0 v w
  | r + 1, v, w =>
      Σ x : V,
        PositiveKernelThenTransitionCode V L v ×
          RelaxedBlockChainCode V L r x w

noncomputable instance instFintypeRelaxedBlockChainCode
    {V : Type*} [Fintype V] [DecidableEq V]
    (L r : ℕ) (v w : V) : Fintype (RelaxedBlockChainCode V L r v w) := by
  induction r generalizing v with
  | zero =>
      change Fintype (KernelPathCode V 0 v w)
      infer_instance
  | succ r ih =>
      change Fintype
        (Σ x : V,
          PositiveKernelThenTransitionCode V L v ×
            RelaxedBlockChainCode V L r x w)
      letI (x : V) : Fintype (RelaxedBlockChainCode V L r x w) := ih x
      infer_instance

namespace RelaxedBlockChainCode

/-- Product of all positive-path and `P`-transition weights in a chain. -/
def weight {V : Type*} (K P : V → V → ℝ≥0∞) {L : ℕ} :
    {r : ℕ} → {v w : V} → RelaxedBlockChainCode V L r v w → ℝ≥0∞
  | 0, _, _, code => KernelPathCode.weight K code
  | _ + 1, _, _, code =>
      code.2.1.weight K P code.1 * weight K P code.2.2

@[simp]
theorem weight_zero {V : Type*}
    (K P : V → V → ℝ≥0∞) {L : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L 0 v w) :
    code.weight K P = 1 := rfl

@[simp]
theorem weight_succ {V : Type*}
    (K P : V → V → ℝ≥0∞) {L r : ℕ} {v w : V}
    (code : RelaxedBlockChainCode V L (r + 1) v w) :
    code.weight K P =
      code.2.1.weight K P code.1 * code.2.2.weight K P := rfl

end RelaxedBlockChainCode

/-- Exact relaxed-block-chain enumeration.

No row bound or endpoint-only certificate is used: the left-hand side sums
over every positive path code, every pre-transition endpoint, every
post-transition state, and every remaining chain. -/
theorem sum_relaxedBlockChainCode_weight_eq_finiteKernelEndpointMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (K P : V → V → ℝ≥0∞) (L r : ℕ) (v w : V) :
    (∑ code : RelaxedBlockChainCode V L r v w,
        code.weight K P) =
      finiteKernelEndpointMass
        (finiteKernelComp (finitePositiveWalkKernel K L) P) r v w := by
  induction r generalizing v with
  | zero =>
      change
        (∑ code : KernelPathCode V 0 v w, code.weight K) =
          finiteKernelEndpointMass
            (finiteKernelComp (finitePositiveWalkKernel K L) P) 0 v w
      exact
        sum_kernelPathCode_weight_eq_finiteKernelEndpointMass
          (finiteKernelComp (finitePositiveWalkKernel K L) P) 0 v w
  | succ r ih =>
      change
        (∑ code :
            Σ x : V,
              PositiveKernelThenTransitionCode V L v ×
                RelaxedBlockChainCode V L r x w,
            code.2.1.weight K P code.1 * code.2.2.weight K P) =
          ∑ x,
            finiteKernelComp (finitePositiveWalkKernel K L) P v x *
              finiteKernelEndpointMass
                (finiteKernelComp (finitePositiveWalkKernel K L) P) r x w
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Fintype.sum_prod_type]
      calc
        (∑ block : PositiveKernelThenTransitionCode V L v,
            ∑ tail : RelaxedBlockChainCode V L r x w,
              block.weight K P x * tail.weight K P) =
            ∑ block : PositiveKernelThenTransitionCode V L v,
              block.weight K P x *
                ∑ tail : RelaxedBlockChainCode V L r x w,
                  tail.weight K P := by
            apply Finset.sum_congr rfl
            intro block hblock
            rw [Finset.mul_sum]
        _ =
            (∑ block : PositiveKernelThenTransitionCode V L v,
                block.weight K P x) *
              ∑ tail : RelaxedBlockChainCode V L r x w,
                tail.weight K P := by
            rw [Finset.sum_mul]
        _ =
            finiteKernelComp (finitePositiveWalkKernel K L) P v x *
              finiteKernelEndpointMass
                (finiteKernelComp (finitePositiveWalkKernel K L) P) r x w := by
            rw [
              sum_positiveKernelThenTransitionCode_weight_eq_finiteKernelComp,
              ih x]

#print axioms
  sum_positiveKernelThenTransitionCode_weight_eq_finiteKernelComp
#print axioms
  sum_relaxedBlockChainCode_weight_eq_finiteKernelEndpointMass

end

end Erdos625
