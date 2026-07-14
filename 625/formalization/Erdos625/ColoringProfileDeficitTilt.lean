import Erdos625.ColoringProfileDeficitMomentConvergence
import Erdos625.ColoringProfileDualOptimalValue
import Erdos625.MeanInversionTools

/-!
# Selected deficit tilts and an unconditional compact-target bound

The finite profile is naturally parametrized in size coordinates by
`profileDualTilt`.  This module transports that selected parameter to the
centered deficit coordinate

`lambda = profileDeficitAffineB alpha - profileDualTilt (alpha + 1) (alpha - T)`.

The exact change of variables shows that the finite deficit mean is strictly
increasing and that the transported tilt realizes every target in the exact
open deficit support `(-1, alpha - 1)`.

Finally, fixed-tilt convergence to the extended Gaussian mean brackets every
compact target interval `A <= T <= B`, with `-1 < A`, between two constants.
Strict monotonicity then gives a single eventual absolute bound for the
selected finite tilt.  The constant is chosen before the target sequence, so
it is independent of every phase or other choice encoded by that sequence.
No Gaussian envelope at a selected tilt is used in this argument.
-/

namespace Erdos625

open Filter Set
open scoped Topology

noncomputable section

/-! ## Exact monotonicity and selection -/

/-- For every nontrivial finite deficit support, the normalized deficit mean
is strictly increasing in the deficit tilt. -/
theorem strictMono_profileDeficitMean {alpha : ℕ} (halpha : 0 < alpha) :
    StrictMono (profileDeficitMean alpha) := by
  have hb : 2 ≤ alpha + 1 := by omega
  intro lambda mu hlambda
  have hdual := (strictMono_profileDualMean hb)
    (show profileDeficitAffineB alpha - mu <
        profileDeficitAffineB alpha - lambda by linarith)
  rw [profileDualMean_eq_alpha_sub_profileDeficitMean,
    profileDualMean_eq_alpha_sub_profileDeficitMean] at hdual
  linarith

/-- The selected finite tilt in normalized deficit coordinates.  The
underlying size target is `alpha - target`; outside the exact interior support
the total fallback behavior is inherited from `profileDualTilt`. -/
noncomputable def profileDeficitTilt (alpha : ℕ) (target : ℝ) : ℝ :=
  profileDeficitAffineB alpha -
    profileDualTilt (alpha + 1) ((alpha : ℝ) - target)

@[simp] theorem profileDeficitAffineB_sub_profileDeficitTilt
    (alpha : ℕ) (target : ℝ) :
    profileDeficitAffineB alpha - profileDeficitTilt alpha target =
      profileDualTilt (alpha + 1) ((alpha : ℝ) - target) := by
  simp [profileDeficitTilt]

/-- A deficit target is in the exact open finite support precisely when its
corresponding size target is in the open size support. -/
theorem deficitTarget_mem_Ioo_iff_sizeTarget_mem_Ioo
    (alpha : ℕ) (target : ℝ) :
    target ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1) ↔
      (alpha : ℝ) - target ∈ Ioo (1 : ℝ) ((alpha + 1 : ℕ) : ℝ) := by
  norm_num [Set.mem_Ioo]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- On the exact interior support, the normalized selected deficit tilt
matches the prescribed target. -/
theorem profileDeficitMean_profileDeficitTilt
    {alpha : ℕ} (halpha : 0 < alpha) {target : ℝ}
    (htarget : target ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1)) :
    profileDeficitMean alpha (profileDeficitTilt alpha target) = target := by
  have hb : 2 ≤ alpha + 1 := by omega
  have hsize :
      (alpha : ℝ) - target ∈
        Ioo (1 : ℝ) ((alpha + 1 : ℕ) : ℝ) :=
    (deficitTarget_mem_Ioo_iff_sizeTarget_mem_Ioo alpha target).mp htarget
  have hdual := profileDualMean_profileDualTilt hb hsize
  have hchange :=
    profileDualMean_eq_alpha_sub_profileDeficitMean
      alpha (profileDeficitTilt alpha target)
  rw [profileDeficitAffineB_sub_profileDeficitTilt, hdual] at hchange
  linarith

/-- Any interior tilt matching the prescribed deficit mean is the selected
normalized deficit tilt. -/
theorem eq_profileDeficitTilt_of_profileDeficitMean_eq
    {alpha : ℕ} (halpha : 0 < alpha) {target lambda : ℝ}
    (htarget : target ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1))
    (hmean : profileDeficitMean alpha lambda = target) :
    lambda = profileDeficitTilt alpha target := by
  exact (strictMono_profileDeficitMean halpha).injective
    (hmean.trans
      (profileDeficitMean_profileDeficitTilt halpha htarget).symm)

/-- Exact existence and uniqueness of a finite normalized deficit tilt on the
open deficit support. -/
theorem existsUnique_profileDeficitMean_eq_of_mem_Ioo
    {alpha : ℕ} (halpha : 0 < alpha) {target : ℝ}
    (htarget : target ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1)) :
    ∃! lambda : ℝ, profileDeficitMean alpha lambda = target := by
  refine ⟨profileDeficitTilt alpha target,
    profileDeficitMean_profileDeficitTilt halpha htarget, ?_⟩
  intro lambda hmean
  exact eq_profileDeficitTilt_of_profileDeficitMean_eq
    halpha htarget hmean

/-! ## A genuinely uniform eventual compact-target bound -/

/-- A compact deficit-target interval strictly above the limiting lower
endpoint admits one eventual selected-tilt bound, simultaneously for every
target in the interval.  Both the constant and the eventual index are chosen
before `target` is introduced.  The conclusion also proves, rather than
assumes, that the entire compact interval is eventually contained in the
exact finite open support.
-/
theorem exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le
    {A B : ℝ} (hA : -1 < A) (hAB : A ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᶠ alpha : ℕ in atTop,
        ∀ target ∈ Icc A B,
          target ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1) ∧
            |profileDeficitTilt alpha target| ≤ M := by
  obtain ⟨L, R, _hLR, hlimitL, hlimitR⟩ :=
    exists_ordered_extendedGaussianMean_bracket
      (show 0 < Real.log 2 by positivity) hA hAB
  have hfiniteL :
      ∀ᶠ alpha : ℕ in atTop, profileDeficitMean alpha L < A :=
    (tendsto_profileDeficitMean L).eventually
      (Iio_mem_nhds hlimitL)
  have hfiniteR :
      ∀ᶠ alpha : ℕ in atTop, B < profileDeficitMean alpha R :=
    (tendsto_profileDeficitMean R).eventually
      (Ioi_mem_nhds hlimitR)
  have hsupportTop :
      ∀ᶠ alpha : ℕ in atTop, B < (alpha : ℝ) - 1 := by
    filter_upwards
      [tendsto_natCast_atTop_atTop.eventually_gt_atTop (B + 1)] with
      alpha halpha
    linarith
  refine ⟨max |L| |R|,
    (abs_nonneg L).trans (le_max_left |L| |R|), ?_⟩
  filter_upwards [hfiniteL, hfiniteR, hsupportTop,
      eventually_gt_atTop 0] with alpha hleft hright hsupport halpha
  intro target htargetCompact
  have htargetInterior :
      target ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1) :=
    ⟨hA.trans_le htargetCompact.1,
      htargetCompact.2.trans_lt hsupport⟩
  have hmatch := profileDeficitMean_profileDeficitTilt
    halpha htargetInterior
  have hmeanLeft :
      profileDeficitMean alpha L <
        profileDeficitMean alpha
          (profileDeficitTilt alpha target) := by
    rw [hmatch]
    exact hleft.trans_le htargetCompact.1
  have hmeanRight :
      profileDeficitMean alpha
          (profileDeficitTilt alpha target) <
        profileDeficitMean alpha R := by
    rw [hmatch]
    exact htargetCompact.2.trans_lt hright
  have htiltLeft : L < profileDeficitTilt alpha target :=
    (strictMono_profileDeficitMean halpha).lt_iff_lt.mp
      hmeanLeft
  have htiltRight : profileDeficitTilt alpha target < R :=
    (strictMono_profileDeficitMean halpha).lt_iff_lt.mp
      hmeanRight
  exact ⟨htargetInterior,
    abs_le_max_abs_abs htiltLeft.le htiltRight.le⟩

/-- Sequence-level corollary with the support hypotheses kept explicit.  Its
eventual index may additionally depend on when the particular sequence enters
`[A,B]` and the finite support; the stronger theorem above is uniform in each
fixed finite-support slice. -/
theorem exists_eventual_abs_profileDeficitTilt_le_on_compact
    {A B : ℝ} (hA : -1 < A) (hAB : A ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ target : ℕ → ℝ,
        (∀ᶠ alpha : ℕ in atTop, target alpha ∈ Icc A B) →
        (∀ᶠ alpha : ℕ in atTop,
          0 < alpha ∧
            target alpha ∈ Ioo (-1 : ℝ) ((alpha : ℝ) - 1)) →
        ∀ᶠ alpha : ℕ in atTop,
          |profileDeficitTilt alpha (target alpha)| ≤ M := by
  obtain ⟨M, hM, huniform⟩ :=
    exists_eventually_forall_mem_Icc_abs_profileDeficitTilt_le hA hAB
  refine ⟨M, hM, ?_⟩
  intro target hcompact hinterior
  filter_upwards [huniform, hcompact, hinterior] with
      alpha huniformAlpha htargetCompact _htargetInterior
  exact (huniformAlpha (target alpha) htargetCompact).2

end

end Erdos625
