import Mathlib.Analysis.Calculus.Deriv.Inverse
import Erdos625.ColoringProfileDualTilt
import Erdos625.ColoringProfileDeficitDual

/-!
# Selected profile tilt and the attained optimal value

After endpoint inversion has been proved, this module selects the unique
target-matching tilt.  It proves the inverse derivative, defines the normalized
entropy value and the resulting finite real-profile optimum, and differentiates
that optimum with respect to the real part count.

All derivative statements are restricted to the open support-mean interval.
No phase-uniform asymptotic estimate or root theorem is asserted here.
-/

namespace Erdos625

open Filter
open scoped Topology

noncomputable section

/-! ## A total selected tilt with an interior specification -/

/-- The unique target-matching tilt on the interior support interval, extended
by zero outside that interval. -/
noncomputable def profileDualTilt (b : ℕ) (target : ℝ) : ℝ :=
  if h : 2 ≤ b ∧ target ∈ Set.Ioo (1 : ℝ) (b : ℝ) then
    Classical.choose
      (existsUnique_profileDualMean_eq_of_mem_Ioo h.1 h.2).exists
  else 0

theorem profileDualMean_profileDualTilt {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    profileDualMean b (profileDualTilt b target) = target := by
  rw [profileDualTilt, dif_pos ⟨hb, htarget⟩]
  exact Classical.choose_spec
    (existsUnique_profileDualMean_eq_of_mem_Ioo hb htarget).exists

theorem eq_profileDualTilt_of_profileDualMean_eq {b : ℕ} (hb : 2 ≤ b)
    {target t : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ))
    (ht : profileDualMean b t = target) :
    t = profileDualTilt b target :=
  profileDualMean_injective hb
    (ht.trans (profileDualMean_profileDualTilt hb htarget).symm)

theorem profileDualMean_eq_iff_eq_profileDualTilt {b : ℕ} (hb : 2 ≤ b)
    {target t : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    profileDualMean b t = target ↔ t = profileDualTilt b target := by
  constructor
  · exact eq_profileDualTilt_of_profileDualMean_eq hb htarget
  · rintro rfl
    exact profileDualMean_profileDualTilt hb htarget

/-! ## Continuity and inverse calculus -/

/-- Interior targets converging to an interior target have convergent selected
tilts.  The proof traps the moving tilt between fixed strict mean brackets. -/
theorem tendsto_profileDualTilt_of_target
    {A : Type*} {l : Filter A} {b : ℕ} (hb : 2 ≤ b)
    (target : A → ℝ) {target₀ : ℝ}
    (htarget : Tendsto target l (𝓝 target₀))
    (htarget₀ : target₀ ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    Tendsto (fun a ↦ profileDualTilt b (target a)) l
      (𝓝 (profileDualTilt b target₀)) := by
  rw [tendsto_order]
  constructor
  · intro lower hlower
    have hMeanLower : profileDualMean b lower < target₀ := by
      calc
        profileDualMean b lower <
            profileDualMean b (profileDualTilt b target₀) :=
          strictMono_profileDualMean hb hlower
        _ = target₀ := profileDualMean_profileDualTilt hb htarget₀
    have hCompare : ∀ᶠ a in l, profileDualMean b lower < target a :=
      (tendsto_const_nhds.eventually_lt htarget) hMeanLower
    have hInterior : ∀ᶠ a in l,
        target a ∈ Set.Ioo (1 : ℝ) (b : ℝ) :=
      htarget (isOpen_Ioo.mem_nhds htarget₀)
    filter_upwards [hCompare, hInterior] with a ha hTa
    rw [← profileDualMean_profileDualTilt hb hTa] at ha
    exact (strictMono_profileDualMean hb).lt_iff_lt.mp ha
  · intro upper hupper
    have hMeanUpper : target₀ < profileDualMean b upper := by
      calc
        target₀ = profileDualMean b (profileDualTilt b target₀) :=
          (profileDualMean_profileDualTilt hb htarget₀).symm
        _ < profileDualMean b upper :=
          strictMono_profileDualMean hb hupper
    have hCompare : ∀ᶠ a in l, target a < profileDualMean b upper :=
      (htarget.eventually_lt tendsto_const_nhds) hMeanUpper
    have hInterior : ∀ᶠ a in l,
        target a ∈ Set.Ioo (1 : ℝ) (b : ℝ) :=
      htarget (isOpen_Ioo.mem_nhds htarget₀)
    filter_upwards [hCompare, hInterior] with a ha hTa
    rw [← profileDualMean_profileDualTilt hb hTa] at ha
    exact (strictMono_profileDualMean hb).lt_iff_lt.mp ha

theorem continuousAt_profileDualTilt {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    ContinuousAt (profileDualTilt b) target :=
  tendsto_profileDualTilt_of_target hb id tendsto_id htarget

/-- The selected tilt has derivative the reciprocal Gibbs variance. -/
theorem hasDerivAt_profileDualTilt {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    HasDerivAt (profileDualTilt b)
      (profileDualVariance b (profileDualTilt b target))⁻¹ target := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hLeftInverse : ∀ᶠ y in 𝓝 target,
      profileDualMean b (profileDualTilt b y) = y := by
    filter_upwards [isOpen_Ioo.mem_nhds htarget] with y hy
    exact profileDualMean_profileDualTilt hb hy
  exact (hasDerivAt_profileDualMean hbPos (profileDualTilt b target)).of_local_left_inverse
    (continuousAt_profileDualTilt hb htarget)
    (profileDualVariance_pos hb (profileDualTilt b target)).ne'
    hLeftInverse

theorem deriv_profileDualTilt {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    deriv (profileDualTilt b) target =
      (profileDualVariance b (profileDualTilt b target))⁻¹ :=
  (hasDerivAt_profileDualTilt hb htarget).deriv

/-! ## Entropy and optimized-value calculus -/

/-- The selected normalized entropy-plus-score candidate at prescribed mean
`target`.  It is the optimum on the interior domain used below; the total
definition uses the zero-tilt fallback outside that domain. -/
def profileDualEntropyValue (b : ℕ) (target : ℝ) : ℝ :=
  Real.log (profileDualPartition b (profileDualTilt b target)) -
    profileDualTilt b target * target

/-- Envelope derivative of the normalized entropy optimum. -/
theorem hasDerivAt_profileDualEntropyValue {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    HasDerivAt (profileDualEntropyValue b)
      (-profileDualTilt b target) target := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hTilt := hasDerivAt_profileDualTilt hb htarget
  have hLog :=
    (hasDerivAt_log_profileDualPartition hbPos
      (profileDualTilt b target)).comp target hTilt
  have hProduct := hTilt.mul (hasDerivAt_id target)
  have hMean := profileDualMean_profileDualTilt hb htarget
  have hSub := (hLog.sub hProduct).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ ↦ rfl)
  apply hSub.congr_deriv
  simp only [id_eq]
  rw [hMean]
  ring

theorem deriv_profileDualEntropyValue {b : ℕ} (hb : 2 ≤ b)
    {target : ℝ} (htarget : target ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    deriv (profileDualEntropyValue b) target =
      -profileDualTilt b target :=
  (hasDerivAt_profileDualEntropyValue hb htarget).deriv

/-- The selected finite real-profile value, written in normalized form.  The
interior theorem below proves that it is attained and optimal. -/
def profileDualOptimalValue (b : ℕ) (n parts : ℝ) : ℝ :=
  n * Real.log n - n + parts - parts * Real.log parts +
    parts * profileDualEntropyValue b (n / parts)

/-- On nonzero part count, the normalized optimum is exactly the selected
dual upper value. -/
theorem profileDualOptimalValue_eq_profileDualUpper
    (b : ℕ) {n parts : ℝ} (hparts : parts ≠ 0) :
    profileDualOptimalValue b n parts =
      profileDualUpper b n parts (profileDualTilt b (n / parts)) := by
  unfold profileDualOptimalValue profileDualEntropyValue profileDualUpper
  field_simp [hparts]
  ring

/-- On the interior mean domain, the selected value is the attained greatest
value of the real finite-profile relaxation. -/
theorem profileDualOptimalValue_isGreatest_profileRealObjective
    {b : ℕ} (hb : 2 ≤ b) {n parts : ℝ} (hparts : 0 < parts)
    (htarget : n / parts ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    IsGreatest
      (profileRealObjective n ''
        {x : RealColoringProfile b |
          RealColoringProfile.IsFeasible x n parts})
      (profileDualOptimalValue b n parts) := by
  have hbPos : 0 < b := lt_of_lt_of_le Nat.zero_lt_two hb
  have hMean := profileDualMean_profileDualTilt hb htarget
  have hMass : parts *
      profileDualMean b (profileDualTilt b (n / parts)) = n := by
    rw [hMean]
    field_simp [hparts.ne']
  rw [profileDualOptimalValue_eq_profileDualUpper b hparts.ne']
  exact profileDualUpper_isGreatest_profileRealObjective
    hbPos hparts hMass

/-- Exact derivative of the attained finite optimum with respect to the real
part count.  This is the finite envelope derivative needed for the manuscript
root slope; it is not an asymptotic estimate. -/
theorem hasDerivAt_profileDualOptimalValue_parts
    {b : ℕ} (hb : 2 ≤ b) {n parts : ℝ} (hparts : 0 < parts)
    (htarget : n / parts ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    HasDerivAt (fun k ↦ profileDualOptimalValue b n k)
      (Real.log (profileDualPartition b
          (profileDualTilt b (n / parts))) - Real.log parts) parts := by
  have hTarget : HasDerivAt (fun k : ℝ ↦ n / k)
      (-n / parts ^ 2) parts := by
    change HasDerivAt ((fun _ : ℝ ↦ n) / id) (-n / parts ^ 2) parts
    apply ((hasDerivAt_const parts n).div
      (hasDerivAt_id parts) hparts.ne').congr_deriv
    simp only [id_eq, zero_mul, mul_one, zero_sub]
  have hEntropy :=
    (hasDerivAt_profileDualEntropyValue hb htarget).comp parts hTarget
  have hLogParts := Real.hasDerivAt_log hparts.ne'
  have hLinearEntropy := (hasDerivAt_id parts).mul hEntropy
  have hMain :=
    (((hasDerivAt_const parts (n * Real.log n - n)).add
      (hasDerivAt_id parts)).sub
        ((hasDerivAt_id parts).mul hLogParts)).add hLinearEntropy
  have hFunction : HasDerivAt
      (fun k ↦ profileDualOptimalValue b n k)
      (0 + 1 - (1 * Real.log parts + parts * parts⁻¹) +
        (1 * profileDualEntropyValue b (n / parts) +
          parts *
            (-profileDualTilt b (n / parts) * (-n / parts ^ 2)))) parts := by
    have h := hMain.congr_of_eventuallyEq
      (f₁ := fun k ↦ profileDualOptimalValue b n k)
      (Filter.Eventually.of_forall fun k ↦ by
        unfold profileDualOptimalValue
        rfl)
    simpa only [id_eq, Function.comp_apply] using h
  apply hFunction.congr_deriv
  simp only [profileDualEntropyValue]
  field_simp [hparts.ne']
  ring

theorem deriv_profileDualOptimalValue_parts
    {b : ℕ} (hb : 2 ≤ b) {n parts : ℝ} (hparts : 0 < parts)
    (htarget : n / parts ∈ Set.Ioo (1 : ℝ) (b : ℝ)) :
    deriv (fun k ↦ profileDualOptimalValue b n k) parts =
      Real.log (profileDualPartition b
        (profileDualTilt b (n / parts))) - Real.log parts :=
  (hasDerivAt_profileDualOptimalValue_parts hb hparts htarget).deriv

end

end Erdos625
