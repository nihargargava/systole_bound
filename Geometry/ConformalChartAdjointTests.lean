module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalChartIntegrationByParts

@[expose] public section

/-!
# Smooth global tests for the weighted chart gradient

Compactly supported coordinate tests and their explicitly differentiated
adjoints extend smoothly by zero to the original manifold. Integration
by parts becomes a pairing of genuine global smooth functions, suitable
for passing to the closure of the actual gradient graph in `L²`.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology ENNReal

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {M : Type*} [TopologicalSpace M]

/-- **Math.** The literal zero-extension of a coordinate test. -/
def conformalChartTestPullback (e : OpenPartialHomeomorph M ℂ) (η : ℂ → ℝ) : M → ℝ :=
  e.source.indicator (fun x => η (e x))

theorem conformalChartTestPullback_apply_source
    (e : OpenPartialHomeomorph M ℂ) (η : ℂ → ℝ) {x : M} (hx : x ∈ e.source) :
    conformalChartTestPullback e η x = η (e x) := by
  simp [conformalChartTestPullback, hx]

theorem conformalChartTestPullback_apply_not_source
    (e : OpenPartialHomeomorph M ℂ) (η : ℂ → ℝ) {x : M} (hx : x ∉ e.source) :
    conformalChartTestPullback e η x = 0 := by
  simp [conformalChartTestPullback, hx]

variable [T2Space M]

/-- **Math.** The global test has support in the actual compact inverse
image of its coordinate support, strictly inside the original chart. -/
theorem conformalChartTestPullback_tsupport_subset
    (e : OpenPartialHomeomorph M ℂ) (η : ℂ → ℝ)
    (hηc : HasCompactSupport η) (hηsub : tsupport η ⊆ e.target) :
    tsupport (conformalChartTestPullback e η) ⊆ e.symm '' tsupport η := by
  have hK : IsCompact (e.symm '' tsupport η) :=
    hηc.image_of_continuousOn (e.symm.continuousOn.mono hηsub)
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  change conformalChartTestPullback e η x ≠ 0 at hx
  have hxs : x ∈ e.source := by
    by_contra hn
    exact hx (conformalChartTestPullback_apply_not_source e η hn)
  have hn : η (e x) ≠ 0 := by
    simpa only [conformalChartTestPullback_apply_source e η hxs] using hx
  exact ⟨e x, subset_closure hn, e.left_inv hxs⟩

theorem conformalChartTestPullback_hasCompactSupport
    (e : OpenPartialHomeomorph M ℂ) (η : ℂ → ℝ)
    (hηc : HasCompactSupport η) (hηsub : tsupport η ⊆ e.target) :
    HasCompactSupport (conformalChartTestPullback e η) :=
  (hηc.image_of_continuousOn (e.symm.continuousOn.mono hηsub)).of_isClosed_subset
    (isClosed_tsupport _) (conformalChartTestPullback_tsupport_subset e η hηc hηsub)

variable [ChartedSpace ℂ M]

/-- **Math.** Genuine compact coordinate support makes the zero-extension
smooth through the chart boundary in the original smooth structure. -/
theorem conformalChartTestPullback_contMDiff
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηsub : tsupport η ⊆ e.target) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (conformalChartTestPullback e η) := by
  apply contMDiff_of_tsupport
  intro x hx
  obtain ⟨z, hz, rfl⟩ := conformalChartTestPullback_tsupport_subset e η hηc hηsub hx
  have hxs : e.symm z ∈ e.source := e.map_target (hηsub hz)
  have hlocal := hη.contMDiff.contMDiffAt.comp (e.symm z)
    (contMDiffAt_of_mem_maximalAtlas he hxs)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hxs] with x hx
  exact conformalChartTestPullback_apply_source e η hx

/-- **Math.** The actual Euclidean coefficient of the formal adjoint of
the weighted derivative, after division by the metric area density. -/
def weightedChartAdjointCoordinate
    (e : OpenPartialHomeomorph M ℂ) (a : ℂ → ℝ)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ) (η : ℂ → ℝ) (z : ℂ) : ℝ :=
  (a z ^ 2)⁻¹ * fderiv ℝ (fun w => τ (e.symm w) * a w * η w) z v

omit [T2Space M] in
theorem weightedChartAdjointCoordinate_tsupport_subset
    (e : OpenPartialHomeomorph M ℂ) (a : ℂ → ℝ)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ) (η : ℂ → ℝ) :
    tsupport (weightedChartAdjointCoordinate e a τ v η) ⊆ tsupport η :=
  tsupport_mul_subset_right.trans
    ((tsupport_fderiv_apply_subset ℝ v).trans tsupport_mul_subset_right)

omit [T2Space M] in
theorem weightedChartAdjointCoordinate_hasCompactSupport
    (e : OpenPartialHomeomorph M ℂ) (a : ℂ → ℝ)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ) (η : ℂ → ℝ)
    (hηc : HasCompactSupport η) :
    HasCompactSupport (weightedChartAdjointCoordinate e a τ v η) :=
  hηc.of_isClosed_subset (isClosed_tsupport _)
    (weightedChartAdjointCoordinate_tsupport_subset e a τ v η)

omit [T2Space M] in
theorem weightedChartAdjointCoordinate_contDiff
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηsub : tsupport η ⊆ e.target) :
    ContDiff ℝ ∞ (weightedChartAdjointCoordinate e a τ v η) := by
  let Φ : ℂ → ℝ := fun z => τ (e.symm z) * a z * η z
  have hΦ : ContDiff ℝ ∞ Φ := contDiff_coordinate_mul_supported e.open_target
    ((smoothFunction_contDiffOn_chart_inverse e he τ).mul ha) hη hηsub
  have hDΦ : ContDiff ℝ ∞ (fun z => fderiv ℝ Φ z v) :=
    (hΦ.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hsub : tsupport (fun z => fderiv ℝ Φ z v) ⊆ e.target :=
    (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_mul_subset_right.trans hηsub)
  exact contDiff_coordinate_mul_supported e.open_target
    ((ha.pow 2).inv (fun z hz => pow_ne_zero _ (hapos z hz).ne')) hDΦ hsub

/-- **Math.** The explicit adjoint is also a genuine smooth global test. -/
theorem weightedChartAdjointTest_contMDiff
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηsub : tsupport η ⊆ e.target) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (conformalChartTestPullback e (weightedChartAdjointCoordinate e a τ v η)) :=
  conformalChartTestPullback_contMDiff e he _
    (weightedChartAdjointCoordinate_contDiff e he a ha hapos τ v η hη hηsub)
    (weightedChartAdjointCoordinate_hasCompactSupport e a τ v η hηc)
    ((weightedChartAdjointCoordinate_tsupport_subset e a τ v η).trans hηsub)

variable [MeasurableSpace M] [BorelSpace M]

omit [ChartedSpace ℂ M] in
/-- **Math.** A zero-extended coordinate test has the exact transported
global pairing, even for an arbitrary real function on the carrier. -/
theorem conformalChartTestPullback_integral
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (η : ℂ → ℝ) (hηsub : tsupport η ⊆ e '' U) (F : M → ℝ) :
    (∫ x, F x * conformalChartTestPullback e η x ∂μ) =
      ∫ z : ℂ, a z ^ 2 * (F (e.symm z) * η z) := by
  have hΩ : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hUs
  have hΩt : e '' U ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs hx)
  calc
    (∫ x, F x * conformalChartTestPullback e η x ∂μ) =
        ∫ x in U, F x * conformalChartTestPullback e η x ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_cases hxs : x ∈ e.source
      · have hzero : η (e x) = 0 := by
          by_contra hn
          obtain ⟨y, hy, heq⟩ := hηsub (subset_closure hn)
          have hyx : y = x := e.injOn (hUs hy) hxs heq
          exact hx (hyx ▸ hy)
        simp [conformalChartTestPullback_apply_source e η hxs, hzero]
      · simp [conformalChartTestPullback_apply_not_source e η hxs]
    _ = ∫ z : ℂ in e '' U, a z ^ 2 * (F (e.symm z) * η z) := by
      rw [conformalChart_setIntegral μ e U hU hUs a ha harea]
      apply setIntegral_congr_fun hΩ.measurableSet
      intro z hz
      dsimp only
      rw [conformalChartTestPullback_apply_source e η (e.map_target (hΩt hz)),
        e.right_inv (hΩt hz)]
    _ = ∫ z : ℂ, a z ^ 2 * (F (e.symm z) * η z) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero : η z = 0 := by
        by_contra hn
        exact hz (hηsub (subset_closure hn))
      simp [hzero]

/-- **Math.** Exact integration by parts as a pairing of genuine smooth
global test functions. This is the identity whose continuous `L²` pairings
pass to the completed gradient graph. -/
theorem weightedChartDerivative_integral_adjoint
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (τ : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (hτ : tsupport τ ⊆ U)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ e '' U) :
    (∫ x, weightedChartDerivative e a τ v f x * conformalChartTestPullback e η x ∂μ) =
      -(∫ x, f x *
        conformalChartTestPullback e (weightedChartAdjointCoordinate e a τ v η) x ∂μ) := by
  have hΩt : e '' U ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs hx)
  have hleft : (∫ x, weightedChartDerivative e a τ v f x * conformalChartTestPullback e η x ∂μ) =
      ∫ x, weightedChartDerivative e a τ v f x * η (e x) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      by_cases hxs : x ∈ e.source
      · rw [conformalChartTestPullback_apply_source e η hxs]
      · have hzero : τ x = 0 := by
          by_contra hn
          exact hxs (hUs (hτ (subset_closure hn)))
        simp [weightedChartDerivative, hzero])
  rw [hleft, weightedChartDerivative_integral_mul μ e he U hU hUs a ha hapos harea
    τ hτ f v η hη hηc hηsub]
  rw [conformalChartTestPullback_integral μ e U hU hUs a ha.continuousOn harea _
    ((weightedChartAdjointCoordinate_tsupport_subset e a τ v η).trans hηsub)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    dsimp only [weightedChartAdjointCoordinate]
    by_cases hzt : z ∈ e.target
    · field_simp [(hapos z hzt).ne']
    · have hd : fderiv ℝ (fun w => τ (e.symm w) * a w * η w) z v = 0 := by
        apply image_eq_zero_of_notMem_tsupport
          (f := fun z => fderiv ℝ (fun w => τ (e.symm w) * a w * η w) z v)
        intro hz
        exact hzt (hΩt (hηsub (tsupport_mul_subset_right
          (tsupport_fderiv_apply_subset ℝ v hz))))
      simp [hd])

#print axioms conformalChartTestPullback_contMDiff
#print axioms weightedChartAdjointTest_contMDiff
#print axioms conformalChartTestPullback_integral
#print axioms weightedChartDerivative_integral_adjoint

end

end SystolicGrowth
