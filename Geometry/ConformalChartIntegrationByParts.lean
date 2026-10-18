module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.WeightedChartDerivative
public import Geometry.GluingConformalAreaCharts
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-!
# Genuine coordinate integration by parts in a conformal chart

Compactly supported tests turn the actual local smooth coordinate
derivative into an integral identity. The existing area law transports
that identity to the original surface measure.
-/

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology ENNReal

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** A locally smooth coordinate function times a smooth test supported
inside its domain is genuinely smooth on the whole coordinate plane. -/
theorem contDiff_coordinate_mul_supported
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ ∞ F Ω) (hη : ContDiff ℝ ∞ η)
    (hsub : tsupport η ⊆ Ω) : ContDiff ℝ ∞ (fun z => F z * η z) := by
  have h : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun z => F z * η z) := by
    apply contMDiff_of_tsupport
    intro z hz
    have hzΩ : z ∈ Ω := hsub (tsupport_mul_subset_right hz)
    exact ((hF.contDiffAt (hΩ.mem_nhds hzΩ)).mul hη.contDiffAt).contMDiffAt
  exact h.contDiff

/-- **Math.** The actual Fréchet coordinate derivative satisfies integration
by parts against every genuine smooth compactly supported test. All three
integrability conditions are consequences, not additional assumptions. -/
theorem coordinate_integral_fderiv_mul_test
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ ∞ F Ω) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hsub : tsupport η ⊆ Ω) (v : ℂ) :
    (∫ z : ℂ, fderiv ℝ F z v * η z) =
      -(∫ z : ℂ, F z * fderiv ℝ η z v) := by
  have hDF : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z v) Ω :=
    (hF.fderiv_of_isOpen hΩ (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiffOn_const
  have hDη : ContDiff ℝ ∞ (fun z => fderiv ℝ η z v) :=
    (hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) by simp)).clm_apply contDiff_const
  have hDηsub : tsupport (fun z => fderiv ℝ η z v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hsub
  have hDFη : Integrable (fun z => fderiv ℝ F z v * η z) :=
    (contDiff_coordinate_mul_supported hΩ hDF hη hsub).continuous.integrable_of_hasCompactSupport
      hηc.mul_left
  have hFDη : Integrable (fun z => F z * fderiv ℝ η z v) :=
    (contDiff_coordinate_mul_supported hΩ hF hDη hDηsub).continuous.integrable_of_hasCompactSupport
      (hηc.fderiv_apply ℝ v).mul_left
  have hFη : Integrable (fun z => F z * η z) :=
    (contDiff_coordinate_mul_supported hΩ hF hη hsub).continuous.integrable_of_hasCompactSupport
      hηc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hDFη hFDη hFη
    (fun z hz => (hF.contDiffAt (hΩ.mem_nhds (hsub hz))).differentiableAt (by simp))
    (fun z _ => (hη.differentiable (by simp)) z)
  linarith

section ChartMeasure

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Math.** The numerical area law on all measurable chart subsets
identifies the actual pullback measure, and hence transports every real
integral. No global measurability of an arbitrary partial chart is needed. -/
theorem conformalChart_setIntegral
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (F : M → ℝ) :
    (∫ x in U, F x ∂μ) = ∫ z : ℂ in e '' U, a z ^ 2 * F (e.symm z) := by
  let Ω := e '' U
  have hΩ : IsOpen Ω := e.isOpen_image_of_subset_source hU hUs
  have hΩt : Ω ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs hx)
  let q : Ω → M := fun z => e.symm z.1
  have hq : MeasurableEmbedding q :=
    (e.symm.continuousOn.mono hΩt).measurableEmbedding hΩ.measurableSet
      (e.symm.injOn.mono hΩt)
  have hv : MeasurableEmbedding (Subtype.val : Ω → ℂ) :=
    MeasurableEmbedding.subtype_coe hΩ.measurableSet
  have hrange : range q = U := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      rcases z.2 with ⟨x, hx, hxz⟩
      change e.symm z.1 ∈ U
      rw [← hxz, e.left_inv (hUs hx)]
      exact hx
    · intro hx
      exact ⟨⟨e x, ⟨x, hx, rfl⟩⟩, e.left_inv (hUs hx)⟩
  let ν : Measure ℂ := volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2))
  have hmeasure : μ.comap q = ν.comap (Subtype.val : Ω → ℂ) := by
    ext s hs
    rw [hq.comap_apply, hv.comap_apply]
    have himage : q '' s = e.symm '' ((Subtype.val : Ω → ℂ) '' s) := by
      rw [image_image]
    rw [himage, harea _ (hv.measurableSet_image.2 hs) (Subtype.coe_image_subset Ω s)]
    exact (withDensity_apply _ (hv.measurableSet_image.2 hs)).symm
  calc
    (∫ x in U, F x ∂μ) = ∫ z : Ω, F (q z) ∂μ.comap q := by
      rw [← hrange, ← hq.map_comap μ, hq.integral_map]
    _ = ∫ z : Ω, F (e.symm z.1) ∂ν.comap (Subtype.val : Ω → ℂ) := by
      rw [hmeasure]
    _ = ∫ z : ℂ in Ω, F (e.symm z) ∂ν :=
      integral_subtype_comap (μ := ν) hΩ.measurableSet (fun z : ℂ => F (e.symm z))
    _ = ∫ z : ℂ in Ω, a z ^ 2 * F (e.symm z) := by
      have hadensity : AEMeasurable (fun z => ENNReal.ofReal (a z ^ 2))
          (volume.restrict Ω) :=
        ((ha.mono hΩt).pow 2).aemeasurable hΩ.measurableSet |>.ennreal_ofReal
      dsimp only [ν]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hadensity
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) _ hΩ.measurableSet]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        dsimp only
        rw [ENNReal.toReal_ofReal (sq_nonneg (a z)), smul_eq_mul])

end ChartMeasure

section WeightedDerivative

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- **Math.** Pullback of the actual weighted gradient component against a
compactly supported test gives the exact Euclidean integration-by-parts
formula with coefficient `(τ ∘ e.symm) * a`. -/
theorem weightedChartDerivative_coordinate_integral
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (τ f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ e.target) :
    (∫ z : ℂ, a z ^ 2 * (weightedChartDerivative e a τ v f (e.symm z) * η z)) =
      -(∫ z : ℂ, f (e.symm z) *
        fderiv ℝ (fun w => τ (e.symm w) * a w * η w) z v) := by
  let Φ : ℂ → ℝ := fun z => τ (e.symm z) * a z * η z
  have hΦ : ContDiff ℝ ∞ Φ :=
    contDiff_coordinate_mul_supported e.open_target
      ((smoothFunction_contDiffOn_chart_inverse e he τ).mul ha) hη hηsub
  have hΦc : HasCompactSupport Φ := hηc.mul_left
  have hΦsub : tsupport Φ ⊆ e.target := tsupport_mul_subset_right.trans hηsub
  have hibp := coordinate_integral_fderiv_mul_test e.open_target
    (smoothFunction_contDiffOn_chart_inverse e he f) hΦ hΦc hΦsub v
  rw [← hibp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z => by
    by_cases hz : η z = 0
    · simp [Φ, hz]
    · have hzt : z ∈ e.target := hηsub (subset_closure hz)
      simp only [weightedChartDerivative, e.right_inv hzt, Φ]
      field_simp [(hapos z hzt).ne'])

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- **Math.** The literal supported smooth gradient component on the
surface satisfies the genuine coordinate weak-derivative identity. The
area law and compact support derive all transport and integration steps. -/
theorem weightedChartDerivative_integral_mul
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
    (∫ x, weightedChartDerivative e a τ v f x * η (e x) ∂μ) =
      -(∫ z : ℂ, f (e.symm z) *
        fderiv ℝ (fun w => τ (e.symm w) * a w * η w) z v) := by
  have hΩ : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hUs
  have hΩt : e '' U ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs hx)
  calc
    (∫ x, weightedChartDerivative e a τ v f x * η (e x) ∂μ) =
        ∫ x in U, weightedChartDerivative e a τ v f x * η (e x) ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : τ x = 0 := by
        by_contra hn
        exact hx (hτ (subset_closure hn))
      simp [weightedChartDerivative, hz]
    _ = ∫ z : ℂ in e '' U,
        a z ^ 2 * (weightedChartDerivative e a τ v f (e.symm z) * η z) := by
      rw [conformalChart_setIntegral μ e U hU hUs a ha.continuousOn harea]
      apply setIntegral_congr_fun hΩ.measurableSet
      intro z hz
      dsimp only
      rw [e.right_inv (hΩt hz)]
    _ = ∫ z : ℂ, a z ^ 2 *
        (weightedChartDerivative e a τ v f (e.symm z) * η z) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero : η z = 0 := by
        by_contra hn
        exact hz (hηsub (subset_closure hn))
      simp [hzero]
    _ = _ := weightedChartDerivative_coordinate_integral e he a ha hapos τ f v η hη hηc
      (hηsub.trans hΩt)

end WeightedDerivative

#print axioms coordinate_integral_fderiv_mul_test
#print axioms conformalChart_setIntegral
#print axioms weightedChartDerivative_coordinate_integral
#print axioms weightedChartDerivative_integral_mul

end

end SystolicGrowth
