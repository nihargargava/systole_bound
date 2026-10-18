module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalClassicalBounds
public import Geometry.GluingConformalDirichlet
public import Geometry.GluingConformalWeakPDE
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Actual canonical patches and weak-to-classical conformal PDE transfer

Canonical seam/interior neighborhoods are constructed with their literal
metric and area coefficients. Their positive area densities transport
a.e. representatives of the actual surface graph value to Lebesgue-a.e.
coordinate representatives, preserving the nonlinear forcing.
-/

open Set Filter Bundle Manifold IsManifold MeasureTheory Riemannian
open scoped Manifold Topology ContDiff
open scoped RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem contDiff_coordinate_mul_supported_of_order {r : ℕ∞ω}
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ r F Ω) (hη : ContDiff ℝ r η)
    (hsub : tsupport η ⊆ Ω) : ContDiff ℝ r (fun z => F z * η z) := by
  have h : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) r
      (fun z => F z * η z) := by
    apply contMDiff_of_tsupport
    intro z hz
    have hzΩ := hsub (tsupport_mul_subset_right hz)
    exact ((hF.contDiffAt (hΩ.mem_nhds hzΩ)).mul hη.contDiffAt).contMDiffAt
  exact h.contDiff

/-- **Math.** A genuine local `C¹` derivative satisfies compact-test
integration by parts, with all integrability conditions derived. -/
theorem coordinate_integral_fderiv_mul_test_C1
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ 1 F Ω) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hsub : tsupport η ⊆ Ω) (d : ℂ) :
    (∫ z : ℂ, fderiv ℝ F z d * η z) = -(∫ z : ℂ, F z * fderiv ℝ η z d) := by
  have hDF : ContDiffOn ℝ 0 (fun z => fderiv ℝ F z d) Ω :=
    (hF.fderiv_of_isOpen hΩ (by norm_num)).clm_apply contDiffOn_const
  have hDη : ContDiff ℝ ∞ (fun z => fderiv ℝ η z d) :=
    (hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const
  have hDηsub := (tsupport_fderiv_apply_subset ℝ d (f := η)).trans hsub
  have hDFη : Integrable (fun z => fderiv ℝ F z d * η z) :=
    (contDiff_coordinate_mul_supported_of_order hΩ hDF (hη.of_le bot_le) hsub).continuous.integrable_of_hasCompactSupport
      hηc.mul_left
  have hone : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top)
  have hFDη : Integrable (fun z => F z * fderiv ℝ η z d) :=
    (contDiff_coordinate_mul_supported_of_order hΩ hF (hDη.of_le hone) hDηsub).continuous.integrable_of_hasCompactSupport
      (hηc.fderiv_apply ℝ d).mul_left
  have hFη : Integrable (fun z => F z * η z) :=
    (contDiff_coordinate_mul_supported_of_order hΩ hF (hη.of_le hone) hsub).continuous.integrable_of_hasCompactSupport
      hηc.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDFη hFDη hFη
    (fun z hz => (hF.contDiffAt (hΩ.mem_nhds (hsub hz))).differentiableAt (by norm_num))
    (fun z _ => hη.differentiable (by simp) z)
  linarith

/-- **Math.** The literal Laplacian trace identity already holds at
classical `C²` regularity, before any infinitely smooth bootstrap. -/
theorem laplacian_complex_eq_conformalPartial_trace_C2 {F : ℂ → ℝ} {z : ℂ}
    (hF : ContDiffAt ℝ 2 F z) :
    Laplacian.laplacian F z = fderiv ℝ (conformalPartialReal F) z 1 +
      fderiv ℝ (conformalPartialImag F) z Complex.I := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt (by norm_num)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  unfold conformalPartialReal conformalPartialImag
  rw [fderiv_clm_apply hdf (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdf (differentiableAt_const Complex.I)]
  simp

private theorem coordinate_integral_second_fderiv_mul_test_C2
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ 2 F Ω) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hsub : tsupport η ⊆ Ω) (d : ℂ) :
    (∫ z : ℂ, F z * fderiv ℝ (fun q => fderiv ℝ η q d) z d) =
      ∫ z : ℂ, fderiv ℝ (fun q => fderiv ℝ F q d) z d * η z := by
  have hDF : ContDiffOn ℝ 1 (fun z => fderiv ℝ F z d) Ω :=
    (hF.fderiv_of_isOpen hΩ (by norm_num)).clm_apply contDiffOn_const
  have hDη : ContDiff ℝ ∞ (fun z => fderiv ℝ η z d) :=
    (hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const
  have h₁ := coordinate_integral_fderiv_mul_test_C1 hΩ (hF.of_le (by norm_num)) hDη
    (hηc.fderiv_apply ℝ d) ((tsupport_fderiv_apply_subset ℝ d).trans hsub) d
  have h₂ := coordinate_integral_fderiv_mul_test_C1 hΩ hDF hη hηc hsub d
  linarith

/-- **Math.** Twice genuine integration by parts transfers the actual
Euclidean Laplacian between a local `C²` function and a compactly supported
smooth test. Integrability is derived from the true support and regularity. -/
theorem coordinate_integral_laplacian_mul_test_C2
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ 2 F Ω) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hsub : tsupport η ⊆ Ω) :
    (∫ z : ℂ, F z * Laplacian.laplacian η z) =
      ∫ z : ℂ, Laplacian.laplacian F z * η z := by
  let DD (f : ℂ → ℝ) (d : ℂ) : ℂ → ℝ := fun z => fderiv ℝ (fun q => fderiv ℝ f q d) z d
  have hηDD (d : ℂ) : ContDiff ℝ ∞ (DD η d) :=
    (((hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const).fderiv_right
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const
  have hηDDsub (d : ℂ) : tsupport (DD η d) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ d).trans ((tsupport_fderiv_apply_subset ℝ d).trans hsub)
  have hFDD (d : ℂ) : ContDiffOn ℝ 0 (DD F d) Ω :=
    (((hF.fderiv_of_isOpen hΩ (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).clm_apply contDiffOn_const).fderiv_of_isOpen
      hΩ (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply contDiffOn_const
  have hLeftInt (d : ℂ) : Integrable (fun z => F z * DD η d z) :=
    (contDiff_coordinate_mul_supported_of_order hΩ (hF.of_le bot_le) ((hηDD d).of_le bot_le)
      (hηDDsub d)).continuous.integrable_of_hasCompactSupport
        ((hηc.fderiv_apply ℝ d).fderiv_apply ℝ d).mul_left
  have hRightInt (d : ℂ) : Integrable (fun z => DD F d z * η z) :=
    (contDiff_coordinate_mul_supported_of_order hΩ (hFDD d) (hη.of_le bot_le)
      hsub).continuous.integrable_of_hasCompactSupport hηc.mul_left
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hLeft : (fun z => F z * Laplacian.laplacian η z) =
      fun z => F z * DD η 1 z + F z * DD η Complex.I z := by
    funext z
    rw [laplacian_complex_eq_conformalPartial_trace_C2 (hη.contDiffAt.of_le htwo)]
    exact mul_add _ _ _
  have hRight : (fun z => Laplacian.laplacian F z * η z) =
      fun z => DD F 1 z * η z + DD F Complex.I z * η z := by
    funext z
    by_cases hz : z ∈ Ω
    · rw [laplacian_complex_eq_conformalPartial_trace_C2 (hF.contDiffAt (hΩ.mem_nhds hz))]
      exact add_mul _ _ _
    · have hzero : η z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h))
      simp only [hzero, mul_zero, add_zero]
  rw [hLeft, hRight, integral_add (hLeftInt 1) (hLeftInt Complex.I),
    integral_add (hRightInt 1) (hRightInt Complex.I),
    coordinate_integral_second_fderiv_mul_test_C2 hΩ hF hη hηc hsub 1,
    coordinate_integral_second_fderiv_mul_test_C2 hΩ hF hη hηc hsub Complex.I]

private theorem continuous_coordinate_mul_supported
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContinuousOn F Ω) (hη : Continuous η) (hsub : tsupport η ⊆ Ω) :
    Continuous (fun z => F z * η z) := by
  apply continuous_of_tsupport
  intro z hz
  exact (hF.continuousAt (hΩ.mem_nhds (hsub (tsupport_mul_subset_right hz)))).mul hη.continuousAt

/-- **Math.** Genuine local `C²` regularity and the distributional
Laplacian equation imply the literal PDE at every point. The proof uses
actual integration by parts, the fundamental test-function lemma and
positivity of Lebesgue measure on nonempty open sets. -/
theorem classical_laplacian_eq_of_test_integrals_C2
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F G : ℂ → ℝ}
    (hF : ContDiffOn ℝ 2 F Ω) (hG : ContinuousOn G Ω)
    (hweak : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ω →
      (∫ z : ℂ, F z * Laplacian.laplacian η z) = ∫ z : ℂ, G z * η z) :
    ∀ z ∈ Ω, Laplacian.laplacian F z = G z := by
  have hDD (d : ℂ) : ContinuousOn (fun z => fderiv ℝ (fun q => fderiv ℝ F q d) z d) Ω :=
    ((((hF.fderiv_of_isOpen hΩ (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).clm_apply contDiffOn_const).fderiv_of_isOpen
      hΩ (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply contDiffOn_const).continuousOn
  have hLap : ContinuousOn (Laplacian.laplacian F) Ω := by
    apply ((hDD 1).add (hDD Complex.I)).congr
    intro z hz
    exact laplacian_complex_eq_conformalPartial_trace_C2 (hF.contDiffAt (hΩ.mem_nhds hz))
  let H : ℂ → ℝ := fun z => Laplacian.laplacian F z - G z
  have hH : ContinuousOn H Ω := hLap.sub hG
  have hzero : ∀ᵐ z ∂volume, z ∈ Ω → H z = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hH.locallyIntegrableOn hΩ.measurableSet)
    intro η hη hηc hsub
    have hLapInt : Integrable (fun z => Laplacian.laplacian F z * η z) :=
      (continuous_coordinate_mul_supported hΩ hLap hη.continuous hsub).integrable_of_hasCompactSupport hηc.mul_left
    have hGInt : Integrable (fun z => G z * η z) :=
      (continuous_coordinate_mul_supported hΩ hG hη.continuous hsub).integrable_of_hasCompactSupport hηc.mul_left
    calc
      (∫ z : ℂ, η z • H z) =
          (∫ z : ℂ, Laplacian.laplacian F z * η z) - ∫ z : ℂ, G z * η z := by
        rw [← integral_sub hLapInt hGInt]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun z => by dsimp [H]; ring)
      _ = 0 := by
        rw [← coordinate_integral_laplacian_mul_test_C2 hΩ hF hη hηc hsub, hweak η hη hηc hsub]
        exact sub_self _
  have hAE : H =ᵐ[volume.restrict Ω] (fun _ => 0) :=
    (ae_restrict_iff' hΩ.measurableSet).mpr hzero
  have heq := Measure.eqOn_open_of_ae_eq hAE hΩ hH continuousOn_const
  intro z hz
  exact sub_eq_zero.mp (heq hz)

section ChartMeasure

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Math.** The ACTUAL positive conformal area law transports every
surface-a.e. equality to Lebesgue-a.e. equality on the coordinate region.
No representative transport is supplied as an additional premise. -/
theorem conformalChart_ae_eq_pullback_iff
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    {F G : M → ℝ} :
    F =ᵐ[μ.restrict U] G ↔ (F ∘ e.symm) =ᵐ[volume.restrict (e '' U)] (G ∘ e.symm) := by
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
  let ν : Measure ℂ := volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2))
  have hmeasure : μ.comap q = ν.comap (Subtype.val : Ω → ℂ) := by
    ext s hs
    rw [hq.comap_apply, hv.comap_apply]
    have himage : q '' s = e.symm '' ((Subtype.val : Ω → ℂ) '' s) := by rw [image_image]
    rw [himage, harea _ (hv.measurableSet_image.2 hs) (Subtype.coe_image_subset Ω s)]
    exact (withDensity_apply _ (hv.measurableSet_image.2 hs)).symm
  have hrange : range q = U := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx, hxz⟩ := z.2
      change e.symm z.1 ∈ U
      rw [← hxz, e.left_inv (hUs hx)]
      exact hx
    · intro hx
      exact ⟨⟨e x, ⟨x, hx, rfl⟩⟩, e.left_inv (hUs hx)⟩
  have haDensity : AEMeasurable (fun z => ENNReal.ofReal (a z ^ 2)) (volume.restrict Ω) :=
    ((ha.mono hΩt).pow 2).aemeasurable hΩ.measurableSet |>.ennreal_ofReal
  constructor
  · intro hFG
    have hsub : ∀ᵐ z ∂μ.comap q, F (q z) = G (q z) := by
      apply (hq.ae_map_iff (μ := μ.comap q) (p := fun x => F x = G x)).mp
      rw [hq.map_comap, hrange]
      exact hFG
    rw [hmeasure] at hsub
    have hdens : (F ∘ e.symm) =ᵐ[ν.restrict Ω] (G ∘ e.symm) :=
      (ae_restrict_iff_subtype hΩ.measurableSet).mpr hsub
    rw [show ν = volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2)) from rfl,
      restrict_withDensity hΩ.measurableSet] at hdens
    have hLeb := (ae_withDensity_iff' haDensity).mp hdens
    filter_upwards [hLeb, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
    exact hz (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hapos z (hΩt hzΩ)))))
  · intro hFG
    have hdens : (F ∘ e.symm) =ᵐ[ν.restrict Ω] (G ∘ e.symm) := by
      rw [show ν = volume.withDensity (fun z => ENNReal.ofReal (a z ^ 2)) from rfl,
        restrict_withDensity hΩ.measurableSet]
      apply (ae_withDensity_iff' haDensity).mpr
      filter_upwards [hFG] with z hz _
      exact hz
    have hsub : ∀ᵐ z ∂μ.comap q, F (q z) = G (q z) := by
      rw [hmeasure]
      exact (ae_restrict_iff_subtype hΩ.measurableSet).mp hdens
    have hmap := (hq.ae_map_iff (μ := μ.comap q) (p := fun x => F x = G x)).mpr hsub
    rwa [hq.map_comap, hrange] at hmap

/-- **Math.** Global surface-a.e. representatives pull back to the actual
Lebesgue coordinate representatives on every genuine conformal region. -/
theorem conformalChart_ae_eq_pullback
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    {F G : M → ℝ} (hFG : F =ᵐ[μ] G) :
    (F ∘ e.symm) =ᵐ[volume.restrict (e '' U)] (G ∘ e.symm) :=
  (conformalChart_ae_eq_pullback_iff μ e U hU hUs a ha hapos harea).mp (ae_restrict_of_ae hFG)

end ChartMeasure

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Every isolated canonical seam chart has a genuine open
metric/area patch with precisely its ORIGINAL chart and its constructed
isothermal change. No arbitrary selected finite-atlas patch is substituted. -/
theorem exists_gluedConformalCanonicalSeamPatch
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (k : Fin (n - 1)) (θ : ℝ)
    (hchart : chartAt ℂ b = P.seamAngularComplexChart k θ)
    (hother : ∀ l : Fin (n - 1), l ≠ k → b ∉ P.closedThinSeamCollar l) :
    ∃ Q : GluedConformalPatch P,
      Q.original = P.seamAngularComplexChart k θ ∧
      Q.change = P.gluedCurvatureBoundedSeamConformalChange ∧
      Q.coefficient = P.gluedCurvatureBoundedSeamConformalFactor ∧ b ∈ Q.region := by
  have hb : b ∈ (P.seamAngularComplexChart k θ).source := by rw [← hchart]; exact mem_chart_source ℂ b
  have hotherNear : ∀ᶠ c in 𝓝 b, ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l := by
    rw [Filter.eventually_all]
    intro l
    by_cases hl : l = k
    · exact Filter.Eventually.of_forall (fun _ h => (h hl).elim)
    · filter_upwards [(P.closedThinSeamCollar_isCompact l).isClosed.isOpen_compl.mem_nhds (hother l hl)]
        with c hc _ hthin
      exact hc (P.thinSeamCollar_subset_closedThinSeamCollar l hthin)
  have hnear : ∀ᶠ c in 𝓝 b, c ∈ (P.seamAngularComplexChart k θ).source ∧
      ∀ l : Fin (n - 1), l ≠ k → c ∉ P.thinSeamCollar l := by
    filter_upwards [(P.seamAngularComplexChart k θ).open_source.mem_nhds hb, hotherNear] with c hc ho
    exact ⟨hc, ho⟩
  obtain ⟨U, hUsub, hU, hbU⟩ := mem_nhds_iff.mp hnear
  have hUsource : U ⊆ (P.gluedCurvatureBoundedSeamConformalChart k θ).source := by
    intro c hc
    simpa only [gluedCurvatureBoundedSeamConformalChart_source] using (hUsub hc).1
  let Q : GluedConformalPatch P := {
    original := P.seamAngularComplexChart k θ
    original_mem := Or.inr ⟨k, θ, rfl⟩
    change := P.gluedCurvatureBoundedSeamConformalChange
    coefficient := P.gluedCurvatureBoundedSeamConformalFactor
    inverseDerivative := P.gluedCurvatureBoundedSeamConformalInverseDerivative
    region := U
    region_open := hU
    region_subset := hUsource
    change_source := P.gluedCurvatureBoundedSeamConformalChange_source
    change_smooth := P.gluedCurvatureBoundedSeamConformalChange_contDiff
    chart_mem := P.gluedCurvatureBoundedSeamConformalChart_mem_maximalAtlas k θ
    coefficient_smooth := P.gluedCurvatureBoundedSeamConformalFactor_contDiffOn.mono (fun _ hz => hz.1)
    coefficient_pos := fun z _ => P.gluedCurvatureBoundedSeamConformalFactor_pos z
    derivative_eq := fun z hz => P.gluedCurvatureBoundedSeamConformalChange_symm_hasFDerivAt hz
    metric_eq := fun c hc v w => P.gluedCurvatureBoundedSmoothMetric_in_conformal_seam_chart
      k θ c (hUsub hc).1 (hUsub hc).2 v w
    area_eq := by
      intro s hs hsub
      apply P.gluedCurvatureBoundedAreaMeasure_conformal_seam_chart_image k θ hs
      · rintro z hz
        obtain ⟨c, hc, rfl⟩ := hsub hz
        exact (P.gluedCurvatureBoundedSeamConformalChart k θ).map_source (hUsource hc)
      · intro z hz l hl
        obtain ⟨c, hc, rfl⟩ := hsub hz
        change (P.gluedCurvatureBoundedSeamConformalChart k θ).symm
          (P.gluedCurvatureBoundedSeamConformalChart k θ c) ∉ P.thinSeamCollar l
        rw [(P.gluedCurvatureBoundedSeamConformalChart k θ).left_inv (hUsource hc)]
        exact (hUsub hc).2 l hl }
  exact ⟨Q, rfl, rfl, rfl, hbU⟩

/-- **Math.** Every canonical exterior interior chart has a genuine open
patch with that SAME chart and the literal positive coefficient `1 / Im z`. -/
theorem exists_gluedConformalCanonicalInteriorPatch
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (hi : P.IsGluedInteriorComplexChart (chartAt ℂ b))
    (hout : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k) :
    ∃ Q : GluedConformalPatch P,
      Q.original = chartAt ℂ b ∧ Q.change = OpenPartialHomeomorph.refl ℂ ∧
      Q.coefficient = (fun z => z.im⁻¹) ∧ b ∈ Q.region := by
  let e := chartAt ℂ b
  have hb : b ∈ e.source := mem_chart_source ℂ b
  have houtNear : ∀ᶠ c in 𝓝 b, ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
    rw [Filter.eventually_all]
    intro k
    filter_upwards [(P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (hout k)]
      with c hc hthin
    exact hc (P.thinSeamCollar_subset_closedThinSeamCollar k hthin)
  have hnear : ∀ᶠ c in 𝓝 b, c ∈ e.source ∧ ∀ k : Fin (n - 1), c ∉ P.thinSeamCollar k := by
    filter_upwards [e.open_source.mem_nhds hb, houtNear] with c hc ho
    exact ⟨hc, ho⟩
  obtain ⟨U, hUsub, hU, hbU⟩ := mem_nhds_iff.mp hnear
  have hUsource : U ⊆ e.source := fun c hc => (hUsub hc).1
  let Q : GluedConformalPatch P := {
    original := e
    original_mem := Or.inl hi
    change := OpenPartialHomeomorph.refl ℂ
    coefficient := fun z => z.im⁻¹
    inverseDerivative := fun _ => ContinuousLinearMap.id ℝ ℂ
    region := U
    region_open := hU
    region_subset := by simpa using hUsource
    change_source := rfl
    change_smooth := contDiff_id
    chart_mem := by simpa using (chart_mem_maximalAtlas (I := modelWithCornersSelf ℝ ℂ) (n := ∞) b)
    coefficient_smooth := by
      simp only [OpenPartialHomeomorph.trans_refl]
      exact Complex.imCLM.contDiff.contDiffOn.inv
        (fun z hz => (P.gluedInteriorComplexChart_target_im_pos e hi hz).ne')
    coefficient_pos := fun z hz => inv_pos.mpr (P.gluedInteriorComplexChart_target_im_pos e hi (by simpa using hz))
    derivative_eq := fun z _ => hasFDerivAt_id z
    metric_eq := by
      intro c hc v w
      simpa using P.gluedCurvatureBoundedSmoothMetric_in_conformal_interior_chart e hi c (hUsub hc).1 (hUsub hc).2 v w
    area_eq := by
      simp only [OpenPartialHomeomorph.trans_refl]
      intro s hs hsub
      apply P.gluedCurvatureBoundedAreaMeasure_conformal_interior_chart_image e hi hs
      · rintro z hz
        obtain ⟨c, hc, rfl⟩ := hsub hz
        exact e.map_source (hUsource hc)
      · intro z hz k
        obtain ⟨c, hc, rfl⟩ := hsub hz
        rw [e.left_inv (hUsource hc)]
        exact (hUsub hc).2 k }
  exact ⟨Q, rfl, rfl, rfl, hbU⟩

/-- **Math.** A classical `C²` representative of the ACTUAL graph value
satisfies the literal scalar PDE on every genuine metric/area patch. Its
weak PDE is derived from the graph equation and then transported through
the positive area density; no classical PDE premise is supplied. -/
theorem gluedConformalGradient_classical_patch_pde_of_representative
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
          P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
          (conformalH1Value _ _ w))
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) 2 u)
    (hAE : u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
      (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v : P.GluedCarrier → ℝ))
    (Q : GluedConformalPatch P) (b : P.GluedCarrier) (hb : b ∈ Q.region) :
    let e := Q.original.trans Q.change
    Laplacian.laplacian (u ∘ e.symm) (e b) =
      Q.coefficient (e b) ^ 2 * (P.gluedCurvatureBoundedGaussian b + conformalCurvatureNonlinearity B (u b)) := by
  let e := Q.original.trans Q.change
  let Ω := e '' Q.region
  let F : ℂ → ℝ := u ∘ e.symm
  let u₀ := conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v
  let G : ℂ → ℝ := fun z => Q.coefficient z ^ 2 *
    (P.gluedCurvatureBoundedGaussian (e.symm z) + conformalCurvatureNonlinearity B (F z))
  have hΩ : IsOpen Ω := e.isOpen_image_of_subset_source Q.region_open Q.region_subset
  have hΩt : Ω ⊆ e.target := by
    rintro z ⟨c, hc, rfl⟩
    exact e.map_source (Q.region_subset hc)
  have htwo : (2 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)
  have hF : ContDiffOn ℝ 2 F e.target :=
    (hu.comp_contMDiffOn ((contMDiffOn_symm_of_mem_maximalAtlas Q.chart_mem).of_le htwo)).contDiffOn
  have hK : ContinuousOn (fun z => P.gluedCurvatureBoundedGaussian (e.symm z)) e.target :=
    P.gluedCurvatureBoundedGaussian_contMDiff.continuous.comp_continuousOn e.symm.continuousOn
  have hG : ContinuousOn G e.target :=
    (Q.coefficient_smooth.continuousOn.pow 2).mul
      (hK.add ((conformalCurvatureNonlinearity_contDiff B).continuous.comp_continuousOn hF.continuousOn))
  have hRep : ∀ᵐ z ∂volume, z ∈ Ω → F z = u₀ (e.symm z) :=
    ae_imp_of_ae_restrict (conformalChart_ae_eq_pullback P.gluedCurvatureBoundedAreaMeasure e Q.region
      Q.region_open Q.region_subset Q.coefficient Q.coefficient_smooth.continuousOn Q.coefficient_pos Q.area_eq hAE)
  have htests : ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ Ω →
      (∫ z : ℂ, F z * Laplacian.laplacian η z) = ∫ z : ℂ, G z * η z := by
    intro η hη hηc hηsub
    have htest := P.gluedConformalGradient_weak_laplacian B hB v hweak Q η hη hηc hηsub
    have hleft : (∫ z : ℂ, F z * Laplacian.laplacian η z) =
        ∫ z : ℂ, u₀ (e.symm z) * Laplacian.laplacian η z := by
      apply integral_congr_ae
      filter_upwards [hRep] with z hz
      by_cases hzΩ : z ∈ Ω
      · rw [hz hzΩ]
      · have hzero : Laplacian.laplacian η z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hzΩ (hηsub (tsupport_complex_laplacian_subset hη h)))
        simp only [hzero, mul_zero]
    have hright : (∫ z : ℂ, Q.coefficient z ^ 2 *
          ((P.gluedCurvatureBoundedGaussian (e.symm z) + conformalCurvatureNonlinearity B (u₀ (e.symm z))) * η z)) =
        ∫ z : ℂ, G z * η z := by
      apply integral_congr_ae
      filter_upwards [hRep] with z hz
      by_cases hzΩ : z ∈ Ω
      · dsimp [G]
        rw [← hz hzΩ]
        ring
      · have hzero : η z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzΩ (hηsub h))
        simp only [hzero, mul_zero]
    exact hleft.trans (htest.trans hright)
  have hpoint := classical_laplacian_eq_of_test_integrals_C2 hΩ (hF.mono hΩt) (hG.mono hΩt)
    htests (e b) ⟨b, hb, rfl⟩
  change Laplacian.laplacian (u ∘ e.symm) (e b) = Q.coefficient (e b) ^ 2 *
    (P.gluedCurvatureBoundedGaussian (e.symm (e b)) + conformalCurvatureNonlinearity B (u (e.symm (e b)))) at hpoint
  rw [e.left_inv (Q.region_subset hb)] at hpoint
  exact hpoint

/-- **Math.** The actual graph weak solution's global classical `C²`
representative satisfies every canonical nonlinear scalar equation.
Both the canonical patches and the PDE are constructed internally. -/
theorem gluedConformalGradient_classicalPDE_of_representative
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
          P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
          (conformalH1Value _ _ w))
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) 2 u)
    (hAE : u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
      (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v : P.GluedCarrier → ℝ)) :
    P.GluedConformalNonlinearClassicalPDE (conformalCurvatureNonlinearity B) u := by
  constructor
  · intro b k θ hchart hother
    obtain ⟨Q, hQe, hQψ, hQa, hb⟩ := P.exists_gluedConformalCanonicalSeamPatch b k θ hchart hother
    have h := P.gluedConformalGradient_classical_patch_pde_of_representative B hB v hweak u hu hAE Q b hb
    simpa only [hQe, hQψ, hQa, gluedCurvatureBoundedSeamConformalChart] using h
  · intro b hi hout
    obtain ⟨Q, hQe, hQψ, hQa, hb⟩ := P.exists_gluedConformalCanonicalInteriorPatch b hi hout
    have h := P.gluedConformalGradient_classical_patch_pde_of_representative B hB v hweak u hu hAE Q b hb
    simpa only [hQe, hQψ, hQa, OpenPartialHomeomorph.trans_refl] using h

/-- **Math.** An actual smooth representative of the constructed graph
solution supplies ALL geometric source fields. The canonical PDE,
maximum-principle bounds, conformal metric, intrinsic curvature, unchanged
systole, marked representation and coherent lift are all derived by the
verified chain; none of those conclusions is supplied as an input. -/
def gluedConformalGradientLiftedOutput_of_smooth_representative
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g)
    (B : ℝ) (hB : 1 < B)
    (hK : ∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ))
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
          P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
          (conformalH1Value _ _ w))
    (u : P.GluedCarrier → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (hAE : u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
      (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v : P.GluedCarrier → ℝ)) :
    ExerciseLiftedChainOutput g (targetSystole C g) :=
  P.gluedConformalPsiLiftedOutput x hn hsum B hB hK u hu
    (P.gluedConformalGradient_classicalPDE_of_representative B hB v hweak u
      (hu.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))) hAE)

#print axioms exists_gluedConformalCanonicalSeamPatch
#print axioms exists_gluedConformalCanonicalInteriorPatch
#print axioms gluedConformalGradient_classical_patch_pde_of_representative
#print axioms gluedConformalGradient_classicalPDE_of_representative
#print axioms gluedConformalGradientLiftedOutput_of_smooth_representative

end ExerciseGluingPreparation

#print axioms conformalChart_ae_eq_pullback
#print axioms conformalChart_ae_eq_pullback_iff
#print axioms coordinate_integral_laplacian_mul_test_C2
#print axioms classical_laplacian_eq_of_test_integrals_C2

end

end SystolicGrowth
