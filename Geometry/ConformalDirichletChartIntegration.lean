module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalDirichletIntegral
public import Geometry.ConformalChartAdjointTests
public import Geometry.ConformalWarpLaplacian

@[expose] public section

/-!
# The actual Dirichlet adjoint on an arbitrary conformal patch

The finite-gradient solver may be tested in any genuine conformal patch,
not only its selected finite cover. The same metric and its actual local
area law reduce the Dirichlet pairing to the Euclidean Laplacian test.
-/

open Set Filter Manifold IsManifold MeasureTheory Riemannian
open scoped ContDiff Manifold Topology

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** Genuine scalar coordinate partial derivatives of a smooth
function remain smooth. -/
theorem contDiff_complex_partial {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ η z v) :=
  (hη.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const

/-- **Math.** The literal Euclidean Laplacian of a smooth test is smooth. -/
theorem contDiff_complex_laplacian {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (Laplacian.laplacian η) := by
  have heq : Laplacian.laplacian η = fun z =>
      fderiv ℝ (fun w => fderiv ℝ η w 1) z 1 +
        fderiv ℝ (fun w => fderiv ℝ η w Complex.I) z Complex.I := by
    funext z
    exact laplacian_complex_eq_conformalPartial_trace (hη.contDiffAt (x := z))
  rw [heq]
  exact (contDiff_complex_partial (contDiff_complex_partial hη 1) 1).add
    (contDiff_complex_partial (contDiff_complex_partial hη Complex.I) Complex.I)

/-- **Math.** Differentiation does not enlarge a smooth test's support. -/
theorem tsupport_complex_laplacian_subset {η : ℂ → ℝ} (hη : ContDiff ℝ ∞ η) :
    tsupport (Laplacian.laplacian η) ⊆ tsupport η := by
  have heq : Laplacian.laplacian η = fun z =>
      fderiv ℝ (fun w => fderiv ℝ η w 1) z 1 +
        fderiv ℝ (fun w => fderiv ℝ η w Complex.I) z Complex.I := by
    funext z
    exact laplacian_complex_eq_conformalPartial_trace (hη.contDiffAt (x := z))
  rw [heq]
  apply (tsupport_add _ _).trans
  apply union_subset
  · exact (tsupport_fderiv_apply_subset ℝ 1).trans (tsupport_fderiv_apply_subset ℝ 1)
  · exact (tsupport_fderiv_apply_subset ℝ Complex.I).trans
      (tsupport_fderiv_apply_subset ℝ Complex.I)

/-- **Math.** The Euclidean Dirichlet pairing has the true negative
Laplacian adjoint for a compactly supported smooth coordinate test. -/
theorem coordinate_dirichlet_integral_eq_neg_laplacian
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {F η : ℂ → ℝ}
    (hF : ContDiffOn ℝ ∞ F Ω) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηsub : tsupport η ⊆ Ω) :
    (∫ z : ℂ, fderiv ℝ F z 1 * fderiv ℝ η z 1 +
        fderiv ℝ F z Complex.I * fderiv ℝ η z Complex.I) =
      -(∫ z : ℂ, F z * Laplacian.laplacian η z) := by
  have hDη (v : ℂ) := contDiff_complex_partial hη v
  have hDsub (v : ℂ) : tsupport (fun z => fderiv ℝ η z v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hηsub
  have hDF (v : ℂ) : ContDiffOn ℝ ∞ (fun z => fderiv ℝ F z v) Ω :=
    (hF.fderiv_of_isOpen hΩ (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiffOn_const
  have hL (v : ℂ) : Integrable (fun z => fderiv ℝ F z v * fderiv ℝ η z v) :=
    (contDiff_coordinate_mul_supported hΩ (hDF v) (hDη v) (hDsub v)).continuous.integrable_of_hasCompactSupport
      (hηc.fderiv_apply ℝ v).mul_left
  have hR (v : ℂ) : Integrable
      (fun z => F z * fderiv ℝ (fun w => fderiv ℝ η w v) z v) :=
    (contDiff_coordinate_mul_supported hΩ hF (contDiff_complex_partial (hDη v) v)
      ((tsupport_fderiv_apply_subset ℝ v).trans (hDsub v))).continuous.integrable_of_hasCompactSupport
      ((hηc.fderiv_apply ℝ v).fderiv_apply ℝ v).mul_left
  rw [integral_add (hL 1) (hL Complex.I)]
  rw [coordinate_integral_fderiv_mul_test hΩ hF (hDη 1)
    (hηc.fderiv_apply ℝ 1) (hDsub 1) 1,
    coordinate_integral_fderiv_mul_test hΩ hF (hDη Complex.I)
      (hηc.fderiv_apply ℝ Complex.I) (hDsub Complex.I) Complex.I]
  rw [← neg_add, ← integral_add (hR 1) (hR Complex.I)]
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  rw [laplacian_complex_eq_conformalPartial_trace (hη.contDiffAt (x := z))]
  exact (mul_add _ _ _).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- **Math.** The actual manifold differential vanishes off a function's
topological support because the function is locally identically zero. -/
theorem smoothFunction_mfderiv_zero_of_notMem_tsupport
    (h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) (hx : x ∉ tsupport h) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ) h x = 0 := by
  have heq : (h : M → ℝ) =ᶠ[𝓝 x] fun _ => 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  rw [heq.mfderiv_eq, mfderiv_const]
  simp

variable [IsManifold 𝓘(ℝ, ℂ) ∞ M]

/-- **Math.** The intrinsic Dirichlet density vanishes wherever the test
function is locally zero. -/
theorem smoothDirichletDensity_eq_zero_off_support
    (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
    (f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) (hx : x ∉ tsupport h) :
    smoothDirichletDensity g f h x = 0 := by
  have hzero : g.metricRiesz x (0 : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) = 0 := by
    symm
    apply g.metricRiesz_unique
    intro w
    change g.inner x 0 w = 0
    simp
  rw [smoothDirichletDensity, smoothFunction_mfderiv_zero_of_notMem_tsupport h x hx,
    hzero]
  simp

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M] in
/-- **Math.** A zero-extended chart test has its literal coordinate
derivative at every point in the chart target. -/
theorem conformalChartTestPullback_fderiv_symm
    (e : OpenPartialHomeomorph M ℂ) (η : ℂ → ℝ)
    {z : ℂ} (hz : z ∈ e.target) :
    fderiv ℝ (fun w => conformalChartTestPullback e η (e.symm w)) z =
      fderiv ℝ η z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [e.open_target.mem_nhds hz] with w hw
  rw [conformalChartTestPullback_apply_source e η (e.map_target hw), e.right_inv hw]

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- **Math.** The true intrinsic Dirichlet integral against a smooth
chart test reduces to the Euclidean negative Laplacian, using the actual
tensor and area laws on that patch. -/
theorem smoothDirichletDensity_integral_test
    (μ : Measure M) (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (hmetric : ∀ x (hx : x ∈ U) v w,
      g.inner x (conformalChartInverseTangent e he x (hUs hx) v)
        (conformalChartInverseTangent e he x (hUs hx) w) =
          a (e x) ^ 2 * (v.re * w.re + v.im * w.im))
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ e '' U) (hηt : tsupport η ⊆ e.target)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    let T : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ := ⟨conformalChartTestPullback e η,
      conformalChartTestPullback_contMDiff e he η hη hηc hηt⟩
    (∫ x, smoothDirichletDensity g f T x ∂μ) =
      -(∫ z : ℂ, f (e.symm z) * Laplacian.laplacian η z) := by
  intro T
  have hΩ : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hUs
  have hΩt : e '' U ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hUs hx)
  have hTs : tsupport T ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := conformalChartTestPullback_tsupport_subset e η hηc hηt hx
    obtain ⟨y, hy, rfl⟩ := hηsub hz
    simpa only [e.left_inv (hUs hy)] using hy
  calc
    _ = ∫ x in U, smoothDirichletDensity g f T x ∂μ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      exact smoothDirichletDensity_eq_zero_off_support g f T x (fun ht => hx (hTs ht))
    _ = ∫ z : ℂ in e '' U,
        fderiv ℝ (fun w => f (e.symm w)) z 1 * fderiv ℝ η z 1 +
          fderiv ℝ (fun w => f (e.symm w)) z Complex.I * fderiv ℝ η z Complex.I := by
      rw [conformalChart_setIntegral μ e U hU hUs a ha harea]
      apply setIntegral_congr_fun hΩ.measurableSet
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      dsimp only
      rw [e.left_inv (hUs hx),
        smoothDirichletDensity_in_conformal_chart g e he x (hUs hx) (a (e x))
          (hapos _ (e.map_source (hUs hx))).ne' (hmetric x hx) f T]
      change a (e x) ^ 2 * ((a (e x) ^ 2)⁻¹ *
        (fderiv ℝ (fun w => f (e.symm w)) (e x) 1 *
            fderiv ℝ (fun w => conformalChartTestPullback e η (e.symm w)) (e x) 1 +
          fderiv ℝ (fun w => f (e.symm w)) (e x) Complex.I *
            fderiv ℝ (fun w => conformalChartTestPullback e η (e.symm w)) (e x) Complex.I)) = _
      rw [conformalChartTestPullback_fderiv_symm e η (e.map_source (hUs hx))]
      field_simp [(hapos _ (e.map_source (hUs hx))).ne']
    _ = ∫ z : ℂ,
        fderiv ℝ (fun w => f (e.symm w)) z 1 * fderiv ℝ η z 1 +
          fderiv ℝ (fun w => f (e.symm w)) z Complex.I * fderiv ℝ η z Complex.I := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hd : fderiv ℝ η z = 0 :=
        fderiv_of_notMem_tsupport ℝ (fun ht => hz (hηsub ht))
      simp [hd]
    _ = _ := coordinate_dirichlet_integral_eq_neg_laplacian hΩ
      ((smoothFunction_contDiffOn_chart_inverse e he f).mono hΩt) hη hηc hηsub

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- **Math.** The coordinate Laplacian divided by the true area density
is a smooth compact global test after zero-extension. -/
theorem conformalChartLaplacianAdjoint_contDiff
    (e : OpenPartialHomeomorph M ℂ)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηt : tsupport η ⊆ e.target) :
    ContDiff ℝ ∞ (fun z => (a z ^ 2)⁻¹ * Laplacian.laplacian η z) :=
  contDiff_coordinate_mul_supported e.open_target
    ((ha.pow 2).inv (fun z hz => pow_ne_zero _ (hapos z hz).ne'))
    (contDiff_complex_laplacian hη) ((tsupport_complex_laplacian_subset hη).trans hηt)

omit [ChartedSpace ℂ M] [IsManifold 𝓘(ℝ, ℂ) ∞ M] in
/-- **Math.** Transporting the Laplacian adjoint back to the surface
cancels the exact conformal area coefficient, for any function. -/
theorem conformalChartLaplacianAdjoint_integral
    (μ : Measure M) (e : OpenPartialHomeomorph M ℂ)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContinuousOn a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηsub : tsupport η ⊆ e '' U)
    (F : M → ℝ) :
    (∫ x, F x * conformalChartTestPullback e
      (fun z => (a z ^ 2)⁻¹ * Laplacian.laplacian η z) x ∂μ) =
        ∫ z : ℂ, F (e.symm z) * Laplacian.laplacian η z := by
  have hsub : tsupport (fun z => (a z ^ 2)⁻¹ * Laplacian.laplacian η z) ⊆ e '' U :=
    tsupport_mul_subset_right.trans ((tsupport_complex_laplacian_subset hη).trans hηsub)
  rw [conformalChartTestPullback_integral μ e U hU hUs a ha harea _ hsub]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ e.target
  · field_simp [(hapos z hz).ne']
  · have hzero : Laplacian.laplacian η z = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      obtain ⟨x, hx, heq⟩ := hηsub (tsupport_complex_laplacian_subset hη hs)
      exact hz (heq ▸ e.map_source (hUs hx))
    simp [hzero]

#print axioms coordinate_dirichlet_integral_eq_neg_laplacian
#print axioms smoothDirichletDensity_eq_zero_off_support
#print axioms smoothDirichletDensity_integral_test
#print axioms conformalChartLaplacianAdjoint_integral

end

end SystolicGrowth
