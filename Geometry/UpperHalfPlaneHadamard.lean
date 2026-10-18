module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.UpperHalfPlaneRiemannianDistance
public import Geometry.UpperHalfPlaneCurvature
public import Geometry.ExponentialGlobalPolarMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.HadamardComplete

@[expose] public section

/-!
# The actual hyperbolic model's global exponential and metric frame

Mathlib's original hyperbolic distance is the distance of the constructed
Poincaré tensor. Its original topology is contractible by the convex
upper-half-plane construction, and its metric is complete.
-/

open Bundle Manifold Riemannian Set UpperHalfPlane
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace SystolicGrowth

noncomputable section

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** At the basepoint, the literal selected-chart metric equals
the actual tangent tensor, since the singleton chart differential is identity. -/
theorem upperHalfPlanePoincareMetric_chartMetricInner_self (p : ℍ) (v w : ℂ) :
    chartMetricInner upperHalfPlanePoincareMetric p
      (extChartAt (modelWithCornersSelf ℝ ℂ) p p) v w =
        @inner ℝ ℂ _ v w / p.im ^ 2 := by
  rw [chartMetricInner_extChartAt_eq_metricInner upperHalfPlanePoincareMetric p
    (mem_chart_source ℂ p) v w]
  simp only [trivializationAt_symm_self, RiemannianMetric.metricInner_apply,
    upperHalfPlanePoincareMetric_inner]

/-- **Math.** The horizontal and vertical vectors scaled by the point's
positive height form an actual Poincaré-orthonormal real frame. -/
def upperHalfPlanePoincareFrame (p : ℍ) : Fin 2 → ℂ :=
  ![p.im • (1 : ℂ), p.im • Complex.I]

/-- **Math.** Exact chart-Gram orthonormality for the constructed model frame. -/
theorem upperHalfPlanePoincareFrame_orthonormal (p : ℍ) (i j : Fin 2) :
    chartMetricInner upperHalfPlanePoincareMetric p
      (extChartAt (modelWithCornersSelf ℝ ℂ) p p)
      (upperHalfPlanePoincareFrame p i) (upperHalfPlanePoincareFrame p j) =
        if i = j then (1 : ℝ) else 0 := by
  rw [upperHalfPlanePoincareMetric_chartMetricInner_self]
  fin_cases i <;> fin_cases j <;>
    simp [upperHalfPlanePoincareFrame, Complex.inner, Complex.mul_re, p.im_pos.ne']

/-- **Math.** Every actual source tangent metric admits a real continuous
linear equivalence to the initial Poincaré metric at `I`. This constructs the
initial isometry needed by constant-curvature normal-coordinate comparison. -/
theorem exists_upperHalfPlanePoincare_initialMetricEquiv
    {M : Type*} [MetricSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (p : M) :
    ∃ A : ℂ ≃L[ℝ] ℂ, ∀ u v : ℂ,
      chartMetricInner upperHalfPlanePoincareMetric UpperHalfPlane.I
        (extChartAt (modelWithCornersSelf ℝ ℂ) UpperHalfPlane.I UpperHalfPlane.I)
        (A u) (A v) =
      chartMetricInner g p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) u v := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin 2 → ℂ, ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt (modelWithCornersSelf ℝ ℂ) p p) (e i) (e j) =
        if i = j then (1 : ℝ) else 0 := by
    obtain ⟨e, horth⟩ := Jacobi.exists_chartOrthonormalBasis_self g p
    let f : Fin 2 ≃ Fin (Module.finrank ℝ ℂ) :=
      (finCongr Complex.finrank_real_complex).symm
    refine ⟨fun i => e (f i), ?_⟩
    intro i j
    simpa only [f.apply_eq_iff_eq] using horth (f i) (f j)
  let B : ℂ → ℂ → ℝ := chartMetricInner g p (extChartAt (modelWithCornersSelf ℝ ℂ) p p)
  have hadd (u v w : ℂ) : B (u + v) w = B u w + B v w :=
    chartMetricInner_add_left g p _ u v w
  have hsmul (s : ℝ) (u v : ℂ) : B (s • u) v = s * B u v :=
    chartMetricInner_smul_left g p _ s u v
  have hBorth (i j : Fin 2) : B (e i) (e j) = if i = j then (1 : ℝ) else 0 := he i j
  have hexp (u : ℂ) : u = B u (e 0) • e 0 + B u (e 1) • e 1 := by
    simpa only [Fin.sum_univ_two] using Jacobi.frameExpansion g p
      (extChartAt (modelWithCornersSelf ℝ ℂ) p p) e
      (by simp [Complex.finrank_real_complex]) he u
  let f : ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun u => ⟨B u (e 0), B u (e 1)⟩
      map_add' := by
        intro u v
        apply Complex.ext
        · change B (u + v) (e 0) = B u (e 0) + B v (e 0)
          exact hadd u v (e 0)
        · change B (u + v) (e 1) = B u (e 1) + B v (e 1)
          exact hadd u v (e 1)
      map_smul' := by
        intro s u
        apply Complex.ext
        · simpa only [Complex.smul_re, RingHom.id_apply, smul_eq_mul] using hsmul s u (e 0)
        · simpa only [Complex.smul_im, RingHom.id_apply, smul_eq_mul] using hsmul s u (e 1) }
  let fInv : ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun z => z.re • e 0 + z.im • e 1
      map_add' := by
        intro u v
        simp only [Complex.add_re, Complex.add_im, add_smul]
        abel
      map_smul' := by
        intro s u
        simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul, mul_smul, smul_add,
          RingHom.id_apply] }
  have hfInv : f.comp fInv = LinearMap.id := by
    apply LinearMap.ext
    intro z
    apply Complex.ext
    · change B (z.re • e 0 + z.im • e 1) (e 0) = z.re
      simp only [hadd, hsmul, hBorth]
      norm_num
    · change B (z.re • e 0 + z.im • e 1) (e 1) = z.im
      simp only [hadd, hsmul, hBorth]
      norm_num
  have hInvf : fInv.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro z
    exact (hexp z).symm
  let A := (LinearEquiv.ofLinearMap f fInv hfInv hInvf).toContinuousLinearEquiv
  refine ⟨A, fun u v => ?_⟩
  rw [upperHalfPlanePoincareMetric_chartMetricInner_self]
  simp only [UpperHalfPlane.I_im, one_pow, div_one]
  change @inner ℝ ℂ _ (f u) (f v) = B u v
  have hcoord : @inner ℝ ℂ _ (f u) (f v) =
      B u (e 0) * B v (e 0) + B u (e 1) * B v (e 1) := by
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    change B v (e 0) * B u (e 0) - B v (e 1) * (-B u (e 1)) = _
    ring
  rw [hcoord]
  calc
    _ = B u (B v (e 0) • e 0 + B v (e 1) • e 1) := by
      simp only [B, chartMetricInner_add_right, chartMetricInner_smul_right]
      ring
    _ = B u v := congrArg (B u) (hexp v).symm

/-- **Math.** The actual global Poincaré exponential at any point of mathlib's
upper half-plane, using the original complete hyperbolic metric. -/
def upperHalfPlanePoincareExpMap (p : ℍ) (v : ℂ) : ℍ :=
  Exponential.expMapGlobal (I := modelWithCornersSelf ℝ ℂ)
    upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric_isRiemannianDist p v

/-- **Math.** Actual Cartan--Hadamard on the complete, simply connected
Poincaré model: its genuine global exponential is a smooth diffeomorphism. -/
def upperHalfPlanePoincareHadamardDiffeomorph (p : ℍ) :
    HadamardModel ℂ ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ :=
  Jacobi.hadamardDiffeomorphOfNonpos_complete upperHalfPlanePoincareMetric
    upperHalfPlanePoincareMetric_isRiemannianDist p
    upperHalfPlanePoincareMetric_curvatureOperatorAt_pair_nonneg

/-- **Math.** The constructed diffeomorphism is exactly the genuine
Poincaré exponential, not merely some unrelated diffeomorphic carrier map. -/
theorem upperHalfPlanePoincareHadamardDiffeomorph_apply
    (p : ℍ) (v : HadamardModel ℂ) :
    upperHalfPlanePoincareHadamardDiffeomorph p v =
      upperHalfPlanePoincareExpMap p (HadamardModel.toModel v) := by
  simpa only [upperHalfPlanePoincareHadamardDiffeomorph, upperHalfPlanePoincareExpMap] using
    congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe upperHalfPlanePoincareMetric
      upperHalfPlanePoincareMetric_isRiemannianDist p
      upperHalfPlanePoincareMetric_curvatureOperatorAt_pair_nonneg) v

/-- **Math.** The actual complete hyperbolic exponential is globally injective. -/
theorem upperHalfPlanePoincareExpMap_injective (p : ℍ) :
    Function.Injective (upperHalfPlanePoincareExpMap p) := by
  intro u v huv
  exact (upperHalfPlanePoincareHadamardDiffeomorph p).injective
    (by simpa only [Diffeomorph.coe_toEquiv, upperHalfPlanePoincareHadamardDiffeomorph_apply,
      HadamardModel.toModel, id_eq] using huv)

/-- **Math.** The actual model exponential is a global open embedding
for mathlib's unchanged upper-half-plane topology. -/
theorem upperHalfPlanePoincareExpMap_isOpenEmbedding (p : ℍ) :
    Topology.IsOpenEmbedding (upperHalfPlanePoincareExpMap p) := by
  have hmap : ⇑(upperHalfPlanePoincareHadamardDiffeomorph p).toHomeomorph =
      upperHalfPlanePoincareExpMap p := by
    funext v
    simpa only [Diffeomorph.coe_toHomeomorph, HadamardModel.toModel, id_eq] using
      upperHalfPlanePoincareHadamardDiffeomorph_apply p v
  rw [← hmap]
  exact (upperHalfPlanePoincareHadamardDiffeomorph p).toHomeomorph.isOpenEmbedding

#synth SimplyConnectedSpace ℍ
#synth CompleteSpace ℍ
#synth SigmaCompactSpace ℍ
#synth LocallyPathConnectedSpace ℍ

#print axioms upperHalfPlanePoincareFrame_orthonormal
#print axioms upperHalfPlanePoincareExpMap
#print axioms exists_upperHalfPlanePoincare_initialMetricEquiv
#print axioms upperHalfPlanePoincareHadamardDiffeomorph
#print axioms upperHalfPlanePoincareExpMap_injective

end
end SystolicGrowth
