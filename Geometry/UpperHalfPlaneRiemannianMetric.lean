module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicGaussianCurvature
public import Geometry.HyperbolicCurveLength
public import Geometry.HyperbolicMetricSegments
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.PullbackMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianDistance
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

@[expose] public section

/-!
# The actual Poincaré tensor on mathlib's upper half-plane

The complex charts and existing hyperbolic metric space remain unchanged.
The smooth tensor is constructed on its actual tangent bundle, using the
inclusion's identity differential and a positive conformal coefficient.
-/

open Bundle Manifold Set Riemannian UpperHalfPlane MeasureTheory
open scoped Manifold ContDiff Topology ENNReal RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000

namespace SystolicGrowth

noncomputable section

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The existing complex singleton atlas is also a smooth real
manifold atlas, without replacing its charts. -/
instance upperHalfPlane_isManifold_real : IsManifold (modelWithCornersSelf ℝ ℂ) ∞ ℍ :=
  UpperHalfPlane.isOpenEmbedding_coe.isManifold_singleton

/-- **Math.** In the existing upper-half-plane atlas, every extended real
chart is exactly the complex inclusion. -/
theorem upperHalfPlane_extChartAt_apply (p z : ℍ) :
    extChartAt (modelWithCornersSelf ℝ ℂ) p z = (z : ℂ) := rfl

/-- **Math.** The complex inclusion is smooth for the real model as well. -/
theorem upperHalfPlane_coe_contMDiff_real :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun z : ℍ => (z : ℂ)) :=
  contMDiff_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe

/-- **Math.** The inclusion's actual tangent differential is the identity. -/
theorem upperHalfPlane_coe_mfderiv_real (z : ℍ) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (fun p : ℍ => (p : ℂ)) z = ContinuousLinearMap.id ℝ ℂ := by
  change mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
    (extChartAt (modelWithCornersSelf ℝ ℂ) z) z = _
  exact mfderiv_extChartAt_self

def Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric : RiemannianMetric (modelWithCornersSelf ℝ ℂ) ℍ where
  inner _ := (innerSL ℝ (E := ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
  symm _ v w := by
    change @inner ℝ ℂ _ v w = @inner ℝ ℂ _ w v
    exact @real_inner_comm ℂ _ _ w v
  pos _ v hv := by
    change 0 < @inner ℝ ℂ _ v v
    exact (@real_inner_self_pos ℂ _ _ v).mpr hv
  isVonNBounded _ := by
    change Bornology.IsVonNBounded ℝ {v : ℂ | @inner ℝ ℂ _ v v < 1}
    have hset : {v : ℂ | @inner ℝ ℂ _ v v < 1} = Metric.ball (0 : ℂ) 1 := by
      ext v
      simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right,
        norm_eq_sqrt_re_inner (𝕜 := ℝ), RCLike.re_to_real]
      conv_rhs => rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    exact hset ▸ NormedSpace.isVonNBounded_ball ℝ ℂ 1
  contMDiff := by
    intro x
    rw [Bundle.contMDiffAt_section]
    have h : (fun b : ℍ =>
        (trivializationAt (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
          (fun y : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) y →L[ℝ]
            TangentSpace (modelWithCornersSelf ℝ ℂ) y →L[ℝ] ℝ)
          x ⟨b, (innerSL ℝ (E := ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)⟩).2) =
        fun _ : ℍ => (innerSL ℝ (E := ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := by
      funext b
      ext v w
      rw [hom_trivializationAt_apply]
      rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial ℍ ℝ)
        (show b ∈ (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) x).baseSet
          from mem_univ b)
        (show b ∈ (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) x).baseSet
          from mem_univ b)
        (by simp)]
      have htriv : trivializationAt ℝ (Bundle.Trivial ℍ ℝ) x =
          Bundle.Trivial.trivialization ℍ ℝ := Bundle.Trivial.eq_trivialization ℍ ℝ _
      simp only [htriv, Bundle.Trivial.linearMapAt_trivialization]
      simp
      have hsame : trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) x =
          trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) b := by
        rw [TangentBundle.trivializationAt_eq_localTriv,
          TangentBundle.trivializationAt_eq_localTriv]
        rfl
      rw [hsame, trivializationAt_symm_self, trivializationAt_symm_self]
      rfl
    rw [h]
    exact contMDiffAt_const

theorem Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric_inner (z : ℍ) (v w : ℂ) :
    Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.inner z v w = @inner ℝ ℂ _ v w := rfl

theorem Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlane_conformalFactor_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℍ => (z.im ^ 2)⁻¹) := by
  have him : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞
      (fun z : ℍ => z.im) :=
    Complex.imCLM.contMDiff.comp upperHalfPlane_coe_contMDiff_real
  intro z
  exact (him z).pow 2 |>.inv₀ (pow_ne_zero 2 z.im_pos.ne')

/-- **Math.** The smooth positive Poincaré metric on the actual upper
half-plane tangent bundle, with tensor `im(z)⁻²` times the Euclidean inner product. -/
def upperHalfPlanePoincareMetric : RiemannianMetric (modelWithCornersSelf ℝ ℂ) ℍ where
  inner z := (z.im ^ 2)⁻¹ • Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.inner z
  symm z v w := by
    simp only [smul_apply, smul_eq_mul]
    rw [Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.symm]
  pos z v hv := by
    simp only [smul_apply, smul_eq_mul]
    exact mul_pos (by have := z.im_pos; positivity)
      (Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.pos z v hv)
  isVonNBounded z := by
    have hc : 0 < (z.im ^ 2)⁻¹ := by have := z.im_pos; positivity
    have hset : {v : ℂ | ((z.im ^ 2)⁻¹ • Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.inner z) v v < 1} =
        Metric.ball (0 : ℂ) (Real.sqrt (1 / (z.im ^ 2)⁻¹)) := by
      ext v
      simp only [smul_apply, smul_eq_mul, Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric_inner,
        Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right,
        Real.lt_sqrt (norm_nonneg v), real_inner_self_eq_norm_sq]
      rw [lt_div_iff₀ hc, mul_comm]
    exact hset ▸ NormedSpace.isVonNBounded_ball ℝ ℂ _
  contMDiff := ContMDiff.smul_section Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlane_conformalFactor_contMDiff
    Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.contMDiff

/-- **Math.** Exact tensor identity with the usual Poincaré inner product. -/
theorem upperHalfPlanePoincareMetric_inner (z : ℍ) (v w : ℂ) :
    upperHalfPlanePoincareMetric.inner z v w = @inner ℝ ℂ _ v w / z.im ^ 2 := by
  change ((z.im ^ 2)⁻¹ • Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric.inner z) v w = _
  simp only [smul_apply, smul_eq_mul, Internal.UpperHalfPlaneRiemannianMetricHelpers.upperHalfPlaneEuclideanMetric_inner, div_eq_mul_inv]
  ring

/-- **Math.** The constructed smooth tensor is the audited native hyperbolic
chart bilinear form, not merely an unrelated metric with the same carrier. -/
theorem upperHalfPlanePoincareMetric_inner_eq_native (z : ℍ) (v w : ℂ) :
    upperHalfPlanePoincareMetric.inner z v w =
      gluingComplexHalfPlaneTangentForm z v w := by
  rw [upperHalfPlanePoincareMetric_inner, gluingComplexHalfPlaneTangentForm_apply]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    UpperHalfPlane.im]
  ring

#print axioms upperHalfPlanePoincareMetric
#print axioms upperHalfPlanePoincareMetric_inner
#print axioms upperHalfPlane_coe_mfderiv_real

end
end SystolicGrowth
