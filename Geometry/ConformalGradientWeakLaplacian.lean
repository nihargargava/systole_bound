module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalDirichletChartIntegration
public import Geometry.ConformalGradientWeakDerivative

@[expose] public section

/-!
# The completed gradient equation is the actual local Laplacian equation

The smooth metric's Dirichlet identity passes to the literal graph closure
by continuous Hilbert pairings. Arbitrary compact tests in any genuine
conformal metric/area patch then recover the Euclidean weak Laplacian.
-/

open Set Filter Manifold IsManifold MeasureTheory Riemannian
open scoped ContDiff Manifold RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℝ, ℂ) ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Fintype ι]
  (μ : Measure M) [IsFiniteMeasure μ]
  (A : ConformalGradientAtlas M ι) (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
  (henergy : ∀ f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯,
    inner ℝ (conformalSmoothGradient μ A f) (conformalSmoothGradient μ A h) =
      ∫ x, smoothDirichletDensity g f h x ∂μ)

include henergy

/-- **Math.** The actual completed gradient pairs against a compact
chart test by the true negative coordinate Laplacian. -/
theorem conformalH1Gradient_laplacian_adjoint
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (hmetric : ∀ x (hx : x ∈ U) v w,
      g.inner x (conformalChartInverseTangent e he x (hUs hx) v)
        (conformalChartInverseTangent e he x (hUs hx) w) =
          a (e x) ^ 2 * (v.re * w.re + v.im * w.im))
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ e '' U) (hηt : tsupport η ⊆ e.target)
    (u : ConformalGradientH1 μ A) :
    let T : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ := ⟨conformalChartTestPullback e η,
      conformalChartTestPullback_contMDiff e he η hη hηc hηt⟩
    inner ℝ (conformalH1Gradient μ A u) (conformalSmoothGradient μ A T) =
      -(∫ z : ℂ, (conformalH1Value μ A u) (e.symm z) *
        Laplacian.laplacian η z) := by
  intro T
  let ξ : ℂ → ℝ := fun z => (a z ^ 2)⁻¹ * Laplacian.laplacian η z
  have hξ := conformalChartLaplacianAdjoint_contDiff e a ha hapos η hη hηt
  have hξs : tsupport ξ ⊆ tsupport η :=
    tsupport_mul_subset_right.trans (tsupport_complex_laplacian_subset hη)
  have hξc : HasCompactSupport ξ := hηc.of_isClosed_subset (isClosed_tsupport _) hξs
  let Q : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ := ⟨conformalChartTestPullback e ξ,
    conformalChartTestPullback_contMDiff e he ξ hξ hξc (hξs.trans hηt)⟩
  let q := smoothFunctionToL2 μ Q
  let t := conformalSmoothGradient μ A T
  have hsmooth (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
      inner ℝ (conformalSmoothGradient μ A f) t =
        -inner ℝ (smoothFunctionToL2 μ f) q := by
    rw [show t = conformalSmoothGradient μ A T from rfl,
      show q = smoothFunctionToL2 μ Q from rfl, henergy,
      smoothFunctionToL2_inner]
    have h := smoothDirichletDensity_integral_test μ g e he U hU hUs a
      ha.continuousOn hapos hmetric harea η hη hηc hηsub hηt f
    apply h.trans
    congr 1
    exact (conformalChartLaplacianAdjoint_integral μ e U hU hUs a ha.continuousOn
      hapos harea η hη hηsub f).symm
  have hlinear (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
      (-(innerSL ℝ q)) (smoothFunctionToL2 μ f) =
        (innerSL ℝ t) (conformalSmoothGradient μ A f) := by
    change -inner ℝ q (smoothFunctionToL2 μ f) = inner ℝ t _
    rw [real_inner_comm (smoothFunctionToL2 μ f) q,
      real_inner_comm (conformalSmoothGradient μ A f) t]
    exact (hsmooth f).symm
  have hc := closedGradientGraph_weak_identity (smoothFunctionToL2 μ)
    (conformalSmoothGradient μ A) (-(innerSL ℝ q)) (innerSL ℝ t) hlinear u
  change -inner ℝ q (conformalH1Value μ A u) =
    inner ℝ t (conformalH1Gradient μ A u) at hc
  rw [real_inner_comm (conformalH1Value μ A u) q,
    real_inner_comm (conformalH1Gradient μ A u) t] at hc
  rw [← hc, show q = smoothFunctionToL2 μ Q from rfl,
    L2_inner_smoothFunctionToL2]
  congr 1
  exact conformalChartLaplacianAdjoint_integral μ e U hU hUs a ha.continuousOn
    hapos harea η hη hηsub (conformalH1Value μ A u)

/-- **Math.** A genuine graph weak equation with an actual `L²` forcing
implies the local Euclidean distributional equation. The forcing may be
identified a.e. before transport, preserving its literal nonlinear form. -/
theorem conformalH1Gradient_weak_laplacian
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (U : Set M) (hU : IsOpen U) (hUs : U ⊆ e.source)
    (a : ℂ → ℝ) (ha : ContDiffOn ℝ ∞ a e.target)
    (hapos : ∀ z ∈ e.target, 0 < a z)
    (hmetric : ∀ x (hx : x ∈ U) v w,
      g.inner x (conformalChartInverseTangent e he x (hUs hx) v)
        (conformalChartInverseTangent e he x (hUs hx) w) =
          a (e x) ^ 2 * (v.re * w.re + v.im * w.im))
    (harea : ∀ s : Set ℂ, MeasurableSet s → s ⊆ e '' U →
      μ (e.symm '' s) = ∫⁻ z : ℂ in s, ENNReal.ofReal (a z ^ 2))
    (u : ConformalGradientH1 μ A) (F : Lp ℝ 2 μ) (f : M → ℝ)
    (hF : F =ᵐ[μ] f)
    (hweak : ∀ w : ConformalGradientH1 μ A,
      inner ℝ (conformalH1Gradient μ A u) (conformalH1Gradient μ A w) =
        -inner ℝ F (conformalH1Value μ A w))
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ e '' U) :
    (∫ z : ℂ, (conformalH1Value μ A u) (e.symm z) * Laplacian.laplacian η z) =
      ∫ z : ℂ, a z ^ 2 * (f (e.symm z) * η z) := by
  have hηt : tsupport η ⊆ e.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hηsub hz
    exact e.map_source (hUs hx)
  let T : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ := ⟨conformalChartTestPullback e η,
    conformalChartTestPullback_contMDiff e he η hη hηc hηt⟩
  let w := closedGradientGraphOfSmooth (smoothFunctionToL2 μ) (conformalSmoothGradient μ A) T
  have hw := hweak w
  change inner ℝ (conformalH1Gradient μ A u) (conformalSmoothGradient μ A T) =
    -inner ℝ F (smoothFunctionToL2 μ T) at hw
  have hadj := conformalH1Gradient_laplacian_adjoint μ A g henergy e he U hU hUs a
    ha hapos hmetric harea η hη hηc hηsub hηt u
  have hp : inner ℝ F (smoothFunctionToL2 μ T) =
      ∫ z : ℂ, a z ^ 2 * (f (e.symm z) * η z) := by
    rw [L2_inner_smoothFunctionToL2]
    calc
      (∫ x, F x * T x ∂μ) = ∫ x, f x * conformalChartTestPullback e η x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hF] with x hx
        rw [hx]
        rfl
      _ = _ := conformalChartTestPullback_integral μ e U hU hUs a ha.continuousOn
        harea η hηsub f
  exact neg_injective (hadj.symm.trans (hw.trans (congrArg Neg.neg hp)))

#print axioms conformalH1Gradient_laplacian_adjoint
#print axioms conformalH1Gradient_weak_laplacian

end

end SystolicGrowth
