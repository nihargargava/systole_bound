module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalGradientGraph
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Metric.RiemannianMetric
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# The intrinsic Dirichlet density in conformal coordinates

The coordinate derivative of an actual smooth function is its manifold
differential composed with the inverse chart derivative. The metric's
genuine Riesz map then identifies the conformal coordinate sum with one
intrinsic scalar, independently of the chosen conformal chart.
-/

open Set Manifold IsManifold Bundle Riemannian
open scoped ContDiff Manifold

namespace SystolicGrowth

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- **Math.** A chart from the original maximal smooth atlas is a genuine
differentiable partial equivalence in both directions. -/
theorem conformalChart_mdifferentiable
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M) :
    e.MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) :=
  ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
    (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩

/-- **Math.** The actual inverse chart differential, with its proved inverse. -/
def conformalChartInverseTangent
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (x : M) (hx : x ∈ e.source) : ℂ ≃L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x :=
  ((conformalChart_mdifferentiable e he).mfderiv hx).symm

/-- **Math.** The coordinate derivative is the actual manifold differential
on the inverse chart tangent, rather than an independently specified covector. -/
theorem smoothFunction_fderiv_chart_inverse
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (x : M) (hx : x ∈ e.source)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (v : ℂ) :
    fderiv ℝ (fun z => f (e.symm z)) (e x) v =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ) f x (conformalChartInverseTangent e he x hx v) := by
  have hf := (f.contMDiff.mdifferentiable (by simp)) (e.symm (e x))
  have hi := (conformalChart_mdifferentiable e he).mdifferentiableAt_symm (e.map_source hx)
  have h := mfderiv_comp_apply (e x) hf hi v
  rw [mfderiv_eq_fderiv, e.left_inv hx] at h
  exact h

variable [IsManifold 𝓘(ℝ, ℂ) ∞ M]

/-- **Math.** The intrinsic pairing of two covectors in an actual conformal
frame. The frame is an equivalence, and its metric law is the tensor law. -/
theorem conformalFrame_metricRiesz_pairing
    (g : RiemannianMetric 𝓘(ℝ, ℂ) M) (x : M)
    (L : ℂ ≃L[ℝ] TangentSpace 𝓘(ℝ, ℂ) x) (a : ℝ) (ha : a ≠ 0)
    (hmetric : ∀ v w : ℂ, g.inner x (L v) (L w) =
      a ^ 2 * (v.re * w.re + v.im * w.im))
    (φ ψ : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ) :
    g.inner x (g.metricRiesz x φ) (g.metricRiesz x ψ) =
      (a ^ 2)⁻¹ * (φ (L 1) * ψ (L 1) + φ (L Complex.I) * ψ (L Complex.I)) := by
  obtain ⟨v, hv⟩ := L.surjective (g.metricRiesz x φ)
  obtain ⟨w, hw⟩ := L.surjective (g.metricRiesz x ψ)
  have hφ1 := g.metricRiesz_inner x φ (L 1)
  have hφI := g.metricRiesz_inner x φ (L Complex.I)
  have hψ1 := g.metricRiesz_inner x ψ (L 1)
  have hψI := g.metricRiesz_inner x ψ (L Complex.I)
  change g.inner x _ _ = _ at hφ1 hφI hψ1 hψI
  rw [← hv, hmetric] at hφ1 hφI
  rw [← hw, hmetric] at hψ1 hψI
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add] at hφ1 hφI hψ1 hψI
  rw [← hv, ← hw, hmetric, ← hφ1, ← hφI, ← hψ1, ← hψI]
  field_simp

/-- **Math.** The original metric's intrinsic Dirichlet density of two
actual smooth scalar functions. -/
def smoothDirichletDensity (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
    (f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (x : M) : ℝ :=
  g.inner x (g.metricRiesz x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ) f x))
    (g.metricRiesz x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ) h x))

/-- **Math.** In any conformal chart the same intrinsic Dirichlet scalar is
the Euclidean derivative pairing divided by the actual area coefficient. -/
theorem smoothDirichletDensity_in_conformal_chart
    (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (x : M) (hx : x ∈ e.source) (a : ℝ) (ha : a ≠ 0)
    (hmetric : ∀ v w : ℂ,
      g.inner x (conformalChartInverseTangent e he x hx v)
        (conformalChartInverseTangent e he x hx w) =
          a ^ 2 * (v.re * w.re + v.im * w.im))
    (f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    smoothDirichletDensity g f h x = (a ^ 2)⁻¹ *
      (fderiv ℝ (fun z => f (e.symm z)) (e x) 1 *
          fderiv ℝ (fun z => h (e.symm z)) (e x) 1 +
        fderiv ℝ (fun z => f (e.symm z)) (e x) Complex.I *
          fderiv ℝ (fun z => h (e.symm z)) (e x) Complex.I) := by
  simp only [smoothFunction_fderiv_chart_inverse e he x hx]
  exact conformalFrame_metricRiesz_pairing g x
    (conformalChartInverseTangent e he x hx) a ha hmetric _ _

/-- **Math.** Squared partition weights turn the two conformal derivative
components into the corresponding weighted intrinsic Dirichlet density. -/
theorem weightedChartDerivative_pair_eq
    (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
    (e : OpenPartialHomeomorph M ℂ) (he : e ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M)
    (x : M) (hx : x ∈ e.source) (a : ℂ → ℝ) (ha : a (e x) ≠ 0)
    (hmetric : ∀ v w : ℂ,
      g.inner x (conformalChartInverseTangent e he x hx v)
        (conformalChartInverseTangent e he x hx w) =
          a (e x) ^ 2 * (v.re * w.re + v.im * w.im))
    (τ f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    weightedChartDerivative e a τ 1 f x * weightedChartDerivative e a τ 1 h x +
        weightedChartDerivative e a τ Complex.I f x *
          weightedChartDerivative e a τ Complex.I h x =
      τ x ^ 2 * smoothDirichletDensity g f h x := by
  rw [smoothDirichletDensity_in_conformal_chart g e he x hx (a (e x)) ha hmetric]
  unfold weightedChartDerivative
  ring

/-- **Math.** The entire finite weighted coordinate gradient has exactly
the original metric's Dirichlet density. Tensor compatibility is needed only
where the corresponding weight is nonzero, not on a whole large chart. -/
theorem sum_weightedChartDerivative_pair_eq
    {ι : Type*} [Fintype ι] (A : ConformalGradientAtlas M ι)
    (g : RiemannianMetric 𝓘(ℝ, ℂ) M) (x : M)
    (hmetric : ∀ i (hx : x ∈ (A.chart i).source), A.weight i x ≠ 0 →
      ∀ v w : ℂ,
      g.inner x (conformalChartInverseTangent (A.chart i) (A.chart_mem i) x hx v)
        (conformalChartInverseTangent (A.chart i) (A.chart_mem i) x hx w) =
          A.coefficient i (A.chart i x) ^ 2 * (v.re * w.re + v.im * w.im))
    (f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    (∑ i, (weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) 1 f x *
        weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) 1 h x +
      weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) Complex.I f x *
        weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) Complex.I h x)) =
      smoothDirichletDensity g f h x := by
  classical
  calc
    _ = ∑ i, (A.weight i x) ^ 2 * smoothDirichletDensity g f h x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : A.weight i x = 0
      · simp [weightedChartDerivative, hi]
      · have hx := A.weight_support i (subset_closure hi)
        exact weightedChartDerivative_pair_eq g (A.chart i) (A.chart_mem i) x hx
          (A.coefficient i) (A.coefficient_pos i _ ((A.chart i).map_source hx)).ne'
          (hmetric i hx hi) (A.weight i) f h
    _ = _ := by rw [← Finset.sum_mul, A.weight_sum_sq, one_mul]

#print axioms smoothFunction_fderiv_chart_inverse
#print axioms conformalFrame_metricRiesz_pairing
#print axioms smoothDirichletDensity_in_conformal_chart
#print axioms sum_weightedChartDerivative_pair_eq

end

end SystolicGrowth
