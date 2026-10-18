module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalDirichletDensity

@[expose] public section

/-!
# The gradient graph inner product is the actual Dirichlet integral

Finite Hilbert-product inner products are converted to integrals of the
literal smooth weighted coordinate derivatives. The conformal tensor
identity then identifies this with the original metric's Dirichlet energy.
-/

open Set Manifold IsManifold MeasureTheory Riemannian
open scoped ContDiff Manifold

namespace SystolicGrowth

noncomputable section

variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Fintype ι]
  (μ : Measure M) [IsFiniteMeasure μ]

/-- **Math.** The actual finite Hilbert-gradient inner product is the
integral of the literal weighted coordinate products. -/
theorem conformalSmoothGradient_inner_eq_integral_components
    (A : ConformalGradientAtlas M ι) (f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    inner ℝ (conformalSmoothGradient μ A f) (conformalSmoothGradient μ A h) =
      ∫ x, ∑ i, (weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) 1 f x *
          weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) 1 h x +
        weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) Complex.I f x *
          weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) Complex.I h x) ∂μ := by
  let D (F : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (ij : ι × Fin 2) : M → ℝ :=
    weightedChartDerivative (A.chart ij.1) (A.coefficient ij.1) (A.weight ij.1)
      (if ij.2 = 0 then 1 else Complex.I) F
  have hae (ij : ι × Fin 2) :
      (fun x => inner ℝ ((conformalSmoothGradient μ A f ij) x)
          ((conformalSmoothGradient μ A h ij) x)) =ᵐ[μ]
        fun x => D f ij x * D h ij x := by
    rcases ij with ⟨i, j⟩
    filter_upwards [conformalGradientComponent_coeFn μ A f i j,
      conformalGradientComponent_coeFn μ A h i j] with x hfx hhx
    rw [Real.inner_apply]
    change (conformalGradientComponent μ A i j f) x *
      (conformalGradientComponent μ A i j h) x = _
    rw [hfx, hhx]
  have hint (ij : ι × Fin 2) : Integrable (fun x => D f ij x * D h ij x) μ :=
    (L2.integrable_inner (𝕜 := ℝ) (conformalSmoothGradient μ A f ij)
      (conformalSmoothGradient μ A h ij)).congr (hae ij)
  calc
    _ = ∑ ij : ι × Fin 2, ∫ x, D f ij x * D h ij x ∂μ := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro ij _
      rw [L2.inner_def]
      exact integral_congr_ae (hae ij)
    _ = ∫ x, ∑ ij : ι × Fin 2, D f ij x * D h ij x ∂μ :=
      (integral_finsetSum Finset.univ (fun ij _ => hint ij)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, D]

variable [IsManifold 𝓘(ℝ, ℂ) ∞ M]

/-- **Math.** Actual chart tensor laws identify the solver's energy with
the original Riemannian metric's Dirichlet integral, not a proxy norm. -/
theorem conformalSmoothGradient_inner_eq_integral_dirichlet
    (A : ConformalGradientAtlas M ι) (g : RiemannianMetric 𝓘(ℝ, ℂ) M)
    (hmetric : ∀ x i (hx : x ∈ (A.chart i).source), A.weight i x ≠ 0 →
      ∀ v w : ℂ,
      g.inner x (conformalChartInverseTangent (A.chart i) (A.chart_mem i) x hx v)
        (conformalChartInverseTangent (A.chart i) (A.chart_mem i) x hx w) =
          A.coefficient i (A.chart i x) ^ 2 * (v.re * w.re + v.im * w.im))
    (f h : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    inner ℝ (conformalSmoothGradient μ A f) (conformalSmoothGradient μ A h) =
      ∫ x, smoothDirichletDensity g f h x ∂μ := by
  rw [conformalSmoothGradient_inner_eq_integral_components]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    sum_weightedChartDerivative_pair_eq A g x (hmetric x) f h

#print axioms conformalSmoothGradient_inner_eq_integral_components
#print axioms conformalSmoothGradient_inner_eq_integral_dirichlet

end

end SystolicGrowth
