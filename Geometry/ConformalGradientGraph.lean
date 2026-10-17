module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.WeightedChartDerivative
public import Geometry.ClosedGradientGraph
public import Geometry.ConformalHilbertGraphSolution
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# The finite-coordinate surface gradient graph

Smooth functions are mapped to their actual `L²` values and to their
square-partition-weighted conformal coordinate derivatives. The closure of
this literal graph constructs the Hilbert space and its nonlinear weak
solution. Coordinate integration by parts is still required to identify
completed graph components as weak derivatives of the function component.
-/

open Set Manifold IsManifold MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

set_option maxHeartbeats 200000

variable (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]
  (ι : Type*) [Fintype ι]

/-- Actual smooth coordinates and supported weights used to construct the
gradient. Metric compatibility is proved in the concrete surface application. -/
structure ConformalGradientAtlas where
  chart : ι → OpenPartialHomeomorph M ℂ
  chart_mem : ∀ i, chart i ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ M
  coefficient : ι → ℂ → ℝ
  coefficient_smooth : ∀ i, ContDiffOn ℝ ∞ (coefficient i) (chart i).target
  coefficient_pos : ∀ i z, z ∈ (chart i).target → 0 < coefficient i z
  weight : ι → C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯
  weight_support : ∀ i, tsupport (weight i) ⊆ (chart i).source
  weight_sum_sq : ∀ x, ∑ i, (weight i x) ^ 2 = 1

variable {M ι}

/-- Forget smoothness, retaining the original continuous function. -/
def smoothFunctionToContinuousLinear :
    C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ →ₗ[ℝ] C(M, ℝ) where
  toFun f := ⟨f, f.contMDiff.continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  (μ : Measure M) [IsFiniteMeasure μ]

/-- The literal `L²` realization of each smooth function. -/
def smoothFunctionToL2 : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ →ₗ[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp smoothFunctionToContinuousLinear

theorem smoothFunctionToL2_coeFn (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) :
    smoothFunctionToL2 μ f =ᵐ[μ] f :=
  ContinuousMap.coeFn_toLp _ _

/-- A genuine coordinate gradient component, including the partition weight
and inverse conformal coefficient, as a linear map into `L²`. -/
def conformalGradientComponent (A : ConformalGradientAtlas M ι) (i : ι) (j : Fin 2) :
    C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ →ₗ[ℝ] Lp ℝ 2 μ :=
  (smoothFunctionToL2 μ).comp (weightedChartDerivativeLinear
    (A.chart i) (A.chart_mem i) (A.coefficient i) (A.coefficient_smooth i)
    (A.coefficient_pos i) (A.weight i) (A.weight_support i)
    (if j = 0 then 1 else Complex.I))

/-- All components in their finite Hilbert product, not the sup-norm product. -/
def conformalSmoothGradient (A : ConformalGradientAtlas M ι) :
    C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ →ₗ[ℝ] PiLp 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ) :=
  (WithLp.linearEquiv 2 ℝ (ι × Fin 2 → Lp ℝ 2 μ)).symm.toLinearMap.comp
    (LinearMap.pi fun ij => conformalGradientComponent μ A ij.1 ij.2)

@[simp] theorem conformalSmoothGradient_apply (A : ConformalGradientAtlas M ι)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (i : ι) (j : Fin 2) :
    conformalSmoothGradient μ A f (i, j) = conformalGradientComponent μ A i j f := rfl

theorem conformalGradientComponent_coeFn (A : ConformalGradientAtlas M ι)
    (f : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯) (i : ι) (j : Fin 2) :
    conformalGradientComponent μ A i j f =ᵐ[μ]
      weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i)
        (if j = 0 then 1 else Complex.I) f :=
  smoothFunctionToL2_coeFn μ _

/-- The actual closure of the smooth function/coordinate-gradient graph. -/
def ConformalGradientH1 (A : ConformalGradientAtlas M ι) :
    Submodule ℝ (WithLp 2 (Lp ℝ 2 μ × PiLp 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ))) :=
  closedGradientGraph (smoothFunctionToL2 μ) (conformalSmoothGradient μ A)

instance conformalGradientH1_completeSpace (A : ConformalGradientAtlas M ι) :
    CompleteSpace (ConformalGradientH1 μ A) := by
  unfold ConformalGradientH1
  infer_instance

/-- The completed graph's genuine `L²` function component. -/
def conformalH1Value (A : ConformalGradientAtlas M ι) :
    ConformalGradientH1 μ A →L[ℝ] Lp ℝ 2 μ :=
  closedGradientGraphValue (smoothFunctionToL2 μ) (conformalSmoothGradient μ A)

/-- The completed graph's genuine finite family of `L²` derivative components. -/
def conformalH1Gradient (A : ConformalGradientAtlas M ι) :
    ConformalGradientH1 μ A →L[ℝ] PiLp 2 (fun _ : ι × Fin 2 => Lp ℝ 2 μ) :=
  closedGradientGraphDerivative (smoothFunctionToL2 μ) (conformalSmoothGradient μ A)

/-- The constructed graph solution satisfies the exact gradient weak
equation. No assumed coercive inverse or weak-solution witness is used. -/
theorem exists_conformalGradientH1_solution
    (A : ConformalGradientAtlas M ι) (B : ℝ) (hB : 1 < B) (K : Lp ℝ 2 μ) :
    ∃ v : ConformalGradientH1 μ A, ∀ w : ConformalGradientH1 μ A,
      inner ℝ (conformalH1Gradient μ A v) (conformalH1Gradient μ A w) =
        -inner ℝ (K + conformalCurvatureNonlinearityLp μ B hB (conformalH1Value μ A v))
          (conformalH1Value μ A w) := by
  exact exists_closedGradientGraph_conformalSolution μ B hB K
    (smoothFunctionToL2 μ) (conformalSmoothGradient μ A)

#print axioms conformalGradientComponent_coeFn
#print axioms exists_conformalGradientH1_solution

end

end SystolicGrowth
