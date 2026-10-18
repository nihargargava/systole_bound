module

public import Geometry.ConformalGradientFirstChainRule
public import Geometry.ConformalCurvatureNonlinearity

@[expose] public section

/-!
# The actual curvature nonlinearity in the completed gradient graph

The smooth, globally Lipschitz extension `Ψ_B` already used in the fixed-point
construction satisfies the proved scalar chain rule after subtracting its
value at zero. No second cutoff is introduced.
-/

open MeasureTheory Filter Set Manifold IsManifold
open scoped ContDiff Topology RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

variable {M ι : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Fintype ι]
  (μ : Measure M) [IsFiniteMeasure μ]

def Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne : C^∞⟮𝓘(ℝ, ℂ), M; ℝ⟯ :=
  ⟨fun _ => 1, contMDiff_const⟩

private theorem smoothOne_gradient_zero
    (A : ConformalGradientAtlas M ι) :
    conformalSmoothGradient μ A (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M)) = 0 := by
  ext ij
  rcases ij with ⟨i, j⟩
  filter_upwards [conformalGradientComponent_coeFn μ A (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M)) i j,
    Lp.coeFn_zero ℝ 2 μ] with x hx hz
  change (conformalGradientComponent μ A i j (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M))) x = _ at hx
  change (conformalGradientComponent μ A i j (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M))) x = _
  rw [hx]
  simpa [weightedChartDerivative, Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne] using hz.symm

/-- The nonlinear term `Ψ_B(u) - 1` belongs to the actual completed
weighted-gradient graph, with its genuine first-derivative chain rule. -/
theorem conformalGradientH1_curvatureNonlinearity_sub_one
    (A : ConformalGradientAtlas M ι) (v : ConformalGradientH1 μ A)
    (B : ℝ) (hB : 1 < B) :
    ∃ w : ConformalGradientH1 μ A,
      conformalH1Value μ A w =ᵐ[μ]
        (fun x => conformalCurvatureNonlinearity B
          ((conformalH1Value μ A v) x) - 1) ∧
      ∀ i : ι, ∀ j : Fin 2,
        conformalH1Gradient μ A w (i, j) =ᵐ[μ]
          (fun x => deriv (conformalCurvatureNonlinearity B)
            ((conformalH1Value μ A v) x) *
            (conformalH1Gradient μ A v (i, j)) x) := by
  let φ : ℝ → ℝ := fun t => conformalCurvatureNonlinearity B t - 1
  have hφ : ContDiff ℝ ∞ φ :=
    (conformalCurvatureNonlinearity_contDiff B).sub contDiff_const
  have hφ0 : φ 0 = 0 := by
    simp [φ]
  have hC : 0 ≤ 4 * B := by linarith
  have hLip : ∀ x y, ‖φ x - φ y‖ ≤ (4 * B) * ‖x - y‖ := by
    intro x y
    have h := (conformalCurvatureNonlinearity_lipschitz hB).norm_sub_le x y
    convert h using 1
    · dsimp [φ]
      congr 1
      ring
    · rfl
  have hderiv : ∀ t, ‖deriv φ t‖ ≤ 4 * B := by
    intro t
    have heq : deriv φ t = deriv (conformalCurvatureNonlinearity B) t := by
      exact deriv_sub_const (f := conformalCurvatureNonlinearity B) 1
    rw [heq, Real.norm_eq_abs]
    have hbd := conformalCurvatureNonlinearity_deriv_mem_Icc hB t
    rw [abs_of_nonneg (by linarith [hbd.1])]
    exact hbd.2
  obtain ⟨w, hwvalue, hwgrad⟩ :=
    conformalGradientH1_comp_smooth_bounded_deriv μ A v φ hφ hφ0
      (4 * B) hC hLip hderiv
  refine ⟨w, ?_, ?_⟩
  · exact hwvalue
  · intro i j
    filter_upwards [hwgrad i j] with x hx
    simpa only [φ, deriv_sub_const] using hx

/-- The complete nonlinear term `Ψ_B(u)` is an actual vector of the
completed graph. Its function component is exactly the `Lp` nonlinearity
used in the fixed-point equation, and its gradient has the expected chain
formula. The additive constant is represented by a genuine smooth graph
vector whose weighted derivative vanishes. -/
theorem conformalGradientH1_curvatureNonlinearity
    (A : ConformalGradientAtlas M ι) (v : ConformalGradientH1 μ A)
    (B : ℝ) (hB : 1 < B) :
    ∃ w : ConformalGradientH1 μ A,
      conformalH1Value μ A w =
        conformalCurvatureNonlinearityLp μ B hB (conformalH1Value μ A v) ∧
      ∀ i : ι, ∀ j : Fin 2,
        conformalH1Gradient μ A w (i, j) =ᵐ[μ]
          (fun x => deriv (conformalCurvatureNonlinearity B)
            ((conformalH1Value μ A v) x) *
            (conformalH1Gradient μ A v (i, j)) x) := by
  obtain ⟨w, hwvalue, hwgrad⟩ :=
    conformalGradientH1_curvatureNonlinearity_sub_one μ A v B hB
  let oneGraph : ConformalGradientH1 μ A :=
    closedGradientGraphOfSmooth (smoothFunctionToL2 μ)
      (conformalSmoothGradient μ A) (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M))
  have honeValue : conformalH1Value μ A oneGraph =ᵐ[μ] (fun _ => 1) := by
    change smoothFunctionToL2 μ (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M)) =ᵐ[μ] (fun _ => 1)
    exact smoothFunctionToL2_coeFn μ _
  have honeGradient : conformalH1Gradient μ A oneGraph = 0 := by
    change conformalSmoothGradient μ A (Internal.ConformalCurvatureWeakChainRuleHelpers.smoothOne (M := M)) = 0
    exact smoothOne_gradient_zero μ A
  have hwholeValue : conformalH1Value μ A (w + oneGraph) =ᵐ[μ]
      (fun x => conformalCurvatureNonlinearity B ((conformalH1Value μ A v) x)) := by
    rw [map_add]
    filter_upwards [Lp.coeFn_add (conformalH1Value μ A w)
      (conformalH1Value μ A oneGraph), hwvalue, honeValue] with x hadd hw hone
    rw [hadd, Pi.add_apply, hw, hone]
    ring
  refine ⟨w + oneGraph, ?_, ?_⟩
  · apply Lp.ext
    exact hwholeValue.trans
      (conformalCurvatureNonlinearityLp_coeFn μ B hB
        (conformalH1Value μ A v)).symm
  · intro i j
    have hgradEq : conformalH1Gradient μ A (w + oneGraph) =
        conformalH1Gradient μ A w := by
      rw [map_add, honeGradient, add_zero]
    rw [hgradEq]
    exact hwgrad i j

#print axioms conformalGradientH1_curvatureNonlinearity_sub_one
#print axioms conformalGradientH1_curvatureNonlinearity

end

end SystolicGrowth
