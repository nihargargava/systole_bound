module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HilbertGraphResolvent
public import Geometry.ClosedGradientGraph
public import Geometry.CoerciveResolventFixedPoint
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# A constructed nonlinear solution in the actual Hilbert graph

The coercive graph inverse, not an assumed resolvent, supplies the `L²`
fixed point. Applying its lift recovers an actual graph vector. Cancelling
the mass terms gives the exact weak conformal-curvature equation against
every graph test vector. Identifying this graph with manifold weak
gradients and proving smooth regularity remain separate geometric steps.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (J : V →L[ℝ] Lp ℝ 2 μ) (hJ : ∀ v : V, ‖J v‖ ≤ ‖v‖)
  (B : ℝ) (hB : 1 < B) (K : Lp ℝ 2 μ)

/-- The actual function fixed point for the constructed graph resolvent,
with the internally chosen positive mass `4 * B + 1`. -/
def conformalHilbertGraphFunction : Lp ℝ 2 μ :=
  conformalCurvatureResolventFixedPoint μ B (4 * B + 1) hB (by linarith) K
    (hilbertGraphResolvent J (by linarith))
    (hilbertGraphResolvent_opNorm_le J hJ (by linarith))

/-- Apply the actual coercive inverse lift to the nonlinear right-hand side. -/
def conformalHilbertGraphSolution : V :=
  let u := conformalHilbertGraphFunction μ J hJ B hB K
  hilbertGraphResolventLift J (show 1 ≤ 4 * B + 1 by linarith)
    ((4 * B + 1) • u - K - conformalCurvatureNonlinearityLp μ B hB u)

theorem conformalHilbertGraphSolution_projection :
    J (conformalHilbertGraphSolution μ J hJ B hB K) =
      conformalHilbertGraphFunction μ J hJ B hB K := by
  have h := conformalCurvatureResolventFixedPoint_equation μ B (4 * B + 1) hB
    (show 4 * B ≤ 4 * B + 1 by linarith) K
    (hilbertGraphResolvent J (show 1 ≤ 4 * B + 1 by linarith))
    (hilbertGraphResolvent_opNorm_le J hJ (by linarith))
  exact h.symm

/-- **Math.** The function and derivative components satisfy the exact
cancelled weak equation. There is no solvability or resolvent hypothesis. -/
theorem conformalHilbertGraphSolution_weak (w : V) :
    let v := conformalHilbertGraphSolution μ J hJ B hB K
    inner ℝ v w - inner ℝ (J v) (J w) =
      -inner ℝ (K + conformalCurvatureNonlinearityLp μ B hB (J v)) (J w) := by
  let u := conformalHilbertGraphFunction μ J hJ B hB K
  have h := hilbertGraphResolventLift_weak J (show 1 ≤ 4 * B + 1 by linarith)
    ((4 * B + 1) • u - K - conformalCurvatureNonlinearityLp μ B hB u) w
  rw [hilbertGraphEnergy_apply] at h
  change inner ℝ (conformalHilbertGraphSolution μ J hJ B hB K) w +
      ((4 * B + 1) - 1) * inner ℝ (J (conformalHilbertGraphSolution μ J hJ B hB K)) (J w) = _ at h
  rw [conformalHilbertGraphSolution_projection] at h
  simp only [inner_sub_left, real_inner_smul_left] at h
  dsimp only
  rw [conformalHilbertGraphSolution_projection, inner_add_left]
  change inner ℝ (conformalHilbertGraphSolution μ J hJ B hB K) w - inner ℝ u (J w) =
    -(inner ℝ K (J w) + inner ℝ (conformalCurvatureNonlinearityLp μ B hB u) (J w))
  linarith

/-- The same exact equation against scalar function representatives. The
nonlinear integral contains the constructed scalar `Ψ`, not an arbitrary
representative of a separately supplied nonlinear `Lp` element. -/
theorem conformalHilbertGraphSolution_weak_integral (w : V) :
    let v := conformalHilbertGraphSolution μ J hJ B hB K
    inner ℝ v w - (∫ x, (J v) x * (J w) x ∂μ) =
      -(∫ x, (K x + conformalCurvatureNonlinearity B ((J v) x)) * (J w) x ∂μ) := by
  let v := conformalHilbertGraphSolution μ J hJ B hB K
  have h := conformalHilbertGraphSolution_weak μ J hJ B hB K w
  have hlinear : inner ℝ (J v) (J w) = ∫ x, (J v) x * (J w) x ∂μ := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
  have hnonlinear : inner ℝ (K + conformalCurvatureNonlinearityLp μ B hB (J v)) (J w) =
      ∫ x, (K x + conformalCurvatureNonlinearity B ((J v) x)) * (J w) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add K (conformalCurvatureNonlinearityLp μ B hB (J v)),
      conformalCurvatureNonlinearityLp_coeFn μ B hB (J v)] with x hx hp
    simp only [Pi.add_apply] at hx
    rw [Real.inner_apply, hx, hp]
  change inner ℝ v w - inner ℝ (J v) (J w) =
    -inner ℝ (K + conformalCurvatureNonlinearityLp μ B hB (J v)) (J w) at h
  rw [hlinear, hnonlinear] at h
  exact h

include hJ in
/-- The nonlinear weak equation has an actual witness in the graph.
The graph's geometric weak-gradient identification is not assumed here. -/
theorem exists_conformalHilbertGraphSolution :
    ∃ v : V, ∀ w : V, inner ℝ v w - inner ℝ (J v) (J w) =
      -inner ℝ (K + conformalCurvatureNonlinearityLp μ B hB (J v)) (J w) := by
  exact ⟨conformalHilbertGraphSolution μ J hJ B hB K,
    conformalHilbertGraphSolution_weak μ J hJ B hB K⟩

#print axioms conformalHilbertGraphSolution_projection
#print axioms conformalHilbertGraphSolution_weak
#print axioms conformalHilbertGraphSolution_weak_integral
#print axioms exists_conformalHilbertGraphSolution

/-- The nonlinear solution in a literal completed gradient graph satisfies
the derivative-component equation, with its function projection constructed
from the graph rather than supplied as an additional contractive map. -/
theorem exists_closedGradientGraph_conformalSolution
    {D G : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (value : D →ₗ[ℝ] Lp ℝ 2 μ) (derivative : D →ₗ[ℝ] G) :
    ∃ v : closedGradientGraph value derivative,
      ∀ w : closedGradientGraph value derivative,
      inner ℝ (closedGradientGraphDerivative value derivative v)
          (closedGradientGraphDerivative value derivative w) =
        -inner ℝ (K + conformalCurvatureNonlinearityLp μ B hB
          (closedGradientGraphValue value derivative v))
          (closedGradientGraphValue value derivative w) := by
  obtain ⟨v, hv⟩ := exists_conformalHilbertGraphSolution μ
    (closedGradientGraphValue value derivative)
    (closedGradientGraphValue_norm_le value derivative) B hB K
  refine ⟨v, fun w => ?_⟩
  have h := hv w
  rw [closedGradientGraph_inner] at h
  simpa only [add_sub_cancel_left] using h

#print axioms exists_closedGradientGraph_conformalSolution

end

end SystolicGrowth
