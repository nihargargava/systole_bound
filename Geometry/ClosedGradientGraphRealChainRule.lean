module

public import Geometry.ClosedGradientGraph
public import Geometry.EuclideanWeakChainRuleL2
public import Geometry.LpGraphAeSubsequence

@[expose] public section

/-!
# The first weak chain rule in a completed real gradient graph

Strong limits of literal smooth values and derivatives yield an element of
the completed graph. The nonlinear chain construction below uses this and
the proved `L²` product convergence, not an assumed weak chain rule.
-/

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace SystolicGrowth

noncomputable section

variable {D H G : Type*} [AddCommGroup D] [Module ℝ D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Any strong joint limit of actual smooth graph pairs is in the closed
gradient graph, with exactly the prescribed value and derivative components. -/
theorem closedGradientGraph_exists_of_smooth_tendsto
    (value : D →ₗ[ℝ] H) (derivative : D →ₗ[ℝ] G)
    (f : ℕ → D) (u : H) (du : G)
    (hu : Tendsto (fun n => value (f n)) atTop (𝓝 u))
    (hdu : Tendsto (fun n => derivative (f n)) atTop (𝓝 du)) :
    ∃ v : closedGradientGraph value derivative,
      closedGradientGraphValue value derivative v = u ∧
      closedGradientGraphDerivative value derivative v = du := by
  let e : WithLp 2 (H × G) ≃L[ℝ] H × G :=
    WithLp.prodContinuousLinearEquiv 2 ℝ H G
  let z : WithLp 2 (H × G) := e.symm (u, du)
  have hzlim : Tendsto (fun n => smoothGradientGraphMap value derivative (f n))
      atTop (𝓝 z) := by
    have hp : Tendsto (fun n => (value (f n), derivative (f n)))
        atTop (𝓝 (u, du)) := by
      simpa only [nhds_prod_eq] using hu.prodMk hdu
    change Tendsto (fun n => e.symm (value (f n), derivative (f n))) atTop (𝓝 z)
    exact (e.symm.continuous.tendsto (u, du)).comp hp
  have hzmem : z ∈ closedGradientGraph value derivative := by
    apply mem_closure_of_tendsto hzlim
    exact Filter.Eventually.of_forall fun n =>
      ⟨f n, rfl⟩
  refine ⟨⟨z, hzmem⟩, ?_, ?_⟩
  · simp [closedGradientGraphValue, z, e]
  · simp [closedGradientGraphDerivative, z, e]

#print axioms closedGradientGraph_exists_of_smooth_tendsto

end

end SystolicGrowth
