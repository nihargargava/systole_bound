module

public import Geometry.BoundedCoefficientL2Convergence

@[expose] public section

/-!
# A.e. subsequences of strongly convergent gradient-graph approximants

Strong `L²` convergence of values provides a pointwise-a.e. convergent
subsequence; the same subsequence retains strong convergence of every
gradient component. This is the extraction used in the first weak chain rule.
-/

open MeasureTheory Filter
open scoped Topology

namespace SystolicGrowth

noncomputable section

theorem lp_two_ae_subsequence_preserves_graph_limit
    {α G : Type*} [MeasurableSpace α] [TopologicalSpace G]
    (μ : Measure α)
    (values : ℕ → Lp ℝ 2 μ) (u : Lp ℝ 2 μ)
    (gradients : ℕ → G) (du : G)
    (hvalues : Tendsto values atTop (𝓝 u))
    (hgradients : Tendsto gradients atTop (𝓝 du)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => values (ns n) x) atTop (𝓝 (u x))) ∧
      Tendsto (fun n => values (ns n)) atTop (𝓝 u) ∧
      Tendsto (fun n => gradients (ns n)) atTop (𝓝 du) := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hvalues).exists_seq_tendsto_ae
  exact ⟨ns, hns, hae, hvalues.comp hns.tendsto_atTop,
    hgradients.comp hns.tendsto_atTop⟩

#print axioms lp_two_ae_subsequence_preserves_graph_limit

end

end SystolicGrowth
