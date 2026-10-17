module

public import Geometry.TwoOpenCoverFundamentalGroup
public import Geometry.GluingChainVanKampen
public import Geometry.GluingChainCoverConnected

@[expose] public section

/-! Surjectivity of the literal native chain-cover amalgam map. -/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every actual based loop class on the original glued carrier is in the image of the
canonical overlap amalgam. Arbitrary continuous loops are allowed. -/
theorem gluedChainCoverAmalgamToFundamentalGroup_surjective
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : Circle) :
    Function.Surjective (P.gluedChainCoverAmalgamToFundamentalGroup k θ) := by
  apply MonoidHom.range_eq_top.1
  have hxU : (P.gluedSeamCircleInclusion k θ).1 ∈ P.gluedChainPrefixNeighborhood k :=
    Or.inr (P.gluedSeamCircleInclusion k θ).2
  have hxV : (P.gluedSeamCircleInclusion k θ).1 ∈ P.gluedChainSuffixNeighborhood k :=
    Or.inr (P.gluedSeamCircleInclusion k θ).2
  have hpcUV : IsPathConnected
      (P.gluedChainPrefixNeighborhood k ∩ P.gluedChainSuffixNeighborhood k) := by
    rw [P.gluedChainPrefixNeighborhood_inter_suffix k]
    exact P.gluedSeamNeighborhood_isPathConnected k
  apply fundamentalGroup_subgroup_eq_top_of_two_open_cover
    (P.gluedChainPrefixNeighborhood_isOpen k) (P.gluedChainSuffixNeighborhood_isOpen k)
    (P.gluedChainPrefixNeighborhood_union_suffix k)
    (P.gluedChainPrefixNeighborhood_isPathConnected k)
    (P.gluedChainSuffixNeighborhood_isPathConnected k) hpcUV hxU hxV
  · rintro γ ⟨δ, rfl⟩
    refine ⟨Monoid.PushoutI.of true δ, ?_⟩
    exact P.gluedChainCoverAmalgamToFundamentalGroup_of k θ true δ
  · rintro γ ⟨δ, rfl⟩
    refine ⟨Monoid.PushoutI.of false δ, ?_⟩
    exact P.gluedChainCoverAmalgamToFundamentalGroup_of k θ false δ

end

end SystolicGrowth.ExerciseGluingPreparation
