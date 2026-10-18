module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalGradientGraph
public import Geometry.SmoothSquaredPartition
public import Geometry.GluingConformalCurvatureAndArea
public import Geometry.GluingConformalAreaCharts

@[expose] public section

/-!
# The actual glued surface's conformal gradient space

The charts, area identities, finite supported weights, smooth derivative
maps and completed gradient graph are all chosen from proved constructors
for the original glued carrier. The nonlinear equation therefore has a
genuine graph witness. Its local distributional interpretation and smooth
regularity remain subsequent proofs, not fields in these constructors.
-/

open Set Bundle Manifold IsManifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** One actual conformal patch, retaining its original chart and
the proved coordinate change, tensor identity and area identity together. -/
structure GluedConformalPatch (P : ExerciseGluingPreparation C g n genera X) where
  original : OpenPartialHomeomorph P.GluedCarrier ℂ
  original_mem : original ∈ P.gluedComplexAtlas
  change : OpenPartialHomeomorph ℂ ℂ
  coefficient : ℂ → ℝ
  inverseDerivative : ℂ → ℂ →L[ℝ] ℂ
  region : Set P.GluedCarrier
  region_open : IsOpen region
  region_subset : region ⊆ (original.trans change).source
  change_source : change.source = univ
  change_smooth : ContDiff ℝ ∞ (change : ℂ → ℂ)
  chart_mem : original.trans change ∈ maximalAtlas 𝓘(ℝ, ℂ) ∞ P.GluedCarrier
  coefficient_smooth : ContDiffOn ℝ ∞ coefficient (original.trans change).target
  coefficient_pos : ∀ z ∈ (original.trans change).target, 0 < coefficient z
  derivative_eq : ∀ z ∈ change.target, HasFDerivAt change.symm (inverseDerivative z) z
  metric_eq : ∀ c ∈ region, ∀ v w : ℂ,
    P.gluedCurvatureBoundedSmoothRiemannianMetric.inner c
      (((tangentBundleCore 𝓘(ℝ, ℂ) P.GluedCarrier).localTriv
        (⟨original, original_mem⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c
          (inverseDerivative ((original.trans change) c) v))
      (((tangentBundleCore 𝓘(ℝ, ℂ) P.GluedCarrier).localTriv
        (⟨original, original_mem⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ c
          (inverseDerivative ((original.trans change) c) w)) =
      coefficient ((original.trans change) c) ^ 2 * (v.re * w.re + v.im * w.im)
  area_eq : ∀ s : Set ℂ, MeasurableSet s → s ⊆ (original.trans change) '' region →
    P.gluedCurvatureBoundedAreaMeasure ((original.trans change).symm '' s) =
      ∫⁻ z : ℂ in s, ENNReal.ofReal (coefficient z ^ 2)

/-- **Math.** Every carrier point has such a patch by the existing concrete
ODE seam/interior constructions; no chart or area law is supplied as input. -/
theorem exists_gluedConformalPatch (P : ExerciseGluingPreparation C g n genera X)
    (b : P.GluedCarrier) : ∃ A : GluedConformalPatch P, b ∈ A.region := by
  obtain ⟨e, he, ψ, a, D, U, hb, hU, hsub, hsource, hψ, hchart, ha, hapos, hD, hmetric, harea⟩ :=
    P.exists_gluedCurvatureBounded_conformal_metric_area_chart b
  exact ⟨⟨e, he, ψ, a, D, U, hU, hsub, hsource, hψ, hchart, ha, hapos, hD, hmetric, harea⟩, hb⟩

/-- **Math.** Select one of the proved concrete patches at each point. -/
def gluedConformalPatch (P : ExerciseGluingPreparation C g n genera X)
    (b : P.GluedCarrier) : GluedConformalPatch P :=
  (P.exists_gluedConformalPatch b).choose

theorem mem_gluedConformalPatch_region (P : ExerciseGluingPreparation C g n genera X)
    (b : P.GluedCarrier) : b ∈ (P.gluedConformalPatch b).region :=
  (P.exists_gluedConformalPatch b).choose_spec

/-- **Math.** Finite weights subordinate to the same selected metric/area
patches. The support condition retains the precise neighborhoods where the
geometric formulas hold, not only the larger chart domains. -/
structure GluedConformalGradientData (P : ExerciseGluingPreparation C g n genera X) where
  size : ℕ
  center : Fin size → P.GluedCarrier
  weight : Fin size → C^∞⟮𝓘(ℝ, ℂ), P.GluedCarrier; ℝ⟯
  weight_support : ∀ i, tsupport (weight i) ⊆ (P.gluedConformalPatch (center i)).region
  weight_sum_sq : ∀ x, ∑ i, (weight i x) ^ 2 = 1

/-- **Math.** Construct the finite supported weights internally by compact
smooth partition of unity, followed by square normalization. -/
def gluedConformalGradientData (P : ExerciseGluingPreparation C g n genera X) :
    GluedConformalGradientData P := by
  classical
  apply Classical.choice
  have hU : ∀ b : P.GluedCarrier, (P.gluedConformalPatch b).region ∈ 𝓝 b := fun b =>
    (P.gluedConformalPatch b).region_open.mem_nhds (P.mem_gluedConformalPatch_region b)
  obtain ⟨N, c, τ, hs, _, hsum⟩ := exists_smoothSquareCover_subordinate
    (fun b : P.GluedCarrier => (P.gluedConformalPatch b).region) hU
  exact ⟨⟨N, c, τ, hs, hsum⟩⟩

/-- **Math.** The concrete chosen patches and weights give the exact atlas
used by the literal smooth gradient maps. -/
def GluedConformalGradientData.toAtlas (P : ExerciseGluingPreparation C g n genera X)
    (A : GluedConformalGradientData P) : ConformalGradientAtlas P.GluedCarrier (Fin A.size) where
  chart i := (P.gluedConformalPatch (A.center i)).original.trans
    (P.gluedConformalPatch (A.center i)).change
  chart_mem i := (P.gluedConformalPatch (A.center i)).chart_mem
  coefficient i := (P.gluedConformalPatch (A.center i)).coefficient
  coefficient_smooth i := (P.gluedConformalPatch (A.center i)).coefficient_smooth
  coefficient_pos i := (P.gluedConformalPatch (A.center i)).coefficient_pos
  weight := A.weight
  weight_support i := (A.weight_support i).trans
    (P.gluedConformalPatch (A.center i)).region_subset
  weight_sum_sq := A.weight_sum_sq

/-- **Math.** The internally constructed finite conformal gradient atlas. -/
def gluedConformalGradientAtlas (P : ExerciseGluingPreparation C g n genera X) :
    ConformalGradientAtlas P.GluedCarrier (Fin P.gluedConformalGradientData.size) :=
  P.gluedConformalGradientData.toAtlas P

/-- **Math.** The actual smooth curvature field as a genuine `L²` function
for the existing finite metric area measure. -/
def gluedConformalGaussianL2 (P : ExerciseGluingPreparation C g n genera X) :
    Lp ℝ 2 P.gluedCurvatureBoundedAreaMeasure :=
  smoothFunctionToL2 P.gluedCurvatureBoundedAreaMeasure
    ⟨P.gluedCurvatureBoundedGaussian, P.gluedCurvatureBoundedGaussian_contMDiff⟩

theorem gluedConformalGaussianL2_coeFn (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedConformalGaussianL2 =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
      P.gluedCurvatureBoundedGaussian :=
  smoothFunctionToL2_coeFn _ _

/-- **Math.** An actual weak graph solution is constructed on the original
glued carrier, with all curvature, atlas, measure and resolvent inputs filled.
Identifying its local PDE and proving its regularity are not assumed here. -/
theorem exists_gluedConformalGradient_solution
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ (B : ℝ) (hB : 1 < B),
      (∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ)) ∧
      ∃ v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
        ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
          inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
            -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
              P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
              (conformalH1Value _ _ w) := by
  obtain ⟨B, hB, hK⟩ := P.exists_gluedCurvatureBoundedGaussian_uniform_bound
  refine ⟨B, hB, fun b => ⟨?_, ?_⟩, ?_⟩
  · linarith [(hK b).2]
  · linarith [(hK b).1]
  · exact exists_conformalGradientH1_solution P.gluedCurvatureBoundedAreaMeasure
      P.gluedConformalGradientAtlas B hB P.gluedConformalGaussianL2

#print axioms exists_gluedConformalPatch
#print axioms gluedConformalGradientData
#print axioms gluedConformalGaussianL2_coeFn
#print axioms exists_gluedConformalGradient_solution

end

end SystolicGrowth.ExerciseGluingPreparation
