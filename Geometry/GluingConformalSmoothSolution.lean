module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalFirstRegularity
public import Geometry.ComplexLocalSemilinearSmooth

@[expose] public section

/-!
# A smooth solution of the conformal curvature equation

The weak conformal curvature equation is expressed in local coordinates.
Local elliptic regularity gives a smooth representative of its solution.
The smooth metric coefficients and Gaussian curvature supply the required
regularity of the coefficients.
-/

-- Use mathlib-style docstrings, not the imported DoCarmo documentation tags.
set_option linter.shared.mathTag false

open Set Filter Manifold IsManifold MeasureTheory
open scoped ContDiff Topology Manifold RealInnerProductSpace

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- An almost-everywhere representative of the weak conformal
solution satisfies the same integral equation against compactly supported
smooth test functions. This step needs no classical second derivatives. -/
theorem conformal_solution_weak_laplacian_of_ae_eq
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
          P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
          (conformalH1Value _ _ w))
    (u : P.GluedCarrier → ℝ)
    (hAE : u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
      (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v))
    (Q : GluedConformalPatch P) (η : ℂ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ (Q.original.trans Q.change) '' Q.region) :
    let e := Q.original.trans Q.change
    (∫ z : ℂ, u (e.symm z) * Laplacian.laplacian η z) =
      ∫ z : ℂ, Q.coefficient z ^ 2 *
        ((P.gluedCurvatureBoundedGaussian (e.symm z) +
          conformalCurvatureNonlinearity B (u (e.symm z))) * η z) := by
  let e := Q.original.trans Q.change
  let Ω := e '' Q.region
  let u₀ := conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v
  have hRep : ∀ᵐ z ∂volume, z ∈ Ω → u (e.symm z) = u₀ (e.symm z) :=
    ae_imp_of_ae_restrict (conformalChart_ae_eq_pullback P.gluedCurvatureBoundedAreaMeasure
      e Q.region Q.region_open Q.region_subset Q.coefficient Q.coefficient_smooth.continuousOn
      Q.coefficient_pos Q.area_eq hAE)
  have htest := P.gluedConformalGradient_weak_laplacian B hB v hweak Q η hη hηc hηsub
  have hleft : (∫ z : ℂ, u (e.symm z) * Laplacian.laplacian η z) =
      ∫ z : ℂ, u₀ (e.symm z) * Laplacian.laplacian η z := by
    apply integral_congr_ae
    filter_upwards [hRep] with z hz
    by_cases hzΩ : z ∈ Ω
    · rw [hz hzΩ]
    · have hzero : Laplacian.laplacian η z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hzΩ (hηsub (tsupport_complex_laplacian_subset hη h)))
      simp only [hzero, mul_zero]
  have hright : (∫ z : ℂ, Q.coefficient z ^ 2 *
      ((P.gluedCurvatureBoundedGaussian (e.symm z) +
        conformalCurvatureNonlinearity B (u₀ (e.symm z))) * η z)) =
      ∫ z : ℂ, Q.coefficient z ^ 2 *
        ((P.gluedCurvatureBoundedGaussian (e.symm z) +
          conformalCurvatureNonlinearity B (u (e.symm z))) * η z) := by
    apply integral_congr_ae
    filter_upwards [hRep] with z hz
    by_cases hzΩ : z ∈ Ω
    · rw [← hz hzΩ]
    · have hzero : η z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hzΩ (hηsub h))
      simp only [hzero, mul_zero]
  exact hleft.trans (htest.trans hright)

/-- In each conformal chart, a `C^r` representative remains
`C^r`, and the metric coefficient and Gaussian curvature are smooth. -/
theorem conformal_coordinate_regularity
    (P : ExerciseGluingPreparation C g n genera X)
    (u : P.GluedCarrier → ℝ) (r : ℕ∞ω) (hr : r ≤ ∞)
    (hu : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) r u) (Q : GluedConformalPatch P) :
    let e := Q.original.trans Q.change
    let Ω := e '' Q.region
    IsOpen Ω ∧ ContDiffOn ℝ r (u ∘ e.symm) Ω ∧
      ContDiffOn ℝ ∞ Q.coefficient Ω ∧
      ContDiffOn ℝ ∞ (P.gluedCurvatureBoundedGaussian ∘ e.symm) Ω := by
  let e := Q.original.trans Q.change
  let Ω := e '' Q.region
  have hΩt : Ω ⊆ e.target := by
    rintro z ⟨b, hb, rfl⟩
    exact e.map_source (Q.region_subset hb)
  refine ⟨e.isOpen_image_of_subset_source Q.region_open Q.region_subset, ?_,
    Q.coefficient_smooth.mono hΩt, ?_⟩
  · exact ((hu.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas Q.chart_mem).of_le hr)).contDiffOn).mono hΩt
  · exact ((P.gluedCurvatureBoundedGaussian_contMDiff.comp_contMDiffOn
      (contMDiffOn_symm_of_mem_maximalAtlas Q.chart_mem)).contDiffOn).mono hΩt

#print axioms conformal_solution_weak_laplacian_of_ae_eq
#print axioms conformal_coordinate_regularity

/-- The weak conformal curvature solution has a smooth global
representative. Local elliptic regularity upgrades its constructed `C¹`
representative, using the smooth metric coefficients and Gaussian curvature. -/
theorem exists_smooth_conformal_curvature_solution
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ (B : ℝ) (hB : 1 < B),
      (∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ)) ∧
      ∃ v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
        (∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
          inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
            -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
              P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
              (conformalH1Value _ _ w)) ∧
        ∃ u : P.GluedCarrier → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ u ∧
          u =ᵐ[P.gluedCurvatureBoundedAreaMeasure]
            (conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v) := by
  obtain ⟨B, hB, hK, v, hweak, u, hu, hAE⟩ := P.exists_gluedConformal_contDiff_one_solution
  refine ⟨B, hB, hK, v, hweak, ?_⟩
  -- Glue local smooth representatives that agree with the same weak solution.
  apply P.exists_gluedConformal_global_representative v ∞ le_rfl
  intro b
  let Q := P.gluedConformalPatch b
  let e := Q.original.trans Q.change
  let Ω := e '' Q.region
  have hbQ : b ∈ Q.region := P.mem_gluedConformalPatch_region b
  obtain ⟨hΩ, huΩ, haΩ, hKΩ⟩ := P.conformal_coordinate_regularity u 1
    (WithTop.coe_le_coe.mpr (show (1 : ℕ∞) ≤ ⊤ from le_top)) hu Q
  -- Elliptic regularity upgrades the chart's C¹ representative to smoothness.
  have hsmooth : ContDiffOn ℝ ∞ (u ∘ e.symm) Ω :=
    complexLocalSemilinear_contDiffOn hΩ (u ∘ e.symm)
      (P.gluedCurvatureBoundedGaussian ∘ e.symm) Q.coefficient
      (conformalCurvatureNonlinearity B) huΩ hKΩ haΩ
      (conformalCurvatureNonlinearity_contDiff B)
      (P.conformal_solution_weak_laplacian_of_ae_eq B hB v hweak u hAE Q)
  refine ⟨Q, Ω, u ∘ e.symm, hbQ, hΩ, ⟨b, hbQ, rfl⟩, Subset.rfl, hsmooth, ?_⟩
  exact (conformalChart_ae_eq_pullback P.gluedCurvatureBoundedAreaMeasure e Q.region
    Q.region_open Q.region_subset Q.coefficient Q.coefficient_smooth.continuousOn
    Q.coefficient_pos Q.area_eq hAE).symm

/-- **Math.** Construct a hyperbolic replacement retaining the target
systole lower bound, a faithful surface-group action and a compact
fundamental set. The smooth curvature solution and its nonnegative bound
supply the metric; marked holonomy and its coherent lift supply the action. -/
def gluedConformalLiftedChainOutput
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    ExerciseLiftedChainOutput g (targetSystole C g) :=
  Classical.choice (by
    obtain ⟨B, hB, hK, v, hweak, u, hu, hAE⟩ := P.exists_smooth_conformal_curvature_solution
    let x : P.GluedCarrier := (P.gluedSeamCircleInclusion ⟨0, by omega⟩ 1).val
    exact ⟨P.gluedConformalGradientLiftedOutput_of_smooth_representative
      x hn hsum B hB hK v hweak u hu hAE⟩)

#print axioms exists_smooth_conformal_curvature_solution
#print axioms gluedConformalLiftedChainOutput

end

end SystolicGrowth.ExerciseGluingPreparation
