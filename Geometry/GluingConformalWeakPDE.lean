module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalGradientWeakLaplacian
public import Geometry.GluingConformalDirichlet
public import Geometry.ConformalCurvatureWeakChainRule

@[expose] public section

/-!
# The constructed glued graph solution satisfies the actual scalar PDE

All energy, tensor, measure and curvature inputs of the local weak
Laplacian theorem are filled by the already constructed original surface.
The forcing is the literal `K + Ψ_B(u)`, not an abstract auxiliary function.
-/

open Set Filter Manifold IsManifold MeasureTheory Riemannian
open scoped ContDiff Manifold RealInnerProductSpace

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The entire actual nonlinear forcing is itself in the
completed gradient graph, by the proved weak chain rule and the smooth
intrinsic curvature field. This supplies its local `H¹` regularity. -/
theorem exists_gluedConformal_forcing_graph
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas) :
    ∃ F : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      conformalH1Value _ _ F = P.gluedConformalGaussianL2 +
        conformalCurvatureNonlinearityLp P.gluedCurvatureBoundedAreaMeasure B hB
          (conformalH1Value _ _ v) := by
  let μ := P.gluedCurvatureBoundedAreaMeasure
  let A := P.gluedConformalGradientAtlas
  obtain ⟨w, hw, _⟩ := conformalGradientH1_curvatureNonlinearity μ A v B hB
  let K : C^∞⟮𝓘(ℝ, ℂ), P.GluedCarrier; ℝ⟯ :=
    ⟨P.gluedCurvatureBoundedGaussian, P.gluedCurvatureBoundedGaussian_contMDiff⟩
  let k : ConformalGradientH1 μ A :=
    closedGradientGraphOfSmooth (smoothFunctionToL2 μ) (conformalSmoothGradient μ A) K
  refine ⟨k + w, ?_⟩
  change conformalH1Value μ A (k + w) = _
  rw [map_add, hw]
  rfl

/-- **Math.** Every actual graph weak solution has the literal local
Euclidean curvature equation on every genuine constructed metric/area
patch. All original-surface geometric inputs are supplied internally. -/
theorem gluedConformalGradient_weak_laplacian
    (P : ExerciseGluingPreparation C g n genera X) (B : ℝ) (hB : 1 < B)
    (v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas)
    (hweak : ∀ w : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
      inner ℝ (conformalH1Gradient _ _ v) (conformalH1Gradient _ _ w) =
        -inner ℝ (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp
          P.gluedCurvatureBoundedAreaMeasure B hB (conformalH1Value _ _ v))
          (conformalH1Value _ _ w))
    (Q : GluedConformalPatch P)
    (η : ℂ → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηsub : tsupport η ⊆ (Q.original.trans Q.change) '' Q.region) :
    let e := Q.original.trans Q.change
    let u := conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v
    (∫ z : ℂ, u (e.symm z) * Laplacian.laplacian η z) =
      ∫ z : ℂ, Q.coefficient z ^ 2 *
        ((P.gluedCurvatureBoundedGaussian (e.symm z) +
          conformalCurvatureNonlinearity B (u (e.symm z))) * η z) := by
  let μ := P.gluedCurvatureBoundedAreaMeasure
  let A := P.gluedConformalGradientAtlas
  let u := conformalH1Value μ A v
  have henergy (f h : C^∞⟮𝓘(ℝ, ℂ), P.GluedCarrier; ℝ⟯) :
      inner ℝ (conformalSmoothGradient μ A f) (conformalSmoothGradient μ A h) =
        ∫ x, smoothDirichletDensity P.gluedCurvatureBoundedSmoothRiemannianMetric f h x ∂μ := by
    rw [conformalSmoothGradient_inner_eq_integral_components]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (P.gluedConformalGradient_sum_pair_eq f h)
  have hforcing :
      (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp μ B hB u : Lp ℝ 2 μ) =ᵐ[μ]
        fun b => P.gluedCurvatureBoundedGaussian b + conformalCurvatureNonlinearity B (u b) := by
    filter_upwards [Lp.coeFn_add P.gluedConformalGaussianL2
      (conformalCurvatureNonlinearityLp μ B hB u), P.gluedConformalGaussianL2_coeFn,
      conformalCurvatureNonlinearityLp_coeFn μ B hB u] with b hb hK hN
    simp only [Pi.add_apply] at hb
    rw [hb, hK, hN]
  exact conformalH1Gradient_weak_laplacian μ A P.gluedCurvatureBoundedSmoothRiemannianMetric
    henergy (Q.original.trans Q.change) Q.chart_mem Q.region Q.region_open Q.region_subset
    Q.coefficient Q.coefficient_smooth Q.coefficient_pos
    (fun b hb => Q.metric_in_inverseTangent P b hb (Q.region_subset hb)) Q.area_eq v
    (P.gluedConformalGaussianL2 + conformalCurvatureNonlinearityLp μ B hB u)
    (fun b => P.gluedCurvatureBoundedGaussian b + conformalCurvatureNonlinearity B (u b))
    hforcing hweak η hη hηc hηsub

/-- **Math.** Construct an actual surface weak solution and its local
scalar curvature PDE simultaneously, with the curvature bound and every
metric/measure/solver input already filled. Smooth regularity is the next
obligation; no local PDE existence is assumed. -/
theorem exists_gluedConformal_weak_scalar_solution
    (P : ExerciseGluingPreparation C g n genera X) :
    ∃ (B : ℝ) (_hB : 1 < B),
      (∀ b, P.gluedCurvatureBoundedGaussian b ∈ Icc (-B) (-1 : ℝ)) ∧
      ∃ v : ConformalGradientH1 P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas,
        ∀ (Q : GluedConformalPatch P) (η : ℂ → ℝ),
          ContDiff ℝ ∞ η → HasCompactSupport η →
          tsupport η ⊆ (Q.original.trans Q.change) '' Q.region →
          let e := Q.original.trans Q.change
          let u := conformalH1Value P.gluedCurvatureBoundedAreaMeasure P.gluedConformalGradientAtlas v
          (∫ z : ℂ, u (e.symm z) * Laplacian.laplacian η z) =
            ∫ z : ℂ, Q.coefficient z ^ 2 *
              ((P.gluedCurvatureBoundedGaussian (e.symm z) +
                conformalCurvatureNonlinearity B (u (e.symm z))) * η z) := by
  obtain ⟨B, hB, hK, v, hweak⟩ := P.exists_gluedConformalGradient_solution
  exact ⟨B, hB, hK, v, fun Q η hη hηc hηsub =>
    P.gluedConformalGradient_weak_laplacian B hB v hweak Q η hη hηc hηsub⟩

#print axioms gluedConformalGradient_weak_laplacian
#print axioms exists_gluedConformal_weak_scalar_solution
#print axioms exists_gluedConformal_forcing_graph

end

end SystolicGrowth.ExerciseGluingPreparation
