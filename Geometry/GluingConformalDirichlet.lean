module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalDirichletDensity
public import Geometry.GluingConformalGradientGraph
public import Geometry.GluingCurveSpeed

@[expose] public section

/-!
# The actual glued surface's intrinsic Dirichlet density

The inverse differential retained by each constructed conformal patch is
identified with the actual manifold chart differential. Consequently the
finite gradient used by the nonlinear solver has exactly the original
smooth metric's Dirichlet density, including chart overlaps.
-/

open Set Manifold IsManifold Bundle Riemannian
open scoped ContDiff Manifold

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The original atlas's inverse tangent trivialization is its
actual inverse-chart manifold derivative. -/
theorem gluedTangentTrivialization_symm_eq_mfderiv
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : ℂ) :
    ((tangentBundleCore 𝓘(ℝ, ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm (e b) v := by
  let T := (tangentBundleCore 𝓘(ℝ, ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  have hi := (mdifferentiable_of_mem_atlas (I := 𝓘(ℝ, ℂ)) he).comp_symm_deriv
    (e.map_source hb)
  rw [e.left_inv hb] at hi
  have hforward : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e b
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm (e b) v) = v :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L v) hi
  have ht := T.symmL_continuousLinearMapAt (R := ℝ) (by exact hb)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm (e b) v)
  have hTforward : T.continuousLinearMapAt ℝ b
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm (e b) v) = v :=
    (congrArg (fun L : TangentSpace 𝓘(ℝ, ℂ) b →L[ℝ] ℂ =>
      L (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) e.symm (e b) v))
      (P.gluedTangentTrivialization_eq_mfderiv e he b hb)).trans hforward
  exact (congrArg (T.symmL ℝ b) hTforward).symm.trans ht

/-- **Math.** The constructed conformal inverse differential equals the
actual inverse chart tangent map on the same original smooth atlas. -/
theorem GluedConformalPatch.inverseTangent_eq
    (P : ExerciseGluingPreparation C g n genera X)
    (A : GluedConformalPatch P) (b : P.GluedCarrier)
    (hb : b ∈ (A.original.trans A.change).source) (v : ℂ) :
    conformalChartInverseTangent (A.original.trans A.change) A.chart_mem b hb v =
      ((tangentBundleCore 𝓘(ℝ, ℂ) P.GluedCarrier).localTriv
        (⟨A.original, A.original_mem⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b
          (A.inverseDerivative ((A.original.trans A.change) b) v) := by
  let e := A.original
  let ψ := A.change
  let z := (e.trans ψ) b
  have hz := (e.trans ψ).map_source hb
  have hbE : b ∈ e.source := hb.1
  have hleft : ψ.symm z = e b := ψ.left_inv hb.2
  have hD := A.derivative_eq z hz.1
  have houter := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, ℂ)) A.original_mem hz.2
  have hinner : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ.symm z :=
    hD.differentiableAt.mdifferentiableAt
  have hc := mfderiv_comp_apply z houter hinner v
  rw [mfderiv_eq_fderiv, hD.fderiv, hleft] at hc
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (e.trans ψ).symm z v = _
  rw [P.gluedTangentTrivialization_symm_eq_mfderiv e A.original_mem b hbE]
  exact hc

/-- **Math.** The actual tensor identity for a patch in the intrinsic
inverse-chart tangent frame used by the Dirichlet comparison. -/
theorem GluedConformalPatch.metric_in_inverseTangent
    (P : ExerciseGluingPreparation C g n genera X)
    (A : GluedConformalPatch P) (b : P.GluedCarrier) (hb : b ∈ A.region)
    (hbs : b ∈ (A.original.trans A.change).source) (v w : ℂ) :
    P.gluedCurvatureBoundedSmoothRiemannianMetric.inner b
      (conformalChartInverseTangent (A.original.trans A.change) A.chart_mem b hbs v)
      (conformalChartInverseTangent (A.original.trans A.change) A.chart_mem b hbs w) =
        A.coefficient ((A.original.trans A.change) b) ^ 2 *
          (v.re * w.re + v.im * w.im) := by
  rw [A.inverseTangent_eq P b hbs v, A.inverseTangent_eq P b hbs w]
  exact A.metric_eq b hb v w

/-- **Math.** The solver's concrete weighted-coordinate gradient has the
original smooth metric's exact Dirichlet density at every carrier point. -/
theorem gluedConformalGradient_sum_pair_eq
    (P : ExerciseGluingPreparation C g n genera X)
    (f h : C^∞⟮𝓘(ℝ, ℂ), P.GluedCarrier; ℝ⟯) (b : P.GluedCarrier) :
    let A := P.gluedConformalGradientAtlas
    (∑ i, (weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) 1 f b *
        weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) 1 h b +
      weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) Complex.I f b *
        weightedChartDerivative (A.chart i) (A.coefficient i) (A.weight i) Complex.I h b)) =
      smoothDirichletDensity P.gluedCurvatureBoundedSmoothRiemannianMetric f h b := by
  apply sum_weightedChartDerivative_pair_eq
  intro i hbs hi v w
  let A := P.gluedConformalGradientData
  let Q := P.gluedConformalPatch (A.center i)
  have hb : b ∈ Q.region := A.weight_support i (subset_closure hi)
  exact Q.metric_in_inverseTangent P b hb hbs v w

#print axioms GluedConformalPatch.inverseTangent_eq
#print axioms GluedConformalPatch.metric_in_inverseTangent
#print axioms gluedConformalGradient_sum_pair_eq

end

end SystolicGrowth.ExerciseGluingPreparation
