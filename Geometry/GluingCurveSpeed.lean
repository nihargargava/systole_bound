module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingRiemannianMetric
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
-- The chart-velocity identification uses the defining tangent/model-space casts.
import all Mathlib.Geometry.Manifold.IsManifold.Basic

@[expose] public section

/-!
# Actual native curve speed in glued coordinates

The manifold chain rule identifies a curve's native tangent velocity with
the inverse tangent trivialization of its actual chart derivative. The
constructed continuous Riemannian metric therefore gives the coordinate
speed formulas, including signed-radius zero seam points. No replacement
velocity, tangent norm or metric agreement hypothesis is used.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology Bundle

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

set_option backward.isDefEq.respectTransparency false in
/-- The forward native atlas trivialization is the actual manifold derivative
of the chart. -/
theorem gluedTangentTrivialization_eq_mfderiv
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) :
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).continuousLinearMapAt ℝ b =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) e b := by
  calc
    _ = (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).coordChange
        (achart ℂ b) (⟨e, he⟩ : atlas ℂ P.GluedCarrier) b :=
      (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv_continuousLinearMapAt
        (by exact hb)
    _ = fderiv ℝ ((chartAt ℂ b).symm.trans e) (chartAt ℂ b b) :=
      P.gluedTangentCoordChange_eq_fderiv (achart ℂ b) ⟨e, he⟩ b
    _ = mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) e b := by
      simp only [mfderiv, ite_eq_left (mdifferentiableAt_atlas he hb),
        writtenInExtChartAt, mfld_simps, fderivWithin_univ]
      ext v
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- Native velocity is the inverse actual chart tangent trivialization of
the ordinary real derivative of the coordinate curve. -/
theorem gluedCurve_velocity_in_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {t : ℝ} (ht : γ t ∈ e.source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1 =
      ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
        (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ (γ t) (deriv (e ∘ γ) t) := by
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
  have hc : (Z.localTriv i).continuousLinearMapAt ℝ (γ t)
      (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1) =
        deriv (e ∘ γ) t := by
    calc
      _ = mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) e (γ t)
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1) :=
        congrArg (fun f : TangentSpace (modelWithCornersSelf ℝ ℂ) (γ t) →L[ℝ] ℂ =>
          f (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1))
          (P.gluedTangentTrivialization_eq_mfderiv e he (γ t) ht)
      _ = mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) (e ∘ γ) t 1 :=
        (mfderiv_comp_apply t (mdifferentiableAt_atlas he ht) hγ 1).symm
      _ = deriv (e ∘ γ) t := by
        rw [mfderiv_eq_fderiv]
        rfl
  rw [← hc]
  exact ((Z.localTriv i).symmL_continuousLinearMapAt (by exact ht) _).symm

set_option backward.isDefEq.respectTransparency false in
/-- Squared native speed in any actual glued atlas chart, using only the
constructed local Riemannian bundle instance. -/
theorem gluedCurve_speed_sq_in_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {t : ℝ} (ht : γ t ∈ e.source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ ^ 2 =
      P.gluingChartTangentForm e (e (γ t)) (deriv (e ∘ γ) t) (deriv (e ∘ γ) t) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  let v := mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
  calc
    ‖v‖ ^ 2 = P.gluedTangentInner (γ t) v v := (real_inner_self_eq_norm_sq v).symm
    _ = P.gluedTangentInner (γ t)
        ((Z.localTriv i).symmL ℝ (γ t) (deriv (e ∘ γ) t))
        ((Z.localTriv i).symmL ℝ (γ t) (deriv (e ∘ γ) t)) :=
      congrArg₂ (fun a b : TangentSpace (modelWithCornersSelf ℝ ℂ) (γ t) =>
        P.gluedTangentInner (γ t) a b)
        (P.gluedCurve_velocity_in_chart e he ht hγ)
        (P.gluedCurve_velocity_in_chart e he ht hγ)
    _ = _ := P.gluedTangentInner_in_chart e he (γ t) ht _ _

set_option backward.isDefEq.respectTransparency false in
/-- Native speed is the square root of the actual coordinate form. -/
theorem gluedCurve_speed_in_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {t : ℝ} (ht : γ t ∈ e.source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ =
      Real.sqrt (P.gluingChartTangentForm e (e (γ t))
        (deriv (e ∘ γ) t) (deriv (e ∘ γ) t)) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [← P.gluedCurve_speed_sq_in_chart e he ht hγ, Real.sqrt_sq (norm_nonneg _)]

/-- A native C¹ curve staying in an actual chart has ordinary C¹ coordinate
functions on the same set; no differentiability outside that set is asserted. -/
theorem gluedCurve_chart_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {s : Set ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ s)
    (hs : MapsTo γ s e.source) : ContDiffOn ℝ 1 (e ∘ γ) s := by
  exact ((contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)).comp hγ hs).contDiffOn

/-- Within-interval C¹ regularity gives a full native derivative at interior
times. Endpoints require within derivatives, not this at-point conclusion. -/
theorem gluedCurve_mdifferentiableAt_Ioo
    (P : ExerciseGluingPreparation C g n genera X)
    {γ : ℝ → P.GluedCarrier} {a b t : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (ht : t ∈ Ioo a b) :
    MDifferentiableAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t :=
  (hγ.mdifferentiableOn one_ne_zero).mdifferentiableAt (Icc_mem_nhds ht.1 ht.2)

set_option backward.isDefEq.respectTransparency false in
/-- The native interior squared speed is the Poincare coordinate speed. -/
theorem gluedCurve_speed_sq_interior
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {γ : ℝ → P.GluedCarrier} {t : ℝ} (ht : γ t ∈ e.source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ ^ 2 =
      ‖deriv (e ∘ γ) t‖ ^ 2 / (e (γ t)).im ^ 2 := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [P.gluedCurve_speed_sq_in_chart e (Or.inl he) ht hγ,
    P.gluingChartTangentForm_interior e he, gluingComplexHalfPlaneTangentForm_self]

set_option backward.isDefEq.respectTransparency false in
/-- The native seam squared speed uses the actual signed collar warp,
without excluding signed radius zero or selecting a nonzero branch. -/
theorem gluedCurve_speed_sq_seam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {t : ℝ} (ht : γ t ∈ (P.seamAngularComplexChart k θ).source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ ^ 2 =
      (deriv (P.seamAngularComplexChart k θ ∘ γ) t).re ^ 2 +
        gluingCollarWarp (gluingRadius C g) (P.seamAngularComplexChart k θ (γ t)).re ^ 2 *
          (deriv (P.seamAngularComplexChart k θ ∘ γ) t).im ^ 2 := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [P.gluedCurve_speed_sq_in_chart (P.seamAngularComplexChart k θ)
      (Or.inr ⟨k, θ, rfl⟩) ht hγ,
    P.gluingChartTangentForm_seam, gluingComplexCollarTangentForm_apply,
    gluingCollarTangentForm_self]

#print axioms gluedTangentTrivialization_eq_mfderiv
#print axioms gluedCurve_velocity_in_chart
#print axioms gluedCurve_speed_sq_in_chart
#print axioms gluedCurve_speed_in_chart
#print axioms gluedCurve_chart_contDiffOn
#print axioms gluedCurve_mdifferentiableAt_Ioo
#print axioms gluedCurve_speed_sq_interior
#print axioms gluedCurve_speed_sq_seam

end SystolicGrowth.ExerciseGluingPreparation
