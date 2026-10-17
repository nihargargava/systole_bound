module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingHalfPlaneUnitProjection
public import Geometry.SpinCoverPullback
public import Geometry.LinearCircleTurnHomotopy
public import Geometry.HalfPlaneSpinCoverClassification
public import Geometry.GluingTangentCircleFiberHomeomorph
public import Geometry.GluingHalfPlaneMetricFiberHomeomorph

@[expose] public section

/-!
# Actual odd monodromy of the geometric half-plane spin pullback

The constructed clutched spin half-turn and its reverse both end at the
literal antipode. Genuine fiber homeomorphisms compare the differential's
physical half-plane turn with this clutched turn up to based homotopy.
Covering homotopy lifting transfers the actual endpoint, not a supplied
oddness or generator-compatibility hypothesis.
-/

open Set Bundle Manifold Riemannian UpperHalfPlane
open scoped Manifold ContDiff Topology UpperHalfPlane unitInterval

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera X)
  (m : ContinuousRiemannianMetric ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))

/-- **Math.** The reverse of the real half-turn starting at the antipode
starts at the original spin and ends at that same literal antipode. -/
def reverseSpinFiberTurn (q : P.GluedSpinCarrier) : C(I, P.GluedSpinCarrier) :=
  (P.spinFiberTurn (P.gluedSpinAntipode q) : C(I, P.GluedSpinCarrier)).comp
    ⟨unitInterval.symm, unitInterval.continuous_symm⟩

@[simp] theorem reverseSpinFiberTurn_zero (q : P.GluedSpinCarrier) :
    P.reverseSpinFiberTurn q 0 = q := by
  change P.spinFiberTurn (P.gluedSpinAntipode q) (unitInterval.symm 0) = q
  rw [unitInterval.symm_zero, (P.spinFiberTurn (P.gluedSpinAntipode q)).target,
    P.gluedSpinAntipode_involutive]

@[simp] theorem reverseSpinFiberTurn_one (q : P.GluedSpinCarrier) :
    P.reverseSpinFiberTurn q 1 = P.gluedSpinAntipode q := by
  change P.spinFiberTurn (P.gluedSpinAntipode q) (unitInterval.symm 1) = _
  rw [unitInterval.symm_one, (P.spinFiberTurn (P.gluedSpinAntipode q)).source]

/-- **Math.** Reversal does not lose the antipodal monodromy of the actual
metric spin covering; the explicit reverse half-turn supplies its lift. -/
theorem liftPath_gluedMetricUnitFiberTurn_symm (q : P.GluedSpinCarrier) :
    (P.gluedMetricUnitSpinSquare_isCoveringMap m).liftPath
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).symm q
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).symm.source =
        P.reverseSpinFiberTurn q := by
  symm
  apply ((P.gluedMetricUnitSpinSquare_isCoveringMap m).eq_liftPath_iff' _).mpr
  refine ⟨?_, P.reverseSpinFiberTurn_zero q⟩
  funext t
  change P.gluedMetricUnitSpinSquare m
    (P.spinFiberTurn (P.gluedSpinAntipode q) (unitInterval.symm t)) =
      P.gluedTangentMetricUnitHomeomorph m
        (P.tangentFiberTurn (P.gluedSpinSquare q) (unitInterval.symm t))
  rw [gluedMetricUnitSpinSquare, Function.comp_apply, P.gluedSpinSquare_spinFiberTurn,
    P.gluedSpinSquare_gluedSpinAntipode]

theorem liftPath_gluedMetricUnitFiberTurn_symm_one (q : P.GluedSpinCarrier) :
    (P.gluedMetricUnitSpinSquare_isCoveringMap m).liftPath
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).symm q
      (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare q)).symm.source 1 =
        P.gluedSpinAntipode q := by
  rw [P.liftPath_gluedMetricUnitFiberTurn_symm, P.reverseSpinFiberTurn_one]

variable {Y : Type*} [TopologicalSpace Y]
  (f : Y → P.MetricUnitTangentCarrier m) (hf : Continuous f)

/-- **Math.** The second coordinate of the real pulled-back path lift is
exactly the real original covering lift of the composed base path. -/
theorem metricSpinPullback_liftPath_lift
    {y₀ y₁ : Y} (γ : Path y₀ y₁) (e : P.MetricSpinPullback m f)
    (he : P.metricSpinPullbackProjection m f e = y₀) :
    (⟨P.metricSpinPullbackLift m f, continuous_coveringPullbackLift _ _⟩ :
        C(P.MetricSpinPullback m f, P.GluedSpinCarrier)).comp
      ((P.metricSpinPullbackProjection_isCoveringMap m f hf).liftPath γ e
        (γ.source.trans he.symm)) =
    (P.gluedMetricUnitSpinSquare_isCoveringMap m).liftPath
      (γ.map hf) e.val.2
        ((γ.map hf).source.trans ((congrArg f he.symm).trans e.property)) := by
  apply ((P.gluedMetricUnitSpinSquare_isCoveringMap m).eq_liftPath_iff' _).mpr
  refine ⟨?_, ?_⟩
  · funext t
    let Γ := (P.metricSpinPullbackProjection_isCoveringMap m f hf).liftPath γ e
      (γ.source.trans he.symm)
    have hΓ := congrFun
      ((P.metricSpinPullbackProjection_isCoveringMap m f hf).liftPath_lifts γ e
        (γ.source.trans he.symm)) t
    exact (Γ t).property.symm.trans (congrArg f hΓ)
  · exact congrArg (P.metricSpinPullbackLift m f)
      ((P.metricSpinPullbackProjection_isCoveringMap m f hf).liftPath_zero γ e
        (γ.source.trans he.symm))

/-- **Math.** The actual homotopy comparison transfers the constructed
antipodal endpoint to the real pullback. The geometric consumer below
constructs this comparison from genuine fiber homeomorphisms. -/
theorem metricSpinPullback_liftPath_one_eq_antipode_of_turn_homotopy
    {y : Y} (γ : Path y y) (e : P.MetricSpinPullback m f)
    (he : P.metricSpinPullbackProjection m f e = y)
    (hcompare :
      (γ.map hf : C(I, P.MetricUnitTangentCarrier m)).HomotopicRel
          (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare e.val.2)) {0, 1} ∨
        (γ.map hf : C(I, P.MetricUnitTangentCarrier m)).HomotopicRel
          (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare e.val.2)).symm {0, 1}) :
    (P.metricSpinPullbackProjection_isCoveringMap m f hf).liftPath γ e
      (γ.source.trans he.symm) 1 = P.metricSpinPullbackAntipode m f e := by
  let hp := P.gluedMetricUnitSpinSquare_isCoveringMap m
  let hstart := (γ.map hf).source.trans ((congrArg f he.symm).trans e.property)
  have hend : hp.liftPath (γ.map hf) e.val.2 hstart 1 =
      P.gluedSpinAntipode e.val.2 := by
    rcases hcompare with h | h
    · rw [hp.liftPath_apply_one_eq_of_homotopicRel h e.val.2 hstart
        (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare e.val.2)).source,
        P.liftPath_gluedMetricUnitFiberTurn]
      exact (P.spinFiberTurn e.val.2).target
    · rw [hp.liftPath_apply_one_eq_of_homotopicRel h e.val.2 hstart
        (P.gluedMetricUnitFiberTurn m (P.gluedSpinSquare e.val.2)).symm.source]
      exact P.liftPath_gluedMetricUnitFiberTurn_symm_one m e.val.2
  apply Subtype.ext
  apply Prod.ext
  · have h := congrFun
      ((P.metricSpinPullbackProjection_isCoveringMap m f hf).liftPath_lifts γ e
        (γ.source.trans he.symm)) 1
    exact h.trans (γ.target.trans he.symm)
  · have h := congrArg (fun Γ : C(I, P.GluedSpinCarrier) => Γ 1)
      (P.metricSpinPullback_liftPath_lift m f hf γ e he)
    exact h.trans hend

variable (x : P.GluedCarrier)
  (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
  (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
    modelWithCornersSelf ℝ ℂ⟯ ℍ)
  (hΦ : LeeLib.Ch02.IsIsometry
    ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    upperHalfPlanePoincareMetric Φ)

omit m f hf in
/-- **Math.** The physical projected standard turn is based homotopic,
relative to both endpoints, to the constructed clutched metric turn or its
reverse. Both fiber parametrizations are constructed genuine homeomorphisms. -/
theorem gluedHalfPlaneStandardFrameOneTurn_metric_homotopic
    (e : P.MetricSpinPullback g0.toContinuousRiemannianMetric
      (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ))
    (he : P.metricSpinPullbackProjection g0.toContinuousRiemannianMetric
      (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ) e = halfPlaneStandardTangentFrame) :
    (halfPlaneStandardFrameOneTurn.map
      (P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ) :
        C(I, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric)).HomotopicRel
          (P.gluedMetricUnitFiberTurn g0.toContinuousRiemannianMetric
            (P.gluedSpinSquare e.val.2)) {0, 1} ∨
      (halfPlaneStandardFrameOneTurn.map
        (P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ) :
          C(I, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric)).HomotopicRel
            (P.gluedMetricUnitFiberTurn g0.toContinuousRiemannianMetric
              (P.gluedSpinSquare e.val.2)).symm {0, 1} := by
  let q := P.gluedSpinSquare e.val.2
  let F := P.gluedHalfPlaneUnitProjection x g0 Φ hΦ
  let M := P.gluedTangentMetricUnitHomeomorph g0.toContinuousRiemannianMetric
  have hq : M q = F halfPlaneStandardTangentFrame := by
    change P.gluedMetricUnitSpinSquare g0.toContinuousRiemannianMetric e.val.2 = _
    exact e.property.symm.trans (congrArg F he)
  have hb : P.gluedTangentBase q = P.gluedHalfPlaneSmoothProjection x Φ UpperHalfPlane.I := by
    calc
      P.gluedTangentBase q = (M q).val.proj :=
        (P.gluedTangentMetricUnitHomeomorph_proj g0.toContinuousRiemannianMetric q).symm
      _ = (F halfPlaneStandardTangentFrame).val.proj := congrArg (fun v => v.val.proj) hq
      _ = _ := rfl
  let H₀ := P.gluedHalfPlaneMetricFiberHomeomorph x g0 Φ hΦ UpperHalfPlane.I
  let H₁ : Circle ≃ₜ P.HalfPlaneProjectedMetricUnitFiber x g0 Φ UpperHalfPlane.I :=
    (P.gluedMetricUnitFiberCircleHomeomorph g0.toContinuousRiemannianMetric q).trans
      (Homeomorph.setCongr (by ext v; simp only [hb]))
  let E := H₀.trans H₁.symm
  let U : C(Circle, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric) :=
    ⟨fun a => (H₁ a).val, continuous_subtype_val.comp H₁.continuous⟩
  have hU (a : Circle) : U a = M (a • q) := rfl
  have hEU (a : Circle) : U (E a) = F ⟨UpperHalfPlane.I, a⟩ := by
    change (H₁ (H₁.symm (H₀ a))).val = _
    rw [H₁.apply_symm_apply]
    exact P.gluedHalfPlaneMetricFiberHomeomorph_apply x g0 Φ hΦ UpperHalfPlane.I a
  have hE : E 1 = 1 := by
    apply H₁.injective
    apply Subtype.ext
    change U (E 1) = U 1
    rw [hEU, hU, one_smul]
    exact hq.symm
  have hleft :
      U.comp ((circleOneTurnLoop 1).map E.continuous : C(I, Circle)) =
        (halfPlaneStandardFrameOneTurn.map
          (P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ) :
            C(I, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric)) := by
    apply ContinuousMap.ext
    intro t
    change U (E (circleOneTurnLoop 1 t)) = F (halfPlaneStandardFrameOneTurn t)
    rw [hEU, circleOneTurnLoop_apply]
    congr 1
    apply HalfPlaneTangentFrame.ext
    · rfl
    · change Circle.exp ((1 : ℂ).arg + 2 * Real.pi * (t : ℝ)) =
        Circle.exp (2 * (Real.pi * (t : ℝ)))
      rw [Complex.arg_one, zero_add, mul_assoc]
  have hright :
      U.comp (circleOneTurnLoop (E 1) : C(I, Circle)) =
        (P.gluedMetricUnitFiberTurn g0.toContinuousRiemannianMetric q :
          C(I, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric)) := by
    apply ContinuousMap.ext
    intro t
    change U (circleOneTurnLoop (E 1) t) = M (P.tangentFiberTurn q t)
    rw [hU, circleOneTurnLoop_apply, hE]
    congr 1
    change Circle.exp ((1 : ℂ).arg + 2 * Real.pi * (t : ℝ)) • q =
      Circle.exp (2 * Real.pi * (t : ℝ)) • q
    rw [Complex.arg_one, zero_add]
  have hrightSymm :
      U.comp ((circleOneTurnLoop (E 1)).symm : C(I, Circle)) =
        ((P.gluedMetricUnitFiberTurn g0.toContinuousRiemannianMetric q).symm :
          C(I, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric)) := by
    apply ContinuousMap.ext
    intro t
    exact congrArg (fun Γ : C(I, P.MetricUnitTangentCarrier g0.toContinuousRiemannianMetric) =>
      Γ (unitInterval.symm t)) hright
  rcases circleHomeomorph_oneTurn_homotopic E 1 with h | h
  · left
    have H := h.map U
    change (U.comp ((circleOneTurnLoop 1).map E.continuous : C(I, Circle))).HomotopicRel
      (U.comp (circleOneTurnLoop (E 1) : C(I, Circle))) {0, 1} at H
    rw [hleft, hright] at H
    exact H
  · right
    have H := h.map U
    change (U.comp ((circleOneTurnLoop 1).map E.continuous : C(I, Circle))).HomotopicRel
      (U.comp ((circleOneTurnLoop (E 1)).symm : C(I, Circle))) {0, 1} at H
    rw [hleft, hrightSymm] at H
    exact H

omit m f hf in
/-- **Math.** Odd monodromy of the genuine geometric half-plane pullback
is proved from the actual constructed spin half-turn, not supplied as data. -/
theorem liftPath_gluedHalfPlaneStandardFrameOneTurn
    (e : P.MetricSpinPullback g0.toContinuousRiemannianMetric
      (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ))
    (he : P.metricSpinPullbackProjection g0.toContinuousRiemannianMetric
      (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ) e = halfPlaneStandardTangentFrame) :
    (P.metricSpinPullbackProjection_isCoveringMap g0.toContinuousRiemannianMetric
      (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ)
      (P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ)).liftPath
      halfPlaneStandardFrameOneTurn e (halfPlaneStandardFrameOneTurn.source.trans he.symm) 1 =
        P.metricSpinPullbackAntipode g0.toContinuousRiemannianMetric
          (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ) e :=
  P.metricSpinPullback_liftPath_one_eq_antipode_of_turn_homotopy
    g0.toContinuousRiemannianMetric (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ)
    (P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ)
    halfPlaneStandardFrameOneTurn e he
    (P.gluedHalfPlaneStandardFrameOneTurn_metric_homotopic x g0 Φ hΦ e he)

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.liftPath_gluedMetricUnitFiberTurn_symm_one
#print axioms ExerciseGluingPreparation.metricSpinPullback_liftPath_lift
#print axioms ExerciseGluingPreparation.metricSpinPullback_liftPath_one_eq_antipode_of_turn_homotopy
#print axioms ExerciseGluingPreparation.gluedHalfPlaneStandardFrameOneTurn_metric_homotopic
#print axioms ExerciseGluingPreparation.liftPath_gluedHalfPlaneStandardFrameOneTurn

end

end SystolicGrowth
