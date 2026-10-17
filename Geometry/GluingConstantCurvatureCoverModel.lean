module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedCoverCurvature
public import Geometry.ConstantCurvatureHalfPlaneModel

@[expose] public section

/-!
# The actual half-plane model of a constant-curvature glued metric

Any genuine smooth constant-curvature `-1` metric on the compact glued
carrier gives a complete metric on its actual based-path universal cover.
The actual sheet charts transfer the full intrinsic curvature tensor, and
the genuine normal-coordinate theorem constructs the smooth half-plane
identification preserving the covering tensor. No model identification,
cover completeness, or cover curvature is supplied as a hypothesis.
-/

open Bundle Manifold Riemannian Set Filter UpperHalfPlane
open scoped Manifold Topology ContDiff UpperHalfPlane

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
  (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The actual pullback tensor of an arbitrary genuine smooth base metric. -/
abbrev gluedSmoothUniversalCoverRiemannianMetric :
    RiemannianMetric (modelWithCornersSelf ℝ ℂ) (P.basedTopologicalUniversalCover x) :=
  (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0

private theorem smoothCoveringMetric_eq_pullback :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
        P.basedTopologicalUniversalCover x → Type) :=
      ⟨(P.gluedSmoothUniversalCoverRiemannianMetric x g0).toRiemannianMetric⟩
    P.gluedSmoothUniversalCoverRiemannianMetric x g0 =
      RiemannianMetric.pullbackOfSmoothImmersion g0 (P.gluedUniversalCoverProjection x)
        (dcSmoothImmersion_of_isLocalDiffeomorph
          (P.gluedUniversalCoverProjection_isLocalDiffeomorph x)) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) :=
    ⟨(P.gluedSmoothUniversalCoverRiemannianMetric x g0).toRiemannianMetric⟩
  apply LeeLib.Ch02.RiemannianMetric.ext_inner
  intro q
  ext u v
  rfl

/-- **Math.** Actual lifted tangent coordinates preserve the whole base
metric tensor, because the genuine sheet projection has identity derivative. -/
theorem gluedSmoothUniversalCover_metricInner_eq
    (q : P.basedTopologicalUniversalCover x) (u v : ℂ) :
    (P.gluedSmoothUniversalCoverRiemannianMetric x g0).metricInner q u v =
      g0.metricInner (P.gluedUniversalCoverProjection x q) u v := by
  change g0.inner (P.gluedUniversalCoverProjection x q)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x) q u)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x) q v) = _
  rw [P.gluedUniversalCoverProjection_mfderiv_eq_id]
  rfl

omit g0 in
private theorem modelCover_mapReading_eventuallyEq_id
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    mapReading (I := modelWithCornersSelf ℝ ℂ) (I' := modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α) =ᶠ[𝓝 y] id :=
  Filter.eventuallyEq_of_mem ((chartAt ℂ α).open_target.mem_nhds hy)
    (P.gluedUniversalCover_projection_writtenInExtChartAt_eqOn x α)

omit g0 in
private theorem modelCover_mapReading_fderiv_eq_id
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    fderiv ℝ (mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α)) y = ContinuousLinearMap.id ℝ ℂ := by
  rw [(P.modelCover_mapReading_eventuallyEq_id x α hy).fderiv_eq]
  exact fderiv_id

omit g0 in
private theorem modelCover_mapReading_hessian_eq_zero
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    fderiv ℝ (fderiv ℝ (mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α))) y = 0 := by
  have hnear : fderiv ℝ (mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α)) =ᶠ[𝓝 y]
        fun _ : ℂ => ContinuousLinearMap.id ℝ ℂ := by
    filter_upwards [(chartAt ℂ α).open_target.mem_nhds hy] with z hz
    exact P.modelCover_mapReading_fderiv_eq_id x α hz
  rw [hnear.fderiv_eq]
  exact fderiv_const_apply _

private theorem smoothCoveringMetric_chartChristoffelBilin_eq
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    Jacobi.chartChristoffelBilin (P.gluedSmoothUniversalCoverRiemannianMetric x g0) α y =
      Jacobi.chartChristoffelBilin g0 (P.gluedUniversalCoverProjection x α) y := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) :=
    ⟨(P.gluedSmoothUniversalCoverRiemannianMetric x g0).toRiemannianMetric⟩
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let q := (chartAt ℂ α).symm y
  have hq : q ∈ (chartAt ℂ α).source := (chartAt ℂ α).map_target hy
  have hbase : P.gluedUniversalCoverProjection x q ∈
      (chartAt ℂ (P.gluedUniversalCoverProjection x α)).source := by
    rw [P.gluedUniversalCover_chartAt_symm_projection x α hy]
    exact (chartAt ℂ (P.gluedUniversalCoverProjection x α)).map_target hy.1
  have hcoord : extChartAt I α q = y := (chartAt ℂ α).right_inv hy
  have hbasecoord : extChartAt I (P.gluedUniversalCoverProjection x α)
      (P.gluedUniversalCoverProjection x q) = y := by
    change (chartAt ℂ (P.gluedUniversalCoverProjection x α))
      (P.gluedUniversalCoverProjection x q) = y
    rw [← P.gluedUniversalCover_chartAt_apply x α q]
    exact (chartAt ℂ α).right_inv hy
  ext u v
  rw [Jacobi.chartChristoffelBilin_apply, Jacobi.chartChristoffelBilin_apply]
  have h := chartChristoffelContraction_mapReading
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x) g0 hq hbase u v
  rw [← P.smoothCoveringMetric_eq_pullback x g0, hcoord, hbasecoord,
    P.modelCover_mapReading_fderiv_eq_id x α hy,
    P.modelCover_mapReading_hessian_eq_zero x α hy] at h
  simpa only [ContinuousLinearMap.id_apply, zero_apply, add_zero] using h

private theorem smoothCoveringMetric_chartCurvature_eq
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) (u v w : ℂ) :
    Jacobi.chartCurvature (P.gluedSmoothUniversalCoverRiemannianMetric x g0) α y u v w =
      Jacobi.chartCurvature g0 (P.gluedUniversalCoverProjection x α) y u v w := by
  have hnear : Jacobi.chartChristoffelBilin
      (P.gluedSmoothUniversalCoverRiemannianMetric x g0) α =ᶠ[𝓝 y]
        Jacobi.chartChristoffelBilin g0 (P.gluedUniversalCoverProjection x α) := by
    filter_upwards [(chartAt ℂ α).open_target.mem_nhds hy] with z hz
    exact P.smoothCoveringMetric_chartChristoffelBilin_eq x g0 α hz
  simp only [Jacobi.chartCurvature_def, Jacobi.christoffelCurvature]
  rw [hnear.fderiv_eq, P.smoothCoveringMetric_chartChristoffelBilin_eq x g0 α hy]

private theorem model_chartFrame_self
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M] (q : M) (u : ℂ) :
    (∑ a : Fin (Module.finrank ℝ ℂ), Geodesic.chartCoord (E := ℂ) a u •
      Tensor.chartBasisVecFiber (I := modelWithCornersSelf ℝ ℂ) q a q) = u := by
  have h := tangent_eq_sum_chartCoord_mfderiv
    (I' := modelWithCornersSelf ℝ ℂ) (mem_chart_source ℂ q) u
  rw [mfderiv_extChartAt_self] at h
  change u = ∑ a : Fin (Module.finrank ℝ ℂ), Geodesic.chartCoord (E := ℂ) a u •
    Tensor.chartBasisVecFiber (I := modelWithCornersSelf ℝ ℂ) q a q at h
  exact h.symm

/-- **Math.** The actual Levi-Civita curvature tensor of any smooth base
metric pulls back to the same intrinsic tensor on the original smooth cover. -/
theorem gluedSmoothUniversalCover_curvatureFormAt_eq
    (q : P.basedTopologicalUniversalCover x) (u v w z : ℂ) :
    (P.gluedSmoothUniversalCoverRiemannianMetric x g0).leviCivitaConnection.curvatureFormAt
        (P.gluedSmoothUniversalCoverRiemannianMetric x g0) q u v w z =
      g0.leviCivitaConnection.curvatureFormAt g0
        (P.gluedUniversalCoverProjection x q) u v w z := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let gc := P.gluedSmoothUniversalCoverRiemannianMetric x g0
  let b := P.gluedUniversalCoverProjection x q
  let y := extChartAt I q q
  have hy : y ∈ (chartAt ℂ q).target := (chartAt ℂ q).map_source (mem_chart_source ℂ q)
  have hcoord : y = extChartAt I b b := P.gluedUniversalCover_chartAt_apply x q q
  have hcover := Jacobi.curvatureFormAt_chartFrame gc (mem_chart_source ℂ q) u v w z
  have hbase := Jacobi.curvatureFormAt_chartFrame g0 (mem_chart_source ℂ b) u v w z
  simp only [model_chartFrame_self] at hcover hbase
  have hcurv := P.smoothCoveringMetric_chartCurvature_eq x g0 q hy u v w
  change Jacobi.chartCurvature gc q y u v w = Jacobi.chartCurvature g0 b y u v w at hcurv
  have hpairCover := chartMetricInner_extChartAt_eq_metricInner gc q
    (mem_chart_source ℂ q) (Jacobi.chartCurvature g0 b y u v w) z
  rw [trivializationAt_symm_self, trivializationAt_symm_self,
    P.gluedSmoothUniversalCover_metricInner_eq x g0 q] at hpairCover
  have hpairBase := chartMetricInner_extChartAt_eq_metricInner g0 b
    (mem_chart_source ℂ b) (Jacobi.chartCurvature g0 b y u v w) z
  rw [trivializationAt_symm_self, trivializationAt_symm_self] at hpairBase
  change gc.leviCivitaConnection.curvatureFormAt gc q u v w z = _
  rw [hcover, hcurv, hpairCover, ← hpairBase, hcoord]
  exact hbase.symm

/-- **Math.** The canonical intrinsic metric of the actual arbitrary smooth covering tensor. -/
@[instance_reducible]
def gluedSmoothUniversalCoverMetricSpace : MetricSpace (P.basedTopologicalUniversalCover x) :=
  LeeLib.Ch02.RiemannianMetric.toMetricSpace (P.gluedSmoothUniversalCoverRiemannianMetric x g0)

theorem gluedSmoothUniversalCoverMetricSpace_isRiemannianDist :
    letI := P.gluedSmoothUniversalCoverMetricSpace x g0
    (P.gluedSmoothUniversalCoverRiemannianMetric x g0).IsRiemannianDist := by
  letI := P.gluedSmoothUniversalCoverMetricSpace x g0
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) :=
    ⟨(P.gluedSmoothUniversalCoverRiemannianMetric x g0).toRiemannianMetric⟩
  change IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) (P.basedTopologicalUniversalCover x)
  exact ⟨fun _ _ => rfl⟩

/-- **Math.** The actual compact base makes its own canonical metric
complete; genuine smooth covering completeness then gives cover completeness. -/
theorem gluedSmoothUniversalCoverMetricSpace_complete :
    letI := P.gluedSmoothUniversalCoverMetricSpace x g0
    CompleteSpace (P.basedTopologicalUniversalCover x) := by
  letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
  letI : CompleteSpace P.GluedCarrier := inferInstance
  letI : ConnectedSpace P.GluedCarrier :=
    { toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
      toNonempty := ⟨x⟩ }
  have hg0 : g0.IsRiemannianDist := by
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
        P.GluedCarrier → Type) := ⟨g0.toRiemannianMetric⟩
    change IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
    exact ⟨fun _ _ => rfl⟩
  exact smoothCoveringMetric_complete_of_complete_base
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x) g0 hg0

variable (hK : ∀ (a : P.GluedCarrier)
    (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
  g0.metricInner a u u * g0.metricInner a v v - (g0.metricInner a u v) ^ 2 =
    g0.metricInner a (g0.leviCivitaConnection.curvatureOperatorAt a u v v) u)

include hK in
/-- **Math.** Constant curvature of the genuine base tensor transfers to
the actual complete simply-connected smooth covering metric. -/
theorem gluedSmoothUniversalCover_curvatureOperatorAt_eq
    (q : P.basedTopologicalUniversalCover x)
    (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) q) :
    let gc := P.gluedSmoothUniversalCoverRiemannianMetric x g0
    gc.metricInner q u u * gc.metricInner q v v - gc.metricInner q u v * gc.metricInner q u v =
      gc.metricInner q (gc.leviCivitaConnection.curvatureOperatorAt q u v v) u := by
  dsimp only
  change _ = (P.gluedSmoothUniversalCoverRiemannianMetric x g0).leviCivitaConnection.curvatureFormAt
    (P.gluedSmoothUniversalCoverRiemannianMetric x g0) q u v v u
  rw [P.gluedSmoothUniversalCover_curvatureFormAt_eq x g0 q,
    P.gluedSmoothUniversalCover_metricInner_eq x g0 q u u,
    P.gluedSmoothUniversalCover_metricInner_eq x g0 q v v,
    P.gluedSmoothUniversalCover_metricInner_eq x g0 q u v]
  rw [Jacobi.curvatureFormAt_eq_metricInner]
  simpa only [pow_two] using hK (P.gluedUniversalCoverProjection x q) u v

/-- **Math.** The actual same-map smooth Poincaré-plane identification,
constructed from constant curvature of the base without further cover hypotheses. -/
def gluedConstantCurvatureHalfPlaneDiffeomorph :
    P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ := by
  letI := P.gluedSmoothUniversalCoverMetricSpace x g0
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedSmoothUniversalCoverMetricSpace_complete x g0
  exact constantCurvatureHalfPlaneDiffeomorph
    (P.gluedSmoothUniversalCoverRiemannianMetric x g0)
    (P.gluedSmoothUniversalCoverMetricSpace_isRiemannianDist x g0)
    (TauCeti.UniversalCover.basepointLift x)
    (P.gluedSmoothUniversalCover_curvatureOperatorAt_eq x g0 hK)

/-- **Math.** The constructed diffeomorphism preserves the full actual
covering tensor, not merely a separately chosen distance or abstract model. -/
theorem gluedConstantCurvatureHalfPlaneDiffeomorph_isIsometry :
    LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric (P.gluedConstantCurvatureHalfPlaneDiffeomorph x g0 hK) := by
  letI := P.gluedSmoothUniversalCoverMetricSpace x g0
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedSmoothUniversalCoverMetricSpace_complete x g0
  exact constantCurvatureHalfPlaneDiffeomorph_isIsometry
    (P.gluedSmoothUniversalCoverRiemannianMetric x g0)
    (P.gluedSmoothUniversalCoverMetricSpace_isRiemannianDist x g0)
    (TauCeti.UniversalCover.basepointLift x)
    (P.gluedSmoothUniversalCover_curvatureOperatorAt_eq x g0 hK)

#print axioms gluedSmoothUniversalCover_curvatureFormAt_eq
#print axioms gluedSmoothUniversalCoverMetricSpace_complete
#print axioms gluedSmoothUniversalCover_curvatureOperatorAt_eq
#print axioms gluedConstantCurvatureHalfPlaneDiffeomorph
#print axioms gluedConstantCurvatureHalfPlaneDiffeomorph_isIsometry

end SystolicGrowth.ExerciseGluingPreparation
