module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedUniversalCover
public import Geometry.GluingUniversalCoverProper
public import Geometry.GluingIntrinsicCurvature
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Connection.PullbackChristoffelLaw

@[expose] public section

/-!
# Intrinsic curvature on the concrete smooth glued cover

The selected lifted charts read the genuine covering projection as the
identity. The pullback Christoffel transformation law therefore identifies
their connections and curvature with those of the actual patched metric.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

local instance coverRiemannianBundle
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) :=
  ⟨(P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x).toRiemannianMetric⟩

/-- **Math.** The original covering topology is sigma compact, as already
proved by properness of its native path metric. No replacement topology or
new countability hypothesis is needed to construct its Levi-Civita connection. -/
instance gluedCurvatureBoundedUniversalCoverSigmaCompactSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    SigmaCompactSpace (P.basedTopologicalUniversalCover x) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  letI := P.gluedUniversalCoverPathMetric_properSpace x
  infer_instance

/-- **Math.** The genuine Lee covering tensor is the same smooth pullback
tensor used by the DoCarmo Christoffel transformation theorem. -/
theorem gluedCurvatureBoundedUniversalCoverRiemannianMetric_eq_pullback
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x =
      Riemannian.RiemannianMetric.pullbackOfSmoothImmersion
        P.gluedCurvatureBoundedSmoothRiemannianMetric (P.gluedUniversalCoverProjection x)
        (Riemannian.dcSmoothImmersion_of_isLocalDiffeomorph
          (P.gluedUniversalCoverProjection_isLocalDiffeomorph x)) := by
  have hi : (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x).inner =
      (Riemannian.RiemannianMetric.pullbackOfSmoothImmersion
        P.gluedCurvatureBoundedSmoothRiemannianMetric (P.gluedUniversalCoverProjection x)
        (Riemannian.dcSmoothImmersion_of_isLocalDiffeomorph
          (P.gluedUniversalCoverProjection_isLocalDiffeomorph x))).inner := by
    funext q
    ext u v
    rfl
  generalize P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x = a at hi ⊢
  generalize Riemannian.RiemannianMetric.pullbackOfSmoothImmersion
    P.gluedCurvatureBoundedSmoothRiemannianMetric (P.gluedUniversalCoverProjection x)
    (Riemannian.dcSmoothImmersion_of_isLocalDiffeomorph
      (P.gluedUniversalCoverProjection_isLocalDiffeomorph x)) = b at hi ⊢
  cases a
  cases b
  cases hi
  rfl

/-- **Math.** The actual pullback metric pairs selected tangent coordinates
exactly as the actual base tensor does at the projected point. -/
theorem gluedCurvatureBoundedUniversalCover_metricInner_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (u v : ℂ) :
    Riemannian.RiemannianMetric.metricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q u v =
      Riemannian.RiemannianMetric.metricInner
        P.gluedCurvatureBoundedSmoothRiemannianMetric
        (P.gluedUniversalCoverProjection x q) u v := by
  change P.gluedCurvatureBoundedSmoothRiemannianMetric.inner
      (P.gluedUniversalCoverProjection x q)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x) q u)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x) q v) = _
  rw [P.gluedUniversalCoverProjection_mfderiv_eq_id]
  rfl

private theorem cover_mapReading_eventuallyEq_id
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    Riemannian.mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α) =ᶠ[𝓝 y] id :=
  Filter.eventuallyEq_of_mem ((chartAt ℂ α).open_target.mem_nhds hy)
    (P.gluedUniversalCover_projection_writtenInExtChartAt_eqOn x α)

private theorem cover_mapReading_fderiv_eq_id
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    fderiv ℝ (Riemannian.mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α)) y = ContinuousLinearMap.id ℝ ℂ := by
  rw [(P.cover_mapReading_eventuallyEq_id x α hy).fderiv_eq]
  exact fderiv_id

private theorem cover_mapReading_hessian_eq_zero
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    fderiv ℝ (fderiv ℝ (Riemannian.mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α))) y = 0 := by
  have hnear : fderiv ℝ (Riemannian.mapReading (I := modelWithCornersSelf ℝ ℂ)
      (I' := modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x) α
      (P.gluedUniversalCoverProjection x α)) =ᶠ[𝓝 y]
        fun _ : ℂ => ContinuousLinearMap.id ℝ ℂ := by
    filter_upwards [(chartAt ℂ α).open_target.mem_nhds hy] with z hz
    exact P.cover_mapReading_fderiv_eq_id x α hz
  rw [hnear.fderiv_eq]
  exact fderiv_const_apply _

/-- **Math.** Christoffel bilinear maps on an actual lifted chart agree
with those on its actual base chart: the projection's Hessian term vanishes. -/
theorem gluedCurvatureBoundedUniversalCover_chartChristoffelBilin_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) :
    Riemannian.Jacobi.chartChristoffelBilin
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) α y =
      Riemannian.Jacobi.chartChristoffelBilin P.gluedCurvatureBoundedSmoothRiemannianMetric
        (P.gluedUniversalCoverProjection x α) y := by
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
  rw [Riemannian.Jacobi.chartChristoffelBilin_apply,
    Riemannian.Jacobi.chartChristoffelBilin_apply]
  have h := Riemannian.chartChristoffelContraction_mapReading
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x)
    P.gluedCurvatureBoundedSmoothRiemannianMetric hq hbase u v
  rw [← P.gluedCurvatureBoundedUniversalCoverRiemannianMetric_eq_pullback x,
    hcoord, hbasecoord, P.cover_mapReading_fderiv_eq_id x α hy,
    P.cover_mapReading_hessian_eq_zero x α hy] at h
  simpa only [ContinuousLinearMap.id_apply, zero_apply, add_zero] using h

/-- **Math.** Differentiating the actual Christoffel equality on a genuine
lifted chart neighborhood identifies the complete chart curvature operators. -/
theorem gluedCurvatureBoundedUniversalCover_chartCurvature_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (α : P.basedTopologicalUniversalCover x) {y : ℂ}
    (hy : y ∈ (chartAt ℂ α).target) (u v w : ℂ) :
    Riemannian.Jacobi.chartCurvature
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) α y u v w =
      Riemannian.Jacobi.chartCurvature P.gluedCurvatureBoundedSmoothRiemannianMetric
        (P.gluedUniversalCoverProjection x α) y u v w := by
  have hnear : Riemannian.Jacobi.chartChristoffelBilin
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) α =ᶠ[𝓝 y]
        Riemannian.Jacobi.chartChristoffelBilin P.gluedCurvatureBoundedSmoothRiemannianMetric
          (P.gluedUniversalCoverProjection x α) := by
    filter_upwards [(chartAt ℂ α).open_target.mem_nhds hy] with z hz
    exact P.gluedCurvatureBoundedUniversalCover_chartChristoffelBilin_eq x α hz
  simp only [Riemannian.Jacobi.chartCurvature_def,
    Riemannian.Jacobi.christoffelCurvature]
  rw [hnear.fderiv_eq,
    P.gluedCurvatureBoundedUniversalCover_chartChristoffelBilin_eq x α hy]

private theorem chartFrame_self
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M] (q : M) (u : ℂ) :
    (∑ a : Fin (Module.finrank ℝ ℂ),
      Riemannian.Geodesic.chartCoord (E := ℂ) a u •
        Riemannian.Tensor.chartBasisVecFiber (I := modelWithCornersSelf ℝ ℂ) q a q) = u := by
  have h := Riemannian.tangent_eq_sum_chartCoord_mfderiv
    (I' := modelWithCornersSelf ℝ ℂ) (mem_chart_source ℂ q) u
  rw [mfderiv_extChartAt_self] at h
  change u = ∑ a : Fin (Module.finrank ℝ ℂ),
    Riemannian.Geodesic.chartCoord (E := ℂ) a u •
      Riemannian.Tensor.chartBasisVecFiber (I := modelWithCornersSelf ℝ ℂ) q a q at h
  exact h.symm

/-- **Math.** The intrinsic curvature form of the actual complete pullback
tensor equals the actual base curvature form in selected tangent coordinates.
Both sides are the real Levi-Civita tensors, not a chart-curvature premise. -/
theorem gluedCurvatureBoundedUniversalCover_curvatureFormAt_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (u v w z : ℂ) :
    (Riemannian.RiemannianMetric.leviCivitaConnection
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)).curvatureFormAt
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q u v w z =
      (Riemannian.RiemannianMetric.leviCivitaConnection
        P.gluedCurvatureBoundedSmoothRiemannianMetric).curvatureFormAt
      P.gluedCurvatureBoundedSmoothRiemannianMetric
      (P.gluedUniversalCoverProjection x q) u v w z := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let coverMetric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  let baseMetric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let b := P.gluedUniversalCoverProjection x q
  let y := (extChartAt I q) q
  have hy : y ∈ (chartAt ℂ q).target := (chartAt ℂ q).map_source (mem_chart_source ℂ q)
  have hcoord : y = (extChartAt I b) b := P.gluedUniversalCover_chartAt_apply x q q
  have hcover := Riemannian.Jacobi.curvatureFormAt_chartFrame coverMetric
    (mem_chart_source ℂ q) u v w z
  have hbase := Riemannian.Jacobi.curvatureFormAt_chartFrame baseMetric
    (mem_chart_source ℂ b) u v w z
  simp only [chartFrame_self] at hcover hbase
  have hcurv := P.gluedCurvatureBoundedUniversalCover_chartCurvature_eq x q hy u v w
  change Riemannian.Jacobi.chartCurvature coverMetric q y u v w =
    Riemannian.Jacobi.chartCurvature baseMetric b y u v w at hcurv
  have hpairCover := Riemannian.chartMetricInner_extChartAt_eq_metricInner coverMetric q
    (mem_chart_source ℂ q) (Riemannian.Jacobi.chartCurvature baseMetric b y u v w) z
  rw [Riemannian.trivializationAt_symm_self, Riemannian.trivializationAt_symm_self,
    P.gluedCurvatureBoundedUniversalCover_metricInner_eq x q] at hpairCover
  have hpairBase := Riemannian.chartMetricInner_extChartAt_eq_metricInner baseMetric b
    (mem_chart_source ℂ b) (Riemannian.Jacobi.chartCurvature baseMetric b y u v w) z
  rw [Riemannian.trivializationAt_symm_self, Riemannian.trivializationAt_symm_self] at hpairBase
  change (Riemannian.RiemannianMetric.leviCivitaConnection coverMetric).curvatureFormAt
      coverMetric q u v w z = _
  rw [hcover, hcurv, hpairCover, ← hpairBase, hcoord]
  exact hbase.symm

/-- **Math.** The actual complete covering metric inherits the full Gram
lower bound on its curvature operator from the verified patched base metric. -/
theorem gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_lower_bound
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
    ∀ u v : TangentSpace I q,
      Riemannian.RiemannianMetric.metricInner metric q u u *
          Riemannian.RiemannianMetric.metricInner metric q v v -
        Riemannian.RiemannianMetric.metricInner metric q u v *
          Riemannian.RiemannianMetric.metricInner metric q u v ≤
        Riemannian.RiemannianMetric.metricInner metric q
          ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
            q u v v) u := by
  dsimp only
  intro u v
  change _ ≤ (Riemannian.RiemannianMetric.leviCivitaConnection
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)).curvatureFormAt
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q u v v u
  rw [P.gluedCurvatureBoundedUniversalCover_curvatureFormAt_eq x q,
    P.gluedCurvatureBoundedUniversalCover_metricInner_eq x q u u,
    P.gluedCurvatureBoundedUniversalCover_metricInner_eq x q v v,
    P.gluedCurvatureBoundedUniversalCover_metricInner_eq x q u v]
  exact P.gluedCurvatureBounded_curvatureOperatorAt_lower_bound
    (P.gluedUniversalCoverProjection x q) u v

/-- **Math.** The genuine complete simply connected cover satisfies the
curvature-operator sign needed by the no-conjugate-point/Hadamard route. -/
theorem gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_pair_nonneg
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
    ∀ u v : TangentSpace I q,
      0 ≤ Riemannian.RiemannianMetric.metricInner metric q
        ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
          q u v v) u := by
  dsimp only
  intro u v
  change 0 ≤ (Riemannian.RiemannianMetric.leviCivitaConnection
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)).curvatureFormAt
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q u v v u
  rw [P.gluedCurvatureBoundedUniversalCover_curvatureFormAt_eq x q]
  exact P.gluedCurvatureBounded_curvatureOperatorAt_pair_nonneg
    (P.gluedUniversalCoverProjection x q) u v

/-- **Math.** Every nondegenerate tangent plane of the genuine complete
covering metric has sectional curvature at most `-1`. -/
theorem gluedCurvatureBoundedUniversalCover_sectionalCurvature_le_neg_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
    letI : Bundle.RiemannianBundle (fun q : P.basedTopologicalUniversalCover x => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    ∀ u v : TangentSpace I q, 0 < Riemannian.wedgeSq u v →
      Riemannian.sectionalCurvature
        ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureFormAt
          metric q) u v ≤ -1 := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  letI : Bundle.RiemannianBundle
      (fun q : P.basedTopologicalUniversalCover x => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection metric
  have hLC : connection.IsLeviCivita metric :=
    connection.isLeviCivita_of_koszulDual metric
      (fun A B Z q => Riemannian.RiemannianMetric.koszulDualSection_dual metric A B Z q)
  have hB := connection.isAlgCurvatureForm_curvatureFormAt metric hLC q
  dsimp only
  intro u v harea
  change connection.curvatureFormAt metric q u v u v / Riemannian.wedgeSq u v ≤ -1
  apply (div_le_iff₀ harea).2
  have hbound : Riemannian.wedgeSq u v ≤
      connection.curvatureFormAt metric q u v v u :=
    P.gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_lower_bound x q u v
  have hskew := hB.antisymm₃₄ u v u v
  linarith

#print axioms gluedCurvatureBoundedUniversalCoverRiemannianMetric_eq_pullback
#print axioms gluedCurvatureBoundedUniversalCover_metricInner_eq
#print axioms gluedCurvatureBoundedUniversalCover_chartChristoffelBilin_eq
#print axioms gluedCurvatureBoundedUniversalCover_chartCurvature_eq
#print axioms gluedCurvatureBoundedUniversalCover_curvatureFormAt_eq
#print axioms gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_lower_bound
#print axioms gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_pair_nonneg
#print axioms gluedCurvatureBoundedUniversalCover_sectionalCurvature_le_neg_one

end

end SystolicGrowth.ExerciseGluingPreparation
