module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedMetricSpace
public import Geometry.GluingUniversalCoverLocalCompactness
public import Geometry.GluingUniversalCoverPathMetric
public import Geometry.GluingUniversalCoverDeck
public import Geometry.SmoothCoveringMetric
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
-- The sheet-chart construction supplies the defining local-diffeomorphism witness.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

@[expose] public section

/-!
# Smooth pullback geometry on the concrete glued universal cover

The sheet charts of the actual endpoint projection pull back the glued
surface's smooth atlas. The pullback tensor and its complete intrinsic
metric are then constructed on this same based-path cover.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The smooth chart lifted through the genuine local sheet at a
point of the original based-path universal cover. -/
def gluedUniversalCoverSmoothChart
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    OpenPartialHomeomorph (P.basedTopologicalUniversalCover x) ℂ :=
  ((P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt q).symm.trans
    (chartAt ℂ (P.gluedUniversalCoverProjection x q))

/-- **Math.** The original cover topology carries the atlas obtained from
actual local sheets and the actual smooth base charts. -/
instance gluedUniversalCoverSmoothChartedSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ChartedSpace ℂ (P.basedTopologicalUniversalCover x) where
  atlas := Set.range (P.gluedUniversalCoverSmoothChart x)
  chartAt := P.gluedUniversalCoverSmoothChart x
  mem_chart_source q := by
    simp only [gluedUniversalCoverSmoothChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · exact (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.self_mem_localInverseAt_target
    · rw [(P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt_symm]
      exact mem_chart_source ℂ _
  chart_mem_atlas q := Set.mem_range_self q

/-- **Math.** The chosen smooth cover chart is exactly the projection's
chosen sheet followed by the selected smooth chart at the projected point. -/
theorem gluedUniversalCover_chartAt
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    chartAt ℂ q =
      ((P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt q).symm.trans
        (chartAt ℂ (P.gluedUniversalCoverProjection x q)) := rfl

/-- **Math.** Selected lifted coordinates are exactly selected base
coordinates of the original endpoint projection. -/
theorem gluedUniversalCover_chartAt_apply
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q z : P.basedTopologicalUniversalCover x) :
    (chartAt ℂ q) z = (chartAt ℂ (P.gluedUniversalCoverProjection x q))
      (P.gluedUniversalCoverProjection x z) := by
  rw [P.gluedUniversalCover_chartAt]
  simp only [OpenPartialHomeomorph.trans_apply,
    (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt_symm]

/-- **Math.** On the actual selected chart domain, projecting its inverse
recovers the actual selected inverse base chart. -/
theorem gluedUniversalCover_chartAt_symm_projection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) {z : ℂ}
    (hz : z ∈ (chartAt ℂ q).target) :
    P.gluedUniversalCoverProjection x ((chartAt ℂ q).symm z) =
      (chartAt ℂ (P.gluedUniversalCoverProjection x q)).symm z := by
  let h := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph
  have hs : (chartAt ℂ (P.gluedUniversalCoverProjection x q)).symm z ∈
      (h.localInverseAt q).source := hz.2
  change P.gluedUniversalCoverProjection x
    (h.localInverseAt q ((chartAt ℂ (P.gluedUniversalCoverProjection x q)).symm z)) = _
  exact h.apply_localInverseAt_of_mem hs

/-- **Math.** In the chosen lifted and base coordinates, the genuine
projection is literally the identity on the lifted chart target. -/
theorem gluedUniversalCover_projection_writtenInExtChartAt_eqOn
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    EqOn (writtenInExtChartAt (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ ℂ) q (P.gluedUniversalCoverProjection x)) id
      (chartAt ℂ q).target := by
  intro z hz
  change (chartAt ℂ (P.gluedUniversalCoverProjection x q))
    (P.gluedUniversalCoverProjection x ((chartAt ℂ q).symm z)) = z
  rw [P.gluedUniversalCover_chartAt_symm_projection x q hz]
  exact (chartAt ℂ (P.gluedUniversalCoverProjection x q)).right_inv hz.1

/-- **Math.** The original endpoint map has identity coordinate expression
on a genuine neighborhood of every selected lifted coordinate. -/
theorem gluedUniversalCover_projection_writtenInExtChartAt_eventuallyEq_id
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    writtenInExtChartAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      q (P.gluedUniversalCoverProjection x) =ᶠ[𝓝 ((chartAt ℂ q) q)] id :=
  Filter.eventuallyEq_of_mem
    ((chartAt ℂ q).open_target.mem_nhds
      ((chartAt ℂ q).map_source (mem_chart_source ℂ q)))
    (P.gluedUniversalCover_projection_writtenInExtChartAt_eqOn x q)

theorem gluedUniversalCoverSmoothChart_transition
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x) :
    let ea := P.gluedUniversalCoverSmoothChart x a
    let eb := P.gluedUniversalCoverSmoothChart x b
    let fa := chartAt ℂ (P.gluedUniversalCoverProjection x a)
    let fb := chartAt ℂ (P.gluedUniversalCoverProjection x b)
    (ea.symm.trans eb).source ⊆ (fa.symm.trans fb).source ∧
      EqOn (ea.symm.trans eb) (fa.symm.trans fb) (ea.symm.trans eb).source := by
  let h := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph
  let sa := h.localInverseAt a
  let sb := h.localInverseAt b
  dsimp only
  have hright {y : P.GluedCarrier} (hy : y ∈ sa.source) :
      P.gluedUniversalCoverProjection x (sa y) = y := h.apply_localInverseAt_of_mem hy
  constructor
  · intro y hy
    change y ∈ ((sa.symm.trans (chartAt ℂ (P.gluedUniversalCoverProjection x a))).symm.trans
      (sb.symm.trans (chartAt ℂ (P.gluedUniversalCoverProjection x b)))).source at hy
    rcases hy with ⟨hya, hyb⟩
    rcases hya with ⟨hyfa, hysa⟩
    rcases hyb with ⟨hysb, hyfb⟩
    change y ∈ (chartAt ℂ (P.gluedUniversalCoverProjection x a)).target ∧
      (chartAt ℂ (P.gluedUniversalCoverProjection x a)).symm y ∈
        (chartAt ℂ (P.gluedUniversalCoverProjection x b)).source
    refine ⟨hyfa, ?_⟩
    change sb.symm (sa ((chartAt ℂ (P.gluedUniversalCoverProjection x a)).symm y)) ∈
      (chartAt ℂ (P.gluedUniversalCoverProjection x b)).source at hyfb
    rw [h.localInverseAt_symm] at hyfb
    rw [hright hysa] at hyfb
    exact hyfb
  · intro y hy
    change y ∈ ((sa.symm.trans (chartAt ℂ (P.gluedUniversalCoverProjection x a))).symm.trans
      (sb.symm.trans (chartAt ℂ (P.gluedUniversalCoverProjection x b)))).source at hy
    have hysa := hy.1.2
    change (chartAt ℂ (P.gluedUniversalCoverProjection x b))
      (sb.symm (sa ((chartAt ℂ (P.gluedUniversalCoverProjection x a)).symm y))) =
        (chartAt ℂ (P.gluedUniversalCoverProjection x b))
          ((chartAt ℂ (P.gluedUniversalCoverProjection x a)).symm y)
    rw [h.localInverseAt_symm, hright hysa]

/-- **Math.** Transition maps in the actual lifted atlas restrict the
smooth base transition maps, so the concrete cover is a smooth manifold. -/
instance gluedUniversalCoverSmoothIsManifold
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    IsManifold (modelWithCornersSelf ℝ ℂ) ∞ (P.basedTopologicalUniversalCover x) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨a, rfl⟩ := he
  obtain ⟨b, rfl⟩ := he'
  let fa := chartAt ℂ (P.gluedUniversalCoverProjection x a)
  let fb := chartAt ℂ (P.gluedUniversalCoverProjection x b)
  have hbase := (contDiffGroupoid ∞ (modelWithCornersSelf ℝ ℂ)).compatible
    (chart_mem_atlas ℂ (P.gluedUniversalCoverProjection x a))
    (chart_mem_atlas ℂ (P.gluedUniversalCoverProjection x b))
  have hbaseDiff : ContDiffOn ℝ ∞ (fa.symm.trans fb) (fa.symm.trans fb).source := by
    have hh := (mem_groupoid_of_pregroupoid.mp hbase).1
    simpa only [contDiffPregroupoid, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, range_id, preimage_id_eq, inter_univ,
      Function.id_comp, Function.comp_id, id_eq] using hh
  obtain ⟨hsource, heq⟩ := P.gluedUniversalCoverSmoothChart_transition x a b
  have hdiff := (hbaseDiff.mono hsource).congr heq
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id_eq, inter_univ, Function.id_comp, Function.comp_id, id_eq] using hdiff

/-- **Math.** The concrete cover is Hausdorff in its original topology,
already realized by its verified native intrinsic metric. -/
instance gluedUniversalCoverSmoothT2Space
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    T2Space (P.basedTopologicalUniversalCover x) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  infer_instance

/-- **Math.** Each actual sheet of the endpoint projection is a local
diffeomorphism for the lifted smooth atlas. -/
theorem gluedUniversalCoverProjection_isLocalDiffeomorph
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    IsLocalDiffeomorph (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (P.gluedUniversalCoverProjection x) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  intro q
  let ea : PartialDiffeomorph I I (P.basedTopologicalUniversalCover x) ℂ ∞ :=
    { toPartialEquiv := (chartAt ℂ q).toPartialEquiv
      open_source := (chartAt ℂ q).open_source
      open_target := (chartAt ℂ q).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let fb : PartialDiffeomorph I I P.GluedCarrier ℂ ∞ :=
    { toPartialEquiv := (chartAt ℂ (P.gluedUniversalCoverProjection x q)).toPartialEquiv
      open_source := (chartAt ℂ (P.gluedUniversalCoverProjection x q)).open_source
      open_target := (chartAt ℂ (P.gluedUniversalCoverProjection x q)).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  let φ := ea.trans fb.symm
  have hchart (z : P.basedTopologicalUniversalCover x) :
      (chartAt ℂ q) z = (chartAt ℂ (P.gluedUniversalCoverProjection x q))
        (P.gluedUniversalCoverProjection x z) := by
    change P.gluedUniversalCoverSmoothChart x q z = _
    simp only [gluedUniversalCoverSmoothChart, OpenPartialHomeomorph.trans_apply,
      (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt_symm]
  refine ⟨φ, ?_, ?_⟩
  · change q ∈ (chartAt ℂ q).source ∧
      (chartAt ℂ q) q ∈ (chartAt ℂ (P.gluedUniversalCoverProjection x q)).target
    refine ⟨mem_chart_source ℂ q, ?_⟩
    rw [hchart]
    exact (chartAt ℂ (P.gluedUniversalCoverProjection x q)).map_source (mem_chart_source ℂ _)
  · intro z hz
    change P.gluedUniversalCoverProjection x z =
      (chartAt ℂ (P.gluedUniversalCoverProjection x q)).symm ((chartAt ℂ q) z)
    rw [hchart]
    have hzs : P.gluedUniversalCoverProjection x z ∈
        (chartAt ℂ (P.gluedUniversalCoverProjection x q)).source := by
      have hs : z ∈ (P.gluedUniversalCoverSmoothChart x q).source := hz.1
      change z ∈
        (((P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt q).symm.trans
          (chartAt ℂ (P.gluedUniversalCoverProjection x q))).source at hs
      have hh := hs.2
      change
        ((P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt q).symm z ∈
          (chartAt ℂ (P.gluedUniversalCoverProjection x q)).source at hh
      rwa [(P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt_symm] at hh
    exact ((chartAt ℂ (P.gluedUniversalCoverProjection x q)).left_inv hzs).symm

/-- **Math.** Since the selected lifted and base coordinates agree under
projection, its differential is the identity on their common real model. -/
theorem gluedUniversalCoverProjection_mfderiv_eq_id
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverProjection x) q = ContinuousLinearMap.id ℝ ℂ := by
  have hd : HasFDerivAt
      (writtenInExtChartAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        q (P.gluedUniversalCoverProjection x)) (ContinuousLinearMap.id ℝ ℂ)
      ((chartAt ℂ q) q) :=
    (hasFDerivAt_id ((chartAt ℂ q) q)).congr_of_eventuallyEq
      (P.gluedUniversalCover_projection_writtenInExtChartAt_eventuallyEq_id x q)
  have hm : HasMFDerivAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverProjection x) q (ContinuousLinearMap.id ℝ ℂ) :=
    ⟨(P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff.continuous.continuousAt,
      hd.hasFDerivWithinAt⟩
  exact hm.mfderiv

/-- **Math.** The literal endpoint projection, bundled with its proved
smoothness on the concrete lifted atlas. -/
def gluedUniversalCoverSmoothProjection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    C^∞⟮modelWithCornersSelf ℝ ℂ, P.basedTopologicalUniversalCover x;
      modelWithCornersSelf ℝ ℂ, P.GluedCarrier⟯ :=
  ⟨P.gluedUniversalCoverProjection x,
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff⟩

/-- **Math.** The genuine endpoint covering is a smooth covering for the
constructed lifted atlas, with surjectivity already proved topologically. -/
theorem gluedUniversalCoverSmoothProjection_isSmoothCoveringMap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    LeeLib.Ch02.IsSmoothCoveringMap (P.gluedUniversalCoverSmoothProjection x) :=
  ⟨P.gluedUniversalCoverProjection_surjective x,
    P.gluedUniversalCoverProjection_isCoveringMap x,
    P.gluedUniversalCoverProjection_isLocalDiffeomorph x⟩

/-- **Math.** The actual smooth pullback of the constructed patched metric
on the original based-path cover. -/
def gluedCurvatureBoundedUniversalCoverRiemannianMetric
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Riemannian.RiemannianMetric (modelWithCornersSelf ℝ ℂ) (P.basedTopologicalUniversalCover x) :=
  (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric
    P.gluedCurvatureBoundedSmoothRiemannianMetric

/-- **Math.** The concrete endpoint projection preserves the actual
pullback tensor; it is a Riemannian covering without an assumed metric bridge. -/
theorem gluedCurvatureBoundedUniversalCover_isRiemannianCovering
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    LeeLib.Ch02.IsRiemannianCovering (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
      P.gluedCurvatureBoundedSmoothRiemannianMetric (P.gluedUniversalCoverSmoothProjection x) :=
  (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).isRiemannianCovering_coveringMetric
    P.gluedCurvatureBoundedSmoothRiemannianMetric

/-- **Math.** The canonical path metric of the actual smooth covering
tensor, keeping the original cover topology. -/
@[instance_reducible]
def gluedCurvatureBoundedUniversalCoverMetricSpace
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    MetricSpace (P.basedTopologicalUniversalCover x) :=
  LeeLib.Ch02.RiemannianMetric.toMetricSpace (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)

/-- **Math.** The covering metric's topology is definitionally the actual
based-path covering topology. -/
theorem gluedCurvatureBoundedUniversalCoverMetricSpace_topology
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace x).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (P.basedTopologicalUniversalCover x)) := rfl

/-- **Math.** The constructed smooth cover metric induces its canonical
ambient distance, as required by the global exponential and Jacobi APIs. -/
theorem gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Riemannian.RiemannianMetric.IsRiemannianDist
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) :=
    ⟨(P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x).toRiemannianMetric⟩
  change IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) (P.basedTopologicalUniversalCover x)
  exact ⟨fun _ _ => rfl⟩

/-- **Math.** The actual pullback covering metric is complete because the
actual compact base metric is complete and the projection is Riemannian. -/
theorem gluedCurvatureBoundedUniversalCoverMetricSpace_complete
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    CompleteSpace (P.basedTopologicalUniversalCover x) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  letI : ConnectedSpace P.GluedCarrier :=
    { toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
      toNonempty := ⟨x⟩ }
  exact SystolicGrowth.smoothCoveringMetric_complete_of_complete_base
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x)
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist

theorem gluedUniversalCover_contMDiff_of_projection_preserving
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (f : P.basedTopologicalUniversalCover x → P.basedTopologicalUniversalCover x)
    (hf : Continuous f)
    (hproj : ∀ q, P.gluedUniversalCoverProjection x (f q) =
      P.gluedUniversalCoverProjection x q) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞ f := by
  intro q
  let h := P.gluedUniversalCoverProjection_isLocalDiffeomorph x (f q)
  have hinv := h.localInverse_contMDiffAt
  rw [hproj q] at hinv
  have hcomp := hinv.comp q
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff.contMDiffAt
  apply hcomp.congr_of_eventuallyEq
  have heq := hf.continuousAt.eventually h.localInverse_eventuallyEq_left
  filter_upwards [heq] with z hz
  change f z = h.localInverse (P.gluedUniversalCoverProjection x z)
  rw [← hproj z]
  exact hz.symm

/-- **Math.** Every member of the existing topological deck subgroup is
smooth in both directions, because its local expressions are actual sheet
inverses of the smooth endpoint projection. -/
def gluedUniversalCoverDeckDiffeomorph
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) :
    P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ P.basedTopologicalUniversalCover x where
  toEquiv := τ.val.toEquiv
  contMDiff_toFun := P.gluedUniversalCover_contMDiff_of_projection_preserving x
    τ.val τ.val.continuous τ.property
  contMDiff_invFun := P.gluedUniversalCover_contMDiff_of_projection_preserving x
    τ.val.symm τ.val.symm.continuous (by
      intro q
      simpa only [Homeomorph.apply_symm_apply] using (τ.property (τ.val.symm q)).symm)

/-- **Math.** The original topological deck element is a genuine smooth
covering automorphism of the same endpoint projection. -/
def gluedUniversalCoverSmoothDeckAut
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) :
    LeeLib.Ch02.CoveringAut (P.gluedUniversalCoverSmoothProjection x) where
  toDiffeomorph := P.gluedUniversalCoverDeckDiffeomorph x τ
  proj_comp := τ.property

/-- **Math.** Original deck maps preserve the actual smooth pullback tensor;
their metric invariance follows from differentiating the projection identity. -/
theorem gluedCurvatureBoundedUniversalCover_deck_isIsometry
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) :
    LeeLib.Ch02.IsIsometry (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
      (P.gluedUniversalCoverDeckDiffeomorph x τ) :=
  SystolicGrowth.smoothCoveringMetric_deck_isIsometry
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x)
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    (P.gluedUniversalCoverSmoothDeckAut x τ)

/-- **Math.** The original deck point maps are isometries of the complete
canonical metric induced by the actual curvature-bounded pullback tensor. -/
theorem gluedCurvatureBoundedUniversalCover_deck_isometry
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Isometry (τ.val : P.basedTopologicalUniversalCover x → P.basedTopologicalUniversalCover x) :=
  SystolicGrowth.smoothCoveringMetric_deck_isometry
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x)
    P.gluedCurvatureBoundedSmoothRiemannianMetric
    (P.gluedUniversalCoverSmoothDeckAut x τ)

#print axioms gluedUniversalCoverSmoothChartedSpace
#print axioms gluedUniversalCoverSmoothIsManifold
#print axioms gluedUniversalCoverProjection_isLocalDiffeomorph
#print axioms gluedUniversalCoverProjection_mfderiv_eq_id
#print axioms gluedUniversalCoverSmoothProjection_isSmoothCoveringMap
#print axioms gluedCurvatureBoundedUniversalCoverRiemannianMetric
#print axioms gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist
#print axioms gluedCurvatureBoundedUniversalCoverMetricSpace_complete
#print axioms gluedUniversalCoverDeckDiffeomorph
#print axioms gluedCurvatureBoundedUniversalCover_deck_isIsometry
#print axioms gluedCurvatureBoundedUniversalCover_deck_isometry

end
end SystolicGrowth.ExerciseGluingPreparation
