module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedCoverCurvature
public import Geometry.GluingCurvatureBoundedCoverBalls
public import Geometry.ExponentialGlobalPolarMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.HadamardComplete

@[expose] public section

/-!
# Actual Cartan--Hadamard geometry of the glued universal cover

Completeness, simple connectedness, smoothness and curvature are constructed
inputs on the original based-path cover. Its actual global exponential is a
diffeomorphism and its radial metric-length disks are the actual metric balls.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Bundle Manifold Riemannian Set
open scoped Manifold ContDiff Topology

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The literal time-one endpoint of the global geodesic for the
actual complete smooth pullback tensor on the original universal cover. -/
def gluedCurvatureBoundedUniversalCoverExpMap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (v : ℂ) :
    P.basedTopologicalUniversalCover x :=
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  Exponential.expMapGlobal (I := modelWithCornersSelf ℝ ℂ)
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x) q v

/-- **Math.** The actual Cartan--Hadamard diffeomorphism is the original
cover's exponential map; all geometric premises have been proved for it. -/
def gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    Riemannian.HadamardModel ℂ ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ P.basedTopologicalUniversalCover x :=
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  Jacobi.hadamardDiffeomorphOfNonpos_complete
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x) q
    (P.gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_pair_nonneg x)

/-- **Math.** The constructed diffeomorphism has exactly the genuine
global exponential point map, not merely an unrelated diffeomorphic carrier. -/
theorem gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (v : Riemannian.HadamardModel ℂ) :
    P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x q v =
      P.gluedCurvatureBoundedUniversalCoverExpMap x q (Riemannian.HadamardModel.toModel v) := by
  let := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  let : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  exact congrFun (Jacobi.hadamardDiffeomorphOfNonpos_complete_coe
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x) q
    (P.gluedCurvatureBoundedUniversalCover_curvatureOperatorAt_pair_nonneg x)) v

/-- **Math.** Nonpositive curvature and genuine simple connectedness make
the actual complete covering exponential globally injective. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_injective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    Function.Injective (P.gluedCurvatureBoundedUniversalCoverExpMap x q) := by
  intro u v huv
  have h := (P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x q).injective
    (show P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x q
        (u : Riemannian.HadamardModel ℂ) =
      P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x q
        (v : Riemannian.HadamardModel ℂ) from by
      simpa only [Diffeomorph.coe_toEquiv, gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph_apply,
        Riemannian.HadamardModel.toModel, id_eq] using huv)
  exact h

/-- **Math.** The literal exponential point map is a global open embedding
of the real tangent plane into the original covering topology. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    Topology.IsOpenEmbedding (P.gluedCurvatureBoundedUniversalCoverExpMap x q) := by
  have hmap : ⇑(P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x q).toHomeomorph =
      P.gluedCurvatureBoundedUniversalCoverExpMap x q := by
    funext v
    simpa only [Diffeomorph.coe_toHomeomorph, Riemannian.HadamardModel.toModel, id_eq] using
      P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph_apply x q v
  rw [← hmap]
  exact (P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x q).toHomeomorph.isOpenEmbedding

/-- **Math.** The genuine global covering exponential is smooth on the
whole real tangent plane. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_contMDiff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) ∞
      (P.gluedCurvatureBoundedUniversalCoverExpMap x q) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  exact Exponential.contMDiff_expMapGlobal
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x) q

/-- **Math.** Every radial geodesic on the genuine Hadamard cover minimizes:
the endpoint distance is exactly its initial actual metric length. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_dist_eq_initialLength
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (v : ℂ) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    dist q (P.gluedCurvatureBoundedUniversalCoverExpMap x q v) =
      Real.sqrt (Riemannian.chartMetricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
        (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  obtain ⟨w, hw, hlength⟩ := SystolicGrowth.exists_expMapGlobal_initialLength_eq_dist
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x) q
    (P.gluedCurvatureBoundedUniversalCoverExpMap x q v)
  have hwv : w = v := P.gluedCurvatureBoundedUniversalCoverExpMap_injective x q hw
  rw [hwv] at hlength
  exact hlength.symm

/-- **Math.** The actual complete-cover exponential maps each open initial
metric-length disk onto the whole genuine metric ball of the same radius. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_image_initialLength_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R : ℝ) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    (P.gluedCurvatureBoundedUniversalCoverExpMap x q) ''
      {v : ℂ | Real.sqrt (Riemannian.chartMetricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
        (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R} = Metric.ball q R := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  exact SystolicGrowth.expMapGlobal_image_initialLength_ball
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x)
    (P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x) q R

/-- **Math.** Initial length is continuous in the genuine metric tensor at
the exponential basepoint, so its open disks are actual open subsets. -/
theorem gluedCurvatureBoundedUniversalCover_initialLength_continuous
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    Continuous (fun v : ℂ => Real.sqrt (Riemannian.chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v)) := by
  let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  have hfun : (fun v : ℂ => Real.sqrt (Riemannian.chartMetricInner metric q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v)) =
      fun v : ℂ => Real.sqrt (metric.inner q v v) := by
    funext v
    rw [Riemannian.chartMetricInner_extChartAt_eq_metricInner metric q
      (mem_chart_source ℂ q) v v]
    simp only [Riemannian.trivializationAt_symm_self,
      Riemannian.RiemannianMetric.metricInner_apply]
  change Continuous (fun v : ℂ => Real.sqrt (Riemannian.chartMetricInner metric q
    (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v))
  rw [hfun]
  exact Real.continuous_sqrt.comp ((metric.inner q).continuous.clm_apply continuous_id)

/-- **Math.** Restricting the literal covering exponential to its genuine
initial-length disk remains an open embedding in the original cover topology. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding_initialLength_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R : ℝ) :
    Topology.IsOpenEmbedding
      (({v : ℂ | Real.sqrt (Riemannian.chartMetricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
        (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R} : Set ℂ).restrict
        (P.gluedCurvatureBoundedUniversalCoverExpMap x q)) := by
  have hopen : IsOpen {v : ℂ | Real.sqrt (Riemannian.chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R} :=
    isOpen_lt (P.gluedCurvatureBoundedUniversalCover_initialLength_continuous x q)
      continuous_const
  exact (P.gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding x q).comp
    hopen.isOpenEmbedding_subtypeVal

/-- **Math.** Up to the unchanged half-systole cutoff, the actual initial
metric-length disk embeds openly in the literal glued surface through its
genuine covering exponential and endpoint projection. -/
theorem gluedCurvatureBoundedUniversalCover_projectedExpMap_isOpenEmbedding_initialLength_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R : ℝ)
    (hR : 2 * R ≤ targetSystole C g) :
    Topology.IsOpenEmbedding
      (({v : ℂ | Real.sqrt (Riemannian.chartMetricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
        (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R} : Set ℂ).restrict
        (P.gluedUniversalCoverProjection x ∘ P.gluedCurvatureBoundedUniversalCoverExpMap x q)) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  let S : Set ℂ := {v : ℂ | Real.sqrt (Riemannian.chartMetricInner
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
    (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R}
  have hexp := P.gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding_initialLength_ball x q R
  have hlocal := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.comp
    hexp.isLocalHomeomorph
  have hinj := P.gluedCurvatureBoundedUniversalCoverProjection_injOn_ball x q R hR
  have hmem (v : S) : P.gluedCurvatureBoundedUniversalCoverExpMap x q v.val ∈ Metric.ball q R := by
    rw [Metric.mem_ball, dist_comm,
      P.gluedCurvatureBoundedUniversalCoverExpMap_dist_eq_initialLength]
    exact v.property
  apply hlocal.isOpenEmbedding_of_injective
  intro a b hab
  apply Subtype.ext
  apply P.gluedCurvatureBoundedUniversalCoverExpMap_injective x q
  exact hinj (hmem a) (hmem b) hab

/-- **Math.** The openly embedded initial-length disk covers the entire
actual patched-metric ball downstairs, not only a smaller coordinate patch. -/
theorem gluedCurvatureBoundedUniversalCover_projectedExpMap_image_initialLength_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R : ℝ) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    (P.gluedUniversalCoverProjection x ∘ P.gluedCurvatureBoundedUniversalCoverExpMap x q) ''
      {v : ℂ | Real.sqrt (Riemannian.chartMetricInner
        (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
        (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R} =
      Metric.ball (P.gluedUniversalCoverProjection x q) R := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  simp only [Function.comp_def]
  rw [← Set.image_image (P.gluedUniversalCoverProjection x)
    (P.gluedCurvatureBoundedUniversalCoverExpMap x q),
    P.gluedCurvatureBoundedUniversalCoverExpMap_image_initialLength_ball x q R,
    P.gluedCurvatureBoundedUniversalCoverProjection_image_ball x q R]

#print axioms gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_injective
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_contMDiff
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_dist_eq_initialLength
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_image_initialLength_ball
#print axioms gluedCurvatureBoundedUniversalCover_initialLength_continuous
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding_initialLength_ball
#print axioms gluedCurvatureBoundedUniversalCover_projectedExpMap_isOpenEmbedding_initialLength_ball
#print axioms gluedCurvatureBoundedUniversalCover_projectedExpMap_image_initialLength_ball

end

end SystolicGrowth.ExerciseGluingPreparation
