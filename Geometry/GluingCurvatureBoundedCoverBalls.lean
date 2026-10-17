module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedUniversalCover
public import Geometry.GluingUniversalCoverPathMetricCompleteness
public import Geometry.MetricPathVariation
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.GlobalExp

@[expose] public section

/-!
# Embedded balls of the actual smooth glued cover

The smooth pullback cover distance dominates the original native path
distance. The original essential-loop lower bound therefore separates
distinct points of a projection fiber in this complete smooth metric, so
balls of radius at most half the target systole project injectively.
-/

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Riemannian
open scoped Manifold Topology ContDiff ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** Projection from the actual smooth pullback cover is
nonexpanding even for the original native metric downstairs. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_native_lipschitz
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    LipschitzWith 1 (P.gluedUniversalCoverProjection x) := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  intro a b
  have hmetric := (P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2
  have hriem := hmetric.riemannianEDist_le
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff a b
  change P.gluedCurvatureBoundedIntrinsicEDist
      (P.gluedUniversalCoverProjection x a) (P.gluedUniversalCoverProjection x b) ≤
    edist a b at hriem
  have hdom := P.gluedCurvatureBoundedIntrinsicEDist_ge_native
    (P.gluedUniversalCoverProjection x a) (P.gluedUniversalCoverProjection x b)
  rw [ENNReal.coe_one, one_mul, P.gluedCarrierIntrinsicMetricSpace_edist]
  exact hdom.trans hriem

/-- **Math.** The complete smooth pullback distance dominates the original
native cover path distance. A genuine minimizing smooth geodesic supplies
the continuous path competitor, rather than an assumed length comparison. -/
theorem gluedCurvatureBoundedUniversalCover_edist_ge_native
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    P.gluedUniversalCoverPathDistance x a b ≤ edist a b := by
  letI := P.gluedCarrierIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  have hg : metric.IsRiemannianDist :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x
  have hp : ∀ v : TangentSpace (modelWithCornersSelf ℝ ℂ) a,
      ∃ γ : ℝ → P.basedTopologicalUniversalCover x, γ 0 = a ∧
        HasDerivAt (fun s => extChartAt (modelWithCornersSelf ℝ ℂ) a (γ s)) v 0 ∧
        Continuous γ ∧ Geodesic.IsGeodesic metric γ := by
    intro v
    exact Geodesic.exists_global_geodesic metric hg a v
  obtain ⟨γ, h0, h1, hc, _, hsegment⟩ :=
    Exponential.exists_minimizing_geodesic_unitInterval metric hg a hp b
  let Γ : Path a b :=
    { toFun := fun t => γ t
      continuous_toFun := hc.comp continuous_subtype_val
      source' := h0
      target' := h1 }
  have hvar : eVariationOn Γ univ = ENNReal.ofReal (dist a b) := by
    apply eVariationOn_path_eq_of_metric_segment Γ
    intro s t
    exact (hsegment s s.property t t.property).trans (mul_comm _ _)
  have hlip : LipschitzWith 1 (P.gluedUniversalCoverProjection x) :=
    P.gluedCurvatureBoundedUniversalCoverProjection_native_lipschitz x
  have hprojvar := hlip.lipschitzOnWith.comp_eVariationOn_le
    (g := Γ) (s := univ) (mapsTo_univ _ _)
  have hprojvar' : P.gluedUniversalCoverProjectedPathVariation x Γ ≤
      eVariationOn Γ univ := by
    dsimp only [gluedUniversalCoverProjectedPathVariation]
    simpa only [ENNReal.coe_one, one_mul] using hprojvar
  calc
    P.gluedUniversalCoverPathDistance x a b ≤
        P.gluedUniversalCoverProjectedPathVariation x Γ :=
      P.gluedUniversalCoverPathDistance_le_projectedPathVariation x Γ
    _ ≤ eVariationOn Γ univ := hprojvar'
    _ = ENNReal.ofReal (dist a b) := hvar
    _ = edist a b := (edist_dist a b).symm

/-- **Math.** Distinct points over one actual base point pay the target
systole in the constructed complete smooth cover metric. -/
theorem targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x)
    (hproj : P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b)
    (hne : a ≠ b) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    targetSystole C g ≤ dist a b := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  have hgap := P.target_le_gluedUniversalCoverPathDistance_of_same_fiber_ne
    x hproj.symm (Ne.symm hne)
  have h := hgap.trans (P.gluedCurvatureBoundedUniversalCover_edist_ge_native x a b)
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

/-- **Math.** Every actual smooth-cover ball of radius at most half the
target systole projects injectively. The radius cutoff is unchanged. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_injOn_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (c : P.basedTopologicalUniversalCover x) (r : ℝ)
    (hr : 2 * r ≤ targetSystole C g) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Set.InjOn (P.gluedUniversalCoverProjection x) (Metric.ball c r) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  intro a ha b hb hproj
  by_contra hne
  have hgap := P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hproj hne
  have ha' : dist a c < r := Metric.mem_ball.mp ha
  have hb' : dist c b < r := by
    simpa only [dist_comm] using Metric.mem_ball.mp hb
  have hdist : dist a b < 2 * r := by
    calc
      dist a b ≤ dist a c + dist c b := dist_triangle a c b
      _ < r + r := add_lt_add ha' hb'
      _ = 2 * r := by ring
  linarith

#print axioms gluedCurvatureBoundedUniversalCoverProjection_native_lipschitz
#print axioms gluedCurvatureBoundedUniversalCover_edist_ge_native
#print axioms targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
#print axioms gluedCurvatureBoundedUniversalCoverProjection_injOn_ball

/-- **Math.** The injective ball projection is an actual open embedding
in the unchanged smooth-cover topology. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_isOpenEmbedding_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (c : P.basedTopologicalUniversalCover x) (r : ℝ)
    (hr : 2 * r ≤ targetSystole C g) :
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    Topology.IsOpenEmbedding
      ((Metric.ball c r).restrict (P.gluedUniversalCoverProjection x)) := by
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  have hlocal := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph
  have hball := (Metric.isOpen_ball (x := c) (ε := r)).isOpenEmbedding_subtypeVal
  have hinj := P.gluedCurvatureBoundedUniversalCoverProjection_injOn_ball x c r hr
  exact (hlocal.comp hball.isLocalHomeomorph).isOpenEmbedding_of_injective
    (fun a b h => Subtype.ext (hinj a.property b.property h))

#print axioms gluedCurvatureBoundedUniversalCoverProjection_isOpenEmbedding_ball

private theorem gluedUniversalCover_lift_contMDiff_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (β : ℝ → P.GluedCarrier) (γ : ℝ → P.basedTopologicalUniversalCover x)
    (hβ : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 β)
    (hγ : Continuous γ)
    (hlift : ∀ t, P.gluedUniversalCoverProjection x (γ t) = β t) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ := by
  intro t
  let h := P.gluedUniversalCoverProjection_isLocalDiffeomorph x (γ t)
  have hinv := h.localInverse_contMDiffAt
  rw [hlift t] at hinv
  have hcomp := (hinv.of_le (by simp)).comp t (hβ t)
  apply hcomp.congr_of_eventuallyEq
  have heq := hγ.continuousAt.eventually h.localInverse_eventuallyEq_left
  filter_upwards [heq] with s hs
  change γ s = h.localInverse (β s)
  rw [← hlift s]
  exact hs.symm

/-- **Math.** The genuine smooth covering projects every metric ball onto
the base metric ball of the same radius. A minimizing base geodesic is
lifted continuously, proved smooth through actual local sheet inverses,
and compared by its preserved Riemannian length. -/
theorem gluedCurvatureBoundedUniversalCoverProjection_image_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (c : P.basedTopologicalUniversalCover x) (r : ℝ) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
    (P.gluedUniversalCoverProjection x) '' Metric.ball c r =
      Metric.ball (P.gluedUniversalCoverProjection x c) r := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  letI : ConnectedSpace P.GluedCarrier :=
    { toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
      toNonempty := ⟨x⟩ }
  let baseMetric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let coverMetric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨baseMetric.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) := ⟨coverMetric.toRiemannianMetric⟩
  have hg : RiemannianMetric.IsRiemannianDist baseMetric :=
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist
  have hcover : coverMetric.IsRiemannianDist :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x
  have hmetric := (P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hle := hmetric.riemannianEDist_le
      (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff a c
    change edist (P.gluedUniversalCoverProjection x a)
        (P.gluedUniversalCoverProjection x c) ≤ edist a c at hle
    have hdist : dist (P.gluedUniversalCoverProjection x a)
        (P.gluedUniversalCoverProjection x c) ≤ dist a c := by
      rw [edist_dist, edist_dist] at hle
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hle
    exact hdist.trans_lt ha
  · intro hq
    have hp : ∀ v : TangentSpace (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x c),
        ∃ β : ℝ → P.GluedCarrier, β 0 = P.gluedUniversalCoverProjection x c ∧
          HasDerivAt (fun s => extChartAt (modelWithCornersSelf ℝ ℂ)
            (P.gluedUniversalCoverProjection x c) (β s)) v 0 ∧
          Continuous β ∧ Geodesic.IsGeodesic baseMetric β := by
      intro v
      exact Geodesic.exists_global_geodesic baseMetric hg _ v
    obtain ⟨β, h0, h1, hc, hgeo, _, hlen⟩ :=
      Exponential.exists_minimizing_geodesic_unitInterval_with_length baseMetric hg
        (P.gluedUniversalCoverProjection x c) hp q
    let βc : C(ℝ, P.GluedCarrier) := ⟨β, hc⟩
    obtain ⟨γc, ⟨hγ0, hγlift⟩, _⟩ :=
      (P.gluedUniversalCoverProjection_isCoveringMap x).existsUnique_continuousMap_lifts
        βc 0 c (by simpa only [βc, ContinuousMap.coe_mk] using h0.symm)
    have hlift (t : ℝ) : P.gluedUniversalCoverProjection x (γc t) = β t :=
      congrFun hγlift t
    have hβsmooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ ℂ) 1 β :=
      contMDiffOn_univ.mp ((hgeo.isGeodesicOn univ).contMDiffOn
        isOpen_univ hc.continuousOn)
    have hγsmooth := P.gluedUniversalCover_lift_contMDiff_one x β γc hβsmooth
      γc.continuous hlift
    have hlength := hmetric.pathELength_comp
      (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff
      (a := (0 : ℝ)) (b := (1 : ℝ)) hγsmooth.contMDiffOn
    have hfun : (P.gluedUniversalCoverProjection x) ∘ γc = β := funext hlift
    change Manifold.pathELength (modelWithCornersSelf ℝ ℂ)
      ((P.gluedUniversalCoverProjection x) ∘ γc) 0 1 =
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) γc 0 1 at hlength
    rw [hfun] at hlength
    have hle : edist (γc 0) (γc 1) ≤
        Manifold.pathELength (modelWithCornersSelf ℝ ℂ) γc 0 1 := by
      rw [hcover.out]
      exact Manifold.riemannianEDist_le_pathELength hγsmooth.contMDiffOn rfl rfl zero_le_one
    rw [hγ0, ← hlength, hlen] at hle
    have hdist : dist c (γc 1) ≤ dist (P.gluedUniversalCoverProjection x c) q := by
      rw [edist_dist] at hle
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hle
    refine ⟨γc 1, ?_, (hlift 1).trans h1⟩
    rw [Metric.mem_ball, dist_comm]
    exact hdist.trans_lt (by simpa only [Metric.mem_ball, dist_comm] using hq)

#print axioms gluedCurvatureBoundedUniversalCoverProjection_image_ball

end
end SystolicGrowth.ExerciseGluingPreparation
