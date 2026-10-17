module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedCoverHadamard
public import Geometry.GluingCurvatureBoundedCoverFiberBalls
public import Geometry.GluingCurvatureBoundedExponential
public import Geometry.ExponentialGlobalGauss
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ParallelFrame
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.LocalIsometryRigidity
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

@[expose] public section

/-!
# Genuine principal-turn polar disks on the patched surface

An orthonormal initial frame is an actual linear coordinate equivalence.
Composing the ordinary principal polar chart with the complete covering
exponential and projection gives an open embedded punctured disk sector.
Its radius is measured by the constructed metric, not the model norm.
-/

set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold Riemannian
open scoped Manifold ContDiff Topology

namespace SystolicGrowth

noncomputable section

/-- **Math.** The real-linear frame map sends `1,I` to the given vectors. -/
def complexFrameLinearMap (e : Fin 2 → ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.reCLM.smulRight (e 0) + Complex.imCLM.smulRight (e 1)

theorem complexFrameLinearMap_apply (e : Fin 2 → ℂ) (z : ℂ) :
    complexFrameLinearMap e z = z.re • e 0 + z.im • e 1 := rfl

theorem complexFrameLinearMap_polar (e : Fin 2 → ℂ) (p : ℝ × ℝ) :
    complexFrameLinearMap e (Complex.polarCoord.symm p) =
      p.1 • exponentialPolarUnit e p.2 := by
  rw [complexFrameLinearMap_apply, Complex.polarCoord_symm_apply]
  simp [exponentialPolarUnit, Complex.mul_re, Complex.mul_im, smul_add, mul_smul]

/-- **Math.** One full principal angular turn, with the origin and boundary
removed. This is the ordinary injective polar-chart domain. -/
def exponentialPolarStrip (R : ℝ) : Set (ℝ × ℝ) :=
  Ioo 0 R ×ˢ Ioo (-Real.pi) Real.pi

theorem exponentialPolarStrip_isOpen (R : ℝ) : IsOpen (exponentialPolarStrip R) :=
  isOpen_Ioo.prod isOpen_Ioo

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** In the actual adapted covering charts, the initial metric
pairing is exactly the base initial pairing; projection differential is
literally the identity in these chart presentations. -/
theorem gluedCurvatureBoundedCover_initialMetric_eq_base
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (u v : ℂ) :
    chartMetricInner (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) u v =
    chartMetricInner P.gluedCurvatureBoundedSmoothRiemannianMetric
      (P.gluedUniversalCoverProjection x q)
      (extChartAt (modelWithCornersSelf ℝ ℂ) (P.gluedUniversalCoverProjection x q)
        (P.gluedUniversalCoverProjection x q)) u v := by
  rw [chartMetricInner_extChartAt_eq_metricInner _ q (mem_chart_source ℂ q),
    chartMetricInner_extChartAt_eq_metricInner _ _ (mem_chart_source ℂ _)]
  simp only [trivializationAt_symm_self]
  have h := (P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2.inner_mfderiv q u v
  change RiemannianMetric.metricInner P.gluedCurvatureBoundedSmoothRiemannianMetric
      (P.gluedUniversalCoverProjection x q)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x) q u)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (P.gluedUniversalCoverProjection x) q v) =
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x).metricInner q u v at h
  rw [P.gluedUniversalCoverProjection_mfderiv_eq_id x q] at h
  exact h.symm

/-- **Math.** The genuine covering exponential projects to the genuine
base exponential with the same initial chart vector. This is geodesic
uniqueness for the actual local isometry, not a choice of disk coordinates. -/
theorem gluedCurvatureBoundedUniversalCoverExpMap_projection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (v : ℂ) :
    P.gluedUniversalCoverProjection x (P.gluedCurvatureBoundedUniversalCoverExpMap x q v) =
      P.gluedCurvatureBoundedExpMap (P.gluedUniversalCoverProjection x q) v := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  letI : CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete
  letI : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let cg := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  let bg : RiemannianMetric I P.GluedCarrier := P.gluedCurvatureBoundedSmoothRiemannianMetric
  letI : RiemannianBundle (TangentSpace I : P.basedTopologicalUniversalCover x → Type) :=
    ⟨cg.toRiemannianMetric⟩
  have hcg : cg.IsRiemannianDist :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x
  have hbg : bg.IsRiemannianDist :=
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist
  let γ := Geodesic.globalGeodesic (I := I) cg hcg q v
  let β := Geodesic.globalGeodesic (I := I) bg hbg (P.gluedUniversalCoverProjection x q) v
  have hγ0 : γ 0 = q := Geodesic.globalGeodesic_zero cg hcg q v
  have hβ0 : β 0 = P.gluedUniversalCoverProjection x q :=
    Geodesic.globalGeodesic_zero bg hbg _ v
  have hγc : Continuous γ := Geodesic.continuous_globalGeodesic cg hcg q v
  have hβc : Continuous β := Geodesic.continuous_globalGeodesic bg hbg _ v
  have hpres : DCPreservesMetric cg bg (P.gluedUniversalCoverProjection x) := by
    intro s a b
    exact ((P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2.inner_mfderiv s a b).symm
  have hprojgeo := Geodesic.isGeodesicOn_comp_of_isLocalDiffeomorph
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x) cg bg hpres isOpen_univ
    hγc.continuousOn (fun t _ => Geodesic.isGeodesic_globalGeodesic cg hcg q v t)
  have hprojd : HasDerivAt (fun t => extChartAt I (P.gluedUniversalCoverProjection x q)
      (P.gluedUniversalCoverProjection x (γ t))) v 0 := by
    have hfun : (fun t => extChartAt I (P.gluedUniversalCoverProjection x q)
        (P.gluedUniversalCoverProjection x (γ t))) =
      (fun t => extChartAt I q (γ t)) := by
      funext t
      change (chartAt ℂ (P.gluedUniversalCoverProjection x q))
        (P.gluedUniversalCoverProjection x (γ t)) = (chartAt ℂ q) (γ t)
      exact (P.gluedUniversalCover_chartAt_apply x q (γ t)).symm
    rw [hfun]
    exact Geodesic.hasDerivAt_chartReading_globalGeodesic cg hcg q v
  have hbd := Geodesic.hasDerivAt_chartReading_globalGeodesic bg hbg
    (P.gluedUniversalCoverProjection x q) v
  have heq := Geodesic.IsGeodesicOn.eqOn_of_deriv_chartReading_eq
    (γ₁ := fun t => P.gluedUniversalCoverProjection x (γ t)) (γ₂ := β)
    (β := P.gluedUniversalCoverProjection x q) isOpen_univ isPreconnected_univ
    hprojgeo (fun t _ => Geodesic.isGeodesic_globalGeodesic bg hbg _ v t)
    ((P.gluedUniversalCoverProjection_isCoveringMap x).continuous.comp hγc).continuousOn hβc.continuousOn
    (mem_univ (0 : ℝ)) (by rw [hγ0, hβ0])
    (by rw [hγ0]; exact mem_chart_source ℂ _)
    (hprojd.deriv.trans hbd.deriv.symm)
  exact heq (mem_univ (1 : ℝ))

/-- **Math.** Orthonormality in the genuine initial metric makes the actual
frame map injective, regardless of the ambient model inner product. -/
theorem gluedCurvatureBoundedCover_frameLinearMap_injective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) :
    Function.Injective (complexFrameLinearMap e) := by
  let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  have hreal (z : ℂ) : chartMetricInner metric q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q)
      (complexFrameLinearMap e z) (e 0) = z.re := by
    dsimp only [metric]
    simp only [complexFrameLinearMap_apply, chartMetricInner_add_left,
      chartMetricInner_smul_left, he]
    norm_num
  have himag (z : ℂ) : chartMetricInner metric q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q)
      (complexFrameLinearMap e z) (e 1) = z.im := by
    dsimp only [metric]
    simp only [complexFrameLinearMap_apply, chartMetricInner_add_left,
      chartMetricInner_smul_left, he]
    norm_num
  intro a b hab
  apply Complex.ext
  · simpa only [hreal] using congrArg (fun v => chartMetricInner metric q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v (e 0)) hab
  · simpa only [himag] using congrArg (fun v => chartMetricInner metric q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v (e 1)) hab

/-- **Math.** The actual initial frame changes the ordinary real polar
chart by a genuine continuous linear equivalence. -/
theorem gluedCurvatureBoundedCover_polarVector_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ) :
    Topology.IsOpenEmbedding (fun p : exponentialPolarStrip R =>
      p.val.1 • exponentialPolarUnit e p.val.2) := by
  have hinj := P.gluedCurvatureBoundedCover_frameLinearMap_injective x q e he
  let L : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (complexFrameLinearMap e).toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hsub : exponentialPolarStrip R ⊆ Complex.polarCoord.target := by
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have hi : Topology.IsOpenEmbedding (Set.inclusion hsub) :=
    Topology.IsOpenEmbedding.inclusion hsub
      ((exponentialPolarStrip_isOpen R).preimage continuous_subtype_val)
  have hpolar := Complex.polarCoord.symm.isOpenEmbedding_restrict.comp hi
  have h := L.toHomeomorph.isOpenEmbedding.comp hpolar
  convert h using 1
  funext p
  exact (complexFrameLinearMap_polar e p.val).symm

/-- **Math.** The actual covering exponential followed by the original
projection, parameterized by initial metric radius and principal angle. -/
def gluedCurvatureBoundedPolarPoint
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ) (p : ℝ × ℝ) :
    P.GluedCarrier :=
  P.gluedUniversalCoverProjection x
    (P.gluedCurvatureBoundedUniversalCoverExpMap x q
      (p.1 • exponentialPolarUnit e p.2))

/-- **Math.** The projected cover polar map is exactly the base metric's
own exponential polar map, so its native area is consumed directly. -/
theorem gluedCurvatureBoundedPolarPoint_eq_baseExpMap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ) (p : ℝ × ℝ) :
    P.gluedCurvatureBoundedPolarPoint x q e p =
      P.gluedCurvatureBoundedExpMap (P.gluedUniversalCoverProjection x q)
        (p.1 • exponentialPolarUnit e p.2) :=
  P.gluedCurvatureBoundedUniversalCoverExpMap_projection x q _

/-- **Math.** The true initial polar vector has metric length `|r|` in
the chosen orthonormal frame, not an assumed Euclidean initial metric. -/
theorem gluedCurvatureBoundedCover_polarVector_initialLength
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (r θ : ℝ) :
    Real.sqrt (chartMetricInner (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q)
      (r • exponentialPolarUnit e θ) (r • exponentialPolarUnit e θ)) = |r| := by
  have hunit := (exponentialPolarDirections_chartMetric
    (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q e he θ).1
  rw [chartMetricInner_smul_left, chartMetricInner_smul_right, hunit,
    mul_one, ← pow_two, Real.sqrt_sq_eq_abs]

/-- **Math.** Every point of the actual polar strip lies in the genuine
base metric ball of the same radius. -/
theorem gluedCurvatureBoundedPolarPoint_mem_ball
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ)
    {p : ℝ × ℝ} (hp : p ∈ exponentialPolarStrip R) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    P.gluedCurvatureBoundedPolarPoint x q e p ∈
      Metric.ball (P.gluedUniversalCoverProjection x q) R := by
  letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
  rw [← P.gluedCurvatureBoundedUniversalCover_projectedExpMap_image_initialLength_ball x q R]
  refine ⟨p.1 • exponentialPolarUnit e p.2, ?_, rfl⟩
  rw [mem_setOf_eq, P.gluedCurvatureBoundedCover_polarVector_initialLength x q e he,
    abs_of_pos hp.1.1]
  exact hp.1.2

/-- **Math.** A genuine metric fiber gap makes the principal-turn polar
sector embed openly at exactly half that gap. -/
theorem gluedCurvatureBoundedPolarPoint_isOpenEmbedding_of_fiber_gap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R L : ℝ)
    (hgap : letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
      ∀ a b : P.basedTopologicalUniversalCover x,
        P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
          a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) :
    Topology.IsOpenEmbedding ((exponentialPolarStrip R).restrict
      (P.gluedCurvatureBoundedPolarPoint x q e)) := by
  let V : exponentialPolarStrip R → ℂ :=
    fun p => p.val.1 • exponentialPolarUnit e p.val.2
  have hV := P.gluedCurvatureBoundedCover_polarVector_isOpenEmbedding x q e he R
  have hlocal := (P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.comp
    ((P.gluedCurvatureBoundedUniversalCoverExpMap_isOpenEmbedding x q).isLocalHomeomorph.comp
      hV.isLocalHomeomorph)
  have hlength (p : exponentialPolarStrip R) : Real.sqrt (chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (V p) (V p)) < R := by
    change Real.sqrt (chartMetricInner _ _ _
      (p.val.1 • exponentialPolarUnit e p.val.2)
      (p.val.1 • exponentialPolarUnit e p.val.2)) < R
    rw [P.gluedCurvatureBoundedCover_polarVector_initialLength x q e he,
      abs_of_pos p.property.1.1]
    exact p.property.1.2
  apply hlocal.isOpenEmbedding_of_injective
  intro a b hab
  have hinj := (P.gluedCurvatureBoundedUniversalCover_projectedExpMap_isOpenEmbedding_initialLength_ball_of_fiber_gap
    x q R L hgap hR).injective
  have hv : (⟨V a, hlength a⟩ : {v : ℂ | Real.sqrt (chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) v v) < R}) =
        ⟨V b, hlength b⟩ := hinj hab
  exact hV.injective (congrArg Subtype.val hv)

/-- **Math.** The native essential-loop lower bound supplies the genuine
principal-turn polar embedding at the unchanged half-target cutoff. -/
theorem gluedCurvatureBoundedPolarPoint_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ)
    (hR : 2 * R ≤ targetSystole C g) :
    Topology.IsOpenEmbedding ((exponentialPolarStrip R).restrict
      (P.gluedCurvatureBoundedPolarPoint x q e)) := by
  apply P.gluedCurvatureBoundedPolarPoint_isOpenEmbedding_of_fiber_gap
    x q e he R (targetSystole C g) ?_ hR
  intro a b hproj hne
  exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hproj hne

#print axioms gluedCurvatureBoundedCover_frameLinearMap_injective
#print axioms gluedCurvatureBoundedCover_initialMetric_eq_base
#print axioms gluedCurvatureBoundedUniversalCoverExpMap_projection
#print axioms gluedCurvatureBoundedCover_polarVector_isOpenEmbedding
#print axioms gluedCurvatureBoundedPolarPoint_isOpenEmbedding
#print axioms gluedCurvatureBoundedPolarPoint_isOpenEmbedding_of_fiber_gap
#print axioms gluedCurvatureBoundedPolarPoint_eq_baseExpMap
#print axioms gluedCurvatureBoundedCover_polarVector_initialLength
#print axioms gluedCurvatureBoundedPolarPoint_mem_ball

end ExerciseGluingPreparation
end
end SystolicGrowth
