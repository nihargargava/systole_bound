module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedSystoleAttainment
public import Geometry.GluingCurvatureBoundedCoverHadamard
public import Geometry.GluingCurvatureBoundedCoverLocalIsometry
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.Extendible

@[expose] public section

/-!
# An actual length-minimizing essential smooth loop

A systole-attaining fiber pair is joined by the genuine covering exponential
geodesic. Its smooth projected segment closes and is essential, and its actual
Riemannian length is the fiber systole. Smooth lifting compares this length
with every essential `C¹` loop, without a replacement-metric attainment premise.
-/

open Set Bundle Manifold Riemannian
open scoped ENNReal ContDiff Topology Manifold unitInterval

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

private theorem gluedCurvatureBounded_lift_contMDiffOn_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (β : ℝ → P.GluedCarrier) (γ : ℝ → P.basedTopologicalUniversalCover x)
    (hβ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 β
      (Icc (0 : ℝ) 1))
    (hγ : Continuous γ)
    (hlift : ∀ t, P.gluedUniversalCoverProjection x (γ t) = β t) :
    ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ
      (Icc (0 : ℝ) 1) := by
  intro t ht
  let h := P.gluedUniversalCoverProjection_isLocalDiffeomorph x (γ t)
  have hinv := h.localInverse_contMDiffAt
  rw [hlift t] at hinv
  have hcomp := (hinv.of_le (by simp)).comp_contMDiffWithinAt t (hβ t ht)
  apply hcomp.congr_of_eventuallyEq_of_mem _ ht
  have heq := hγ.continuousAt.eventually h.localInverse_eventuallyEq_left
  filter_upwards [heq.filter_mono nhdsWithin_le_nhds] with s hs
  change γ s = h.localInverse (β s)
  rw [← hlift s]
  exact hs.symm

/-- **Math.** Every actual essential `C¹` loop pays the smooth fiber
systole. Its smooth lift and length preservation are constructed through
the genuine local covering sheets, not supplied as hypotheses. -/
private theorem gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential_continuous
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier)
    (β : ℝ → P.GluedCarrier)
    (hβ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 β
      (Icc (0 : ℝ) 1)) (hβc : Continuous β)
    (ℓ : Path y y) (hℓ : ∀ t : I, ℓ t = β t)
    (hess : ¬ ℓ.Homotopic (Path.refl y)) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
    P.gluedCurvatureBoundedFiberSystole x ≤
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) β 0 1 := by
  let := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  let coverMetric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  let : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) := ⟨coverMetric.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
  obtain ⟨a, ha⟩ := P.gluedUniversalCoverProjection_surjective x y
  have h0 : β 0 = y := (hℓ 0).symm.trans ℓ.source
  have h1 : β 1 = y := (hℓ 1).symm.trans ℓ.target
  let βc : C(ℝ, P.GluedCarrier) := ⟨β, hβc⟩
  obtain ⟨γc, ⟨hγ0, hγlift⟩, _⟩ :=
    (P.gluedUniversalCoverProjection_isCoveringMap x).existsUnique_continuousMap_lifts
      βc 0 a (ha.trans h0.symm)
  have hlift (t : ℝ) : P.gluedUniversalCoverProjection x (γc t) = β t :=
    congrFun hγlift t
  have hp : P.gluedUniversalCoverProjection x (γc 1) =
      P.gluedUniversalCoverProjection x a := (hlift 1).trans (h1.trans ha.symm)
  let Γ : Path a (γc 1) :=
    { toFun := fun t => γc t
      continuous_toFun := γc.continuous.comp continuous_subtype_val
      source' := hγ0
      target' := rfl }
  have hΓess : ¬ ((Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast
      rfl hp.symm).Homotopic (Path.refl (P.gluedUniversalCoverProjection x a)) := by
    subst y
    have heq : (Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast
        rfl hp.symm = ℓ := by
      apply Path.ext
      funext t
      exact (hlift t).trans (hℓ t).symm
    simpa only [heq] using hess
  have hne : a ≠ γc 1 := by
    intro heq
    exact hΓess ((P.gluedUniversalCover_projectedPath_nullhomotopic_iff x hp Γ).mpr heq.symm)
  have hγsmooth := P.gluedCurvatureBounded_lift_contMDiffOn_one x β γc hβ
    γc.continuous hlift
  have hlength := (P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2.pathELength_comp
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff
    (a := (0 : ℝ)) (b := (1 : ℝ)) hγsmooth
  have hfun : (P.gluedUniversalCoverProjection x) ∘ γc = β := funext hlift
  change Manifold.pathELength (modelWithCornersSelf ℝ ℂ)
    ((P.gluedUniversalCoverProjection x) ∘ γc) 0 1 =
    Manifold.pathELength (modelWithCornersSelf ℝ ℂ) γc 0 1 at hlength
  rw [hfun] at hlength
  have hle : edist (γc 0) (γc 1) ≤
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) γc 0 1 := by
    rw [(P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x).out]
    exact Manifold.riemannianEDist_le_pathELength hγsmooth rfl rfl zero_le_one
  rw [hγ0, ← hlength] at hle
  exact (P.gluedCurvatureBoundedFiberSystole_le_edist x a (γc 1) hp.symm hne).trans hle

/-- **Math.** Every essential loop that is `C¹` on its closed parameter
interval has actual smooth length at least the fiber systole. No regularity
is required outside the measured interval. -/
theorem gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential_on
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier)
    (β : ℝ → P.GluedCarrier)
    (hβ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 β
      (Icc (0 : ℝ) 1))
    (ℓ : Path y y) (hℓ : ∀ t : I, ℓ t = β t)
    (hess : ¬ ℓ.Homotopic (Path.refl y)) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
    P.gluedCurvatureBoundedFiberSystole x ≤
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) β 0 1 := by
  let : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
  have hext : EqOn (ℓ.extend : ℝ → P.GluedCarrier) β (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (ℓ.extend_apply ht).trans (hℓ ⟨t, ht⟩)
  have hsmooth : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1
      (ℓ.extend : ℝ → P.GluedCarrier) (Icc (0 : ℝ) 1) := hβ.congr hext
  have h := P.gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential_continuous
    x y ℓ.extend hsmooth ℓ.continuous_extend ℓ (fun t => (ℓ.extend_extends' t).symm) hess
  exact h.trans_eq (Manifold.pathELength_congr hext)

/-- **Math.** The global `C¹` specialization of the interval-admissible
essential-loop length bound. -/
theorem gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier)
    (β : ℝ → P.GluedCarrier)
    (hβ : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 β)
    (ℓ : Path y y) (hℓ : ∀ t : I, ℓ t = β t)
    (hess : ¬ ℓ.Homotopic (Path.refl y)) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
    P.gluedCurvatureBoundedFiberSystole x ≤
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) β 0 1 :=
  P.gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential_on
    x y β hβ.contMDiffOn ℓ hℓ hess

/-- **Math.** Every essential continuous loop pays the actual smooth fiber
systole in metric variation. Actual local isometry preserves its continuous
lift's variation, so differentiability and finite variation are unnecessary. -/
theorem gluedCurvatureBoundedFiberSystole_le_eVariationOn_of_essential
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier)
    (ℓ : Path y y) (hess : ¬ ℓ.Homotopic (Path.refl y)) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    P.gluedCurvatureBoundedFiberSystole x ≤ eVariationOn ℓ univ := by
  let := P.gluedCurvatureBoundedIntrinsicMetricSpace
  let := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  obtain ⟨a, ha⟩ := P.gluedUniversalCoverProjection_surjective x y
  subst y
  let Γ := P.gluedUniversalCoverPathLift x a ℓ
  have h0 : Γ 0 = a := P.gluedUniversalCoverPathLift_zero x a ℓ
  have hp : P.gluedUniversalCoverProjection x (Γ 1) =
      P.gluedUniversalCoverProjection x a :=
    (P.gluedUniversalCoverProjection_pathLift x a ℓ 1).trans ℓ.target
  have hne : a ≠ Γ 1 := by
    intro heq
    exact hess ((P.gluedUniversalCoverLoopLift_one_eq_iff x a ℓ).mp heq.symm)
  have hfun : P.gluedUniversalCoverProjection x ∘ Γ = ℓ :=
    funext (P.gluedUniversalCoverProjection_pathLift x a ℓ)
  have hvar := P.gluedCurvatureBoundedUniversalCoverProjection_eVariationOn x Γ Γ.continuous
  rw [hfun] at hvar
  have hcost := eVariationOn.edist_le Γ (mem_univ (0 : I)) (mem_univ (1 : I))
  rw [h0] at hcost
  exact (P.gluedCurvatureBoundedFiberSystole_le_edist x a (Γ 1) hp.symm hne).trans
    (hcost.trans_eq hvar.symm)

/-- **Math.** The actual smooth metric has an essential length-minimizing
loop given by a `C∞` geodesic segment on `ℝ` with equal endpoints at `0,1`.
This does not yet assert matching endpoint jets or a periodic parametrization. -/
theorem exists_gluedCurvatureBounded_systolic_loop
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
    ∃ (y : P.GluedCarrier) (β : ℝ → P.GluedCarrier) (ℓ : Path y y),
      ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) ∞ β ∧
      Geodesic.IsGeodesic P.gluedCurvatureBoundedSmoothRiemannianMetric β ∧
      β 0 = y ∧ β 1 = y ∧ (∀ t : I, ℓ t = β t) ∧
      ¬ ℓ.Homotopic (Path.refl y) ∧
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) β 0 1 =
        ENNReal.ofReal (P.gluedCurvatureBoundedFiberSystole x).toReal := by
  let := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  let : CompleteSpace (P.basedTopologicalUniversalCover x) :=
    P.gluedCurvatureBoundedUniversalCoverMetricSpace_complete x
  let metric := P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x
  let hg := P.gluedCurvatureBoundedUniversalCoverMetricSpace_isRiemannianDist x
  let : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type) := ⟨metric.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
  obtain ⟨a, b, hp, hne, hdist⟩ :=
    P.exists_gluedCurvatureBoundedFiberSystole_toReal_attaining_pair x hn hsum
  obtain ⟨v, hv⟩ := (P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x a).surjective b
  change P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph x a v = b at hv
  have hvexp : P.gluedCurvatureBoundedUniversalCoverExpMap x a
      (Riemannian.HadamardModel.toModel v) = b :=
    (P.gluedCurvatureBoundedUniversalCoverHadamardDiffeomorph_apply x a v).symm.trans hv
  let γ := Geodesic.globalGeodesic metric hg a (Riemannian.HadamardModel.toModel v)
  have hγ0 : γ 0 = a := Geodesic.globalGeodesic_zero metric hg a _
  have hγ1 : γ 1 = b := by
    calc
      γ 1 = Exponential.expMapGlobal metric hg a (Riemannian.HadamardModel.toModel v) :=
        (Exponential.expMapGlobal_def metric hg a _).symm
      _ = P.gluedCurvatureBoundedUniversalCoverExpMap x a
          (Riemannian.HadamardModel.toModel v) := rfl
      _ = b := hvexp
  have hγc : Continuous γ := Geodesic.continuous_globalGeodesic metric hg a _
  have hγgeo : Geodesic.IsGeodesic metric γ := Geodesic.isGeodesic_globalGeodesic metric hg a _
  have hray (t : ℝ) : P.gluedCurvatureBoundedUniversalCoverExpMap x a
      (t • Riemannian.HadamardModel.toModel v) = γ t :=
    Exponential.expMapGlobal_smul metric hg a _ t
  have hline : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) ∞
      (fun t : ℝ => t • Riemannian.HadamardModel.toModel v) :=
    contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
  have hγsmooth : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) ∞ γ := by
    simpa only [Function.comp_def, hray] using
      (P.gluedCurvatureBoundedUniversalCoverExpMap_contMDiff x a).comp hline
  let β : ℝ → P.GluedCarrier := P.gluedUniversalCoverProjection x ∘ γ
  let Γ : Path a b :=
    { toFun := fun t => γ t
      continuous_toFun := hγc.comp continuous_subtype_val
      source' := hγ0
      target' := hγ1 }
  let ℓ : Path (P.gluedUniversalCoverProjection x a) (P.gluedUniversalCoverProjection x a) :=
    (Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast rfl hp
  have hβsmooth : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) ∞ β :=
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff.comp hγsmooth
  have hpres : DCPreservesMetric metric P.gluedCurvatureBoundedSmoothRiemannianMetric
      (P.gluedUniversalCoverProjection x) := by
    intro s u w
    exact ((P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2.inner_mfderiv s u w).symm
  have hβgeo : Geodesic.IsGeodesic P.gluedCurvatureBoundedSmoothRiemannianMetric β :=
    Geodesic.isGeodesic_comp_of_isLocalDiffeomorph
      (P.gluedUniversalCoverProjection_isLocalDiffeomorph x) metric
      P.gluedCurvatureBoundedSmoothRiemannianMetric hpres hγc hγgeo
  have hess : ¬ ℓ.Homotopic (Path.refl (P.gluedUniversalCoverProjection x a)) :=
    fun h => hne ((P.gluedUniversalCover_projectedPath_nullhomotopic_iff x hp.symm Γ).mp h).symm
  have hlength := (P.gluedCurvatureBoundedUniversalCover_isRiemannianCovering x).2.pathELength_comp
    (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff
    (a := (0 : ℝ)) (b := (1 : ℝ)) (hγsmooth.of_le (by simp)).contMDiffOn
  have hsrc : γ 0 ∈ (chartAt ℂ a).source := by rw [hγ0]; exact mem_chart_source ℂ a
  have hspeed := (hγgeo 0).speedSq_eq_chartMetricInner_of_mem_source hγc.continuousAt hsrc
  have hvderiv := (Geodesic.hasDerivAt_chartReading_globalGeodesic metric hg a
    (Riemannian.HadamardModel.toModel v)).deriv
  rw [hvderiv] at hspeed
  simp only [Geodesic.chartReading, hγ0] at hspeed
  have hcoverlength := (hγgeo.isGeodesicOn univ).pathELength_eq isOpen_univ
    isPreconnected_univ hγc.continuousOn (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
  have hexpdist := P.gluedCurvatureBoundedUniversalCoverExpMap_dist_eq_initialLength x a
    (Riemannian.HadamardModel.toModel v)
  have hvdist := (congrArg (dist a) hvexp.symm).trans hexpdist
  rw [hdist] at hvdist
  rw [hspeed, ← hvdist] at hcoverlength
  refine ⟨P.gluedUniversalCoverProjection x a, β, ℓ, hβsmooth, hβgeo,
    congrArg (P.gluedUniversalCoverProjection x) hγ0,
    (congrArg (P.gluedUniversalCoverProjection x) hγ1).trans hp.symm,
    fun _ => rfl, hess, ?_⟩
  exact hlength.trans (by simpa only [sub_zero, one_mul, mul_one] using hcoverlength)

/-- **Math.** The same actual essential smooth geodesic segment realizes
metric variation as well as tangent-integral length, hence minimizes length
among all continuous essential loops, not only smooth competitors. -/
theorem exists_gluedCurvatureBounded_systolic_loop_variation
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) :
    letI := P.gluedCurvatureBoundedIntrinsicMetricSpace
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
    ∃ (y : P.GluedCarrier) (β : ℝ → P.GluedCarrier) (ℓ : Path y y),
      ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) ∞ β ∧
      Geodesic.IsGeodesic P.gluedCurvatureBoundedSmoothRiemannianMetric β ∧
      β 0 = y ∧ β 1 = y ∧ (∀ t : I, ℓ t = β t) ∧
      ¬ ℓ.Homotopic (Path.refl y) ∧
      Manifold.pathELength (modelWithCornersSelf ℝ ℂ) β 0 1 =
        P.gluedCurvatureBoundedFiberSystole x ∧
      eVariationOn ℓ univ = P.gluedCurvatureBoundedFiberSystole x := by
  let := P.gluedCurvatureBoundedIntrinsicMetricSpace
  let : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type) := ⟨P.gluedCurvatureBoundedSmoothRiemannianMetric.toRiemannianMetric⟩
  let : IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) P.GluedCarrier :=
    P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist
  obtain ⟨y, β, ℓ, hβ, hgeo, h0, h1, hℓ, hess, hlength⟩ :=
    P.exists_gluedCurvatureBounded_systolic_loop x hn hsum
  rw [ENNReal.ofReal_toReal (P.gluedCurvatureBoundedFiberSystole_lt_top x hn hsum).ne] at hlength
  have hparam : eVariationOn (fun t : I => β t) univ =
      eVariationOn β (Icc (0 : ℝ) 1) := by
    simpa only [Function.comp_def, image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn β
        (t := univ) (fun t : I => (t : ℝ)) (fun _ _ _ _ h => h)
  have hℓfun : (ℓ : I → P.GluedCarrier) = fun t : I => β t := funext hℓ
  have hupper : eVariationOn ℓ univ ≤ P.gluedCurvatureBoundedFiberSystole x := by
    rw [hℓfun, hparam]
    exact (OpenGA.HopfRinow.eVariationOn_le_pathELength
      (hβ.of_le (by simp)).contMDiffOn).trans_eq hlength
  have hlower := P.gluedCurvatureBoundedFiberSystole_le_eVariationOn_of_essential x y ℓ hess
  exact ⟨y, β, ℓ, hβ, hgeo, h0, h1, hℓ, hess, hlength, le_antisymm hupper hlower⟩

#print axioms gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential
#print axioms gluedCurvatureBoundedFiberSystole_le_pathELength_of_essential_on
#print axioms gluedCurvatureBoundedFiberSystole_le_eVariationOn_of_essential
#print axioms exists_gluedCurvatureBounded_systolic_loop
#print axioms exists_gluedCurvatureBounded_systolic_loop_variation

end SystolicGrowth.ExerciseGluingPreparation

end
