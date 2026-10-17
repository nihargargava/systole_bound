module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedPolarDisk
public import Geometry.GluingCurvatureBoundedAreaCharts
public import Geometry.ExponentialGlobalAngularComparison
public import Geometry.LocalMeasureComparison
public import Geometry.HyperbolicPolarStripIntegral

@[expose] public section

/-!
# Actual smooth glued disk-area lower bound

The genuine injective polar strip is measured by the already constructed
native ODE area. Local selected-chart determinant identities and actual
angular Jacobi comparison give hyperbolic area domination.
-/

open Set Bundle Manifold Riemannian MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

/-- **Math.** The actual principal polar strip in complex radius/angle coordinates. -/
def complexExponentialPolarStrip (R : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo 0 R ∧ z.im ∈ Ioo (-Real.pi) Real.pi}

theorem complexExponentialPolarStrip_isOpen (R : ℝ) :
    IsOpen (complexExponentialPolarStrip R) :=
  (exponentialPolarStrip_isOpen R).preimage Complex.equivRealProdCLM.continuous

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance (P : ExerciseGluingPreparation C g n genera X) :
    MetricSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace

local instance (P : ExerciseGluingPreparation C g n genera X) :
    CompleteSpace P.GluedCarrier := P.gluedCurvatureBoundedIntrinsicMetricSpace_complete

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The actual projected exponential polar point in complex
radius/angle coordinates; the point map is unchanged. -/
def gluedCurvatureBoundedComplexPolarPoint
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ) (z : ℂ) : P.GluedCarrier :=
  P.gluedCurvatureBoundedPolarPoint x q e (z.re, z.im)

/-- **Math.** The actual complex principal strip embeds openly at the
unchanged half-systole cutoff. -/
theorem gluedCurvatureBoundedComplexPolarPoint_isOpenEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ)
    (hR : 2 * R ≤ targetSystole C g) :
    Topology.IsOpenEmbedding ((complexExponentialPolarStrip R).domRestrict
      (P.gluedCurvatureBoundedComplexPolarPoint x q e)) := by
  let h : complexExponentialPolarStrip R ≃ₜ exponentialPolarStrip R :=
    Complex.equivRealProdCLM.toHomeomorph.sets rfl
  exact (P.gluedCurvatureBoundedPolarPoint_isOpenEmbedding x q e he R hR).comp
    h.isOpenEmbedding

/-- **Math.** Actual cover-fiber separation, at any bound `L`, gives an
open complex polar strip at the unchanged radius condition `2R ≤ L`. -/
theorem gluedCurvatureBoundedComplexPolarPoint_isOpenEmbedding_of_fiber_gap
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
    Topology.IsOpenEmbedding ((complexExponentialPolarStrip R).domRestrict
      (P.gluedCurvatureBoundedComplexPolarPoint x q e)) := by
  let h : complexExponentialPolarStrip R ≃ₜ exponentialPolarStrip R :=
    Complex.equivRealProdCLM.toHomeomorph.sets rfl
  exact (P.gluedCurvatureBoundedPolarPoint_isOpenEmbedding_of_fiber_gap
    x q e he R L hgap hR).comp h.isOpenEmbedding

/-- **Math.** Around each point of the genuine polar strip, actual native
surface area dominates the hyperbolic radial density on every measurable
sector lying in the selected neighborhood. -/
theorem exists_local_gluedCurvatureBoundedPolar_area_domination_of_fiber_gap
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
    (hR : 2 * R ≤ L) (z : ℂ) :
    ∃ W : Set P.GluedCarrier,
      P.gluedCurvatureBoundedComplexPolarPoint x q e z ∈ W ∧ IsOpen W ∧
      ∀ s : Set ℂ, MeasurableSet s → s ⊆ complexExponentialPolarStrip R →
        (∀ w ∈ s, P.gluedCurvatureBoundedComplexPolarPoint x q e w ∈ W) →
        ((volume : Measure ℂ).withDensity (fun w => ENNReal.ofReal (Real.sinh w.re))) s ≤
          P.gluedCurvatureBoundedAreaMeasure
            (P.gluedCurvatureBoundedComplexPolarPoint x q e '' s) := by
  let F := P.gluedCurvatureBoundedComplexPolarPoint x q e
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let hg := P.gluedCurvatureBoundedIntrinsicMetricSpace_isRiemannianDist
  let p := P.gluedUniversalCoverProjection x q
  let ζ := F z
  obtain ⟨W, hzW, hW, hWsrc, harea⟩ :=
    P.exists_local_gluedCurvatureBoundedArea_selected_chart ζ
  refine ⟨W, hzW, hW, ?_⟩
  intro s hs hsub hFW
  have hpoint (w : ℂ) : F w = Exponential.expMapGlobal metric hg p
      (w.re • exponentialPolarUnit e w.im) :=
    P.gluedCurvatureBoundedPolarPoint_eq_baseExpMap x q e (w.re, w.im)
  have hsrc : ∀ w ∈ s, Exponential.expMapGlobal metric hg p
      (w.re • exponentialPolarUnit e w.im) ∈ (chartAt ℂ ζ).source := by
    intro w hw
    rw [← hpoint w]
    exact hWsrc (hFW w hw)
  have hFemb := P.gluedCurvatureBoundedComplexPolarPoint_isOpenEmbedding_of_fiber_gap
    x q e he R L hgap hR
  have hFinj : InjOn F s := by
    intro a ha b hb hab
    have h := hFemb.injective
      (show (complexExponentialPolarStrip R).domRestrict F ⟨a, hsub ha⟩ =
        (complexExponentialPolarStrip R).domRestrict F ⟨b, hsub hb⟩ from hab)
    exact congrArg Subtype.val h
  let A := globalExponentialComplexPolarChart metric hg p ζ e
  have hAeq (w : ℂ) : A w = (chartAt ℂ ζ) (F w) := by
    rw [hpoint w]
    rfl
  have hAinj : InjOn A s := by
    intro a ha b hb hab
    apply hFinj ha hb
    apply (chartAt ℂ ζ).injOn (hWsrc (hFW a ha)) (hWsrc (hFW b hb))
    simpa only [hAeq] using hab
  have hAD : ∀ w ∈ s, HasFDerivWithinAt A (fderiv ℝ A w) s w := by
    intro w hw
    exact (globalExponentialComplexPolarChart_fderiv_columns metric hg p ζ e w
      (hsrc w hw)).1.hasFDerivAt.hasFDerivWithinAt
  have hAs : MeasurableSet (A '' s) := measurable_image_of_fderivWithin hs hAD hAinj
  have hAW : A '' s ⊆ (chartAt ℂ ζ) '' W := by
    rintro y ⟨w, hw, rfl⟩
    exact ⟨F w, hFW w hw, (hAeq w).symm⟩
  have hback : (chartAt ℂ ζ).symm '' (A '' s) = F '' s := by
    rw [image_image]
    apply image_congr
    intro w hw
    rw [hAeq, (chartAt ℂ ζ).left_inv (hWsrc (hFW w hw))]
  have hμ : P.gluedCurvatureBoundedAreaMeasure (F '' s) =
      ∫⁻ w in s, ENNReal.ofReal
        (Real.sqrt (globalExponentialPolarGram metric hg p ζ e w.re w.im).det) := by
    rw [← hback, harea (A '' s) hAs hAW]
    exact nativeComplexChartMetricArea_image_globalExponentialPolar metric hg p ζ e
      hs hsrc hAinj
  have hebase : ∀ i j : Fin 2, chartMetricInner metric p
      (extChartAt (modelWithCornersSelf ℝ ℂ) p p) (e i) (e j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    exact (P.gluedCurvatureBoundedCover_initialMetric_eq_base x q (e i) (e j)).symm.trans
      (he i j)
  rw [withDensity_apply _ hs, hμ]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hs] with w hw
  exact ENNReal.ofReal_le_ofReal
    (sinh_le_globalExponentialPolar_sqrt_det metric hg p ζ e w.im w.re
      (hsub hw).1.1 hebase P.gluedCurvatureBounded_curvatureOperatorAt_lower_bound
      (hsrc w hw))

/-- **Math.** The target-systole specialization preserves the actual
selected-neighborhood area domination contract. -/
theorem exists_local_gluedCurvatureBoundedPolar_area_domination
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ)
    (hR : 2 * R ≤ targetSystole C g) (z : ℂ) :
    ∃ W : Set P.GluedCarrier,
      P.gluedCurvatureBoundedComplexPolarPoint x q e z ∈ W ∧ IsOpen W ∧
      ∀ s : Set ℂ, MeasurableSet s → s ⊆ complexExponentialPolarStrip R →
        (∀ w ∈ s, P.gluedCurvatureBoundedComplexPolarPoint x q e w ∈ W) →
        ((volume : Measure ℂ).withDensity (fun w => ENNReal.ofReal (Real.sinh w.re))) s ≤
          P.gluedCurvatureBoundedAreaMeasure
            (P.gluedCurvatureBoundedComplexPolarPoint x q e '' s) := by
  apply P.exists_local_gluedCurvatureBoundedPolar_area_domination_of_fiber_gap
    x q e he R (targetSystole C g) ?_ hR z
  intro a b hp hne
  exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hp hne

/-- **Math.** The actual native area pulled back through the embedded polar
strip dominates the hyperbolic density globally. Local chart formulas are
assembled by a countable measurable partition, not assumed globally. -/
theorem gluedCurvatureBoundedPolarAreaMeasure_ge_hyperbolic_of_fiber_gap
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
    (((volume : Measure ℂ).comap
      (Subtype.val : complexExponentialPolarStrip R → ℂ)).withDensity
        (fun z => ENNReal.ofReal (Real.sinh z.val.re))) ≤
      P.gluedCurvatureBoundedAreaMeasure.comap
        ((complexExponentialPolarStrip R).domRestrict
          (P.gluedCurvatureBoundedComplexPolarPoint x q e)) := by
  let T := complexExponentialPolarStrip R
  let F := T.domRestrict (P.gluedCurvatureBoundedComplexPolarPoint x q e)
  let ν := ((volume : Measure ℂ).comap (Subtype.val : T → ℂ)).withDensity
    (fun z => ENNReal.ofReal (Real.sinh z.val.re))
  let ρ := P.gluedCurvatureBoundedAreaMeasure.comap F
  change ν ≤ ρ
  have hF := P.gluedCurvatureBoundedComplexPolarPoint_isOpenEmbedding_of_fiber_gap
    x q e he R L hgap hR
  have hFm : MeasurableEmbedding F := hF.measurableEmbedding
  have hval : MeasurableEmbedding (Subtype.val : T → ℂ) :=
    MeasurableEmbedding.subtype_coe (complexExponentialPolarStrip_isOpen R).measurableSet
  have hν : ν = ((volume : Measure ℂ).withDensity
      (fun w => ENNReal.ofReal (Real.sinh w.re))).comap (Subtype.val : T → ℂ) := by
    exact (gluingMeasure_comap_withDensity hval volume
      (fun w => ENNReal.ofReal (Real.sinh w.re))).symm
  apply measure_le_of_locally_le ν ρ
  intro z
  obtain ⟨W, hzW, hW, hlocal⟩ :=
    P.exists_local_gluedCurvatureBoundedPolar_area_domination_of_fiber_gap
      x q e he R L hgap hR z.val
  let U := F ⁻¹' W
  refine ⟨U, hW.preimage hF.continuous, hzW, ?_⟩
  intro t ht htU
  have hA : MeasurableSet ((Subtype.val : T → ℂ) '' t) := hval.measurableSet_image.mpr ht
  have hAT : (Subtype.val : T → ℂ) '' t ⊆ T := by
    rintro w ⟨v, _, rfl⟩
    exact v.property
  have hAW : ∀ w ∈ (Subtype.val : T → ℂ) '' t,
      P.gluedCurvatureBoundedComplexPolarPoint x q e w ∈ W := by
    rintro w ⟨v, hv, rfl⟩
    exact htU hv
  have h := hlocal ((Subtype.val : T → ℂ) '' t) hA hAT hAW
  rw [hν, hval.comap_apply, hFm.comap_apply]
  simpa only [image_image, Function.comp_def, F, Set.domRestrict_apply] using h

/-- **Math.** The target-systole specialization of actual polar measure
domination uses the already proved native cover fiber separation. -/
theorem gluedCurvatureBoundedPolarAreaMeasure_ge_hyperbolic
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ)
    (hR : 2 * R ≤ targetSystole C g) :
    (((volume : Measure ℂ).comap
      (Subtype.val : complexExponentialPolarStrip R → ℂ)).withDensity
        (fun z => ENNReal.ofReal (Real.sinh z.val.re))) ≤
      P.gluedCurvatureBoundedAreaMeasure.comap
        ((complexExponentialPolarStrip R).domRestrict
          (P.gluedCurvatureBoundedComplexPolarPoint x q e)) := by
  apply P.gluedCurvatureBoundedPolarAreaMeasure_ge_hyperbolic_of_fiber_gap
    x q e he R (targetSystole C g) ?_ hR
  intro a b hp hne
  exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hp hne

/-- **Math.** The genuine smooth ball at the half-systole cutoff has at
least hyperbolic area. Only its embedded principal polar sector is used;
no assertion about the omitted cut ray or its area is needed. -/
theorem gluedCurvatureBounded_ball_area_lower_bound_of_frame_of_fiber_gap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R L : ℝ) (hR0 : 0 ≤ R)
    (hgap : letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
      ∀ a b : P.basedTopologicalUniversalCover x,
        P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
          a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) :
    ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) ≤
      P.gluedCurvatureBoundedAreaMeasure
        (Metric.ball (P.gluedUniversalCoverProjection x q) R) := by
  have h := P.gluedCurvatureBoundedPolarAreaMeasure_ge_hyperbolic_of_fiber_gap
    x q e he R L hgap hR
  have htotal := Measure.le_iff'.mp h univ
  have hmass : (((volume : Measure ℂ).comap
      (Subtype.val : complexExponentialPolarStrip R → ℂ)).withDensity
        (fun z => ENNReal.ofReal (Real.sinh z.val.re))) univ =
        ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) :=
    hyperbolicPolarPrincipalStrip_withDensity_univ hR0
  rw [hmass] at htotal
  have hF := P.gluedCurvatureBoundedComplexPolarPoint_isOpenEmbedding_of_fiber_gap
    x q e he R L hgap hR
  rw [hF.measurableEmbedding.comap_apply, image_univ] at htotal
  refine htotal.trans (measure_mono ?_)
  rintro y ⟨z, rfl⟩
  exact P.gluedCurvatureBoundedPolarPoint_mem_ball x q e he R z.property

/-- **Math.** The original target-cutoff area statement is the direct
specialization of the actual geometric fiber-gap area theorem. -/
theorem gluedCurvatureBounded_ball_area_lower_bound_of_frame
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (e : Fin 2 → ℂ)
    (he : ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : 2 * R ≤ targetSystole C g) :
    ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) ≤
      P.gluedCurvatureBoundedAreaMeasure
        (Metric.ball (P.gluedUniversalCoverProjection x q) R) := by
  apply P.gluedCurvatureBounded_ball_area_lower_bound_of_frame_of_fiber_gap
    x q e he R (targetSystole C g) hR0 ?_ hR
  intro a b hp hne
  exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hp hne

/-- **Math.** The ball-area lower bound has no supplied frame, area formula,
or disk embedding: all three are constructed from the actual smooth metric. -/
theorem gluedCurvatureBounded_ball_area_lower_bound_of_fiber_gap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R L : ℝ) (hR0 : 0 ≤ R)
    (hgap : letI := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
      ∀ a b : P.basedTopologicalUniversalCover x,
        P.gluedUniversalCoverProjection x a = P.gluedUniversalCoverProjection x b →
          a ≠ b → L ≤ dist a b)
    (hR : 2 * R ≤ L) :
    ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) ≤
      P.gluedCurvatureBoundedAreaMeasure
        (Metric.ball (P.gluedUniversalCoverProjection x q) R) := by
  let := P.gluedCurvatureBoundedUniversalCoverMetricSpace x
  have hframe : ∃ e : Fin 2 → ℂ, ∀ i j : Fin 2, chartMetricInner
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
      (extChartAt (modelWithCornersSelf ℝ ℂ) q q) (e i) (e j) =
        if i = j then (1 : ℝ) else 0 := by
    obtain ⟨e, horth⟩ := Jacobi.exists_chartOrthonormalBasis_self
      (P.gluedCurvatureBoundedUniversalCoverRiemannianMetric x) q
    let f : Fin 2 ≃ Fin (Module.finrank ℝ ℂ) :=
      (finCongr Complex.finrank_real_complex).symm
    refine ⟨fun i => e (f i), ?_⟩
    intro i j
    simpa only [f.apply_eq_iff_eq] using horth (f i) (f j)
  obtain ⟨e, he⟩ := hframe
  exact P.gluedCurvatureBounded_ball_area_lower_bound_of_frame_of_fiber_gap
    x q e he R L hR0 hgap hR

/-- **Math.** The ball-area target specialization constructs its initial
orthonormal frame and uses the proved target fiber separation. -/
theorem gluedCurvatureBounded_ball_area_lower_bound
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : 2 * R ≤ targetSystole C g) :
    ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) ≤
      P.gluedCurvatureBoundedAreaMeasure
        (Metric.ball (P.gluedUniversalCoverProjection x q) R) := by
  apply P.gluedCurvatureBounded_ball_area_lower_bound_of_fiber_gap
    x q R (targetSystole C g) hR0 ?_ hR
  intro a b hp hne
  exact P.targetSystole_le_gluedCurvatureBoundedUniversalCover_dist_of_same_fiber_ne
    x a b hp hne

/-- **Math.** Every actual smooth ball at radius at most half the target
systole has the hyperbolic lower bound for the constructed ODE area measure. -/
theorem gluedCurvatureBoundedAreaMeasure_ball_lower_bound
    (P : ExerciseGluingPreparation C g n genera X) (a : P.GluedCarrier)
    (R : ℝ) (hR0 : 0 ≤ R) (hR : 2 * R ≤ targetSystole C g) :
    ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) ≤
      P.gluedCurvatureBoundedAreaMeasure (Metric.ball a R) := by
  obtain ⟨q, hq⟩ := P.gluedUniversalCoverProjection_surjective a a
  simpa only [hq] using P.gluedCurvatureBounded_ball_area_lower_bound a q R hR0 hR

#print axioms gluedCurvatureBoundedComplexPolarPoint_isOpenEmbedding
#print axioms exists_local_gluedCurvatureBoundedPolar_area_domination
#print axioms gluedCurvatureBoundedPolarAreaMeasure_ge_hyperbolic
#print axioms gluedCurvatureBounded_ball_area_lower_bound_of_frame
#print axioms gluedCurvatureBounded_ball_area_lower_bound
#print axioms gluedCurvatureBoundedAreaMeasure_ball_lower_bound
#print axioms gluedCurvatureBounded_ball_area_lower_bound_of_fiber_gap

end ExerciseGluingPreparation

end SystolicGrowth

end
