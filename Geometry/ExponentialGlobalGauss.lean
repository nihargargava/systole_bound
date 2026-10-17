module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ExponentialGlobalPolarMetric
public import Geometry.JacobiRadialPairing
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Exponential.CInftyGlobal

@[expose] public section

/-!
# Global exponential Gauss lemma and polar Gram tensor

The actual global exponential differential satisfies the Gauss pairing
identity. The proof constructs manifold Jacobi fields on the entire segment
and uses their intrinsic radial pairing, with no chart containing the ray.
-/

open Set Bundle Manifold Riemannian
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M]

/-- **Math.** One terminal chart and one actual global exponential differential
simultaneously represent every initialized Jacobi field and satisfy the
global Gauss pairing. This pins angular comparison to the same differential. -/
theorem exists_globalExponentialGauss_jacobi
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) (v : E) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ
        (Exponential.expMapGlobal (I := I) g hg p w)) D v ∧
      (∀ J DJ : ℝ → E,
        Jacobi.IsJacobiFieldAlongOn (I := I) g
          (Geodesic.globalGeodesic (I := I) g hg p v) J DJ 0 1 →
        J 0 = 0 →
        D (DJ 0) = Jacobi.chartVectorRep (I := I)
          (Geodesic.globalGeodesic (I := I) g hg p v) ζ J 1) ∧
      (∀ Z : E,
        chartMetricInner g ζ
          (extChartAt I ζ (Exponential.expMapGlobal (I := I) g hg p v))
          (D v) (D Z) = chartMetricInner g p (extChartAt I p p) v Z) := by
  obtain ⟨α, ζ, D, _, hζ, hD, htransport⟩ :=
    Jacobi.hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  let γ := Geodesic.globalGeodesic (I := I) g hg p v
  have hγ0 : γ 0 = p := Geodesic.globalGeodesic_zero g hg p v
  have hc : Continuous γ := Geodesic.continuous_globalGeodesic g hg p v
  have hgeo : Geodesic.IsGeodesicOn (I := I) g γ (Icc 0 1) :=
    fun s _ => Geodesic.isGeodesic_globalGeodesic g hg p v s
  have hγc : ∀ s ∈ Icc 0 1, ContinuousAt γ s := fun _ _ => hc.continuousAt
  have ht0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have ht1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
  have hsrc : γ 1 ∈ (chartAt H ζ).source := hζ
  have hD' : HasFDerivAt (fun w : E => extChartAt I ζ
      (Exponential.expMapGlobal (I := I) g hg p w)) D ((1 : ℝ) • v) := by
    simpa only [one_smul] using hD
  have hrad := hD'.comp_hasDerivAt (1 : ℝ) ((hasDerivAt_id (1 : ℝ)).smul_const v)
  have hray (s : ℝ) : Exponential.expMapGlobal (I := I) g hg p (s • v) = γ s :=
    Exponential.expMapGlobal_smul (I := I) g hg p v s
  have hrad' : HasDerivAt (fun s => extChartAt I ζ (γ s)) (D v) 1 := by
    simpa only [Function.comp_def, id_eq, one_smul, hray] using hrad
  have hv0 : mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) = v := by
    rw [(hgeo 0 ht0).mfderiv_apply_one hc.continuousAt]
    have hv := (Geodesic.hasDerivAt_chartReading_globalGeodesic g hg p v).deriv
    change deriv (fun s => extChartAt I (γ 0) (γ s)) 0 = v
    rw [hγ0]
    exact hv
  refine ⟨ζ, D, hζ, hD, htransport, ?_⟩
  intro Z
  obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
    Jacobi.exists_isJacobiFieldAlongOn (I := I) zero_lt_one hgeo hγc
      (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
  have hDZ : D Z = Jacobi.chartVectorRep (I := I) γ ζ J 1 := by
    rw [← hDJ0]
    exact htransport J DJ hJ hJ0
  have hpair := jacobiRadialPairing_eq_time_mul_initial g hJ hgeo hγc hJ0 ht1
  rw [one_mul, hDJ0, hv0] at hpair
  have hrep := Jacobi.metricInner_eq_chartMetricInner_rep g hsrc J
    (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
  rw [chartVectorRep_geodesic_velocity_eq_deriv
    (hgeo 1 ht1) hc.continuousAt hsrc, hrad'.deriv, ← hDZ] at hrep
  change chartMetricInner g ζ (extChartAt I ζ (γ 1)) (D v) (D Z) = _
  rw [chartMetricInner_symm, ← hrep, hpair]
  rw [hγ0, chartMetricInner_extChartAt_eq_metricInner g p (mem_chart_source H p),
    trivializationAt_symm_self, trivializationAt_symm_self, g.metricInner_comm]

/-- **Math.** The global exponential differential preserves radial pairings
at every initial vector. Only the endpoint is read in its chosen chart. -/
theorem exists_globalExponentialGauss
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) (v : E) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ
        (Exponential.expMapGlobal (I := I) g hg p w)) D v ∧
      ∀ Z : E,
        chartMetricInner g ζ
          (extChartAt I ζ (Exponential.expMapGlobal (I := I) g hg p v))
          (D v) (D Z) = chartMetricInner g p (extChartAt I p p) v Z := by
  obtain ⟨ζ, D, hsrc, hD, _, hgauss⟩ := exists_globalExponentialGauss_jacobi g hg p v
  exact ⟨ζ, D, hsrc, hD, hgauss⟩

/-- **Math.** Reading the actual complete-manifold exponential map in a
terminal chart, with no restriction on the intermediate geodesic. -/
def globalExponentialChartMap (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p ζ : M) (w : E) : E :=
  extChartAt I ζ (Exponential.expMapGlobal (I := I) g hg p w)

/-- **Math.** The actual global exponential map in radial and angular parameters. -/
def globalExponentialPolarChart (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → E) (q : ℝ × ℝ) : E :=
  globalExponentialChartMap g hg p ζ (q.1 • exponentialPolarUnit e q.2)

/-- **Math.** Actual radial and angular differential images in the terminal chart. -/
def globalExponentialPolarFrame (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → E) (r θ : ℝ) (i : Fin 2) : E :=
  fderiv ℝ (globalExponentialChartMap g hg p ζ) (r • exponentialPolarUnit e θ)
    (if i = 0 then exponentialPolarUnit e θ else r • exponentialPolarNormal e θ)

/-- **Math.** The genuine metric Gram tensor of the global polar differential. -/
def globalExponentialPolarGram (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → E) (r θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => chartMetricInner g ζ (globalExponentialPolarChart g hg p ζ e (r, θ))
    (globalExponentialPolarFrame g hg p ζ e r θ i)
    (globalExponentialPolarFrame g hg p ζ e r θ j)

/-- **Math.** Metric length of the actual angular exponential differential. -/
def globalExponentialPolarAngularLength
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p ζ : M) (e : Fin 2 → E) (θ r : ℝ) : ℝ :=
  Real.sqrt (globalExponentialPolarGram g hg p ζ e r θ 1 1)

/-- **Math.** At every positive radius, a terminal chart gives the true polar
derivatives, diagonal warped metric, and angular-length area density of the
global exponential map. All Gauss identities are derived internally. -/
theorem exists_globalExponentialPolarMetric
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (r θ : ℝ) (hr : 0 < r) :
    ∃ ζ : M,
      Exponential.expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
        (chartAt H ζ).source ∧
      HasDerivAt (fun t => globalExponentialPolarChart g hg p ζ e (t, θ))
        (globalExponentialPolarFrame g hg p ζ e r θ 0) r ∧
      HasDerivAt (fun a => globalExponentialPolarChart g hg p ζ e (r, a))
        (globalExponentialPolarFrame g hg p ζ e r θ 1) θ ∧
      globalExponentialPolarGram g hg p ζ e r θ =
        gluingWarpedMetric (globalExponentialPolarAngularLength g hg p ζ e θ) (r, θ) ∧
      (globalExponentialPolarGram g hg p ζ e r θ).det =
        globalExponentialPolarGram g hg p ζ e r θ 1 1 ∧
      Real.sqrt (globalExponentialPolarGram g hg p ζ e r θ).det =
        globalExponentialPolarAngularLength g hg p ζ e θ r := by
  let U := exponentialPolarUnit e θ
  let N := exponentialPolarNormal e θ
  obtain ⟨ζ, D, hζ, hD, hgauss⟩ := exists_globalExponentialGauss g hg p (r • U)
  let f := globalExponentialChartMap g hg p ζ
  change HasFDerivAt f D (r • U) at hD
  have hDf : fderiv ℝ f (r • U) = D := hD.fderiv
  have hrad : HasDerivAt (fun t => globalExponentialPolarChart g hg p ζ e (t, θ))
      (globalExponentialPolarFrame g hg p ζ e r θ 0) r := by
    change HasDerivAt (fun t => f (t • U)) (fderiv ℝ f (r • U) U) r
    rw [hDf]
    simpa only [Function.comp_def, id_eq, one_smul] using
      hD.comp_hasDerivAt r ((hasDerivAt_id r).smul_const U)
  have hang : HasDerivAt (fun a => globalExponentialPolarChart g hg p ζ e (r, a))
      (globalExponentialPolarFrame g hg p ζ e r θ 1) θ := by
    change HasDerivAt (fun a => f (r • exponentialPolarUnit e a))
      (fderiv ℝ f (r • U) (r • N)) θ
    rw [hDf]
    simpa only [Function.comp_def, Pi.smul_apply] using
      hD.comp_hasDerivAt θ ((exponentialPolarUnit_hasDerivAt e θ).const_smul r)
  have hrot := exponentialPolarDirections_chartMetric g p e he θ
  have h00 : globalExponentialPolarGram g hg p ζ e r θ 0 0 = 1 := by
    have h := hgauss U
    simp only [map_smul, chartMetricInner_smul_left] at h
    rw [show chartMetricInner g p (extChartAt I p p) U U = 1 from hrot.1,
      mul_one] at h
    have hcancel := mul_left_cancel₀ hr.ne' (h.trans (mul_one r).symm)
    change chartMetricInner g ζ (f (r • U))
      (fderiv ℝ f (r • U) U) (fderiv ℝ f (r • U) U) = 1
    rw [hDf]
    exact hcancel
  have h01 : globalExponentialPolarGram g hg p ζ e r θ 0 1 = 0 := by
    have h := hgauss (r • N)
    have hright : chartMetricInner g p (extChartAt I p p) (r • U) (r • N) = 0 := by
      simp only [chartMetricInner_smul_left, chartMetricInner_smul_right,
        show chartMetricInner g p (extChartAt I p p) U N = 0 from hrot.2.1, mul_zero]
    rw [hright, map_smul, chartMetricInner_smul_left] at h
    have hz := (mul_eq_zero.mp h).resolve_left hr.ne'
    change chartMetricInner g ζ (f (r • U))
      (fderiv ℝ f (r • U) U) (fderiv ℝ f (r • U) (r • N)) = 0
    rw [hDf]
    exact hz
  have h10 : globalExponentialPolarGram g hg p ζ e r θ 1 0 = 0 := by
    rw [globalExponentialPolarGram, chartMetricInner_symm]
    exact h01
  have h11 : 0 ≤ globalExponentialPolarGram g hg p ζ e r θ 1 1 := by
    exact chartMetricInner_self_nonneg_of_mem_target g ζ
      ((extChartAt I ζ).map_source (by rw [extChartAt_source]; exact hζ)) _
  have hmetric : globalExponentialPolarGram g hg p ζ e r θ =
      gluingWarpedMetric (globalExponentialPolarAngularLength g hg p ζ e θ) (r, θ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gluingWarpedMetric, globalExponentialPolarAngularLength,
        h00, h01, h10, Real.sq_sqrt h11]
  have hdet : (globalExponentialPolarGram g hg p ζ e r θ).det =
      globalExponentialPolarGram g hg p ζ e r θ 1 1 := by
    simp [Matrix.det_fin_two, h00, h01, h10]
  refine ⟨ζ, hζ, hrad, hang, hmetric, hdet, ?_⟩
  rw [hdet]
  rfl

/-- **Math.** The complete exponential is differentiable in every terminal
chart containing its endpoint, not just in a chart selected by existence. -/
theorem globalExponentialChartMap_hasFDerivAt_of_mem_source
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M) (v : E)
    (hζ : Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source) :
    HasFDerivAt (globalExponentialChartMap g hg p ζ)
      (fderiv ℝ (globalExponentialChartMap g hg p ζ) v) v := by
  exact ((contMDiffAt_extChartAt' hζ).comp v
    (Exponential.contMDiff_expMapGlobal g hg p v)).contDiffAt.differentiableAt
      (by norm_num) |>.hasFDerivAt

/-- **Math.** Actual exponential differentials transform by the true tangent
coordinate change between any two terminal charts. -/
theorem globalExponentialChartMap_fderiv_change
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p α ζ : M) (v : E)
    (hα : Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H α).source)
    (hζ : Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source) :
    fderiv ℝ (globalExponentialChartMap g hg p ζ) v =
      (tangentCoordChange I α ζ (Exponential.expMapGlobal (I := I) g hg p v)).comp
        (fderiv ℝ (globalExponentialChartMap g hg p α) v) := by
  let q := Exponential.expMapGlobal (I := I) g hg p v
  have hsymm : (extChartAt I α).symm (extChartAt I α q) = q :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hα)
  have hT : HasFDerivAt (chartTransition (I := I) α ζ)
      (tangentCoordChange I α ζ q) (extChartAt I α q) := by
    have h := hasFDerivAt_chartTransition (I := I)
      (extChartAt_mem_chartTransitionSource (I := I) hα hζ)
    rwa [hsymm] at h
  have hF := globalExponentialChartMap_hasFDerivAt_of_mem_source g hg p α v hα
  have hcomp := hT.comp v hF
  have hev : (globalExponentialChartMap g hg p ζ) =ᶠ[𝓝 v]
      (chartTransition (I := I) α ζ) ∘ globalExponentialChartMap g hg p α := by
    have hmem := (Exponential.contMDiff_expMapGlobal g hg p).continuous.continuousAt
      |>.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hα)
    filter_upwards [hmem] with w hw
    exact (chartTransition_extChartAt (I := I) (β := α) (α := ζ) hw).symm
  exact (hcomp.congr_of_eventuallyEq hev).fderiv

/-- **Math.** Pairings of actual exponential differential images are
independent of the terminal chart used to read the endpoint. -/
theorem globalExponentialChartMap_metricInner_change
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p α ζ : M) (v a b : E)
    (hα : Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H α).source)
    (hζ : Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source) :
    chartMetricInner g ζ (globalExponentialChartMap g hg p ζ v)
        (fderiv ℝ (globalExponentialChartMap g hg p ζ) v a)
        (fderiv ℝ (globalExponentialChartMap g hg p ζ) v b) =
      chartMetricInner g α (globalExponentialChartMap g hg p α v)
        (fderiv ℝ (globalExponentialChartMap g hg p α) v a)
        (fderiv ℝ (globalExponentialChartMap g hg p α) v b) := by
  have hD := globalExponentialChartMap_fderiv_change g hg p ζ α v hζ hα
  rw [hD]
  exact chartMetricInner_change g α ζ hα hζ _ _

/-- **Math.** The global Gauss identity holds in any terminal chart whose
source contains the endpoint. No intermediate chart containment is needed. -/
theorem globalExponentialChartGauss_of_mem_source
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M) (v Z : E)
    (hζ : Exponential.expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source) :
    chartMetricInner g ζ (globalExponentialChartMap g hg p ζ v)
        (fderiv ℝ (globalExponentialChartMap g hg p ζ) v v)
        (fderiv ℝ (globalExponentialChartMap g hg p ζ) v Z) =
      chartMetricInner g p (extChartAt I p p) v Z := by
  obtain ⟨α, D, hα, hD, hgauss⟩ := exists_globalExponentialGauss g hg p v
  rw [globalExponentialChartMap_metricInner_change g hg p α ζ v v Z hα hζ]
  change HasFDerivAt (globalExponentialChartMap g hg p α) D v at hD
  rw [hD.fderiv]
  exact hgauss Z

/-- **Math.** The genuine global polar Gram tensor is unchanged by reading
its endpoint in a different terminal chart. -/
theorem globalExponentialPolarGram_chart_independent
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E) (r θ : ℝ) {α ζ : M}
    (hα : Exponential.expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ) ∈ (chartAt H α).source)
    (hζ : Exponential.expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ) ∈ (chartAt H ζ).source) :
    globalExponentialPolarGram g hg p α e r θ =
      globalExponentialPolarGram g hg p ζ e r θ := by
  ext i j
  exact (globalExponentialChartMap_metricInner_change g hg p α ζ
    (r • exponentialPolarUnit e θ)
    (if i = 0 then exponentialPolarUnit e θ else r • exponentialPolarNormal e θ)
    (if j = 0 then exponentialPolarUnit e θ else r • exponentialPolarNormal e θ)
    hα hζ).symm

/-- **Math.** The actual angular differential length is terminal-chart
independent, so an intrinsic Jacobi estimate transfers to every native chart. -/
theorem globalExponentialPolarAngularLength_chart_independent
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E) (r θ : ℝ) {α ζ : M}
    (hα : Exponential.expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ) ∈ (chartAt H α).source)
    (hζ : Exponential.expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ) ∈ (chartAt H ζ).source) :
    globalExponentialPolarAngularLength g hg p α e θ r =
      globalExponentialPolarAngularLength g hg p ζ e θ r := by
  unfold globalExponentialPolarAngularLength
  rw [globalExponentialPolarGram_chart_independent g hg p e r θ hα hζ]

/-- **Math.** Every terminal chart gives unit radial Gram, zero mixed Gram,
and nonnegative angular Gram for the actual polar differential. -/
theorem globalExponentialPolarGram_entries_of_mem_source
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (r θ : ℝ) (hr : 0 < r)
    (hζ : Exponential.expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ) ∈ (chartAt H ζ).source) :
    globalExponentialPolarGram g hg p ζ e r θ 0 0 = 1 ∧
      globalExponentialPolarGram g hg p ζ e r θ 0 1 = 0 ∧
      globalExponentialPolarGram g hg p ζ e r θ 1 0 = 0 ∧
      0 ≤ globalExponentialPolarGram g hg p ζ e r θ 1 1 := by
  obtain ⟨α, hα, _, _, hmetric, _, _⟩ :=
    exists_globalExponentialPolarMetric g hg p e he r θ hr
  have hGram := globalExponentialPolarGram_chart_independent g hg p e r θ hα hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hGram, hmetric]
    simp [gluingWarpedMetric]
  · rw [← hGram, hmetric]
    simp [gluingWarpedMetric]
  · rw [← hGram, hmetric]
    simp [gluingWarpedMetric]
  · exact chartMetricInner_self_nonneg_of_mem_target g ζ
      ((extChartAt I ζ).map_source (by rw [extChartAt_source]; exact hζ)) _

/-- **Math.** Actual global polar derivatives and determinant-area density
hold in any chosen native terminal chart containing the exponential endpoint. -/
theorem globalExponentialPolarMetric_of_mem_source
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (r θ : ℝ) (hr : 0 < r)
    (hζ : Exponential.expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ) ∈ (chartAt H ζ).source) :
    HasDerivAt (fun t => globalExponentialPolarChart g hg p ζ e (t, θ))
        (globalExponentialPolarFrame g hg p ζ e r θ 0) r ∧
      HasDerivAt (fun a => globalExponentialPolarChart g hg p ζ e (r, a))
        (globalExponentialPolarFrame g hg p ζ e r θ 1) θ ∧
      globalExponentialPolarGram g hg p ζ e r θ =
        gluingWarpedMetric (globalExponentialPolarAngularLength g hg p ζ e θ) (r, θ) ∧
      (globalExponentialPolarGram g hg p ζ e r θ).det =
        globalExponentialPolarGram g hg p ζ e r θ 1 1 ∧
      Real.sqrt (globalExponentialPolarGram g hg p ζ e r θ).det =
        globalExponentialPolarAngularLength g hg p ζ e θ r := by
  let U := exponentialPolarUnit e θ
  let f := globalExponentialChartMap g hg p ζ
  have hD := globalExponentialChartMap_hasFDerivAt_of_mem_source g hg p ζ (r • U) hζ
  obtain ⟨h00, h01, h10, h11⟩ :=
    globalExponentialPolarGram_entries_of_mem_source g hg p ζ e he r θ hr hζ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change HasDerivAt (fun t => f (t • U)) (fderiv ℝ f (r • U) U) r
    simpa only [Function.comp_def, id_eq, one_smul] using
      hD.comp_hasDerivAt r ((hasDerivAt_id r).smul_const U)
  · change HasDerivAt (fun a => f (r • exponentialPolarUnit e a))
      (fderiv ℝ f (r • U) (r • exponentialPolarNormal e θ)) θ
    simpa only [Function.comp_def, Pi.smul_apply] using
      hD.comp_hasDerivAt θ ((exponentialPolarUnit_hasDerivAt e θ).const_smul r)
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [gluingWarpedMetric, globalExponentialPolarAngularLength,
        h00, h01, h10, Real.sq_sqrt h11]
  · simp [Matrix.det_fin_two, h00, h01, h10]
  · change Real.sqrt _ = Real.sqrt _
    congr 1
    simp [Matrix.det_fin_two, h00, h01, h10]

#print axioms exists_globalExponentialGauss_jacobi
#print axioms exists_globalExponentialGauss
#print axioms exists_globalExponentialPolarMetric
#print axioms globalExponentialChartGauss_of_mem_source
#print axioms globalExponentialPolarGram_chart_independent
#print axioms globalExponentialPolarMetric_of_mem_source

end SystolicGrowth

end
