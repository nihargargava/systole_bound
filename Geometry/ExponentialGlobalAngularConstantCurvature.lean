module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.JacobiConstantCurvature
public import Geometry.ExponentialGlobalGauss

@[expose] public section

/-!
# Exact global exponential polar metric in curvature minus one

The genuine angular Jacobi field identifies the actual exponential
differential in a terminal chart. Constant curvature makes its length
exactly `sinh r`; together with the global Gauss identity this gives the
hyperbolic polar tensor, without requiring a chart to contain the whole ray.
-/

open Set Bundle Manifold Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M]

/-- **Math.** The actual complete-manifold exponential has identity
differential at the origin in its initial chart. Global radial homogeneity
and the genuine initial geodesic velocity determine every derivative column. -/
theorem globalExponentialChartMap_fderiv_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    fderiv ℝ (globalExponentialChartMap g hg p p) (0 : E) =
      ContinuousLinearMap.id ℝ E := by
  have hsrc : expMapGlobal (I := I) g hg p (0 : E) ∈ (chartAt H p).source := by
    rw [expMapGlobal_zero]
    exact mem_chart_source H p
  have hD := globalExponentialChartMap_hasFDerivAt_of_mem_source g hg p p 0 hsrc
  ext w
  have hD' : HasFDerivAt (globalExponentialChartMap g hg p p)
      (fderiv ℝ (globalExponentialChartMap g hg p p) 0) ((0 : ℝ) • w) := by
    simpa only [zero_smul] using hD
  have hline := hD'.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const w)
  have hray (t : ℝ) : expMapGlobal (I := I) g hg p (t • w) =
      globalGeodesic (I := I) g hg p w t := expMapGlobal_smul g hg p w t
  have hline' : HasDerivAt
      (fun t => extChartAt I p (globalGeodesic (I := I) g hg p w t))
      (fderiv ℝ (globalExponentialChartMap g hg p p) 0 w) 0 := by
    simpa only [Function.comp_def, id_eq, zero_smul, one_smul,
      globalExponentialChartMap, hray] using hline
  exact hline'.unique (hasDerivAt_chartReading_globalGeodesic g hg p w)

#print axioms globalExponentialChartMap_fderiv_zero

/-- **Math.** In constant curvature minus one the actual global
exponential angular differential has length exactly `sinh r`, in every
terminal chart containing its endpoint. -/
theorem globalExponentialPolarAngularLength_eq_sinh
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hdim : Module.finrank ℝ E = 2)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y =
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    (hζ : expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
      (chartAt H ζ).source) :
    globalExponentialPolarAngularLength g hg p ζ e θ r = Real.sinh r := by
  let γ := globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)
  have hgeo : IsGeodesicOn g γ (Icc (0 : ℝ) 1) :=
    fun t _ => isGeodesic_globalGeodesic g hg p (r • exponentialPolarUnit e θ) t
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t :=
    fun _ _ => (continuous_globalGeodesic g hg p (r • exponentialPolarUnit e θ)).continuousAt
  obtain ⟨J, DJ, hJac, hJ0, hDJ0⟩ := Jacobi.exists_isJacobiFieldAlongOn
    (I := I) zero_lt_one hgeo hc (0 : TangentSpace I (γ 0))
      (r • exponentialPolarNormal e θ : TangentSpace I (γ 0))
  have hlength := exponentialAngularJacobi_intrinsicNorm_eq_sinh
    g hg p e hdim θ r hr he hK hJac hJ0 hDJ0
  obtain ⟨α, D, hα, hD, htransport, _⟩ :=
    exists_globalExponentialGauss_jacobi g hg p (r • exponentialPolarUnit e θ)
  have hangular : D (r • exponentialPolarNormal e θ) =
      Jacobi.chartVectorRep (I := I) γ α J 1 := by
    rw [← hDJ0]
    exact htransport J DJ hJac hJ0
  have hmetric := Jacobi.metricInner_eq_chartMetricInner_rep
    (γ := γ) (τ := 1) g hα J J
  have hDf : fderiv ℝ (globalExponentialChartMap g hg p α)
      (r • exponentialPolarUnit e θ) = D := hD.fderiv
  have hαlength : globalExponentialPolarAngularLength g hg p α e θ r =
      jacobiIntrinsicNorm g γ J 1 := by
    change Real.sqrt (chartMetricInner g α
      (extChartAt I α (expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ)))
      (fderiv ℝ (globalExponentialChartMap g hg p α)
        (r • exponentialPolarUnit e θ) (r • exponentialPolarNormal e θ))
      (fderiv ℝ (globalExponentialChartMap g hg p α)
        (r • exponentialPolarUnit e θ) (r • exponentialPolarNormal e θ))) = _
    rw [hDf, hangular]
    exact (congrArg Real.sqrt hmetric).symm
  rw [← globalExponentialPolarAngularLength_chart_independent g hg p e r θ hα hζ]
  exact hαlength.trans hlength

/-- **Math.** The genuine global exponential polar tensor in a complete
constant-curvature-minus-one surface is `dr² + sinh(r)² dθ²` in every
terminal chart. -/
theorem globalExponentialPolarGram_eq_hyperbolic
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hdim : Module.finrank ℝ E = 2)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y =
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    (hζ : expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
      (chartAt H ζ).source) :
    globalExponentialPolarGram g hg p ζ e r θ = gluingWarpedMetric Real.sinh (r, θ) := by
  have hlength := globalExponentialPolarAngularLength_eq_sinh g hg p ζ e θ r hr he hdim hK hζ
  rw [(globalExponentialPolarMetric_of_mem_source g hg p ζ e he r θ hr hζ).2.2.1]
  ext i j
  simp only [gluingWarpedMetric, hlength]

/-- **Math.** The literal determinant density of the genuine global
exponential polar metric is exactly the hyperbolic radial density. -/
theorem globalExponentialPolar_sqrt_det_eq_sinh
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hdim : Module.finrank ℝ E = 2)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y =
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    (hζ : expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
      (chartAt H ζ).source) :
    Real.sqrt (globalExponentialPolarGram g hg p ζ e r θ).det = Real.sinh r := by
  rw [(globalExponentialPolarMetric_of_mem_source g hg p ζ e he r θ hr hζ).2.2.2.2]
  exact globalExponentialPolarAngularLength_eq_sinh g hg p ζ e θ r hr he hdim hK hζ

#print axioms globalExponentialPolarAngularLength_eq_sinh
#print axioms globalExponentialPolarGram_eq_hyperbolic
#print axioms globalExponentialPolar_sqrt_det_eq_sinh

/-- **Math.** The complete exponential's metric pullback is determined
on every pair of initial vectors by their radial and normal components.
This upgrades the polar-frame tensor identity to the full tangent tensor
needed to identify two constant-curvature covering metrics. -/
theorem globalExponentialChartMap_metricInner_eq_hyperbolic
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hdim : Module.finrank ℝ E = 2)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y =
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    (hζ : expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
      (chartAt H ζ).source) (u v : E) :
    chartMetricInner g ζ
        (globalExponentialChartMap g hg p ζ (r • exponentialPolarUnit e θ))
        (fderiv ℝ (globalExponentialChartMap g hg p ζ)
          (r • exponentialPolarUnit e θ) u)
        (fderiv ℝ (globalExponentialChartMap g hg p ζ)
          (r • exponentialPolarUnit e θ) v) =
      chartMetricInner g p (extChartAt I p p) u (exponentialPolarUnit e θ) *
        chartMetricInner g p (extChartAt I p p) v (exponentialPolarUnit e θ) +
      (Real.sinh r / r) ^ 2 *
        chartMetricInner g p (extChartAt I p p) u (exponentialPolarNormal e θ) *
        chartMetricInner g p (extChartAt I p p) v (exponentialPolarNormal e θ) := by
  let U := exponentialPolarUnit e θ
  let N := exponentialPolarNormal e θ
  let D := fderiv ℝ (globalExponentialChartMap g hg p ζ) (r • U)
  let y := globalExponentialChartMap g hg p ζ (r • U)
  let B := chartMetricInner g p (extChartAt I p p)
  let f : Fin 2 → E := fun i => if i = 0 then U else N
  have hrot := exponentialPolarDirections_chartMetric g p e he θ
  have hf : ∀ i j : Fin 2, B (f i) (f j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [f, ↓reduceIte]
    · exact hrot.1
    · exact hrot.2.1
    · exact (chartMetricInner_symm g p _ N U).trans hrot.2.1
    · exact hrot.2.2
  have hdecomp (w : E) : w = B w U • U + B w N • N := by
    have hh := Jacobi.frameExpansion g p (extChartAt I p p) f (by simp [hdim]) hf w
    rw [Fin.sum_univ_two] at hh
    change w = B w U • U + B w (f 1) • f 1 at hh
    have hf1 : f 1 = N := by norm_num [f]
    rw [hf1] at hh
    exact hh
  have hGram := globalExponentialPolarGram_eq_hyperbolic g hg p ζ e θ r hr he hdim hK hζ
  have hUU : chartMetricInner g ζ y (D U) (D U) = 1 := by
    have h := congrArg (fun G => G 0 0) hGram
    simpa only [globalExponentialPolarGram, globalExponentialPolarFrame, globalExponentialPolarChart,
      gluingWarpedMetric, ↓reduceIte] using h
  have hUN : chartMetricInner g ζ y (D U) (D N) = 0 := by
    have h := congrArg (fun G => G 0 1) hGram
    change chartMetricInner g ζ y (D U) (D (r • N)) = 0 at h
    rw [map_smul, chartMetricInner_smul_right] at h
    exact (mul_eq_zero.mp h).resolve_left hr.ne'
  have hNU : chartMetricInner g ζ y (D N) (D U) = 0 :=
    (chartMetricInner_symm g ζ y (D N) (D U)).trans hUN
  have hNN : chartMetricInner g ζ y (D N) (D N) = (Real.sinh r / r) ^ 2 := by
    have h := congrArg (fun G => G 1 1) hGram
    change chartMetricInner g ζ y (D (r • N)) (D (r • N)) = Real.sinh r ^ 2 at h
    rw [map_smul, chartMetricInner_smul_left, chartMetricInner_smul_right] at h
    rw [div_pow, eq_div_iff (pow_ne_zero 2 hr.ne')]
    nlinarith only [h]
  have hDw (w : E) : D w = B w U • D U + B w N • D N := by
    exact (congrArg D (hdecomp w)).trans (by simp)
  change chartMetricInner g ζ y (D u) (D v) = _
  rw [hDw u, hDw v]
  simp only [chartMetricInner_add_left, chartMetricInner_add_right,
    chartMetricInner_smul_left, chartMetricInner_smul_right, hUU, hUN, hNU, hNN,
    mul_one, mul_zero, add_zero, zero_add]
  ring

#print axioms globalExponentialChartMap_metricInner_eq_hyperbolic

end
end SystolicGrowth
