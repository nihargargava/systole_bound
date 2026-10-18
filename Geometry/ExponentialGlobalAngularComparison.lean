module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.JacobiIntrinsicNormComparison
public import Geometry.ExponentialGlobalGauss

@[expose] public section

/-!
# Global exponential angular comparison

Construct the actual angular manifold Jacobi field, then use the genuine
exponential differential's universal endpoint identification to transfer
intrinsic hyperbolic norm comparison to the actual polar angular length.
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

/-- **Math.** One actual terminal exponential differential simultaneously
satisfies the global Gauss identity and the hyperbolic angular-length bound.
The angular Jacobi field is constructed, and no chart must contain the ray. -/
theorem exists_globalExponentialAngularComparison
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y ≤
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
        (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
        D (r • exponentialPolarUnit e θ) ∧
      (∀ Z : E, chartMetricInner g ζ
        (extChartAt I ζ (expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ)))
        (D (r • exponentialPolarUnit e θ)) (D Z) =
          chartMetricInner g p (extChartAt I p p) (r • exponentialPolarUnit e θ) Z) ∧
      Real.sinh r ≤ globalExponentialPolarAngularLength g hg p ζ e θ r := by
  let γ := globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)
  have hgeo : IsGeodesicOn g γ (Icc (0 : ℝ) 1) :=
    fun t _ => isGeodesic_globalGeodesic g hg p (r • exponentialPolarUnit e θ) t
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t :=
    fun _ _ => (continuous_globalGeodesic g hg p (r • exponentialPolarUnit e θ)).continuousAt
  obtain ⟨J, DJ, hJac, hJ0, hDJ0⟩ := Jacobi.exists_isJacobiFieldAlongOn
    (I := I) zero_lt_one hgeo hc (0 : TangentSpace I (γ 0))
      (r • exponentialPolarNormal e θ : TangentSpace I (γ 0))
  have hlength := sinh_le_exponentialAngularJacobi_intrinsicNorm
    g hg p e θ r hr he hK hJac hJ0 hDJ0
  obtain ⟨ζ, D, hζ, hD, htransport, hgauss⟩ :=
    exists_globalExponentialGauss_jacobi g hg p (r • exponentialPolarUnit e θ)
  have hangular : D (r • exponentialPolarNormal e θ) =
      Jacobi.chartVectorRep (I := I) γ ζ J 1 := by
    rw [← hDJ0]
    exact htransport J DJ hJac hJ0
  have hmetric := Jacobi.metricInner_eq_chartMetricInner_rep
    (γ := γ) (τ := 1) g hζ J J
  have hDf : fderiv ℝ (globalExponentialChartMap g hg p ζ)
      (r • exponentialPolarUnit e θ) = D := hD.fderiv
  refine ⟨ζ, D, hζ, hD, hgauss, ?_⟩
  change Real.sinh r ≤ Real.sqrt (chartMetricInner g ζ
    (extChartAt I ζ (expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ)))
    (fderiv ℝ (globalExponentialChartMap g hg p ζ)
      (r • exponentialPolarUnit e θ) (r • exponentialPolarNormal e θ))
    (fderiv ℝ (globalExponentialChartMap g hg p ζ)
      (r • exponentialPolarUnit e θ) (r • exponentialPolarNormal e θ)))
  rw [hDf, hangular]
  exact hlength.trans_eq (congrArg Real.sqrt hmetric)

/-- **Math.** The actual global exponential angular differential has
length at least `sinh r` in every terminal chart containing its endpoint. -/
theorem sinh_le_globalExponentialPolarAngularLength
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y ≤
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    (hζ : expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
      (chartAt H ζ).source) :
    Real.sinh r ≤ globalExponentialPolarAngularLength g hg p ζ e θ r := by
  obtain ⟨α, _, hα, _, _, hlength⟩ :=
    exists_globalExponentialAngularComparison g hg p e θ r hr he hK
  rw [← globalExponentialPolarAngularLength_chart_independent g hg p e r θ hα hζ]
  exact hlength

/-- **Math.** The literal determinant-area density of the actual global
exponential polar metric is at least the hyperbolic density `sinh r`.
This is the pointwise geometric input to the polar disk-area integral. -/
theorem sinh_le_globalExponentialPolar_sqrt_det
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p ζ : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y ≤
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    (hζ : expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
      (chartAt H ζ).source) :
    Real.sinh r ≤ Real.sqrt (globalExponentialPolarGram g hg p ζ e r θ).det := by
  rw [(globalExponentialPolarMetric_of_mem_source g hg p ζ e he r θ hr hζ).2.2.2.2]
  exact sinh_le_globalExponentialPolarAngularLength g hg p ζ e θ r hr he hK hζ

#print axioms exists_globalExponentialAngularComparison
#print axioms sinh_le_globalExponentialPolarAngularLength
#print axioms sinh_le_globalExponentialPolar_sqrt_det

end
end SystolicGrowth
