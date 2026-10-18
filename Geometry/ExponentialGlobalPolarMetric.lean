module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ExponentialPolarMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ExpDifferential
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.GramBound

@[expose] public section

/-!
# Global exponential polar derivatives

The complete-manifold exponential map is chart-independent. Its radial
polar differential has unit metric length at every radius, not just inside
one normal coordinate neighborhood. Angular Jacobi comparison and the
mixed Gram entry are separate geometric steps.
-/

open Set Bundle Manifold Riemannian
open scoped Manifold ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace M]

omit [SigmaCompactSpace M] in
/-- **Math.** The chart squared speed of the actual global geodesic equals
the metric squared length of its initial vector, in every terminal chart. -/
theorem globalGeodesic_chartSpeedSq_eq_initial
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) (v : E)
    (t : ℝ) (α : M)
    (hα : Geodesic.globalGeodesic (I := I) g hg p v t ∈ (chartAt H α).source) :
    chartMetricInner g α
        (extChartAt I α (Geodesic.globalGeodesic (I := I) g hg p v t))
        (deriv (fun s => extChartAt I α
          (Geodesic.globalGeodesic (I := I) g hg p v s)) t)
        (deriv (fun s => extChartAt I α
          (Geodesic.globalGeodesic (I := I) g hg p v s)) t) =
      chartMetricInner g p (extChartAt I p p) v v := by
  let γ := Geodesic.globalGeodesic (I := I) g hg p v
  have hgeo : Geodesic.IsGeodesicOn (I := I) g γ univ :=
    fun s _ => Geodesic.isGeodesic_globalGeodesic g hg p v s
  have hcont : Continuous γ := Geodesic.continuous_globalGeodesic g hg p v
  have hspeed := hgeo.speedSq_eq isOpen_univ isPreconnected_univ hcont.continuousOn
    (mem_univ t) (mem_univ (0 : ℝ))
  have hterminal := (hgeo t (mem_univ t)).speedSq_eq_chartMetricInner_of_mem_source
    hcont.continuousAt hα
  have hbase : γ 0 ∈ (chartAt H p).source := by
    dsimp only [γ]
    rw [Geodesic.globalGeodesic_zero]
    exact mem_chart_source H p
  have hinitial := (hgeo 0 (mem_univ 0)).speedSq_eq_chartMetricInner_of_mem_source
    hcont.continuousAt hbase
  have hv := (Geodesic.hasDerivAt_chartReading_globalGeodesic g hg p v).deriv
  rw [hterminal, hinitial] at hspeed
  dsimp only [γ] at hspeed
  rw [hv] at hspeed
  simp only [Geodesic.chartReading, Geodesic.globalGeodesic_zero] at hspeed
  exact hspeed

/-- **Math.** At every radius, one terminal chart reads both actual polar
derivatives of the global exponential map, and the radial Gram entry is one.
No chart-containment condition on the whole radial geodesic is required. -/
theorem exists_globalExponentialPolar_derivatives
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then (1 : ℝ) else 0) (r θ : ℝ) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      Exponential.expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e θ) ∈
        (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ
        (Exponential.expMapGlobal (I := I) g hg p w)) D (r • exponentialPolarUnit e θ) ∧
      HasDerivAt (fun t => extChartAt I ζ
        (Exponential.expMapGlobal (I := I) g hg p (t • exponentialPolarUnit e θ)))
        (D (exponentialPolarUnit e θ)) r ∧
      HasDerivAt (fun a => extChartAt I ζ
        (Exponential.expMapGlobal (I := I) g hg p (r • exponentialPolarUnit e a)))
        (D (r • exponentialPolarNormal e θ)) θ ∧
      chartMetricInner g ζ
        (extChartAt I ζ (Exponential.expMapGlobal (I := I) g hg p
          (r • exponentialPolarUnit e θ)))
        (D (exponentialPolarUnit e θ)) (D (exponentialPolarUnit e θ)) = 1 := by
  obtain ⟨α, ζ, D, _, hζ, hD, _⟩ :=
    Jacobi.hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p
      (r • exponentialPolarUnit e θ)
  have hrad := hD.comp_hasDerivAt r
    ((hasDerivAt_id r).smul_const (exponentialPolarUnit e θ))
  have hang := hD.comp_hasDerivAt θ
    ((exponentialPolarUnit_hasDerivAt e θ).const_smul r)
  have hrad'' : HasDerivAt (fun t => extChartAt I ζ
      (Exponential.expMapGlobal (I := I) g hg p
        (t • exponentialPolarUnit (E := E) e θ)))
      (D (exponentialPolarUnit e θ)) r := by
    simpa only [Function.comp_def, id_eq, one_smul] using hrad
  refine ⟨ζ, D, hζ, hD, hrad'', ?_, ?_⟩
  · simpa only [Function.comp_def, Pi.smul_apply] using hang
  have hray (t : ℝ) :
      Exponential.expMapGlobal (I := I) g hg p
        (t • exponentialPolarUnit (E := E) e θ) =
      Geodesic.globalGeodesic (I := I) g hg p
        (exponentialPolarUnit (E := E) e θ) t :=
    Exponential.expMapGlobal_smul (I := I) g hg p
      (exponentialPolarUnit (E := E) e θ) t
  have hrad' : HasDerivAt (fun t => extChartAt I ζ
      (Geodesic.globalGeodesic (I := I) g hg p
        (exponentialPolarUnit (E := E) e θ) t))
      (D (exponentialPolarUnit e θ)) r := by
    simpa only [hray] using hrad''
  have hsrc : Geodesic.globalGeodesic (I := I) g hg p
      (exponentialPolarUnit (E := E) e θ) r ∈ (chartAt H ζ).source := by
    simpa only [hray] using hζ
  have hspeed := globalGeodesic_chartSpeedSq_eq_initial g hg p
    (exponentialPolarUnit e θ) r ζ hsrc
  rw [hrad'.deriv] at hspeed
  rw [hray]
  exact hspeed.trans (exponentialPolarDirections_chartMetric g p e he θ).1

#print axioms globalGeodesic_chartSpeedSq_eq_initial
#print axioms exists_globalExponentialPolar_derivatives

omit [SigmaCompactSpace M] in
/-- **Math.** The radial geodesic gives the global endpoint-distance upper
bound by the metric length of its initial vector. -/
theorem dist_expMapGlobal_le_initialLength
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) (v : E) :
    dist p (Exponential.expMapGlobal (I := I) g hg p v) ≤
      Real.sqrt (chartMetricInner g p (extChartAt I p p) v v) := by
  let γ := Geodesic.globalGeodesic (I := I) g hg p v
  have hgeo : Geodesic.IsGeodesicOn (I := I) g γ univ :=
    fun s _ => Geodesic.isGeodesic_globalGeodesic g hg p v s
  have hc : Continuous γ := Geodesic.continuous_globalGeodesic g hg p v
  have h := hgeo.dist_le g hg isOpen_univ isPreconnected_univ hc.continuousOn
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) zero_le_one
  have hsrc : γ 0 ∈ (chartAt H p).source := by
    dsimp only [γ]
    rw [Geodesic.globalGeodesic_zero]
    exact mem_chart_source H p
  have hspeed := (hgeo 0 (mem_univ 0)).speedSq_eq_chartMetricInner_of_mem_source
    hc.continuousAt hsrc
  dsimp only [γ] at hspeed h
  rw [(Geodesic.hasDerivAt_chartReading_globalGeodesic g hg p v).deriv] at hspeed
  simp only [Geodesic.chartReading, Geodesic.globalGeodesic_zero] at hspeed
  rw [hspeed] at h
  simpa only [Geodesic.globalGeodesic_zero, Exponential.expMapGlobal,
    sub_zero, mul_one] using h

omit [SigmaCompactSpace M] in
/-- **Math.** A minimizing geodesic constructs an exponential preimage whose
initial metric length is exactly the endpoint distance. -/
theorem exists_expMapGlobal_initialLength_eq_dist [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p q : M) :
    ∃ v : E, Exponential.expMapGlobal (I := I) g hg p v = q ∧
      Real.sqrt (chartMetricInner g p (extChartAt I p p) v v) = dist p q := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        Geodesic.IsGeodesic (I := I) g γ := by
    intro v
    exact Geodesic.exists_global_geodesic (I := I) g hg p v
  obtain ⟨γ, h0, h1, hc, hgeo, hmin⟩ :=
    Exponential.exists_minimizing_geodesic_unitInterval (I := I) g hg p hp q
  let v : E := deriv (fun s => extChartAt I p (γ s)) 0
  have hsrc : γ 0 ∈ (chartAt H p).source := by
    rw [h0]
    exact mem_chart_source H p
  have hv : HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
    have h := ((hgeo 0).eventually_hasDerivAt_extChartAt hc.continuousAt hsrc).self_of_nhds
    simpa only [v, h.deriv] using h
  refine ⟨v, (Exponential.expMapGlobal_eq_of_isGeodesic g hg hgeo hc h0 hv).trans h1, ?_⟩
  have hspeed := (hgeo 0).speedSq_eq_chartMetricInner_of_mem_source hc.continuousAt hsrc
  simp only [Geodesic.chartReading, h0] at hspeed
  have hminspeed := Exponential.sqrt_speedSq_eq_dist_of_minimizing (I := I) g hg
    (lo := (-1 : ℝ)) (hi := (2 : ℝ)) (γ := γ) (q₁ := p) (q₂ := q)
    (by norm_num) (by norm_num) (hgeo.isGeodesicOn _) hc.continuousOn h0 h1 hmin
  rw [hspeed] at hminspeed
  exact hminspeed

omit [SigmaCompactSpace M] in
/-- **Math.** The exponential image of the initial metric-length ball is
the actual metric ball, at any radius. This is surjectivity onto balls, not
an assertion of injectivity before the systole bound is applied. -/
theorem expMapGlobal_image_initialLength_ball [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) (R : ℝ) :
    (fun v : E => Exponential.expMapGlobal (I := I) g hg p v) ''
        {v | Real.sqrt (chartMetricInner g p (extChartAt I p p) v v) < R} =
      Metric.ball p R := by
  ext q
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [Metric.mem_ball, dist_comm]
    exact (dist_expMapGlobal_le_initialLength g hg p v).trans_lt hv
  · intro hq
    obtain ⟨v, hv, hlength⟩ := exists_expMapGlobal_initialLength_eq_dist g hg p q
    refine ⟨v, ?_, hv⟩
    rw [mem_setOf_eq, hlength, dist_comm]
    exact hq

#print axioms dist_expMapGlobal_le_initialLength
#print axioms exists_expMapGlobal_initialLength_eq_dist
#print axioms expMapGlobal_image_initialLength_ball

end
end SystolicGrowth
