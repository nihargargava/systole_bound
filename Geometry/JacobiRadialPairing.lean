module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.JacobiExistence
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Intrinsic radial pairing of a Jacobi field

The scalar pairing of a Jacobi field with the geodesic velocity is affine.
The proof localizes the actual manifold Jacobi certificate separately at
each time; no single chart must contain the whole geodesic segment.
-/

open Set Bundle Manifold Riemannian Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace SystolicGrowth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The chart curvature contraction is orthogonal to its repeated
radial vector, by the actual intrinsic curvature form's last-pair skewness. -/
theorem chartMetricInner_chartCurvature_radial_eq_zero
    (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source) (w v : E) :
    chartMetricInner g α (extChartAt I α p)
      (Jacobi.chartCurvature g α (extChartAt I α p) w v v) v = 0 := by
  classical
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  have hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
  have hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have hbridge := Jacobi.curvatureFormAt_chartFrame g hp w v v v
  have hzero := hB.self_right
    (∑ a, Geodesic.chartCoord (E := E) a w • Tensor.chartBasisVecFiber (I := I) α a p)
    (∑ a, Geodesic.chartCoord (E := E) a v • Tensor.chartBasisVecFiber (I := I) α a p)
    (∑ a, Geodesic.chartCoord (E := E) a v • Tensor.chartBasisVecFiber (I := I) α a p)
  rw [hzero] at hbridge
  linarith

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** In any chart containing the foot of a geodesic, the chart
reading of its actual manifold velocity is the derivative of that chart curve. -/
theorem chartVectorRep_geodesic_velocity_eq_deriv
    {g : RiemannianMetric I M} {γ : ℝ → M} {α : M} {t : ℝ}
    (hgeo : Geodesic.HasGeodesicEquationAt g γ t) (hc : ContinuousAt γ t)
    (hsrc : γ t ∈ (chartAt H α).source) :
    Jacobi.chartVectorRep (I := I) γ α
        (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) t =
      deriv (fun s => extChartAt I α (γ s)) t := by
  rw [Jacobi.chartVectorRep_apply, hgeo.mfderiv_apply_one hc,
    ← hgeo.deriv_extChartAt_eq hc hsrc]

/-- **Math.** Actual intrinsic Jacobi pairings satisfy `q' = d` and `d' = 0`
at every interior time. The chart is chosen at that time, independently of
the rest of the segment. -/
theorem jacobiRadialPairings_hasDerivAt
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {a b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ a b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (J s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)))
      (g.metricInner (γ t) (DJ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) t ∧
      HasDerivAt (fun s => g.metricInner (γ s) (DJ s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) 0 t := by
  let q : ℝ → ℝ := fun s => g.metricInner (γ s) (J s)
    (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
  let d : ℝ → ℝ := fun s => g.metricInner (γ s) (DJ s)
    (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
  change HasDerivAt q (d t) t ∧ HasDerivAt d 0 t
  have htcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hwindow : (γ ⁻¹' (chartAt H (γ t)).source ∩ Ioo a b) ∈ 𝓝 t :=
    inter_mem ((hγc t htcc).preimage_mem_nhds
      ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t))))
      (Ioo_mem_nhds ht.1 ht.2)
  obtain ⟨c, e, htce, hce, hsubwindow⟩ := exists_Icc_mem_subset_of_mem_nhds hwindow
  have hsub : Icc c e ⊆ Icc a b :=
    fun s hs => Ioo_subset_Icc_self (hsubwindow hs).2
  have hsrc : ∀ s ∈ Icc c e, γ s ∈ (chartAt H (γ t)).source :=
    fun s hs => (hsubwindow hs).1
  have htioo : t ∈ Ioo c e := by
    have h := mem_interior_iff_mem_nhds.mpr hce
    rwa [interior_Icc] at h
  have hJF := hJac.isJacobiFieldOn_of_mem_source hgeo hγc hsub hsrc
  let u := Geodesic.chartLocalCurve (I := I) γ t
  let VJ := Jacobi.chartVectorRep (I := I) γ (γ t) J
  let VDJ := Jacobi.chartVectorRep (I := I) γ (γ t) DJ
  obtain ⟨v, acc, hdu, _, hdd, hacc⟩ := hgeo t htcc
  have hu : DifferentiableAt ℝ u t := hdu.differentiableAt
  have hvel : DifferentiableAt ℝ (deriv u) t := hdd.differentiableAt
  have hJd : DifferentiableAt ℝ VJ t :=
    ((hJF.hasDerivWithinAt_fst t htce).hasDerivAt hce).differentiableAt
  have hDJd : DifferentiableAt ℝ VDJ t :=
    ((hJF.hasDerivWithinAt_snd t htce).hasDerivAt hce).differentiableAt
  have hcov : covariantDerivCoord g (γ t) u (deriv u) t = 0 := by
    rw [covariantDerivCoord_def, hdd.deriv, hdu.deriv]
    exact hacc
  have hfst : covariantDerivCoord g (γ t) u VJ t = VDJ t :=
    hJF.covariantDerivCoord_fst htioo
  have hsnd : covariantDerivCoord g (γ t) u VDJ t =
      -Jacobi.chartCurvature g (γ t) (u t) (VJ t) (deriv u t) (deriv u t) :=
    hJF.covariantDerivCoord_snd htioo
  have hymem : u t ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source (mem_extChartAt_source (γ t))
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE g (γ t) i j) (u t) :=
    fun i j => Jacobi.differentiableAt_chartGramOnE g (γ t) hymem i j
  have hbase : (extChartAt I (γ t)).symm (u t) ∈
      (trivializationAt E (TangentSpace I) (γ t)).baseSet :=
    Jacobi.symm_extChartAt_mem_baseSet (mem_chart_source H (γ t))
  have hrep (U : ℝ → E) (s : ℝ) (hs : s ∈ Icc c e) :
      g.metricInner (γ s) (U s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) =
        chartMetricInner g (γ t) (u s)
          (Jacobi.chartVectorRep (I := I) γ (γ t) U s) (deriv u s) := by
    have heq := Jacobi.metricInner_eq_chartMetricInner_rep g (hsrc s hs)
      U (fun z => mfderiv 𝓘(ℝ, ℝ) I γ z (1 : ℝ))
    rw [chartVectorRep_geodesic_velocity_eq_deriv
      (hgeo s (hsub hs)) (hγc s (hsub hs)) (hsrc s hs)] at heq
    exact heq
  have hevq : q =ᶠ[𝓝 t] fun s => chartMetricInner g (γ t) (u s) (VJ s) (deriv u s) :=
    Filter.eventually_of_mem hce fun s hs => hrep J s hs
  have hevd : d =ᶠ[𝓝 t] fun s => chartMetricInner g (γ t) (u s) (VDJ s) (deriv u s) :=
    Filter.eventually_of_mem hce fun s hs => hrep DJ s hs
  constructor
  · have hraw := hasDerivAt_chartMetricInner_along g (γ t) u VJ (deriv u)
      hu hJd hvel hG hbase
    rw [hfst, hcov] at hraw
    have hdval : chartMetricInner g (γ t) (u t) (VDJ t) (deriv u t) = d t :=
      (hrep DJ t htce).symm
    simpa only [chartMetricInner_zero_right, add_zero, hdval] using
      hraw.congr_of_eventuallyEq hevq
  · have hraw := hasDerivAt_chartMetricInner_along g (γ t) u VDJ (deriv u)
      hu hDJd hvel hG hbase
    have hcurv : chartMetricInner g (γ t) (u t)
        (Jacobi.chartCurvature g (γ t) (u t) (VJ t) (deriv u t) (deriv u t))
        (deriv u t) = 0 :=
      chartMetricInner_chartCurvature_radial_eq_zero g (mem_chart_source H (γ t))
        (VJ t) (deriv u t)
    rw [hsnd, hcov, Jacobi.chartMetricInner_neg_left,
      hcurv,
      chartMetricInner_zero_right, neg_zero, add_zero] at hraw
    exact hraw.congr_of_eventuallyEq hevd

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Both intrinsic radial pairings are continuous through all
chart changes, including the segment endpoints. -/
theorem jacobiRadialPairings_continuousOn
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ a b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s) :
    ContinuousOn (fun s => g.metricInner (γ s) (J s)
      (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) (Icc a b) ∧
    ContinuousOn (fun s => g.metricInner (γ s) (DJ s)
      (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) (Icc a b) := by
  have hcont (U : ℝ → E) (hU : U = J ∨ U = DJ) :
      ContinuousOn (fun s => g.metricInner (γ s) (U s)
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) (Icc a b) := by
    intro t ht
    obtain ⟨α, c, d, _, htcd, hsub, hnbhd, hsrc, hJF⟩ := hJac t ht
    let u : ℝ → E := fun s => extChartAt I α (γ s)
    have hu : ContinuousOn u (Icc c d) := by
      intro s hs
      exact (Jacobi.IsGeodesicOn.differentiableAt_extChartAt hgeo (hsub hs)
        (hγc s (hsub hs)) (hsrc s hs)).continuousAt.continuousWithinAt
    have hmem : ∀ s ∈ Icc c d, u s ∈ (extChartAt I α).target :=
      fun s hs => (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc s hs)
    have hUc : ContinuousOn (Jacobi.chartVectorRep (I := I) γ α U) (Icc c d) := by
      rcases hU with rfl | rfl
      · exact hJF.continuousOn_fst
      · exact hJF.continuousOn_snd
    have hvc : ContinuousOn (deriv u) (Icc c d) := by
      intro s hs
      exact (Jacobi.IsGeodesicOn.continuousAt_deriv_extChartAt hgeo (hsub hs)
        (hγc s (hsub hs)) (hsrc s hs)).continuousWithinAt
    have hpairc := Jacobi.continuousOn_chartMetricInner_pairing g α hu hmem hUc hvc
    have hc := (hpairc t htcd).mono_of_mem_nhdsWithin hnbhd
    have hrep (s : ℝ) (hs : s ∈ Icc c d) :
        g.metricInner (γ s) (U s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) =
          chartMetricInner g α (u s)
            (Jacobi.chartVectorRep (I := I) γ α U s) (deriv u s) := by
      have heq := Jacobi.metricInner_eq_chartMetricInner_rep g (hsrc s hs)
        U (fun z => mfderiv 𝓘(ℝ, ℝ) I γ z (1 : ℝ))
      rw [chartVectorRep_geodesic_velocity_eq_deriv
        (hgeo s (hsub hs)) (hγc s (hsub hs)) (hsrc s hs)] at heq
      exact heq
    refine hc.congr_of_eventuallyEq ?_ (hrep t htcd)
    exact Filter.eventually_of_mem hnbhd fun s hs => hrep s hs
  exact ⟨hcont J (Or.inl rfl), hcont DJ (Or.inr rfl)⟩

private theorem eq_initial_of_hasDerivAt_zero {f : ℝ → ℝ} {b : ℝ}
    (hc : ContinuousOn f (Icc 0 b))
    (hd : ∀ t ∈ Ioo 0 b, HasDerivAt f 0 t) {t : ℝ} (ht : t ∈ Icc 0 b) :
    f t = f 0 := by
  by_cases ht0 : t = 0
  · rw [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  obtain ⟨s, _, heq⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) htpos
    (hc.mono (Icc_subset_Icc le_rfl ht.2))
    (fun s hs => hd s ⟨hs.1, hs.2.trans_le ht.2⟩)
  have : f t - f 0 = 0 := by
    exact (div_eq_zero_iff.mp heq.symm).resolve_right (sub_ne_zero.mpr ht0)
  exact sub_eq_zero.mp this

/-- **Math.** A manifold Jacobi field vanishing initially has radial pairing
equal to time times its initial covariant-derivative pairing. The segment may
cross arbitrarily many coordinate charts. -/
theorem jacobiRadialPairing_eq_time_mul_initial
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s) (hJ0 : J 0 = 0)
    (ht : t ∈ Icc 0 b) :
    g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) =
      t * g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) := by
  let q : ℝ → ℝ := fun s => g.metricInner (γ s) (J s)
    (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
  let d : ℝ → ℝ := fun s => g.metricInner (γ s) (DJ s)
    (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
  change q t = t * d 0
  have hcont := jacobiRadialPairings_continuousOn g hJac hgeo hγc
  have hder (s : ℝ) (hs : s ∈ Ioo 0 b) :=
    jacobiRadialPairings_hasDerivAt g hJac hgeo hγc hs
  have hdconst : ∀ s ∈ Icc 0 b, d s = d 0 := by
    intro s hs
    exact eq_initial_of_hasDerivAt_zero hcont.2 (fun x hx => (hder x hx).2) hs
  have hzero : ∀ s ∈ Ioo 0 b, HasDerivAt (fun x => q x - x * d 0) 0 s := by
    intro s hs
    have hh := (hder s hs).1.sub ((hasDerivAt_id s).mul_const (d 0))
    change HasDerivAt (fun x => q x - x * d 0) (d s - 1 * d 0) s at hh
    simpa only [hdconst s (Ioo_subset_Icc_self hs), one_mul, sub_self] using hh
  have hconst := eq_initial_of_hasDerivAt_zero
    (hcont.1.sub (continuousOn_id.mul continuousOn_const)) hzero ht
  have hq0 : q 0 = 0 := by
    dsimp [q]
    rw [hJ0]
    exact g.metricInner_zero_left _ _
  change q t - t * d 0 = q 0 - 0 * d 0 at hconst
  simpa only [hq0, zero_mul, sub_zero, sub_eq_zero] using hconst

/-- **Math.** An initially normal Jacobi variation remains perpendicular to
the actual geodesic velocity on the entire closed segment. -/
theorem jacobiRadialPairing_eq_zero_of_initial_orthogonal
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s) (hJ0 : J 0 = 0)
    (horth : g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0)
    (ht : t ∈ Icc 0 b) :
    g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0 := by
  rw [jacobiRadialPairing_eq_time_mul_initial g hJac hgeo hγc hJ0 ht, horth, mul_zero]

#print axioms jacobiRadialPairings_hasDerivAt
#print axioms jacobiRadialPairings_continuousOn
#print axioms jacobiRadialPairing_eq_time_mul_initial
#print axioms jacobiRadialPairing_eq_zero_of_initial_orthogonal

end SystolicGrowth

end
