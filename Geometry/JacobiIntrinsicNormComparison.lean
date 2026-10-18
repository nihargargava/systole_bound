module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.JacobiRadialPairing
public import Geometry.JacobiCurvatureCoefficient
public import Geometry.ExponentialPolarMetric
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.JacobiNonpositiveManifold
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Intrinsic Jacobi norm comparison

Intrinsic energy and its derivative are computed by localizing at each
time separately. Their curvature inequality therefore survives all chart
changes along the geodesic.
-/

open Set Bundle Manifold Riemannian Filter
open Riemannian.Geodesic
open scoped ContDiff Manifold Topology

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
/-- **Math.** Cauchy--Schwarz for the actual metric, proved from its
positive quadratic form. -/
theorem metricInner_sq_le_self_mul_self
    (g : RiemannianMetric I M) (p : M) (x y : TangentSpace I p) :
    (g.metricInner p x y) ^ 2 ≤ g.metricInner p x x * g.metricInner p y y := by
  by_cases hx : x = 0
  · simp [hx]
  have hxpos := g.metricInner_self_pos p x hx
  have h := g.metricInner_self_nonneg p
    ((g.metricInner p x y) • x - (g.metricInner p x x) • y)
  simp only [g.metricInner_sub_left, g.metricInner_sub_right,
    g.metricInner_smul_left, g.metricInner_smul_right] at h
  rw [g.metricInner_comm p y x] at h
  have hprod : 0 ≤ g.metricInner p x x *
      (g.metricInner p x x * g.metricInner p y y - (g.metricInner p x y) ^ 2) := by
    nlinarith only [h]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hxpos).mp hprod)

/-- **Math.** The actual intrinsic curvature Gram bound transfers to
the coordinate Jacobi curvature contraction with its correct opposite sign. -/
theorem chartMetricInner_chartCurvature_le_neg_gram
    (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source)
    (hK : ∀ x y : TangentSpace I p,
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (w v : E) :
    chartMetricInner g α (extChartAt I α p)
      (Jacobi.chartCurvature g α (extChartAt I α p) w v v) w ≤
      -(chartMetricInner g α (extChartAt I α p) w w *
        chartMetricInner g α (extChartAt I α p) v v -
        chartMetricInner g α (extChartAt I α p) w v ^ 2) := by
  let X := (trivializationAt E (TangentSpace I) α).symm p w
  let Y := (trivializationAt E (TangentSpace I) α).symm p v
  have hbound := hK X Y
  rw [← Jacobi.curvatureFormAt_eq_metricInner] at hbound
  have hbridge := Jacobi.curvatureFormAt_chartFrame g hp w v v w
  rw [← Riemannian.trivializationAt_symm_eq_sum_chartBasisVecFiber α p w hp,
    ← Riemannian.trivializationAt_symm_eq_sum_chartBasisVecFiber α p v hp] at hbridge
  have hmetric (a c : E) :=
    Riemannian.chartMetricInner_extChartAt_eq_metricInner g α hp a c
  rw [← hmetric w w, ← hmetric v v, ← hmetric w v] at hbound
  change _ ≤ g.leviCivitaConnection.curvatureFormAt g p X Y Y X at hbound
  change g.leviCivitaConnection.curvatureFormAt g p X Y Y X = _ at hbridge
  rw [hbridge] at hbound
  nlinarith only [hbound]

/-- **Math.** At each interior time, the intrinsic energy `q=|J|²`
satisfies `q'=2d`, where `d=⟨DJ,J⟩`. Its actual derivative satisfies
`d' ≥ |DJ|² + |J∧γ'|²` under `K ≤ -1`. No chart contains the whole ray
and no transported frame is assumed. -/
theorem jacobiIntrinsicEnergy_hasDerivAt_of_curvature_bound
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {a b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ a b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (J s) (J s))
      (2 * g.metricInner (γ t) (DJ t) (J t)) t ∧
    ∃ d : ℝ,
      HasDerivAt (fun s => g.metricInner (γ s) (DJ s) (J s)) d t ∧
      g.metricInner (γ t) (DJ t) (DJ t) +
        (g.metricInner (γ t) (J t) (J t) * Geodesic.speedSq g γ t -
          g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) ^ 2) ≤ d := by
  have htcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  obtain ⟨α, c, e, _, htce, hsub, hnbhd, hsrc, hJF⟩ := hJac t htcc
  have hnhds : Icc c e ∈ 𝓝 t := by
    rwa [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds ht.1 ht.2)] at hnbhd
  have htioo : t ∈ Ioo c e := by
    have h := mem_interior_iff_mem_nhds.mpr hnhds
    rwa [interior_Icc] at h
  let u : ℝ → E := fun s => extChartAt I α (γ s)
  let VJ := Jacobi.chartVectorRep (I := I) γ α J
  let VDJ := Jacobi.chartVectorRep (I := I) γ α DJ
  have hsrct := hsrc t htce
  have hu : DifferentiableAt ℝ u t :=
    Jacobi.IsGeodesicOn.differentiableAt_extChartAt hgeo htcc (hγc t htcc) hsrct
  have hJd : DifferentiableAt ℝ VJ t :=
    ((hJF.hasDerivWithinAt_fst t htce).hasDerivAt hnhds).differentiableAt
  have hDJd : DifferentiableAt ℝ VDJ t :=
    ((hJF.hasDerivWithinAt_snd t htce).hasDerivAt hnhds).differentiableAt
  have hymem : u t ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrct)
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE g α i j) (u t) :=
    fun i j => Jacobi.differentiableAt_chartGramOnE g α hymem i j
  have hbase : (extChartAt I α).symm (u t) ∈
      (trivializationAt E (TangentSpace I) α).baseSet :=
    Jacobi.symm_extChartAt_mem_baseSet hsrct
  have hfst : covariantDerivCoord g α u VJ t = VDJ t :=
    hJF.covariantDerivCoord_fst htioo
  have hsnd : covariantDerivCoord g α u VDJ t =
      -Jacobi.chartCurvature g α (u t) (VJ t) (deriv u t) (deriv u t) :=
    hJF.covariantDerivCoord_snd htioo
  have hrep (V W : ℝ → E) (s : ℝ) (hs : s ∈ Icc c e) :
      g.metricInner (γ s) (V s) (W s) =
        chartMetricInner g α (u s)
          (Jacobi.chartVectorRep (I := I) γ α V s)
          (Jacobi.chartVectorRep (I := I) γ α W s) :=
    Jacobi.metricInner_eq_chartMetricInner_rep g (hsrc s hs) V W
  have hev (V W : ℝ → E) :
      (fun s => g.metricInner (γ s) (V s) (W s)) =ᶠ[𝓝 t]
        fun s => chartMetricInner g α (u s)
          (Jacobi.chartVectorRep (I := I) γ α V s)
          (Jacobi.chartVectorRep (I := I) γ α W s) :=
    Filter.eventually_of_mem hnhds fun s hs => hrep V W s hs
  constructor
  · have hraw := hasDerivAt_chartMetricInner_along g α u VJ VJ
      hu hJd hJd hG hbase
    rw [hfst, chartMetricInner_symm g α (u t) (VJ t) (VDJ t)] at hraw
    have hvalue : chartMetricInner g α (u t) (VDJ t) (VJ t) +
        chartMetricInner g α (u t) (VDJ t) (VJ t) =
        2 * g.metricInner (γ t) (DJ t) (J t) := by
      rw [← hrep DJ J t htce]
      ring
    rw [hvalue] at hraw
    exact hraw.congr_of_eventuallyEq (hev J J)
  · have hraw := hasDerivAt_chartMetricInner_along g α u VDJ VJ
      hu hDJd hJd hG hbase
    rw [hfst, hsnd, Jacobi.chartMetricInner_neg_left] at hraw
    refine ⟨_, hraw.congr_of_eventuallyEq (hev DJ J), ?_⟩
    have hcurv := chartMetricInner_chartCurvature_le_neg_gram
      g hsrct (hK (γ t)) (VJ t) (deriv u t)
    have hJJ := hrep J J t htce
    have hDJDJ := hrep DJ DJ t htce
    have hvel : chartMetricInner g α (u t) (deriv u t) (deriv u t) =
        Geodesic.speedSq g γ t :=
      Jacobi.chartMetricInner_deriv_extChartAt (hgeo t htcc) (hγc t htcc) hsrct
    have hcross : chartMetricInner g α (u t) (VJ t) (deriv u t) =
        g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
      have h := hrep J (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) t htce
      rw [chartVectorRep_geodesic_velocity_eq_deriv
        (hgeo t htcc) (hγc t htcc) hsrct] at h
      exact h.symm
    rw [← hJJ, hvel, hcross] at hcurv
    rw [← hDJDJ]
    linarith only [hcurv]

/-- **Math.** The actual intrinsic metric length of a tangent field along a curve. -/
def jacobiIntrinsicNorm (g : RiemannianMetric I M) (γ : ℝ → M) (J : ℝ → E)
    (t : ℝ) : ℝ := Real.sqrt (g.metricInner (γ t) (J t) (J t))

/-- **Math.** The derivative expression for intrinsic Jacobi length away from zero. -/
def jacobiIntrinsicNormSlope (g : RiemannianMetric I M) (γ : ℝ → M)
    (J DJ : ℝ → E) (t : ℝ) : ℝ :=
  g.metricInner (γ t) (DJ t) (J t) / jacobiIntrinsicNorm g γ J t

/-- **Math.** Wherever the actual Jacobi field is nonzero, its intrinsic
norm is twice differentiable and satisfies
`f'' ≥ |J∧γ'|² / f`. This is proved from the local covariant equations,
the actual curvature bound, and Cauchy--Schwarz. It does not assume a
globally defined parallel frame or a global coordinate chart. -/
theorem jacobiIntrinsicNorm_hasDerivAt_and_slope_lower_bound
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {a b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ a b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (ht : t ∈ Ioo a b) (hne : J t ≠ 0) :
    ∃ d : ℝ,
      HasDerivAt (jacobiIntrinsicNorm g γ J) (jacobiIntrinsicNormSlope g γ J DJ t) t ∧
      HasDerivAt (jacobiIntrinsicNormSlope g γ J DJ) d t ∧
      (g.metricInner (γ t) (J t) (J t) * Geodesic.speedSq g γ t -
        g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) ^ 2) /
          jacobiIntrinsicNorm g γ J t ≤ d := by
  let q : ℝ → ℝ := fun s => g.metricInner (γ s) (J s) (J s)
  let d : ℝ → ℝ := fun s => g.metricInner (γ s) (DJ s) (J s)
  let f : ℝ → ℝ := jacobiIntrinsicNorm g γ J
  let G := q t * Geodesic.speedSq g γ t -
    g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) ^ 2
  obtain ⟨hqder, dd, hdder, hdd⟩ :=
    jacobiIntrinsicEnergy_hasDerivAt_of_curvature_bound g hJac hgeo hγc hK ht
  have hqpos : 0 < q t := g.metricInner_self_pos (γ t) (J t) hne
  have hfpos : 0 < f t := Real.sqrt_pos.mpr hqpos
  have hfsq : (f t) ^ 2 = q t := Real.sq_sqrt hqpos.le
  have hfder : HasDerivAt f (d t / f t) t := by
    have hh := hqder.sqrt hqpos.ne'
    have hvalue : 2 * d t / (2 * f t) = d t / f t := by ring
    exact hvalue ▸ hh
  let A := (dd * f t - d t * (d t / f t)) / (f t) ^ 2
  have hA : HasDerivAt (jacobiIntrinsicNormSlope g γ J DJ) A t :=
    hdder.div hfder hfpos.ne'
  have hAform : A * (f t) ^ 3 = dd * q t - (d t) ^ 2 := by
    dsimp only [A]
    rw [← hfsq]
    field_simp
  have hcs : (d t) ^ 2 ≤ g.metricInner (γ t) (DJ t) (DJ t) * q t :=
    metricInner_sq_le_self_mul_self g (γ t) (DJ t) (J t)
  have hlower : G * q t ≤ A * (f t) ^ 3 := by
    have hh := mul_le_mul_of_nonneg_right hdd hqpos.le
    change (g.metricInner (γ t) (DJ t) (DJ t) + G) * q t ≤ dd * q t at hh
    nlinarith only [hh, hcs, hAform]
  have hlower' : G * (f t) ^ 2 ≤ (A * f t) * (f t) ^ 2 := by
    rw [← hfsq] at hlower
    nlinarith only [hlower]
  refine ⟨A, hfder, hA, ?_⟩
  change G / f t ≤ A
  apply (div_le_iff₀ hfpos).mpr
  exact le_of_mul_le_mul_right hlower' (sq_pos_of_pos hfpos)

/-- **Math.** An actual Jacobi field with nonzero initial covariant
derivative and zero initial value cannot vanish again under `K ≤ -1`.
This uses the verified intrinsic nonpositive-curvature energy squeeze. -/
theorem jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 ≠ 0) (ht : t ∈ Ioc 0 b) :
    0 < jacobiIntrinsicNorm g γ J t := by
  apply Real.sqrt_pos.mpr
  apply g.metricInner_self_pos
  intro hJt
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
  have hrestrict := hJac.mono le_rfl ht.1 ht.2
  have hnonpos : ∀ (p : M) (x y : TangentSpace I p),
      0 ≤ g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x := by
    intro p x y
    exact (sub_nonneg.mpr (metricInner_sq_le_self_mul_self g p x y)).trans
      (by simpa only [pow_two] using hK p x y)
  have hzero := Jacobi.IsJacobiFieldAlongOn.forall_eq_zero_of_nonpos_of_endpoints
    g ht.1 hrestrict (fun s hs => hgeo s (hsub hs))
    (fun s hs => hγc s (hsub hs)) hnonpos hJ0 hJt
  exact hDJ0 (hrestrict.deriv_eq_zero_of_forall_eq_zero ht.1 hzero)

omit [SigmaCompactSpace M] in
/-- **Math.** Actual pairings of a Jacobi field and its covariant
derivative are continuous on the whole segment, including both endpoints. -/
theorem jacobiIntrinsicPairing_continuousOn
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ V W : ℝ → E} {a b : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ a b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s)
    (hV : V = J ∨ V = DJ) (hW : W = J ∨ W = DJ) :
    ContinuousOn (fun s => g.metricInner (γ s) (V s) (W s)) (Icc a b) := by
  intro t ht
  obtain ⟨α, c, e, _, htce, hsub, hnbhd, hsrc, hJF⟩ := hJac t ht
  let u : ℝ → E := fun s => extChartAt I α (γ s)
  have hu : ContinuousOn u (Icc c e) := by
    intro s hs
    exact (Jacobi.IsGeodesicOn.differentiableAt_extChartAt hgeo (hsub hs)
      (hγc s (hsub hs)) (hsrc s hs)).continuousAt.continuousWithinAt
  have hmem : ∀ s ∈ Icc c e, u s ∈ (extChartAt I α).target :=
    fun s hs => (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc s hs)
  have hVc : ContinuousOn (Jacobi.chartVectorRep (I := I) γ α V) (Icc c e) := by
    rcases hV with rfl | rfl
    · exact hJF.continuousOn_fst
    · exact hJF.continuousOn_snd
  have hWc : ContinuousOn (Jacobi.chartVectorRep (I := I) γ α W) (Icc c e) := by
    rcases hW with rfl | rfl
    · exact hJF.continuousOn_fst
    · exact hJF.continuousOn_snd
  have hraw := Jacobi.continuousOn_chartMetricInner_pairing g α hu hmem hVc hWc
  have hrep (s : ℝ) (hs : s ∈ Icc c e) :=
    Jacobi.metricInner_eq_chartMetricInner_rep g (hsrc s hs) V W
  refine ((hraw t htce).mono_of_mem_nhdsWithin hnbhd).congr_of_eventuallyEq
    (Filter.eventually_of_mem hnbhd fun s hs => hrep s hs) (hrep t htce)

omit [SigmaCompactSpace M] in
private theorem tendsto_chartMetricInner_of_tendsto
    {X : Type*} {l : Filter X} (g : RiemannianMetric I M) (α : M)
    {u V W : X → E} {y v w : E} (hy : y ∈ (extChartAt I α).target)
    (hu : Tendsto u l (𝓝 y)) (hV : Tendsto V l (𝓝 v)) (hW : Tendsto W l (𝓝 w)) :
    Tendsto (fun s => chartMetricInner g α (u s) (V s) (W s)) l
      (𝓝 (chartMetricInner g α y v w)) := by
  simp only [chartMetricInner_def]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  exact (((Jacobi.differentiableAt_chartGramOnE g α hy i j).continuousAt.tendsto.comp
    hu).mul ((Geodesic.chartCoordFunctional (E := E) i).continuous.tendsto v |>.comp hV)).mul
      ((Geodesic.chartCoordFunctional (E := E) j).continuous.tendsto w |>.comp hW)

omit [SigmaCompactSpace M] in
/-- **Math.** The right limit of the actual intrinsic norm derivative at
the zero initial Jacobi value is the metric length of its initial covariant
derivative. The proof uses only the actual local Jacobi equation at time zero. -/
theorem jacobiIntrinsicNormSlope_tendsto_initial
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b : ℝ}
    (hb : 0 < b) (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 ≠ 0) :
    Tendsto (jacobiIntrinsicNormSlope g γ J DJ) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (g.metricInner (γ 0) (DJ 0) (DJ 0)))) := by
  obtain ⟨α, c, e, hce, htce, hsub, _, hsrc, hJF⟩ := hJac 0 ⟨le_rfl, hb.le⟩
  have hc0 : c = 0 := le_antisymm htce.1 ((hsub (left_mem_Icc.mpr hce.le)).1)
  subst c
  have he : 0 < e := hce
  let u : ℝ → E := fun s => extChartAt I α (γ s)
  let VJ := Jacobi.chartVectorRep (I := I) γ α J
  let VDJ := Jacobi.chartVectorRep (I := I) γ α DJ
  let B : ℝ → E := fun s => s⁻¹ • VJ s
  have hVJ0 : VJ 0 = 0 := by simp [VJ, hJ0]
  have hraw := hJF.hasDerivWithinAt_fst 0 ⟨le_rfl, he.le⟩
  change HasDerivWithinAt VJ
    (VDJ 0 - chartChristoffelContraction g α (deriv u 0) (VJ 0) (u 0))
      (Icc 0 e) 0 at hraw
  have hzero : chartChristoffelContraction g α (deriv u 0) (VJ 0) (u 0) = 0 := by
    rw [hVJ0, chartChristoffelContraction_symm, chartChristoffelContraction_zero_left]
  have hVJder : HasDerivWithinAt VJ (VDJ 0) (Icc 0 e) 0 := by
    simpa only [hzero, sub_zero] using hraw
  have hB : Tendsto B (𝓝[>] (0 : ℝ)) (𝓝 (VDJ 0)) := by
    have hh := hasDerivWithinAt_iff_tendsto_slope.mp hVJder
    have hset : Icc (0 : ℝ) e \ {0} = Ioc 0 e := by
      ext s
      simp only [Set.mem_sdiff, mem_Icc, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨hs, hne⟩
        exact ⟨lt_of_le_of_ne hs.1 (Ne.symm hne), hs.2⟩
      · exact fun hs => ⟨⟨hs.1.le, hs.2⟩, hs.1.ne'⟩
    rw [hset, nhdsWithin_Ioc_eq_nhdsGT he] at hh
    change Tendsto (fun s => (s - 0)⁻¹ • (VJ s - VJ 0))
      (𝓝[>] (0 : ℝ)) (𝓝 (VDJ 0)) at hh
    simpa only [sub_zero, hVJ0] using hh
  have hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 (u 0)) :=
    (Jacobi.IsGeodesicOn.differentiableAt_extChartAt hgeo ⟨le_rfl, hb.le⟩
      (hγc 0 ⟨le_rfl, hb.le⟩) (hsrc 0 ⟨le_rfl, he.le⟩)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hVDJ : Tendsto VDJ (𝓝[>] (0 : ℝ)) (𝓝 (VDJ 0)) := by
    have hh := hJF.continuousOn_snd 0 ⟨le_rfl, he.le⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE he] at hh
    exact hh.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  have hy : u 0 ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc 0 ⟨le_rfl, he.le⟩)
  have hBB := tendsto_chartMetricInner_of_tendsto g α hy hu hB hB
  have hDB := tendsto_chartMetricInner_of_tendsto g α hy hu hVDJ hB
  have hmetric := Jacobi.metricInner_eq_chartMetricInner_rep
    g (hsrc 0 ⟨le_rfl, he.le⟩) DJ DJ
  change g.metricInner (γ 0) (DJ 0) (DJ 0) =
    chartMetricInner g α (u 0) (VDJ 0) (VDJ 0) at hmetric
  have hpos : 0 < chartMetricInner g α (u 0) (VDJ 0) (VDJ 0) := by
    rw [← hmetric]
    exact g.metricInner_self_pos _ _ hDJ0
  have hlimit := hDB.div (Real.continuous_sqrt.tendsto _ |>.comp hBB)
    (Real.sqrt_pos.mpr hpos).ne'
  have hvalue : chartMetricInner g α (u 0) (VDJ 0) (VDJ 0) /
      Real.sqrt (chartMetricInner g α (u 0) (VDJ 0) (VDJ 0)) =
      Real.sqrt (g.metricInner (γ 0) (DJ 0) (DJ 0)) := by
    rw [← hmetric]
    apply (div_eq_iff (Real.sqrt_pos.mpr (g.metricInner_self_pos _ _ hDJ0)).ne').mpr
    exact (Real.mul_self_sqrt (g.metricInner_self_nonneg _ _)).symm
  rw [hvalue] at hlimit
  apply hlimit.congr'
  filter_upwards [Ioc_mem_nhdsGT he] with s hs
  have hrepJJ := Jacobi.metricInner_eq_chartMetricInner_rep g (hsrc s ⟨hs.1.le, hs.2⟩) J J
  have hrepDJJ := Jacobi.metricInner_eq_chartMetricInner_rep g (hsrc s ⟨hs.1.le, hs.2⟩) DJ J
  have hVJB : VJ s = s • B s := by simp [B, smul_smul, hs.1.ne']
  have hJJ : g.metricInner (γ s) (J s) (J s) =
      s ^ 2 * chartMetricInner g α (u s) (B s) (B s) := by
    rw [hrepJJ]
    change chartMetricInner g α (u s) (VJ s) (VJ s) = _
    rw [hVJB, chartMetricInner_smul_left, chartMetricInner_smul_right]
    ring
  have hDJJ : g.metricInner (γ s) (DJ s) (J s) =
      s * chartMetricInner g α (u s) (VDJ s) (B s) := by
    rw [hrepDJJ]
    change chartMetricInner g α (u s) (VDJ s) (VJ s) = _
    rw [hVJB, chartMetricInner_smul_right]
  rw [jacobiIntrinsicNormSlope, jacobiIntrinsicNorm, hJJ, hDJJ,
    Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_pos hs.1]
  simp only [Pi.div_apply, Function.comp_apply, mul_div_mul_left _ _ hs.1.ne']

/-- **Math.** The intrinsic norm and its actual derivative extended by
the initial derivative length are continuous on the entire closed segment. -/
theorem jacobiIntrinsicNorm_and_updatedSlope_continuousOn
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b : ℝ}
    (hb : 0 < b) (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : Geodesic.IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 ≠ 0) :
    ContinuousOn (jacobiIntrinsicNorm g γ J) (Icc 0 b) ∧
    ContinuousOn (Function.update (jacobiIntrinsicNormSlope g γ J DJ) 0
      (Real.sqrt (g.metricInner (γ 0) (DJ 0) (DJ 0)))) (Icc 0 b) := by
  have hqcont := jacobiIntrinsicPairing_continuousOn g hJac hgeo hγc
    (V := J) (W := J) (Or.inl rfl) (Or.inl rfl)
  have hdcont := jacobiIntrinsicPairing_continuousOn g hJac hgeo hγc
    (V := DJ) (W := J) (Or.inr rfl) (Or.inl rfl)
  have hfcont : ContinuousOn (jacobiIntrinsicNorm g γ J) (Icc 0 b) :=
    Real.continuous_sqrt.comp_continuousOn hqcont
  refine ⟨hfcont, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    rw [continuousWithinAt_update_same, Icc_sdiff_left, nhdsWithin_Ioc_eq_nhdsGT hb]
    exact jacobiIntrinsicNormSlope_tendsto_initial g hb hJac hgeo hγc hJ0 hDJ0
  · rw [continuousWithinAt_update_of_ne ht0]
    exact (hdcont t ht).div (hfcont t ht)
      (jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
        g hJac hgeo hγc hK hJ0 hDJ0 ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩).ne'

/-- **Math.** A globally defined actual geodesic and its initially normal
Jacobi field satisfy the full intrinsic hyperbolic norm comparison.
The initial squared lengths are genuine metric data. Normality everywhere,
absence of zeros, endpoint slope, and the comparison inequality are derived
internally; there is no whole-ray chart-containment premise. -/
theorem sinh_le_jacobiIntrinsicNorm_of_initial_normal
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b speed : ℝ}
    (hb : 0 < b) (hspeed : 0 < speed)
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : Geodesic.IsGeodesic g γ) (hγc : Continuous γ)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y ≤
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hJ0 : J 0 = 0)
    (hDJ0norm : g.metricInner (γ 0) (DJ 0) (DJ 0) = speed ^ 2)
    (hspeed0 : Geodesic.speedSq g γ 0 = speed ^ 2)
    (horth0 : g.metricInner (γ 0) (DJ 0)
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    Real.sinh (speed * t) ≤ jacobiIntrinsicNorm g γ J t := by
  let hgeoon : Geodesic.IsGeodesicOn g γ (Icc 0 b) := fun s _ => hgeo s
  have hc : ∀ s ∈ Icc 0 b, ContinuousAt γ s := fun _ _ => hγc.continuousAt
  have hDJ0 : DJ 0 ≠ 0 := by
    intro hh
    rw [hh, g.metricInner_zero_left] at hDJ0norm
    nlinarith [sq_pos_of_pos hspeed]
  have hinitial : Real.sqrt (g.metricInner (γ 0) (DJ 0) (DJ 0)) = speed := by
    rw [hDJ0norm, Real.sqrt_sq_eq_abs, abs_of_pos hspeed]
  let v := Function.update (jacobiIntrinsicNormSlope g γ J DJ) 0 speed
  have hcont := jacobiIntrinsicNorm_and_updatedSlope_continuousOn
    g hb hJac hgeoon hc hK hJ0 hDJ0
  rw [hinitial] at hcont
  have hvder (s : ℝ) (hs : s ∈ Ioo 0 b) :
      ∃ d, HasDerivAt v d s ∧ speed ^ 2 * jacobiIntrinsicNorm g γ J s ≤ d := by
    have hpos := jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
      g hJac hgeoon hc hK hJ0 hDJ0 ⟨hs.1, hs.2.le⟩
    have hne : J s ≠ 0 := by
      intro hh
      simp [jacobiIntrinsicNorm, hh] at hpos
    obtain ⟨d, _, hd, hineq⟩ :=
      jacobiIntrinsicNorm_hasDerivAt_and_slope_lower_bound g hJac hgeoon hc hK hs hne
    have horth := jacobiRadialPairing_eq_zero_of_initial_orthogonal
      g hJac hgeoon hc hJ0 horth0 (Ioo_subset_Icc_self hs)
    have hspeedSq : Geodesic.speedSq g γ s = speed ^ 2 := by
      have hguniv : Geodesic.IsGeodesicOn g γ univ := fun x _ => hgeo x
      exact (hguniv.speedSq_eq isOpen_univ isPreconnected_univ hγc.continuousOn
        (mem_univ s) (mem_univ 0)).trans hspeed0
    have hgram : (g.metricInner (γ s) (J s) (J s) * Geodesic.speedSq g γ s -
        g.metricInner (γ s) (J s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) ^ 2) /
        jacobiIntrinsicNorm g γ J s = speed ^ 2 * jacobiIntrinsicNorm g γ J s := by
      rw [horth, hspeedSq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
      have hsq : jacobiIntrinsicNorm g γ J s ^ 2 = g.metricInner (γ s) (J s) (J s) :=
        Real.sq_sqrt (g.metricInner_self_nonneg _ _)
      rw [← hsq]
      field_simp
    rw [hgram] at hineq
    refine ⟨d, hd.congr_of_eventuallyEq ?_, hineq⟩
    filter_upwards [isOpen_ne.mem_nhds hs.1.ne'] with x hx
    exact Function.update_of_ne hx _ _
  apply sinh_le_of_second_deriv_ge_mul_self_on_Icc hcont.1 hcont.2
    (v := v) (speed := speed) ?_ hvder ?_ ?_ ht
  · intro s hs
    have hpos := jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
      g hJac hgeoon hc hK hJ0 hDJ0 ⟨hs.1, hs.2.le⟩
    have hne : J s ≠ 0 := by
      intro hh
      simp [jacobiIntrinsicNorm, hh] at hpos
    obtain ⟨_, hf, _, _⟩ :=
      jacobiIntrinsicNorm_hasDerivAt_and_slope_lower_bound g hJac hgeoon hc hK hs hne
    simpa only [v, Function.update_of_ne hs.1.ne'] using hf
  · simp [jacobiIntrinsicNorm, hJ0]
  · simp [v]

/-- **Math.** The actual angular Jacobi field of the complete-manifold
exponential geodesic has endpoint length at least `sinh r`, even when the
geodesic crosses charts. All initial metric and orthogonality data are
derived from the initial polar orthonormal pair. -/
theorem sinh_le_exponentialAngularJacobi_intrinsicNorm [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y ≤
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    {J DJ : ℝ → E}
    (hJac : Jacobi.IsJacobiFieldAlongOn g
      (globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)) J DJ 0 1)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 = r • exponentialPolarNormal e θ) :
    Real.sinh r ≤ jacobiIntrinsicNorm g
      (globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)) J 1 := by
  let γ := globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p (r • exponentialPolarUnit e θ)
  have hc : Continuous γ := continuous_globalGeodesic g hg p (r • exponentialPolarUnit e θ)
  have hgeo : IsGeodesic g γ := isGeodesic_globalGeodesic g hg p (r • exponentialPolarUnit e θ)
  have hsrc0 : γ 0 ∈ (chartAt H p).source := by
    rw [hγ0]
    exact mem_chart_source H p
  have hvel0 : deriv (fun s => extChartAt I p (γ s)) 0 = r • exponentialPolarUnit e θ :=
    (hasDerivAt_chartReading_globalGeodesic g hg p (r • exponentialPolarUnit e θ)).deriv
  have hDJrep : Jacobi.chartVectorRep (I := I) γ p DJ 0 = r • exponentialPolarNormal e θ := by
    rw [Jacobi.chartVectorRep_apply, hγ0, hDJ0]
    exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)
  have hrot := exponentialPolarDirections_chartMetric g p e he θ
  have hDJnorm : g.metricInner (γ 0) (DJ 0) (DJ 0) = r ^ 2 := by
    rw [Jacobi.metricInner_eq_chartMetricInner_rep g hsrc0 DJ DJ,
      hDJrep, hγ0, chartMetricInner_smul_left, chartMetricInner_smul_right, hrot.2.2]
    ring
  have hspeed0 : speedSq g γ 0 = r ^ 2 := by
    have hh := Jacobi.chartMetricInner_deriv_extChartAt (hgeo 0) hc.continuousAt hsrc0
    rw [hvel0, hγ0, chartMetricInner_smul_left, chartMetricInner_smul_right, hrot.1] at hh
    nlinarith only [hh]
  have horth0 : g.metricInner (γ 0) (DJ 0)
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0 := by
    rw [Jacobi.metricInner_eq_chartMetricInner_rep g hsrc0 DJ
      (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)),
      chartVectorRep_geodesic_velocity_eq_deriv (hgeo 0) hc.continuousAt hsrc0,
      hDJrep, hvel0, hγ0, chartMetricInner_smul_left, chartMetricInner_smul_right,
      chartMetricInner_symm g p _ (exponentialPolarNormal e θ) (exponentialPolarUnit e θ),
      hrot.2.1]
    simp
  simpa only [mul_one] using sinh_le_jacobiIntrinsicNorm_of_initial_normal g
    zero_lt_one hr hJac hgeo hc hK hJ0 hDJnorm hspeed0 horth0
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)

#print axioms metricInner_sq_le_self_mul_self
#print axioms chartMetricInner_chartCurvature_le_neg_gram
#print axioms jacobiIntrinsicEnergy_hasDerivAt_of_curvature_bound
#print axioms jacobiIntrinsicNorm_hasDerivAt_and_slope_lower_bound
#print axioms jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
#print axioms jacobiIntrinsicPairing_continuousOn
#print axioms jacobiIntrinsicNormSlope_tendsto_initial
#print axioms jacobiIntrinsicNorm_and_updatedSlope_continuousOn
#print axioms sinh_le_jacobiIntrinsicNorm_of_initial_normal
#print axioms sinh_le_exponentialAngularJacobi_intrinsicNorm

end
end SystolicGrowth
