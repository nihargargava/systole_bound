module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.JacobiIntrinsicNormComparison

@[expose] public section

/-!
# Exact intrinsic angular Jacobi comparison at constant curvature

In dimension two, both an initially normal Jacobi field and its
covariant derivative lie in the one-dimensional normal space. Their
Cauchy--Schwarz equality makes the intrinsic norm equation exact.
-/

open Set Bundle Manifold Riemannian Riemannian.Geodesic Filter
open scoped ContDiff Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** In dimension two, two vectors orthogonal to a nonzero
radial vector have equality in the metric Cauchy--Schwarz inequality. -/
theorem metricInner_sq_eq_self_mul_self_of_normal_dim_two
    (g : RiemannianMetric I M) (p : M) (hdim : Module.finrank ℝ E = 2)
    (x y z : TangentSpace I p) (hz : z ≠ 0)
    (hxz : g.metricInner p x z = 0) (hyz : g.metricInner p y z = 0) :
    (g.metricInner p x y) ^ 2 = g.metricInner p x x * g.metricInner p y y := by
  classical
  by_contra hne
  let Q := g.metricInner p x x
  let D := g.metricInner p x y
  let V := g.metricInner p y y
  have hgap : Q * V - D ^ 2 ≠ 0 := by
    intro h
    apply hne
    change D ^ 2 = Q * V
    exact (sub_eq_zero.mp h).symm
  let w : Fin 3 → TangentSpace I p := ![z, x, y]
  have hw0 : w 0 = z := rfl
  have hw1 : w 1 = x := rfl
  have hw2 : w 2 = y := rfl
  have hlin : LinearIndependent ℝ w := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    have hzz := congrArg (fun u => g.metricInner p u z) ha
    have hxx := congrArg (fun u => g.metricInner p u x) ha
    have hyy := congrArg (fun u => g.metricInner p u y) ha
    simp only [Fin.sum_univ_three, hw0, hw1, hw2,
      g.metricInner_add_left, g.metricInner_smul_left,
      g.metricInner_zero_left, hxz, hyz, mul_zero, add_zero] at hzz
    have ha0 : a 0 = 0 := (mul_eq_zero.mp hzz).resolve_right
      (g.metricInner_self_pos p z hz).ne'
    simp only [Fin.sum_univ_three, hw0, hw1, hw2,
      g.metricInner_add_left, g.metricInner_smul_left,
      g.metricInner_zero_left, ha0, zero_mul, zero_add] at hxx hyy
    rw [g.metricInner_comm p y x] at hxx
    change a 1 * Q + a 2 * D = 0 at hxx
    change a 1 * D + a 2 * V = 0 at hyy
    have hp1 : a 1 * (Q * V - D ^ 2) = 0 := by
      linear_combination V * hxx - D * hyy
    have hp2 : a 2 * (Q * V - D ^ 2) = 0 := by
      linear_combination Q * hyy - D * hxx
    have ha1 : a 1 = 0 := (mul_eq_zero.mp hp1).resolve_right hgap
    have ha2 : a 2 = 0 := (mul_eq_zero.mp hp2).resolve_right hgap
    intro i
    fin_cases i
    · exact ha0
    · exact ha1
    · exact ha2
  have hcard := hlin.fintype_card_le_finrank
  change 3 ≤ Module.finrank ℝ E at hcard
  omega

/-- **Math.** Constant intrinsic curvature `-1` gives the exact negative
Gram value of the actual coordinate Jacobi curvature contraction. -/
theorem chartMetricInner_chartCurvature_eq_neg_gram
    (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source)
    (hK : ∀ x y : TangentSpace I p,
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y =
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (w v : E) :
    chartMetricInner g α (extChartAt I α p)
      (Jacobi.chartCurvature g α (extChartAt I α p) w v v) w =
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
  change _ = g.leviCivitaConnection.curvatureFormAt g p X Y Y X at hbound
  change g.leviCivitaConnection.curvatureFormAt g p X Y Y X = _ at hbridge
  rw [hbridge] at hbound
  nlinarith only [hbound]

/-- **Math.** Under actual constant curvature `-1`, the intrinsic Jacobi
energy derivative has exact derivative `|DJ|² + |J∧γ'|²`. The chart is
selected separately at each interior time. -/
theorem jacobiIntrinsicEnergy_hasDerivAt_of_constant_curvature
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {a b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ a b)
    (hgeo : IsGeodesicOn g γ (Icc a b))
    (hγc : ∀ s ∈ Icc a b, ContinuousAt γ s)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y =
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (DJ s) (J s))
      (g.metricInner (γ t) (DJ t) (DJ t) +
        (g.metricInner (γ t) (J t) (J t) * speedSq g γ t -
          g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) ^ 2)) t := by
  have htcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  obtain ⟨α, c, e, _, htce, _, hnbhd, hsrc, hJF⟩ := hJac t htcc
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
  have hev : (fun s => g.metricInner (γ s) (DJ s) (J s)) =ᶠ[𝓝 t]
      fun s => chartMetricInner g α (u s) (VDJ s) (VJ s) :=
    Filter.eventually_of_mem hnhds fun s hs => hrep DJ J s hs
  have hraw := hasDerivAt_chartMetricInner_along g α u VDJ VJ
    hu hDJd hJd hG hbase
  rw [hfst, hsnd, Jacobi.chartMetricInner_neg_left] at hraw
  have hcurv := chartMetricInner_chartCurvature_eq_neg_gram
    g hsrct (hK (γ t)) (VJ t) (deriv u t)
  have hJJ := hrep J J t htce
  have hDJDJ := hrep DJ DJ t htce
  have hvel : chartMetricInner g α (u t) (deriv u t) (deriv u t) = speedSq g γ t :=
    Jacobi.chartMetricInner_deriv_extChartAt (hgeo t htcc) (hγc t htcc) hsrct
  have hcross : chartMetricInner g α (u t) (VJ t) (deriv u t) =
      g.metricInner (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) := by
    have h := hrep J (fun s => mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) t htce
    rw [chartVectorRep_geodesic_velocity_eq_deriv
      (hgeo t htcc) (hγc t htcc) hsrct] at h
    exact h.symm
  rw [← hJJ, hvel, hcross] at hcurv
  rw [hcurv, ← hDJDJ, neg_neg, add_comm] at hraw
  exact hraw.congr_of_eventuallyEq hev

/-- **Math.** The covariant derivative of an initially normal Jacobi
field is also normal at every interior time, since the actual radial
pairing vanishes identically and its derivative is this pairing. -/
theorem jacobiRadialCovDerivative_pairing_eq_zero_of_initial_normal
    (g : RiemannianMetric I M) {γ : ℝ → M} {J DJ : ℝ → E} {b t : ℝ}
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s) (hJ0 : J 0 = 0)
    (horth0 : g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0)
    (ht : t ∈ Ioo 0 b) :
    g.metricInner (γ t) (DJ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) = 0 := by
  have hder := (jacobiRadialPairings_hasDerivAt g hJac hgeo hγc ht).1
  have hev : (fun s => g.metricInner (γ s) (J s)
      (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact jacobiRadialPairing_eq_zero_of_initial_orthogonal
      g hJac hgeo hγc hJ0 horth0 hs
  exact hder.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev)

/-- **Math.** At constant curvature `-1` on a surface, the intrinsic
normal Jacobi norm's derivative satisfies the exact hyperbolic equation
`f'' = speed² f`. Both normalities and Cauchy--Schwarz equality are derived
from the actual field and the dimension condition. -/
theorem jacobiIntrinsicNormSlope_hasDerivAt_of_constant_curvature
    (g : RiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    {γ : ℝ → M} {J DJ : ℝ → E} {b speed t : ℝ}
    (hspeed : 0 < speed)
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : IsGeodesicOn g γ (Icc 0 b))
    (hγc : ∀ s ∈ Icc 0 b, ContinuousAt γ s)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y =
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 ≠ 0)
    (horth0 : g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0)
    (ht : t ∈ Ioo 0 b) (hspeedt : speedSq g γ t = speed ^ 2) :
    HasDerivAt (jacobiIntrinsicNormSlope g γ J DJ)
      (speed ^ 2 * jacobiIntrinsicNorm g γ J t) t := by
  have hKle (p : M) (x y : TangentSpace I p) := (hK p x y).le
  have hpos := jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
    g hJac hgeo hγc hKle hJ0 hDJ0 ⟨ht.1, ht.2.le⟩
  have hne : J t ≠ 0 := by
    intro hh
    simp [jacobiIntrinsicNorm, hh] at hpos
  have horth := jacobiRadialPairing_eq_zero_of_initial_orthogonal
    g hJac hgeo hγc hJ0 horth0 (Ioo_subset_Icc_self ht)
  have hDJorth := jacobiRadialCovDerivative_pairing_eq_zero_of_initial_normal
    g hJac hgeo hγc hJ0 horth0 ht
  have hvelne : mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) ≠ 0 := by
    intro hh
    rw [speedSq_def, hh, g.metricInner_zero_left] at hspeedt
    nlinarith [sq_pos_of_pos hspeed]
  have hcs := metricInner_sq_eq_self_mul_self_of_normal_dim_two
    g (γ t) hdim (DJ t) (J t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) hvelne hDJorth horth
  have hd := jacobiIntrinsicEnergy_hasDerivAt_of_constant_curvature
    g hJac hgeo hγc hK ht
  rw [horth, hspeedt, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hd
  obtain ⟨_, hf, _, _⟩ := jacobiIntrinsicNorm_hasDerivAt_and_slope_lower_bound
    g hJac hgeo hγc hKle ht hne
  have hraw := hd.div hf hpos.ne'
  have hsq : jacobiIntrinsicNorm g γ J t ^ 2 = g.metricInner (γ t) (J t) (J t) :=
    Real.sq_sqrt (g.metricInner_self_nonneg _ _)
  have hcoef : ((g.metricInner (γ t) (DJ t) (DJ t) +
        g.metricInner (γ t) (J t) (J t) * speed ^ 2) * jacobiIntrinsicNorm g γ J t -
      g.metricInner (γ t) (DJ t) (J t) * jacobiIntrinsicNormSlope g γ J DJ t) /
        jacobiIntrinsicNorm g γ J t ^ 2 = speed ^ 2 * jacobiIntrinsicNorm g γ J t := by
    rw [jacobiIntrinsicNormSlope, ← hsq]
    rw [← hsq] at hcs
    field_simp
    nlinarith only [hcs]
  exact hcoef ▸ hraw

/-- **Math.** The actual normal Jacobi norm on a constant-curvature
surface is exactly the hyperbolic scalar solution throughout the segment.
Its initial slope and closed-interval continuity are derived internally. -/
theorem jacobiIntrinsicNorm_eq_sinh_of_initial_normal
    (g : RiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    {γ : ℝ → M} {J DJ : ℝ → E} {b speed : ℝ}
    (hb : 0 < b) (hspeed : 0 < speed)
    (hJac : Jacobi.IsJacobiFieldAlongOn g γ J DJ 0 b)
    (hgeo : IsGeodesic g γ) (hγc : Continuous γ)
    (hK : ∀ (p : M) (x y : TangentSpace I p),
      g.metricInner p x x * g.metricInner p y y -
        g.metricInner p x y * g.metricInner p x y =
      g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x)
    (hJ0 : J 0 = 0)
    (hDJ0norm : g.metricInner (γ 0) (DJ 0) (DJ 0) = speed ^ 2)
    (hspeed0 : speedSq g γ 0 = speed ^ 2)
    (horth0 : g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) = 0)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    jacobiIntrinsicNorm g γ J t = Real.sinh (speed * t) := by
  have hKle (p : M) (x y : TangentSpace I p) := (hK p x y).le
  let hgeoon : IsGeodesicOn g γ (Icc 0 b) := fun s _ => hgeo s
  have hc : ∀ s ∈ Icc 0 b, ContinuousAt γ s := fun _ _ => hγc.continuousAt
  have hDJ0 : DJ 0 ≠ 0 := by
    intro hh
    rw [hh, g.metricInner_zero_left] at hDJ0norm
    nlinarith [sq_pos_of_pos hspeed]
  have hinitial : Real.sqrt (g.metricInner (γ 0) (DJ 0) (DJ 0)) = speed := by
    rw [hDJ0norm, Real.sqrt_sq_eq_abs, abs_of_pos hspeed]
  let f := jacobiIntrinsicNorm g γ J
  let v := Function.update (jacobiIntrinsicNormSlope g γ J DJ) 0 speed
  have hcont := jacobiIntrinsicNorm_and_updatedSlope_continuousOn
    g hb hJac hgeoon hc hKle hJ0 hDJ0
  rw [hinitial] at hcont
  have hspeedSq (s : ℝ) : speedSq g γ s = speed ^ 2 := by
    have hguniv : IsGeodesicOn g γ univ := fun x _ => hgeo x
    exact (hguniv.speedSq_eq isOpen_univ isPreconnected_univ hγc.continuousOn
      (mem_univ s) (mem_univ 0)).trans hspeed0
  have hf (s : ℝ) (hs : s ∈ Ioo 0 b) : HasDerivAt f (v s) s := by
    have hpos := jacobiIntrinsicNorm_pos_of_initial_derivative_ne_zero
      g hJac hgeoon hc hKle hJ0 hDJ0 ⟨hs.1, hs.2.le⟩
    have hne : J s ≠ 0 := by
      intro hh
      simp [jacobiIntrinsicNorm, hh] at hpos
    obtain ⟨_, hder, _, _⟩ :=
      jacobiIntrinsicNorm_hasDerivAt_and_slope_lower_bound g hJac hgeoon hc hKle hs hne
    simpa only [v, Function.update_of_ne hs.1.ne'] using hder
  have hv (s : ℝ) (hs : s ∈ Ioo 0 b) : HasDerivAt v (speed ^ 2 * f s) s := by
    have hder := jacobiIntrinsicNormSlope_hasDerivAt_of_constant_curvature
      g hdim hspeed hJac hgeoon hc hK hJ0 hDJ0 horth0 hs (hspeedSq s)
    apply hder.congr_of_eventuallyEq
    filter_upwards [isOpen_ne.mem_nhds hs.1.ne'] with x hx
    exact Function.update_of_ne hx _ _
  have hupper : f t ≤ Real.sinh (speed * t) := by
    have hh := sinh_le_of_second_deriv_ge_mul_self_on_Icc
      (speed := -speed) (f := -f) (v := -v) hcont.1.neg hcont.2.neg
      (fun s hs => (hf s hs).neg)
      (fun s hs => ⟨_, (hv s hs).neg, by
        simp only [neg_sq, Pi.neg_apply, mul_neg]
        exact le_rfl⟩)
      (by simp [f, jacobiIntrinsicNorm, hJ0]) (by simp [v]) ht
    simpa only [neg_mul, Real.sinh_neg, Pi.neg_apply, neg_le_neg_iff] using hh
  exact le_antisymm hupper (sinh_le_jacobiIntrinsicNorm_of_initial_normal
    g hb hspeed hJac hgeo hγc hKle hJ0 hDJ0norm hspeed0 horth0 ht)

/-- **Math.** At constant curvature `-1` on a complete smooth surface,
the actual angular Jacobi field of the global exponential geodesic has
endpoint norm exactly `sinh r`. Only actual initial polar data are supplied;
the ray may cross arbitrarily many charts. -/
theorem exponentialAngularJacobi_intrinsicNorm_eq_sinh [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (e : Fin 2 → E) (hdim : Module.finrank ℝ E = 2) (θ r : ℝ) (hr : 0 < r)
    (he : ∀ i j : Fin 2,
      chartMetricInner g p (extChartAt I p p) (e i) (e j) =
        if i = j then 1 else 0)
    (hK : ∀ (q : M) (x y : TangentSpace I q),
      g.metricInner q x x * g.metricInner q y y -
        g.metricInner q x y * g.metricInner q x y =
      g.metricInner q (g.leviCivitaConnection.curvatureOperatorAt q x y y) x)
    {J DJ : ℝ → E}
    (hJac : Jacobi.IsJacobiFieldAlongOn g
      (globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)) J DJ 0 1)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 = r • exponentialPolarNormal e θ) :
    jacobiIntrinsicNorm g
      (globalGeodesic (I := I) g hg p (r • exponentialPolarUnit e θ)) J 1 = Real.sinh r := by
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
  simpa only [mul_one] using jacobiIntrinsicNorm_eq_sinh_of_initial_normal
    g hdim zero_lt_one hr hJac hgeo hc hK hJ0 hDJnorm hspeed0 horth0
      (by norm_num : (1 : ℝ) ∈ Icc 0 1)

#print axioms metricInner_sq_eq_self_mul_self_of_normal_dim_two
#print axioms chartMetricInner_chartCurvature_eq_neg_gram
#print axioms jacobiIntrinsicEnergy_hasDerivAt_of_constant_curvature
#print axioms jacobiRadialCovDerivative_pairing_eq_zero_of_initial_normal
#print axioms jacobiIntrinsicNormSlope_hasDerivAt_of_constant_curvature
#print axioms jacobiIntrinsicNorm_eq_sinh_of_initial_normal
#print axioms exponentialAngularJacobi_intrinsicNorm_eq_sinh

end
end SystolicGrowth
