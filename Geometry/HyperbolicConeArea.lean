module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingWarpedGaussianCurvature
public import Geometry.GluingCircleAngularMeasure
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.JacobiNonpositiveCurvature
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# Genuine punctured hyperbolic-cone coordinate area

The angular variable has the existing circle arclength measure of total
length `2π`. The radial tensor is `dt² + (a/(2π) sinh t)² dθ²` for `t > 0`.
Its actual connection, curvature and determinant give the measure computed
below. A radial cylinder strip is not yet identified with a metric ball in
the completed cone, or with a disk in a general Alexandrov surface.
-/

open Set Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace SystolicGrowth

noncomputable section

/-- Scalar Jacobi comparison: a twice differentiable function starting with
the hyperbolic initial data and satisfying `f'' ≥ f` stays above `sinh` on
the nonnegative ray. The proof factors the differential inequality through
the two integrating factors `exp(-t)` and `exp(t)`; no positivity assumption
on `f` is needed. This is the one-dimensional comparison input for the
surface disk-area argument. -/
theorem sinh_le_of_second_deriv_ge_self
    (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t)
    (hzero : f 0 = 0) (hderivzero : f' 0 = 1)
    (hcurv : ∀ t, 0 ≤ t → f t ≤ f'' t)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.sinh t ≤ f t := by
  let g : ℝ → ℝ := fun x => f x - Real.sinh x
  let d : ℝ → ℝ := fun x => f' x - Real.cosh x
  let dd : ℝ → ℝ := fun x => f'' x - Real.sinh x
  let h : ℝ → ℝ := fun x => Real.exp (-x) * (d x + g x)
  let k : ℝ → ℝ := fun x => Real.exp x * g x
  have hg (x : ℝ) : HasDerivAt g (d x) x := by
    dsimp [g, d]
    exact (hf x).sub (Real.hasDerivAt_sinh x)
  have hd (x : ℝ) : HasDerivAt d (dd x) x := by
    dsimp [d, dd]
    exact (hf' x).sub (Real.hasDerivAt_cosh x)
  have hExpNeg (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hh (x : ℝ) :
      HasDerivAt h (Real.exp (-x) * (f'' x - f x)) x := by
    have htmp : HasDerivAt h
        (-Real.exp (-x) * (d x + g x) + Real.exp (-x) * (dd x + d x)) x :=
      (hExpNeg x).mul ((hd x).add (hg x))
    have hval :
        -Real.exp (-x) * (d x + g x) + Real.exp (-x) * (dd x + d x) =
          Real.exp (-x) * (f'' x - f x) := by
      dsimp [d, g, dd]
      ring
    rw [hval] at htmp
    exact htmp
  have hMono : MonotoneOn h (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hh x).continuousAt.continuousWithinAt)
      (fun x _ => (hh x).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx0 : x ∈ Set.Ici (0 : ℝ) := interior_subset hx
    rw [(hh x).deriv]
    exact mul_nonneg (Real.exp_pos (-x)).le
      (sub_nonneg.mpr (hcurv x hx0))
  have hzero' : h 0 = 0 := by
    simp [h, g, d, hzero, hderivzero]
  have hsum_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ d x + g x := by
    have hmono := hMono (by simp) (by simpa using hx) hx
    have hval : 0 ≤ h x := by
      calc
        0 = h 0 := hzero'.symm
        _ ≤ h x := hmono
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos (-x))).mp
      (by simpa [h] using hval)
  have hk (x : ℝ) : HasDerivAt k (Real.exp x * (d x + g x)) x := by
    have htmp : HasDerivAt k
        (Real.exp x * g x + Real.exp x * d x) x :=
      (Real.hasDerivAt_exp x).mul (hg x)
    have hval : Real.exp x * g x + Real.exp x * d x =
        Real.exp x * (d x + g x) := by ring
    rw [hval] at htmp
    exact htmp
  have kMono : MonotoneOn k (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hk x).continuousAt.continuousWithinAt)
      (fun x _ => (hk x).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx0 : x ∈ Set.Ici (0 : ℝ) := interior_subset hx
    rw [(hk x).deriv]
    exact mul_nonneg (Real.exp_pos x).le (hsum_nonneg x hx0)
  have hk0 : k 0 = 0 := by simp [k, g, hzero]
  have hk_nonneg : 0 ≤ k t := by
    have hmono := kMono (by simp) (by simpa using ht) ht
    calc
      0 = k 0 := hk0.symm
      _ ≤ k t := hmono
  have hprod : 0 ≤ Real.exp t * (f t - Real.sinh t) := by
    simpa [k, g] using hk_nonneg
  have hdiff : 0 ≤ f t - Real.sinh t :=
    (mul_nonneg_iff_of_pos_left (Real.exp_pos t)).mp hprod
  exact sub_nonneg.mp hdiff

/-- Finite-interval scalar comparison, with derivatives only within the
closed interval. This matches the endpoint regularity of the Jacobi ODE
library and requires no extension of the solution beyond its interval. -/
theorem sinh_le_of_second_deriv_ge_self_on_Icc
    (f f' f'' : ℝ → ℝ) {b : ℝ}
    (hf : ∀ t ∈ Icc 0 b, HasDerivWithinAt f (f' t) (Icc 0 b) t)
    (hf' : ∀ t ∈ Icc 0 b, HasDerivWithinAt f' (f'' t) (Icc 0 b) t)
    (hzero : f 0 = 0) (hderivzero : f' 0 = 1)
    (hcurv : ∀ t ∈ Icc 0 b, f t ≤ f'' t)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    Real.sinh t ≤ f t := by
  let g : ℝ → ℝ := fun x => f x - Real.sinh x
  let d : ℝ → ℝ := fun x => f' x - Real.cosh x
  let dd : ℝ → ℝ := fun x => f'' x - Real.sinh x
  let h : ℝ → ℝ := fun x => Real.exp (-x) * (d x + g x)
  let k : ℝ → ℝ := fun x => Real.exp x * g x
  have hg (x : ℝ) (hx : x ∈ Icc 0 b) :
      HasDerivWithinAt g (d x) (Icc 0 b) x := by
    dsimp [g, d]
    exact (hf x hx).sub (Real.hasDerivAt_sinh x).hasDerivWithinAt
  have hd (x : ℝ) (hx : x ∈ Icc 0 b) :
      HasDerivWithinAt d (dd x) (Icc 0 b) x := by
    dsimp [d, dd]
    exact (hf' x hx).sub (Real.hasDerivAt_cosh x).hasDerivWithinAt
  have hExpNeg (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hh (x : ℝ) (hx : x ∈ Icc 0 b) :
      HasDerivWithinAt h (Real.exp (-x) * (f'' x - f x)) (Icc 0 b) x := by
    have htmp : HasDerivWithinAt h
        (-Real.exp (-x) * (d x + g x) + Real.exp (-x) * (dd x + d x))
        (Icc 0 b) x :=
      (hExpNeg x).hasDerivWithinAt.mul ((hd x hx).add (hg x hx))
    convert htmp using 1
    dsimp [d, g, dd]
    ring
  have hMono : MonotoneOn h (Icc 0 b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b)
      (fun x hx => (hh x hx).continuousWithinAt)
      (fun x hx => (hh x (interior_subset hx)).mono interior_subset) ?_
    intro x hx
    exact mul_nonneg (Real.exp_pos (-x)).le
      (sub_nonneg.mpr (hcurv x (interior_subset hx)))
  have hzero' : h 0 = 0 := by
    simp [h, g, d, hzero, hderivzero]
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hsum_nonneg (x : ℝ) (hx : x ∈ Icc 0 b) : 0 ≤ d x + g x := by
    have hval : 0 ≤ h x := by
      simpa [hzero'] using hMono h0 hx hx.1
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos (-x))).mp
      (by simpa [h] using hval)
  have hk (x : ℝ) (hx : x ∈ Icc 0 b) :
      HasDerivWithinAt k (Real.exp x * (d x + g x)) (Icc 0 b) x := by
    have htmp : HasDerivWithinAt k
        (Real.exp x * g x + Real.exp x * d x) (Icc 0 b) x :=
      (Real.hasDerivAt_exp x).hasDerivWithinAt.mul (hg x hx)
    convert htmp using 1
    ring
  have kMono : MonotoneOn k (Icc 0 b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 b)
      (fun x hx => (hk x hx).continuousWithinAt)
      (fun x hx => (hk x (interior_subset hx)).mono interior_subset) ?_
    intro x hx
    exact mul_nonneg (Real.exp_pos x).le (hsum_nonneg x (interior_subset hx))
  have hk0 : k 0 = 0 := by simp [k, g, hzero]
  have hk_nonneg : 0 ≤ k t := by simpa [hk0] using kMono h0 ht ht.1
  have hdiff : 0 ≤ f t - Real.sinh t :=
    (mul_nonneg_iff_of_pos_left (Real.exp_pos t)).mp
      (by simpa [k, g] using hk_nonneg)
  exact sub_nonneg.mp hdiff

/-- A scalar Jacobi field with unit positive initial velocity remains
positive before the end of its interval under `k ≤ -1`. Positivity follows
from the actual no-conjugate theorem and initial derivative, rather than
being supplied as a premise to comparison. -/
theorem scalarJacobi_pos_of_curvature_le_neg_one
    {k f v : ℝ → ℝ} {b : ℝ}
    (hfv : Riemannian.Jacobi.IsJacobiPairOn
      (fun t => k t • ContinuousLinearMap.id ℝ ℝ) 0 b f v)
    (hk : ∀ t ∈ Icc 0 b, k t ≤ -1)
    (hf0 : f 0 = 0) (hv0 : v 0 = 1)
    {t : ℝ} (ht : t ∈ Ioc 0 b) :
    0 < f t := by
  let A : ℝ → ℝ →L[ℝ] ℝ :=
    fun x => min (k x) 0 • ContinuousLinearMap.id ℝ ℝ
  have hpair : Riemannian.Jacobi.IsJacobiPairOn A 0 b f v := by
    refine ⟨hfv.1, ?_⟩
    intro x hx
    simpa [A, min_eq_left (show k x ≤ 0 by linarith [hk x hx])] using hfv.2 x hx
  have hA (x y : ℝ) : inner ℝ (A x y) y ≤ (0 : ℝ) := by
    simpa [A, pow_two, mul_assoc, mul_left_comm] using
      mul_nonpos_of_nonpos_of_nonneg (min_le_right (k x) 0) (sq_nonneg y)
  have hne := hpair.ne_zero_of_nonpos_curv hA hf0 (by simp [hv0])
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, ht.1.le.trans ht.2⟩
  have hderiv : HasDerivWithinAt f 1 (Ioc 0 t) 0 := by
    simpa [hv0] using (hfv.1 0 h0).mono
      (show Ioc 0 t ⊆ Icc 0 b from fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩)
  have hslope : Tendsto (slope f 0) (𝓝[Ioc 0 t] 0) (𝓝 1) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hderiv
  have hpositive : ∀ᶠ x in 𝓝[Ioc 0 t] 0, 0 < slope f 0 x :=
    hslope.eventually (eventually_gt_nhds zero_lt_one)
  letI : NeBot (𝓝[Ioc 0 t] 0) := left_nhdsWithin_Ioc_neBot ht.1
  have hmem : ∀ᶠ x in 𝓝[Ioc 0 t] 0, x ∈ Ioc 0 t := self_mem_nhdsWithin
  obtain ⟨s, hs, hfs⟩ := (hmem.and hpositive).exists
  have hfspos : 0 < f s := by
    have hslopepos : 0 < f s / s := by
      simpa [slope, hf0, div_eq_mul_inv, mul_comm] using hfs
    exact (div_pos_iff_of_pos_right hs.1).mp hslopepos
  by_contra hft
  have hcont : ContinuousOn f (Icc s t) := by
    intro x hx
    exact ((hfv.1 x ⟨hs.1.le.trans hx.1, hx.2.trans ht.2⟩).continuousWithinAt).mono
      (fun y hy => ⟨hs.1.le.trans hy.1, hy.2.trans ht.2⟩)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc' hs.2 hcont
    (show (0 : ℝ) ∈ Icc (f t) (f s) from ⟨le_of_not_gt hft, hfspos.le⟩)
  exact hne u ⟨hs.1.trans_le hu.1, hu.2.trans ht.2⟩ hfu

/-- The finite-interval scalar Jacobi equation with curvature at most `-1`
and hyperbolic initial data gives the polar-density comparison `sinh ≤ f`.
The solution's sign is derived internally. -/
theorem sinh_le_scalarJacobi_of_curvature_le_neg_one
    {k f v : ℝ → ℝ} {b : ℝ}
    (hfv : Riemannian.Jacobi.IsJacobiPairOn
      (fun t => k t • ContinuousLinearMap.id ℝ ℝ) 0 b f v)
    (hk : ∀ t ∈ Icc 0 b, k t ≤ -1)
    (hf0 : f 0 = 0) (hv0 : v 0 = 1)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    Real.sinh t ≤ f t := by
  apply sinh_le_of_second_deriv_ge_self_on_Icc f v (fun x => -(k x * f x))
    hfv.1 (by simpa using hfv.2) hf0 hv0
    (fun x hx => ?_) ht
  have hfx : 0 ≤ f x := by
    by_cases hx0 : x = 0
    · simp [hx0, hf0]
    · exact (scalarJacobi_pos_of_curvature_le_neg_one hfv hk hf0 hv0
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩).le
  nlinarith [mul_le_mul_of_nonneg_right (hk x hx) hfx]

local instance hyperbolicConeCircleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance hyperbolicConeCircleBorelSpace : BorelSpace Circle := ⟨rfl⟩

/-- The genuine cone polar warp for total cone angle `a`. -/
def hyperbolicConePolarWarp (a t : ℝ) : ℝ :=
  (a / (2 * Real.pi)) * Real.sinh t

theorem hyperbolicConePolarWarp_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < hyperbolicConePolarWarp a t := by
  exact mul_pos (div_pos ha (by positivity)) (Real.sinh_pos_iff.mpr ht)

theorem hyperbolicConePolarWarp_contDiff_infty (a : ℝ) :
    ContDiff ℝ ⊤ (hyperbolicConePolarWarp a) :=
  contDiff_const.mul Real.contDiff_sinh

theorem hyperbolicConePolarWarp_contDiff (a : ℝ) :
    ContDiff ℝ 2 (hyperbolicConePolarWarp a) :=
  (hyperbolicConePolarWarp_contDiff_infty a).of_le le_top

theorem hyperbolicConePolarWarp_deriv (a : ℝ) :
    deriv (hyperbolicConePolarWarp a) = fun t => (a / (2 * Real.pi)) * Real.cosh t := by
  funext t
  exact ((Real.hasDerivAt_sinh t).const_mul (a / (2 * Real.pi))).deriv

theorem hyperbolicConePolarWarp_second_deriv (a : ℝ) :
    deriv (deriv (hyperbolicConePolarWarp a)) = hyperbolicConePolarWarp a := by
  rw [hyperbolicConePolarWarp_deriv]
  funext t
  exact ((Real.hasDerivAt_cosh t).const_mul (a / (2 * Real.pi))).deriv

/-- The actual connection is the Koszul connection of the literal cone
polar metric; no curvature or connection coefficients are supplied. -/
theorem hyperbolicConePolarChristoffel_eq_metric_formula
    {a : ℝ} (ha : 0 < a) {p : ℝ × ℝ} (ht : 0 < p.1) (l i j : Fin 2) :
    gluingWarpedChristoffel (hyperbolicConePolarWarp a) l i j p = (1 / 2 : ℝ) *
      ∑ m : Fin 2, gluingWarpedInverseMetric (hyperbolicConePolarWarp a) p l m *
        (gluingWarpedCoordinatePartial
            (fun q => gluingWarpedMetric (hyperbolicConePolarWarp a) q m j) i p +
          gluingWarpedCoordinatePartial
            (fun q => gluingWarpedMetric (hyperbolicConePolarWarp a) q i m) j p -
          gluingWarpedCoordinatePartial
            (fun q => gluingWarpedMetric (hyperbolicConePolarWarp a) q i j) m p) :=
  gluingWarpedChristoffel_eq_metric_formula (hyperbolicConePolarWarp_contDiff a)
    (hyperbolicConePolarWarp_pos ha ht) l i j

theorem hyperbolicConePolarMetric_gaussianCurvature
    {a : ℝ} (ha : 0 < a) {p : ℝ × ℝ} (ht : 0 < p.1) :
    gluingWarpedGaussianCurvature (hyperbolicConePolarWarp a) p = -1 := by
  rw [gluingWarpedGaussianCurvature_eq (hyperbolicConePolarWarp_contDiff a)
      (hyperbolicConePolarWarp_pos ha ht), hyperbolicConePolarWarp_second_deriv,
    neg_div, div_self (hyperbolicConePolarWarp_pos ha ht).ne']

theorem hyperbolicConePolarMetric_areaDensity
    {a : ℝ} (ha : 0 < a) {p : ℝ × ℝ} (ht : 0 < p.1) :
    Real.sqrt (gluingWarpedMetric (hyperbolicConePolarWarp a) p).det =
      hyperbolicConePolarWarp a p.1 :=
  gluingWarpedMetric_areaDensity (hyperbolicConePolarWarp_pos ha ht)

/-- The coordinate metric is genuinely positive definite, and its
derived Gaussian curvature and determinant density have the cone formulas. -/
theorem hyperbolicConePolarMetric_geometry
    {a : ℝ} (ha : 0 < a) {p : ℝ × ℝ} (ht : 0 < p.1) :
    (∀ v : Fin 2 → ℝ, v ≠ 0 →
      0 < gluingWarpedMetricForm (hyperbolicConePolarWarp a) p v v) ∧
      gluingWarpedGaussianCurvature (hyperbolicConePolarWarp a) p = -1 ∧
      Real.sqrt (gluingWarpedMetric (hyperbolicConePolarWarp a) p).det =
        hyperbolicConePolarWarp a p.1 := by
  refine ⟨fun _ hv => gluingWarpedMetricForm_pos (hyperbolicConePolarWarp_pos ha ht) hv,
    hyperbolicConePolarMetric_gaussianCurvature ha ht,
    hyperbolicConePolarMetric_areaDensity ha ht⟩

/-- Actual punctured-cone coordinate area: positive radial Lebesgue
measure times standard circle arclength, with the computed warp density. -/
def hyperbolicConePolarAreaMeasure (a : ℝ) : Measure (ℝ × Circle) :=
  (((volume : Measure ℝ).restrict (Ioi 0)).prod gluingCircleAngularLengthMeasure).withDensity
    (fun p => ENNReal.ofReal (hyperbolicConePolarWarp a p.1))

/-- The cylinder measure really is determinant area of the computed
coordinate metric, not a supplied polar area formula. -/
theorem hyperbolicConePolarAreaMeasure_eq_metricArea {a : ℝ} (ha : 0 < a) :
    hyperbolicConePolarAreaMeasure a =
      (((volume : Measure ℝ).restrict (Ioi 0)).prod gluingCircleAngularLengthMeasure).withDensity
        (fun p => ENNReal.ofReal
          (Real.sqrt (gluingWarpedMetric (hyperbolicConePolarWarp a) (p.1, 0)).det)) := by
  apply withDensity_congr_ae
  have hbase : ((volume : Measure ℝ).restrict (Ioi 0)).prod gluingCircleAngularLengthMeasure =
      ((volume : Measure ℝ).prod gluingCircleAngularLengthMeasure).restrict
        (Ioi 0 ×ˢ (univ : Set Circle)) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := gluingCircleAngularLengthMeasure) (Ioi 0) univ)
  rw [hbase]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  rw [hyperbolicConePolarMetric_areaDensity ha (p := (p.1, 0)) (show 0 < p.1 from hp.1)]

/-- The genuine unwrapped angular chart on a bounded positive-radius cone
cylinder. -/
def hyperbolicConePolarAngularChart (R θ₀ θ₁ : ℝ)
    (p : Set.Ioo (0 : ℝ) R × Set.Ioo θ₀ θ₁) : ℝ × Circle :=
  (p.1.1, Circle.exp p.2.1)

/-- On every angular interval shorter than a full turn, this polar chart is
an open embedding of the original positive-radius and angle coordinates. -/
theorem hyperbolicConePolarAngularChart_isOpenEmbedding {R θ₀ θ₁ : ℝ}
    (hwidth : θ₁ - θ₀ < 2 * Real.pi) :
    Topology.IsOpenEmbedding (hyperbolicConePolarAngularChart R θ₀ θ₁) := by
  have hr : Topology.IsOpenEmbedding
      (Subtype.val : Set.Ioo (0 : ℝ) R → ℝ) :=
    isOpen_Ioo.isOpenEmbedding_subtypeVal
  have hθ : Topology.IsOpenEmbedding (gluingCircleIntervalMap θ₀ θ₁) :=
    gluingCircleIntervalMap_isOpenEmbedding hwidth
  convert hr.prodMap hθ using 1
  funext p
  rfl

/-- In an unwrapped angular chart, the actual polar determinant-area pulls
back to radial-angular Lebesgue measure with the computed warp density. -/
theorem hyperbolicConePolarAreaMeasure_comap_angularChart
    {a R θ₀ θ₁ : ℝ} (hwidth : θ₁ - θ₀ < 2 * Real.pi) :
    (hyperbolicConePolarAreaMeasure a).comap
        (hyperbolicConePolarAngularChart R θ₀ θ₁) =
      (((volume : Measure ℝ).comap
          (Subtype.val : Set.Ioo (0 : ℝ) R → ℝ)).prod
        ((volume : Measure ℝ).comap
          (Subtype.val : Set.Ioo θ₀ θ₁ → ℝ))).withDensity
        (fun p => ENNReal.ofReal (hyperbolicConePolarWarp a p.1.1)) := by
  let fr : Set.Ioo (0 : ℝ) R → ℝ := Subtype.val
  let fθ : Set.Ioo θ₀ θ₁ → Circle := gluingCircleIntervalMap θ₀ θ₁
  have hrOpen : Topology.IsOpenEmbedding fr := by
    exact isOpen_Ioo.isOpenEmbedding_subtypeVal
  have hθOpen : Topology.IsOpenEmbedding fθ :=
    gluingCircleIntervalMap_isOpenEmbedding hwidth
  have hprod : MeasurableEmbedding (Prod.map fr fθ) :=
    hrOpen.measurableEmbedding.prodMap hθOpen.measurableEmbedding
  have hchart : hyperbolicConePolarAngularChart R θ₀ θ₁ = Prod.map fr fθ := by
    funext p
    rfl
  have hrbase :
      ((volume.restrict (Set.Ioi (0 : ℝ))).comap fr) =
        (volume : Measure ℝ).comap fr := by
    apply Measure.ext
    intro s hs
    rw [hrOpen.measurableEmbedding.comap_apply
        (volume.restrict (Set.Ioi (0 : ℝ))) s,
      hrOpen.measurableEmbedding.comap_apply (volume : Measure ℝ) s,
      Measure.restrict_apply
        (hrOpen.measurableEmbedding.measurableSet_image.mpr hs)]
    have himage : fr '' s ⊆ Set.Ioi (0 : ℝ) := by
      rintro x ⟨p, hp, rfl⟩
      exact p.2.1
    rw [inter_eq_left.mpr himage]
  letI : IsFiniteMeasure
      ((volume : Measure ℝ).comap fr) := by
    refine ⟨?_⟩
    change ((volume : Measure ℝ).comap
      (Subtype.val : Set.Ioo (0 : ℝ) R → ℝ)) Set.univ < ∞
    rw [comap_subtype_coe_apply measurableSet_Ioo]
    rw [Set.image_univ, Subtype.range_val, Real.volume_Ioo]
    finiteness
  letI : IsFiniteMeasure
      (gluingCircleAngularLengthMeasure.comap fθ) := by
    change IsFiniteMeasure
      (gluingCircleAngularLengthMeasure.comap (gluingCircleIntervalMap θ₀ θ₁))
    rw [gluingCircleAngularLengthMeasure_comap_interval hwidth]
    refine ⟨?_⟩
    change ((volume : Measure ℝ).comap
      (Subtype.val : Set.Ioo θ₀ θ₁ → ℝ)) Set.univ < ∞
    rw [comap_subtype_coe_apply measurableSet_Ioo]
    rw [Set.image_univ, Subtype.range_val, Real.volume_Ioo]
    finiteness
  letI : SigmaFinite
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).comap fr) := by
    rw [hrbase]
    infer_instance
  rw [hchart, hyperbolicConePolarAreaMeasure,
    gluingMeasure_comap_withDensity hprod
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        gluingCircleAngularLengthMeasure)
      (fun p => ENNReal.ofReal (hyperbolicConePolarWarp a p.1)),
    gluingMeasure_comap_prodMap hrOpen.measurableEmbedding
      hθOpen.measurableEmbedding
      ((volume : Measure ℝ).restrict (Set.Ioi 0))
      gluingCircleAngularLengthMeasure,
    hrbase, gluingCircleAngularLengthMeasure_comap_interval hwidth]
  rfl

theorem hyperbolicConePolarWarp_integral {a R : ℝ} (hR : 0 ≤ R) :
    (∫ t : ℝ in Ioo 0 R, hyperbolicConePolarWarp a t) =
      (a / (2 * Real.pi)) * (Real.cosh R - 1) := by
  have hd : ∀ t ∈ uIcc 0 R,
      HasDerivAt (fun x : ℝ => (a / (2 * Real.pi)) * Real.cosh x)
        (hyperbolicConePolarWarp a t) t := by
    intro t _
    exact (Real.hasDerivAt_cosh t).const_mul _
  have hi : IntervalIntegrable (hyperbolicConePolarWarp a) volume 0 R :=
    (hyperbolicConePolarWarp_contDiff a).continuous.intervalIntegrable _ _
  rw [← integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hR, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp only [Real.cosh_zero, mul_one]
  ring

theorem hyperbolicConePolarWarp_lintegral {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    (∫⁻ t : ℝ in Ioo 0 R, ENNReal.ofReal (hyperbolicConePolarWarp a t)) =
      ENNReal.ofReal ((a / (2 * Real.pi)) * (Real.cosh R - 1)) := by
  have hi : IntegrableOn (hyperbolicConePolarWarp a) (Ioo 0 R) :=
    ((hyperbolicConePolarWarp_contDiff a).continuous.continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hp : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioo 0 R)] hyperbolicConePolarWarp a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hyperbolicConePolarWarp_pos ha ht.1).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hp, hyperbolicConePolarWarp_integral hR]

/-- Exact determinant-area mass of the actual punctured polar cylinder
`0 < t < R`. This is not yet a completed-cone metric-ball statement. -/
theorem hyperbolicConePolarAreaMeasure_radial_strip
    {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    hyperbolicConePolarAreaMeasure a (Ioo 0 R ×ˢ (univ : Set Circle)) =
      ENNReal.ofReal (a * (Real.cosh R - 1)) := by
  have hm : Measurable (fun p : ℝ × Circle => ENNReal.ofReal (hyperbolicConePolarWarp a p.1)) :=
    ((hyperbolicConePolarWarp_contDiff a).continuous.comp continuous_fst).measurable.ennreal_ofReal
  rw [hyperbolicConePolarAreaMeasure,
    withDensity_apply _ (measurableSet_Ioo.prod MeasurableSet.univ),
    setLIntegral_prod (fun p : ℝ × Circle => ENNReal.ofReal (hyperbolicConePolarWarp a p.1))
      hm.aemeasurable]
  simp only [setLIntegral_const, gluingCircleAngularLengthMeasure_univ]
  have hinter : Ioo (0 : ℝ) R ∩ Ioi 0 = Ioo 0 R := by
    exact inter_eq_left.mpr (fun t ht => ht.1)
  rw [Measure.restrict_restrict measurableSet_Ioo, hinter,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    hyperbolicConePolarWarp_lintegral ha hR,
    ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg ha.le (by positivity))
      (sub_nonneg.mpr (Real.one_le_cosh R)))]
  congr 1
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  field_simp

/-- The same radial area formula holds when the cylinder is cut by `t < R`:
the polar area measure is supported on positive radii. -/
theorem hyperbolicConePolarAreaMeasure_Iio_strip
    {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R) :
    hyperbolicConePolarAreaMeasure a (Iio R ×ˢ (univ : Set Circle)) =
      ENNReal.ofReal (a * (Real.cosh R - 1)) := by
  have hm : Measurable (fun p : ℝ × Circle => ENNReal.ofReal (hyperbolicConePolarWarp a p.1)) :=
    ((hyperbolicConePolarWarp_contDiff a).continuous.comp continuous_fst).measurable.ennreal_ofReal
  rw [hyperbolicConePolarAreaMeasure,
    withDensity_apply _ (measurableSet_Iio.prod MeasurableSet.univ),
    setLIntegral_prod (fun p : ℝ × Circle => ENNReal.ofReal (hyperbolicConePolarWarp a p.1))
      hm.aemeasurable]
  simp only [setLIntegral_const, gluingCircleAngularLengthMeasure_univ]
  have hinter : Iio R ∩ Ioi 0 = Ioo 0 R := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨hR', ht⟩
      exact ⟨ht, hR'⟩
    · rintro ⟨ht, hR'⟩
      exact ⟨hR', ht⟩
  rw [Measure.restrict_restrict measurableSet_Iio, hinter,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    hyperbolicConePolarWarp_lintegral ha hR,
    ← ENNReal.ofReal_mul (mul_nonneg (div_nonneg ha.le (by positivity))
      (sub_nonneg.mpr (Real.one_le_cosh R)))]
  congr 1
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  field_simp

/-- Cone angle at least `2π` gives the standard hyperbolic radial-area
lower bound on this genuine coordinate cylinder. -/
theorem hyperbolicConePolarAreaMeasure_radial_strip_lower_bound
    {a R : ℝ} (ha : 2 * Real.pi ≤ a) (hR : 0 ≤ R) :
    ENNReal.ofReal (2 * Real.pi * (Real.cosh R - 1)) ≤
      hyperbolicConePolarAreaMeasure a (Ioo 0 R ×ˢ (univ : Set Circle)) := by
  rw [hyperbolicConePolarAreaMeasure_radial_strip (by linarith [Real.pi_pos]) hR]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right ha (sub_nonneg.mpr (Real.one_le_cosh R))

#print axioms hyperbolicConePolarChristoffel_eq_metric_formula
#print axioms hyperbolicConePolarMetric_geometry
#print axioms hyperbolicConePolarAreaMeasure_eq_metricArea
#print axioms hyperbolicConePolarAngularChart_isOpenEmbedding
#print axioms hyperbolicConePolarAreaMeasure_comap_angularChart
#print axioms hyperbolicConePolarAreaMeasure_radial_strip
#print axioms hyperbolicConePolarAreaMeasure_Iio_strip
#print axioms hyperbolicConePolarAreaMeasure_radial_strip_lower_bound
#print axioms sinh_le_of_second_deriv_ge_self
#print axioms sinh_le_of_second_deriv_ge_self_on_Icc
#print axioms scalarJacobi_pos_of_curvature_le_neg_one
#print axioms sinh_le_scalarJacobi_of_curvature_le_neg_one

end
end SystolicGrowth
