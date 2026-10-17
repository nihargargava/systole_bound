module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.UpperHalfPlaneRiemannianMetric
public import Geometry.CurvatureTwoDimensional
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality

@[expose] public section

/-!
# Intrinsic constant curvature of the actual upper half-plane

The Poincaré tensor on mathlib's unchanged complex atlas has its genuine
Levi-Civita connection and curvature computed here. The all-pairs identity
uses the actual metric, not an independent coordinate-curvature certificate.
-/

open Bundle Manifold Set Riemannian UpperHalfPlane
open scoped Manifold Topology ContDiff

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SystolicGrowth

noncomputable section

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The actual singleton-atlas metric is the literal Poincaré coordinate
tensor throughout its chart domain. -/
theorem upperHalfPlanePoincareMetric_chartMetricInner_eq
    (α : ℍ) {y : ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) (u v : ℂ) :
    chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
      upperHalfPlanePoincareMetric α y u v =
        (y.im ^ 2)⁻¹ * (u.re * v.re + u.im * v.im) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let q := (extChartAt I α).symm y
  let τ := trivializationAt ℂ (TangentSpace I) α
  have hq : q ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hcoord : (extChartAt I α) q = y := (extChartAt I α).right_inv hy
  have hbridge := chartMetricInner_extChartAt_eq_metricInner
    (I := I) upperHalfPlanePoincareMetric α hq u v
  rw [hcoord] at hbridge
  rw [hbridge]
  have hsame : τ = trivializationAt ℂ (TangentSpace I) q := by
    dsimp only [τ]
    rw [TangentBundle.trivializationAt_eq_localTriv,
      TangentBundle.trivializationAt_eq_localTriv]
    rfl
  change upperHalfPlanePoincareMetric.metricInner q (τ.symm q u) (τ.symm q v) = _
  rw [hsame, trivializationAt_symm_self, trivializationAt_symm_self]
  change upperHalfPlanePoincareMetric.inner q u v = _
  rw [upperHalfPlanePoincareMetric_inner_eq_native, gluingComplexHalfPlaneTangentForm_apply]
  have him : (q : ℂ).im = y.im := congrArg Complex.im hcoord
  simp only [him, Complex.mul_re, Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
  ring

private theorem upperHalfPlane_chart_im_pos (α : ℍ) {y : ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) : 0 < y.im := by
  have h := (extChartAt (modelWithCornersSelf ℝ ℂ) α).right_inv hy
  change (((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y : ℍ) : ℂ) = y at h
  rw [← h]
  exact UpperHalfPlane.im_pos _

private theorem poincareInner_hasFDerivAt {y : ℂ} (hy : y.im ≠ 0) (u v : ℂ) :
    HasFDerivAt
      (fun z : ℂ => (z.im ^ 2)⁻¹ * (u.re * v.re + u.im * v.im))
      (((-2 / y.im ^ 3) * (u.re * v.re + u.im * v.im)) • Complex.imCLM) y := by
  have hinv : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-2 / y.im ^ 3) y.im := by
    convert ((hasDerivAt_id y.im).pow 2).inv (pow_ne_zero 2 hy) using 1 <;> try rfl
    simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    field_simp [hy]
  have h := (hinv.hasFDerivAt.comp y Complex.imCLM.hasFDerivAt).mul_const
    (u.re * v.re + u.im * v.im)
  convert h using 1
  all_goals first | rfl | (ext a; simp; ring)

/-- **Math.** Differentiating the actual metric along an affine path gives its genuine
Levi-Civita metric-compatibility balance. -/
theorem upperHalfPlanePoincareMetric_chartChristoffel_balance
    (α : ℍ) {y : ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) (a b c : ℂ) :
    (-2 / y.im ^ 3) * a.im * (b.re * c.re + b.im * c.im) =
      chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
        upperHalfPlanePoincareMetric α y
        (Jacobi.chartChristoffelBilin (I := modelWithCornersSelf ℝ ℂ)
          upperHalfPlanePoincareMetric α y a b) c +
      chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
        upperHalfPlanePoincareMetric α y b
        (Jacobi.chartChristoffelBilin (I := modelWithCornersSelf ℝ ℂ)
          upperHalfPlanePoincareMetric α y a c) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := upperHalfPlanePoincareMetric
  let path : ℝ → ℂ := fun t => y + t • a
  have hp : path 0 = y := by simp [path]
  have hpath : HasDerivAt path a 0 := by
    simpa [path] using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add y
  have hypos := upperHalfPlane_chart_im_pos α hy
  have hnear : (fun z => chartMetricInner (I := I) metric α z b c) =ᶠ[𝓝 y]
      fun z => (z.im ^ 2)⁻¹ * (b.re * c.re + b.im * c.im) := by
    filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy] with z hz
    exact upperHalfPlanePoincareMetric_chartMetricInner_eq α hz b c
  have hactual := (poincareInner_hasFDerivAt hypos.ne' b c).congr_of_eventuallyEq hnear
  have hactualAt : HasFDerivAt
      (fun z => chartMetricInner (I := I) metric α z b c)
      (((-2 / y.im ^ 3) * (b.re * c.re + b.im * c.im)) • Complex.imCLM)
      (path 0) := by simpa only [hp] using hactual
  have hscalar := hactualAt.comp_hasDerivAt (0 : ℝ) hpath
  have hG (i j : Fin (Module.finrank ℝ ℂ)) :
      DifferentiableAt ℝ (chartGramOnE (I := I) metric α i j) (path 0) := by
    rw [hp]
    exact ((chartGramOnE_contDiffOn metric α i j).differentiableOn
      (by norm_num)).differentiableAt ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hbase : (extChartAt I α).symm (path 0) ∈
      (trivializationAt ℂ (TangentSpace I) α).baseSet := by
    rw [hp, trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hconnection := hasDerivAt_chartMetricInner_along
    (I := I) metric α path (fun _ => b) (fun _ => c) hpath.differentiableAt
    (differentiableAt_const b) (differentiableAt_const c) hG hbase
  have heq := hscalar.unique hconnection
  simpa only [hp, covariantDerivCoord_def, hpath.deriv, deriv_const,
    zero_add, Function.comp_apply, smul_apply, Complex.imCLM_apply, smul_eq_mul,
    Jacobi.chartChristoffelBilin_apply, mul_assoc, mul_left_comm, mul_comm] using heq

/-- **Math.** The computed torsion-free metric-compatible connection is the actual
chart Christoffel bilinear map, in the unchanged complex atlas. -/
theorem upperHalfPlanePoincareMetric_chartChristoffelBilin_eq
    (α : ℍ) {y : ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) (u v : ℂ) :
    Jacobi.chartChristoffelBilin (I := modelWithCornersSelf ℝ ℂ)
      upperHalfPlanePoincareMetric α y u v =
        Complex.mk (-(u.re * v.im + u.im * v.re) / y.im)
          ((u.re * v.re - u.im * v.im) / y.im) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := upperHalfPlanePoincareMetric
  let Γ : ℂ → ℂ → ℂ := fun a b => Jacobi.chartChristoffelBilin (I := I) metric α y a b
  let K : ℂ → ℂ → ℂ := fun a b =>
    Complex.mk (-(a.re * b.im + a.im * b.re) / y.im)
      ((a.re * b.re - a.im * b.im) / y.im)
  let D : ℂ → ℂ → ℂ → ℝ := fun a b c =>
    (-2 / y.im ^ 3) * a.im * (b.re * c.re + b.im * c.im)
  have hypos := upperHalfPlane_chart_im_pos α hy
  have hinner (a b : ℂ) : chartMetricInner (I := I) metric α y a b =
      (y.im ^ 2)⁻¹ * (a.re * b.re + a.im * b.im) :=
    upperHalfPlanePoincareMetric_chartMetricInner_eq α hy a b
  have hbalance (a b c : ℂ) : D a b c =
      chartMetricInner (I := I) metric α y (Γ a b) c +
      chartMetricInner (I := I) metric α y b (Γ a c) :=
    upperHalfPlanePoincareMetric_chartChristoffel_balance α hy a b c
  have hsymm (a b : ℂ) : Γ a b = Γ b a :=
    Jacobi.chartChristoffelBilin_symm metric α y a b
  have hkoszul (a b c : ℂ) : 2 * chartMetricInner (I := I) metric α y (Γ a b) c =
      D a b c + D b a c - D c a b := by
    have h₁ := hbalance a b c
    have h₂ := hbalance b a c
    have h₃ := hbalance c a b
    rw [hsymm b a] at h₂
    rw [hsymm c a, hsymm c b] at h₃
    rw [chartMetricInner_symm (I := I) metric α y (Γ a c) b] at h₃
    linarith [h₁, h₂, h₃]
  have hKkoszul (a b c : ℂ) : 2 * chartMetricInner (I := I) metric α y (K a b) c =
      D a b c + D b a c - D c a b := by
    rw [hinner]
    dsimp only [K, D]
    field_simp [hypos.ne']
    ring
  have hpair (a b c : ℂ) : chartMetricInner (I := I) metric α y (Γ a b) c =
      chartMetricInner (I := I) metric α y (K a b) c := by
    linarith [hkoszul a b c, hKkoszul a b c]
  apply Complex.ext
  · have h := hpair u v 1
    rw [hinner, hinner] at h
    have h' : (y.im ^ 2)⁻¹ * (Γ u v).re = (y.im ^ 2)⁻¹ * (K u v).re := by
      simpa only [Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero] using h
    exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 hypos.ne')) h'
  · have h := hpair u v Complex.I
    rw [hinner, hinner] at h
    have h' : (y.im ^ 2)⁻¹ * (Γ u v).im = (y.im ^ 2)⁻¹ * (K u v).im := by
      simpa only [Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add] using h
    exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 hypos.ne')) h'

/-- **Math.** Differentiating the actual Christoffel map gives the Poincaré
curvature component on the real/angular coordinate plane. -/
theorem upperHalfPlanePoincareMetric_chartCurvature_real_angular
    (α : ℍ) {y : ℂ}
    (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) :
    Jacobi.chartCurvature (I := modelWithCornersSelf ℝ ℂ)
      upperHalfPlanePoincareMetric α y 1 Complex.I Complex.I =
        Complex.ofReal (-(y.im ^ 2)⁻¹) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := upperHalfPlanePoincareMetric
  let F : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    Jacobi.chartChristoffelBilin (I := I) metric α
  have hyInterior : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy
  have hFdiff : DifferentiableAt ℝ F y :=
    Jacobi.differentiableAt_chartChristoffelBilin metric α hyInterior
  have hfirst (a : ℂ) :
      fderiv ℝ (fun z : ℂ => F z a) y = (fderiv ℝ F y).flip a := by
    rw [fderiv_clm_apply hFdiff (differentiableAt_const a)]
    ext d b
    simp
  have hFaDiff (a : ℂ) : DifferentiableAt ℝ (fun z : ℂ => F z a) y :=
    hFdiff.clm_apply (differentiableAt_const a)
  have hsecond (a b : ℂ) :
      fderiv ℝ (fun z : ℂ => F z a b) y =
        (fderiv ℝ (fun z : ℂ => F z a) y).flip b := by
    rw [fderiv_clm_apply (hFaDiff a) (differentiableAt_const b)]
    ext d
    simp
  have hFderiv_apply (a b d : ℂ) :
      fderiv ℝ (fun z : ℂ => F z a b) y d = fderiv ℝ F y d a b := by
    calc
      _ = (fderiv ℝ (fun z : ℂ => F z a) y d) b := by
        rw [hsecond a b]
        simp
      _ = (fderiv ℝ F y d a) b := by
        rw [hfirst a]
        simp
  have hypos := upperHalfPlane_chart_im_pos α hy
  have hnear := (isOpen_extChartAt_target (I := I) α).mem_nhds hy
  have h1I : (fun z : ℂ => F z 1 Complex.I) =ᶠ[𝓝 y]
      fun z => Complex.ofReal (-z.im⁻¹) := by
    filter_upwards [hnear] with z hz
    have h := upperHalfPlanePoincareMetric_chartChristoffelBilin_eq α hz (1 : ℂ) Complex.I
    apply Complex.ext
    · simpa only [F, metric, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im, mul_one, mul_zero, zero_mul, add_zero, one_mul,
        neg_div, one_div, Complex.ofReal_re] using congrArg Complex.re h
    · simpa only [F, metric, Complex.one_re, Complex.one_im, Complex.I_re,
        Complex.I_im, mul_one, mul_zero, zero_mul, zero_sub, zero_div,
        neg_zero, Complex.ofReal_im] using congrArg Complex.im h
  have hII : (fun z : ℂ => F z Complex.I Complex.I) =ᶠ[𝓝 y]
      fun z => Complex.ofReal (-z.im⁻¹) * Complex.I := by
    filter_upwards [hnear] with z hz
    have h := upperHalfPlanePoincareMetric_chartChristoffelBilin_eq α hz Complex.I Complex.I
    apply Complex.ext
    · simpa only [F, metric, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_mul, zero_add, zero_div, neg_zero, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, sub_zero] using congrArg Complex.re h
    · simpa only [F, metric, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        zero_mul, zero_add, zero_sub, neg_div, one_div, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, add_zero] using congrArg Complex.im h
  have hinv : HasDerivAt (fun t : ℝ => -t⁻¹) ((y.im ^ 2)⁻¹) y.im := by
    convert ((hasDerivAt_id y.im).inv hypos.ne').neg using 1
    all_goals first | rfl | simp only [id_eq, neg_div, neg_neg, one_div]
  have hinvC : HasFDerivAt (fun z : ℂ => Complex.ofReal (-z.im⁻¹))
      (Complex.ofRealCLM.comp (((y.im ^ 2)⁻¹) • Complex.imCLM)) y := by
    have hcomp := hinv.hasFDerivAt.comp y Complex.imCLM.hasFDerivAt
    convert Complex.ofRealCLM.hasFDerivAt.comp y hcomp using 1
    all_goals first | rfl | (ext z; simp; ring)
  have h1Ideriv : fderiv ℝ (fun z : ℂ => F z 1 Complex.I) y Complex.I =
      Complex.ofReal ((y.im ^ 2)⁻¹) := by
    rw [h1I.fderiv_eq, hinvC.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hIIderiv : fderiv ℝ (fun z : ℂ => F z Complex.I Complex.I) y 1 = 0 := by
    rw [hII.fderiv_eq, (hinvC.mul_const Complex.I).fderiv]
    simp [ContinuousLinearMap.comp_apply]
  have hAt (a b : ℂ) : F y a b =
      Complex.mk (-(a.re * b.im + a.im * b.re) / y.im)
        ((a.re * b.re - a.im * b.im) / y.im) :=
    upperHalfPlanePoincareMetric_chartChristoffelBilin_eq α hy a b
  rw [Jacobi.chartCurvature_def, Jacobi.christoffelCurvature]
  rw [← hFderiv_apply Complex.I Complex.I 1, ← hFderiv_apply 1 Complex.I Complex.I,
    hIIderiv, h1Ideriv, hAt 1 (F y Complex.I Complex.I), hAt Complex.I (F y 1 Complex.I),
    hAt Complex.I Complex.I, hAt 1 Complex.I]
  apply Complex.ext <;>
    simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]

/-- **Math.** The intrinsic reversed coordinate curvature numerator equals
the square of the genuine Poincaré conformal coefficient. -/
theorem upperHalfPlanePoincareMetric_curvatureFormAt_real_angular (q : ℍ) :
    upperHalfPlanePoincareMetric.leviCivitaConnection.curvatureFormAt
      upperHalfPlanePoincareMetric q (1 : ℂ) Complex.I Complex.I (1 : ℂ) =
        (((q : ℂ).im ^ 2)⁻¹) ^ 2 := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  have hframe (v : ℂ) :
      (∑ i : Fin (Module.finrank ℝ ℂ),
        Geodesic.chartCoord (E := ℂ) i v • Tensor.chartBasisVecFiber (I := I) q i q) = v := by
    have hvec (i : Fin (Module.finrank ℝ ℂ)) :
        Tensor.chartBasisVecFiber (I := I) q i q = Module.finBasis ℝ ℂ i := by
      rw [Tensor.chartBasisVecFiber, trivializationAt_symm_self]
    simp_rw [hvec]
    simpa only [Geodesic.chartCoord_def] using (Module.finBasis ℝ ℂ).sum_repr v
  have hbridge := Jacobi.curvatureFormAt_chartFrame (I := I)
    upperHalfPlanePoincareMetric (α := q) (p := q) (mem_chart_source ℂ q)
    (1 : ℂ) Complex.I Complex.I (1 : ℂ)
  rw [hframe 1, hframe Complex.I,
    upperHalfPlanePoincareMetric_chartCurvature_real_angular q (mem_extChartAt_target q),
    upperHalfPlanePoincareMetric_chartMetricInner_eq q (mem_extChartAt_target q)] at hbridge
  simpa only [upperHalfPlane_extChartAt_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero, mul_neg, neg_neg, pow_two]
    using hbridge

/-- **Math.** Every actual tangent pair on the unchanged upper half-plane
has constant curvature `-1`, with the DoCarmo reversed-pair convention. -/
theorem upperHalfPlanePoincareMetric_curvatureOperatorAt_eq (q : ℍ)
    (x y : TangentSpace (modelWithCornersSelf ℝ ℂ) q) :
    upperHalfPlanePoincareMetric.metricInner q x x *
        upperHalfPlanePoincareMetric.metricInner q y y -
      upperHalfPlanePoincareMetric.metricInner q x y *
        upperHalfPlanePoincareMetric.metricInner q x y =
      upperHalfPlanePoincareMetric.metricInner q
        (upperHalfPlanePoincareMetric.leviCivitaConnection.curvatureOperatorAt q x y y) x := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := upperHalfPlanePoincareMetric
  let connection := metric.leviCivitaConnection
  letI : Bundle.RiemannianBundle (fun q : ℍ => TangentSpace I q) := ⟨metric.toRiemannianMetric⟩
  let e : Module.Basis (Fin 2) ℝ (TangentSpace I q) := Complex.basisOneI
  have he0 : e 0 = (1 : ℂ) := by
    exact congrFun Complex.coe_basisOneI 0
  have he1 : e 1 = Complex.I := by
    exact congrFun Complex.coe_basisOneI 1
  have hLC : connection.IsLeviCivita metric :=
    connection.isLeviCivita_of_koszulDual metric
      (fun U V W p => metric.koszulDualSection_dual U V W p)
  have hB := connection.isAlgCurvatureForm_curvatureFormAt metric hLC q
  have hrev : connection.curvatureFormAt metric q (e 0) (e 1) (e 1) (e 0) =
      (((q : ℂ).im ^ 2)⁻¹) ^ 2 := by
    rw [he0, he1]
    exact upperHalfPlanePoincareMetric_curvatureFormAt_real_angular q
  have hbase : connection.curvatureFormAt metric q (e 0) (e 1) (e 0) (e 1) =
      -(((q : ℂ).im ^ 2)⁻¹) ^ 2 := by
    rw [hB.antisymm₃₄, hrev]
  have hmetric (a b : ℂ) : metric.metricInner q a b =
      (((q : ℂ).im ^ 2)⁻¹) * (a.re * b.re + a.im * b.im) := by
    change upperHalfPlanePoincareMetric.inner q a b = _
    rw [upperHalfPlanePoincareMetric_inner_eq_native, gluingComplexHalfPlaneTangentForm_apply]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
    ring
  have hwedge : wedgeSq (e 0) (e 1) = (((q : ℂ).im ^ 2)⁻¹) ^ 2 := by
    change metric.metricInner q (e 0) (e 0) * metric.metricInner q (e 1) (e 1) -
      metric.metricInner q (e 0) (e 1) * metric.metricInner q (e 0) (e 1) = _
    rw [he0, he1, hmetric, hmetric, hmetric]
    simp [pow_two]
  have hdiag := hB.diag_eq_det_sq_mul_basis e x y
  have hgram := wedgeSq_eq_det_sq_mul_basis e x y
  rw [hbase] at hdiag
  rw [hwedge] at hgram
  have hskew := hB.antisymm₃₄ x y x y
  change wedgeSq x y = connection.curvatureFormAt metric q x y y x
  linarith

/-- **Math.** The genuine upper-half-plane curvature operator has the
nonnegative reversed pairing required by Cartan--Hadamard. -/
theorem upperHalfPlanePoincareMetric_curvatureOperatorAt_pair_nonneg (q : ℍ)
    (x y : TangentSpace (modelWithCornersSelf ℝ ℂ) q) :
    0 ≤ upperHalfPlanePoincareMetric.metricInner q
      (upperHalfPlanePoincareMetric.leviCivitaConnection.curvatureOperatorAt q x y y) x := by
  rw [← upperHalfPlanePoincareMetric_curvatureOperatorAt_eq]
  letI : Bundle.RiemannianBundle
    (fun p : ℍ => TangentSpace (modelWithCornersSelf ℝ ℂ) p) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  exact sub_nonneg.mpr (real_inner_mul_inner_self_le x y)

#print axioms upperHalfPlanePoincareMetric_chartMetricInner_eq
#print axioms upperHalfPlanePoincareMetric_chartChristoffel_balance
#print axioms upperHalfPlanePoincareMetric_chartChristoffelBilin_eq
#print axioms upperHalfPlanePoincareMetric_chartCurvature_real_angular
#print axioms upperHalfPlanePoincareMetric_curvatureFormAt_real_angular
#print axioms upperHalfPlanePoincareMetric_curvatureOperatorAt_eq
#print axioms upperHalfPlanePoincareMetric_curvatureOperatorAt_pair_nonneg

end
end SystolicGrowth
