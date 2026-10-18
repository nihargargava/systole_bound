module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainBoundedCurvatureCurvature
public import Geometry.CurvatureTwoDimensional
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# Intrinsic curvature on the unchanged interior of the glued metric

The literal Poincaré coordinate tensor is transferred to the actual patched
metric and its chart Levi-Civita connection, away from the closed seam strips.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The chart inner product of the actual patched metric is the native
Poincaré tensor whenever this interior point avoids the smoothing strips. -/
theorem gluedCurvatureBoundedInterior_chartMetricInner_eq
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.thinSeamCollar k)
    (u v : ℂ) :
    Riemannian.chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
      P.gluedCurvatureBoundedSmoothRiemannianMetric α y u v =
        (y.im ^ 2)⁻¹ * (u.re * v.re + u.im * v.im) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p := (extChartAt I α).symm y
  let τ := trivializationAt ℂ (TangentSpace I) α
  have hp : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := hp
  have hcoord : (chartAt ℂ α) p = y := by
    simpa only [p, extChartAt_coe, I, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq] using
      (extChartAt I α).right_inv hy
  have hmetric := (P.gluedCurvatureBoundedSmoothMetric_interior_chart
    (chartAt ℂ α) hi p hp houtside).2 u v
  have hvec (w : ℂ) : τ.symmL ℝ p w =
      ((tangentBundleCore I P.GluedCarrier).localTriv
        (⟨chartAt ℂ α, Or.inl hi⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ p w := by
    simp only [τ, TangentBundle.trivializationAt_eq_localTriv]
    rfl
  rw [← hvec u, ← hvec v] at hmetric
  have hbridge := Riemannian.chartMetricInner_extChartAt_eq_metricInner
    (I := I) P.gluedCurvatureBoundedSmoothRiemannianMetric α hp u v
  have hextcoord : (extChartAt I α) p = y := (extChartAt I α).right_inv hy
  rw [hextcoord] at hbridge
  rw [hbridge, ← Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase u,
    ← Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase v]
  change P.gluedCurvatureBoundedSmoothRiemannianMetric.inner p
    (τ.symmL ℝ p u) (τ.symmL ℝ p v) = _
  rw [hmetric, hcoord, gluingComplexHalfPlaneTangentForm_apply]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
  ring

/-- **Math.** The unchanged-chart formula holds on a neighborhood, including every
point outside all closed smoothing strips. -/
theorem gluedCurvatureBoundedInterior_outside_near
    (P : ExerciseGluingPreparation C g n genera X) (α : P.GluedCarrier)
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k) :
    ∀ᶠ z in 𝓝 y, z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target ∧
      ∀ k : Fin (n - 1),
        (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z ∉ P.closedThinSeamCollar k := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  have hsymm : ContinuousAt (extChartAt I α).symm y :=
    (continuousOn_extChartAt_symm (I := I) α).continuousAt
      ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hall : ∀ᶠ z in 𝓝 y, ∀ k : Fin (n - 1),
      (extChartAt I α).symm z ∉ P.closedThinSeamCollar k := by
    rw [Filter.eventually_all]
    intro k
    exact hsymm.preimage_mem_nhds
      ((P.closedThinSeamCollar_isCompact k).isClosed.isOpen_compl.mem_nhds (houtside k))
  filter_upwards [(isOpen_extChartAt_target (I := I) α).mem_nhds hy, hall] with z hz ho
  exact ⟨hz, ho⟩

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

/-- **Math.** Directional metric compatibility gives the Poincaré derivative balance
for the actual chart connection, with no preferred finite basis assumption. -/
theorem gluedCurvatureBoundedInterior_chartChristoffel_balance
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k)
    (a b c : ℂ) :
    (-2 / y.im ^ 3) * a.im * (b.re * c.re + b.im * c.im) =
      Riemannian.chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α y
        (Riemannian.Jacobi.chartChristoffelBilin (I := modelWithCornersSelf ℝ ℂ)
          P.gluedCurvatureBoundedSmoothRiemannianMetric α y a b) c +
      Riemannian.chartMetricInner (I := modelWithCornersSelf ℝ ℂ)
        P.gluedCurvatureBoundedSmoothRiemannianMetric α y b
        (Riemannian.Jacobi.chartChristoffelBilin (I := modelWithCornersSelf ℝ ℂ)
          P.gluedCurvatureBoundedSmoothRiemannianMetric α y a c) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let path : ℝ → ℂ := fun t => y + t • a
  have hp : path 0 = y := by simp [path]
  have hpath : HasDerivAt path a 0 := by
    simpa [path] using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add y
  have hymetric : 0 < y.im := by
    have hpSource : (extChartAt I α).symm y ∈ (chartAt ℂ α).source := by
      rw [← extChartAt_source I α]
      exact (extChartAt I α).map_target hy
    have hcoord : (chartAt ℂ α) ((extChartAt I α).symm y) = y := by
      simpa only [extChartAt_coe, I, modelWithCornersSelf_coe,
        Function.comp_apply, id_eq] using
        (extChartAt I α).right_inv hy
    rw [← hcoord]
    exact P.gluedInteriorComplexChart_target_im_pos (chartAt ℂ α) hi
      ((chartAt ℂ α).map_source hpSource)
  have hnear : (fun z => Riemannian.chartMetricInner (I := I) metric α z b c) =ᶠ[𝓝 y]
      fun z => (z.im ^ 2)⁻¹ * (b.re * c.re + b.im * c.im) := by
    filter_upwards [P.gluedCurvatureBoundedInterior_outside_near α hy houtside]
      with z hz
    exact P.gluedCurvatureBoundedInterior_chartMetricInner_eq α hi hz.1
      (fun k hk => hz.2 k (P.thinSeamCollar_subset_closedThinSeamCollar k hk)) b c
  have hactual := (poincareInner_hasFDerivAt hymetric.ne' b c).congr_of_eventuallyEq hnear
  have hactualAt : HasFDerivAt
      (fun z => Riemannian.chartMetricInner (I := I) metric α z b c)
      (((-2 / y.im ^ 3) * (b.re * c.re + b.im * c.im)) • Complex.imCLM)
      (path 0) := by simpa only [hp] using hactual
  have hscalar := hactualAt.comp_hasDerivAt (0 : ℝ) hpath
  have hG (i j : Fin (Module.finrank ℝ ℂ)) :
      DifferentiableAt ℝ (Riemannian.chartGramOnE (I := I) metric α i j) (path 0) := by
    rw [hp]
    exact ((Riemannian.chartGramOnE_contDiffOn metric α i j).differentiableOn
      (by norm_num)).differentiableAt ((isOpen_extChartAt_target (I := I) α).mem_nhds hy)
  have hbase : (extChartAt I α).symm (path 0) ∈
      (trivializationAt ℂ (TangentSpace I) α).baseSet := by
    rw [hp, Riemannian.trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hconnection := Riemannian.hasDerivAt_chartMetricInner_along
    (I := I) metric α path (fun _ => b) (fun _ => c) hpath.differentiableAt
    (differentiableAt_const b) (differentiableAt_const c) hG hbase
  have heq := hscalar.unique hconnection
  simpa only [hp, Riemannian.covariantDerivCoord_def, hpath.deriv, deriv_const,
    zero_add, Function.comp_apply, smul_apply,
    Complex.imCLM_apply, smul_eq_mul,
    Riemannian.Jacobi.chartChristoffelBilin_apply, mul_assoc, mul_left_comm, mul_comm]
    using heq

/-- **Math.** The actual interior chart connection is the explicit
Levi-Civita connection of the original Poincaré tensor. -/
theorem gluedCurvatureBoundedInterior_chartChristoffelBilin_eq
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k)
    (u v : ℂ) :
    Riemannian.Jacobi.chartChristoffelBilin (I := modelWithCornersSelf ℝ ℂ)
      P.gluedCurvatureBoundedSmoothRiemannianMetric α y u v =
        Complex.mk (-(u.re * v.im + u.im * v.re) / y.im)
          ((u.re * v.re - u.im * v.im) / y.im) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let Γ : ℂ → ℂ → ℂ := fun a b =>
    Riemannian.Jacobi.chartChristoffelBilin (I := I) metric α y a b
  let K : ℂ → ℂ → ℂ := fun a b =>
    Complex.mk (-(a.re * b.im + a.im * b.re) / y.im)
      ((a.re * b.re - a.im * b.im) / y.im)
  let D : ℂ → ℂ → ℂ → ℝ := fun a b c =>
    (-2 / y.im ^ 3) * a.im * (b.re * c.re + b.im * c.im)
  have hp : (extChartAt I α).symm y ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hcoord : (chartAt ℂ α) ((extChartAt I α).symm y) = y := by
    simpa only [extChartAt_coe, I, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq] using (extChartAt I α).right_inv hy
  have hypos : 0 < y.im := by
    rw [← hcoord]
    exact P.gluedInteriorComplexChart_target_im_pos (chartAt ℂ α) hi
      ((chartAt ℂ α).map_source hp)
  have hinner (a b : ℂ) : Riemannian.chartMetricInner (I := I) metric α y a b =
      (y.im ^ 2)⁻¹ * (a.re * b.re + a.im * b.im) :=
    P.gluedCurvatureBoundedInterior_chartMetricInner_eq α hi hy
      (fun k hk => houtside k (P.thinSeamCollar_subset_closedThinSeamCollar k hk)) a b
  have hbalance (a b c : ℂ) : D a b c =
      Riemannian.chartMetricInner (I := I) metric α y (Γ a b) c +
      Riemannian.chartMetricInner (I := I) metric α y b (Γ a c) :=
    P.gluedCurvatureBoundedInterior_chartChristoffel_balance α hi hy houtside a b c
  have hsymm (a b : ℂ) : Γ a b = Γ b a :=
    Riemannian.Jacobi.chartChristoffelBilin_symm metric α y a b
  have hkoszul (a b c : ℂ) :
      2 * Riemannian.chartMetricInner (I := I) metric α y (Γ a b) c =
        D a b c + D b a c - D c a b := by
    have h₁ := hbalance a b c
    have h₂ := hbalance b a c
    have h₃ := hbalance c a b
    rw [hsymm b a] at h₂
    rw [hsymm c a, hsymm c b] at h₃
    rw [Riemannian.chartMetricInner_symm (I := I) metric α y (Γ a c) b] at h₃
    linarith [h₁, h₂, h₃]
  have hKkoszul (a b c : ℂ) :
      2 * Riemannian.chartMetricInner (I := I) metric α y (K a b) c =
        D a b c + D b a c - D c a b := by
    rw [hinner]
    dsimp only [K, D]
    field_simp [hypos.ne']
    ring
  have hpair (a b c : ℂ) :
      Riemannian.chartMetricInner (I := I) metric α y (Γ a b) c =
        Riemannian.chartMetricInner (I := I) metric α y (K a b) c := by
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

/-- **Math.** The actual interior chart curvature has the constant-curvature
Poincaré component `R(∂x, ∂y)∂y = -y⁻² ∂x`. -/
theorem gluedCurvatureBoundedInterior_chartCurvature_real_angular
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k) :
    Riemannian.Jacobi.chartCurvature (I := modelWithCornersSelf ℝ ℂ)
      P.gluedCurvatureBoundedSmoothRiemannianMetric α y 1 Complex.I Complex.I =
        Complex.ofReal (-(y.im ^ 2)⁻¹) := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let F : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    Riemannian.Jacobi.chartChristoffelBilin (I := I) metric α
  have hyInterior : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy
  have hFdiff : DifferentiableAt ℝ F y :=
    Riemannian.Jacobi.differentiableAt_chartChristoffelBilin metric α hyInterior
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
  have hp : (extChartAt I α).symm y ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hcoord : (chartAt ℂ α) ((extChartAt I α).symm y) = y := by
    simpa only [extChartAt_coe, I, modelWithCornersSelf_coe,
      Function.comp_apply, id_eq] using (extChartAt I α).right_inv hy
  have hypos : 0 < y.im := by
    rw [← hcoord]
    exact P.gluedInteriorComplexChart_target_im_pos (chartAt ℂ α) hi
      ((chartAt ℂ α).map_source hp)
  have hnear := P.gluedCurvatureBoundedInterior_outside_near α hy houtside
  have h1I : (fun z : ℂ => F z 1 Complex.I) =ᶠ[𝓝 y]
      fun z => Complex.ofReal (-z.im⁻¹) := by
    filter_upwards [hnear] with z hz
    have h := P.gluedCurvatureBoundedInterior_chartChristoffelBilin_eq
      α hi hz.1 hz.2 (1 : ℂ) Complex.I
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
    have h := P.gluedCurvatureBoundedInterior_chartChristoffelBilin_eq
      α hi hz.1 hz.2 Complex.I Complex.I
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
    P.gluedCurvatureBoundedInterior_chartChristoffelBilin_eq α hi hy houtside a b
  rw [Riemannian.Jacobi.chartCurvature_def, Riemannian.Jacobi.christoffelCurvature]
  rw [← hFderiv_apply Complex.I Complex.I 1, ← hFderiv_apply 1 Complex.I Complex.I,
    hIIderiv, h1Ideriv, hAt 1 (F y Complex.I Complex.I), hAt Complex.I (F y 1 Complex.I),
    hAt Complex.I Complex.I, hAt 1 Complex.I]
  apply Complex.ext <;>
    simp [Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]

/-- **Math.** The actual intrinsic curvature form on the unchanged interior
chart frame is the Poincaré numerator `y⁻⁴`. -/
theorem gluedCurvatureBoundedInterior_curvatureFormAt_real_angular
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    (Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureFormAt metric p
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p (1 : ℂ))
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p Complex.I)
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p Complex.I)
      ((trivializationAt ℂ (TangentSpace I) α).symmL ℝ p (1 : ℂ)) =
        ((y.im ^ 2)⁻¹) ^ 2 := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p := (extChartAt I α).symm y
  let τ := trivializationAt ℂ (TangentSpace I) α
  have hp : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := hp
  have hframe (v : ℂ) :
      (∑ i : Fin (Module.finrank ℝ ℂ),
        Riemannian.Geodesic.chartCoord (E := ℂ) i v •
          Riemannian.Tensor.chartBasisVecFiber (I := I) α i p) = τ.symmL ℝ p v := by
    calc
      _ = ∑ i : Fin (Module.finrank ℝ ℂ),
          Riemannian.Geodesic.chartCoord (E := ℂ) i v •
            τ.symmL ℝ p (Module.finBasis ℝ ℂ i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Riemannian.Tensor.chartBasisVecFiber]
          exact congrArg (fun z => Riemannian.Geodesic.chartCoord (E := ℂ) i v • z)
            ((Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase
              (Module.finBasis ℝ ℂ i)).symm)
      _ = τ.symmL ℝ p (∑ i : Fin (Module.finrank ℝ ℂ),
          Riemannian.Geodesic.chartCoord (E := ℂ) i v • Module.finBasis ℝ ℂ i) := by
          simp only [map_sum, map_smul]
      _ = τ.symmL ℝ p v := by
          congr 1
          simpa only [Riemannian.Geodesic.chartCoord_def] using
            (Module.finBasis ℝ ℂ).sum_repr v
  have hbridge := Riemannian.Jacobi.curvatureFormAt_chartFrame
    (E := ℂ) (H := ℂ) (I := I) (M := P.GluedCarrier)
    (g := P.gluedCurvatureBoundedSmoothRiemannianMetric)
    (α := α) (p := p) hp (1 : ℂ) Complex.I Complex.I (1 : ℂ)
  rw [hframe 1, hframe Complex.I] at hbridge
  have hcoord : (extChartAt I α) p = y := (extChartAt I α).right_inv hy
  rw [hcoord, P.gluedCurvatureBoundedInterior_chartCurvature_real_angular
    α hi hy houtside] at hbridge
  change (Riemannian.RiemannianMetric.leviCivitaConnection
    P.gluedCurvatureBoundedSmoothRiemannianMetric).curvatureFormAt
    P.gluedCurvatureBoundedSmoothRiemannianMetric p
    (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I)
    (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p (1 : ℂ)) = _
  rw [hbridge, P.gluedCurvatureBoundedInterior_chartMetricInner_eq α hi hy
    (fun k hk => houtside k (P.thinSeamCollar_subset_closedThinSeamCollar k hk))]
  simp [pow_two]

/-- **Math.** The actual Riemannian sectional curvature of the unchanged
interior chart frame is exactly `-1`. -/
theorem gluedCurvatureBoundedInterior_sectionalCurvature_eq_neg_one
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    let τ := trivializationAt ℂ (TangentSpace I) α
    letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
      ⟨metric.toRiemannianMetric⟩
    Riemannian.sectionalCurvature
      ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureFormAt metric p)
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I) = -1 := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p := (extChartAt I α).symm y
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let τ := trivializationAt ℂ (TangentSpace I) α
  let A : TangentSpace I p := τ.symmL ℝ p (1 : ℂ)
  let B : TangentSpace I p := τ.symmL ℝ p Complex.I
  letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  have hp : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := hp
  have hcoord : (extChartAt I α) p = y := (extChartAt I α).right_inv hy
  have hchartInner (a b : ℂ) :
      Riemannian.RiemannianMetric.metricInner metric p
        (τ.symmL ℝ p a) (τ.symmL ℝ p b) =
          (y.im ^ 2)⁻¹ * (a.re * b.re + a.im * b.im) := by
    have h := Riemannian.chartMetricInner_extChartAt_eq_metricInner
      (I := I) metric α hp a b
    rw [hcoord] at h
    rw [Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase a,
      Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase b, ← h]
    exact P.gluedCurvatureBoundedInterior_chartMetricInner_eq α hi hy
      (fun k hk => houtside k (P.thinSeamCollar_subset_closedThinSeamCollar k hk)) a b
  have haa : inner ℝ A A = (y.im ^ 2)⁻¹ := by
    change Riemannian.RiemannianMetric.metricInner metric p
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p (1 : ℂ)) = _
    rw [hchartInner]
    simp only [Complex.one_re, Complex.one_im, mul_zero, add_zero, mul_one]
  have hbb : inner ℝ B B = (y.im ^ 2)⁻¹ := by
    change Riemannian.RiemannianMetric.metricInner metric p
      (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p Complex.I) = _
    rw [hchartInner]
    simp only [Complex.I_re, Complex.I_im, mul_zero, zero_add, mul_one]
  have hab : inner ℝ A B = 0 := by
    change Riemannian.RiemannianMetric.metricInner metric p
      (τ.symmL ℝ p (1 : ℂ)) (τ.symmL ℝ p Complex.I) = _
    rw [hchartInner]
    simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
      zero_mul, add_zero, mul_zero]
  have hwedge : Riemannian.wedgeSq A B = ((y.im ^ 2)⁻¹) ^ 2 := by
    rw [Riemannian.wedgeSq, haa, hbb, hab]
    ring
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection metric
  have hLC : connection.IsLeviCivita metric :=
    connection.isLeviCivita_of_koszulDual metric
      (fun U V W q => Riemannian.RiemannianMetric.koszulDualSection_dual metric U V W q)
  have hB := connection.isAlgCurvatureForm_curvatureFormAt metric hLC p
  have hform : connection.curvatureFormAt metric p A B B A = ((y.im ^ 2)⁻¹) ^ 2 :=
    P.gluedCurvatureBoundedInterior_curvatureFormAt_real_angular α hi hy houtside
  have hnum : connection.curvatureFormAt metric p A B A B = -((y.im ^ 2)⁻¹) ^ 2 := by
    have h := hB.antisymm₃₄ A B A B
    rw [hform] at h
    exact h
  have hypos : 0 < y.im := by
    have hcoord' : (chartAt ℂ α) p = y := by
      simpa only [p, extChartAt_coe, I, modelWithCornersSelf_coe,
        Function.comp_apply, id_eq] using (extChartAt I α).right_inv hy
    rw [← hcoord']
    exact P.gluedInteriorComplexChart_target_im_pos (chartAt ℂ α) hi
      ((chartAt ℂ α).map_source hp)
  change connection.curvatureFormAt metric p A B A B / Riemannian.wedgeSq A B = -1
  rw [hnum, hwedge, neg_div,
    div_self (pow_ne_zero 2 (inv_ne_zero (pow_ne_zero 2 hypos.ne')))]

/-- **Math.** The unchanged interior satisfies the intrinsic curvature
operator lower bound on every pair of tangent vectors. -/
theorem gluedCurvatureBoundedInterior_curvatureOperatorAt_lower_bound
    (P : ExerciseGluingPreparation C g n genera X)
    (α : P.GluedCarrier) (hi : P.IsGluedInteriorComplexChart (chartAt ℂ α))
    {y : ℂ} (hy : y ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (houtside : ∀ k : Fin (n - 1),
      (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm y ∉ P.closedThinSeamCollar k) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let p := (extChartAt I α).symm y
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    ∀ u v : TangentSpace I p,
      Riemannian.RiemannianMetric.metricInner metric p u u *
          Riemannian.RiemannianMetric.metricInner metric p v v -
        Riemannian.RiemannianMetric.metricInner metric p u v *
          Riemannian.RiemannianMetric.metricInner metric p u v ≤
        Riemannian.RiemannianMetric.metricInner metric p
          ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
            p u v v) u := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let p := (extChartAt I α).symm y
  let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
  let τ := trivializationAt ℂ (TangentSpace I) α
  letI : Bundle.RiemannianBundle (fun q : P.GluedCarrier => TangentSpace I q) :=
    ⟨metric.toRiemannianMetric⟩
  have hp : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hy
  have hpBase : p ∈ τ.baseSet := hp
  let e : Module.Basis (Fin 2) ℝ (TangentSpace I p) :=
    Complex.basisOneI.map (τ.continuousLinearEquivAt ℝ p hpBase).symm.toLinearEquiv
  have he0 : e 0 = τ.symmL ℝ p (1 : ℂ) := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI,
      Matrix.cons_val_zero, ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have he1 : e 1 = τ.symmL ℝ p Complex.I := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI,
      Matrix.cons_val_one, Matrix.cons_val_zero, ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have hlin : LinearIndependent ℝ ![e 0, e 1] := by
    convert e.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  have harea : 0 < Riemannian.wedgeSq (e 0) (e 1) :=
    (Riemannian.wedgeSq_pos_iff_linearIndependent (e 0) (e 1)).2 hlin
  let connection := Riemannian.RiemannianMetric.leviCivitaConnection metric
  have hsectional : Riemannian.sectionalCurvature (connection.curvatureFormAt metric p)
      (e 0) (e 1) ≤ -1 := by
    rw [he0, he1, P.gluedCurvatureBoundedInterior_sectionalCurvature_eq_neg_one
      α hi hy houtside]
  dsimp only
  intro u v
  have hbase := (div_le_iff₀ harea).mp hsectional
  have h := Riemannian.curvatureOperatorAt_pair_lower_bound_of_basis_pair
    (I := I) metric p e (-1) hbase u v
  simpa only [neg_neg, one_mul] using h

/-- **Math.** At an actual glued point with an interior canonical chart and
outside all closed smoothing strips, the intrinsic curvature-operator bound
holds on its actual tangent space. -/
theorem gluedCurvatureBounded_curvatureOperatorAt_lower_bound_of_interior_outside_closedThinSeamCollars
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier)
    (hi : P.IsGluedInteriorComplexChart (chartAt ℂ b))
    (houtside : ∀ k : Fin (n - 1), b ∉ P.closedThinSeamCollar k) :
    let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
    let metric := P.gluedCurvatureBoundedSmoothRiemannianMetric
    ∀ u v : TangentSpace I b,
      Riemannian.RiemannianMetric.metricInner metric b u u *
          Riemannian.RiemannianMetric.metricInner metric b v v -
        Riemannian.RiemannianMetric.metricInner metric b u v *
          Riemannian.RiemannianMetric.metricInner metric b u v ≤
        Riemannian.RiemannianMetric.metricInner metric b
          ((Riemannian.RiemannianMetric.leviCivitaConnection metric).curvatureOperatorAt
            b u v v) u := by
  let I : ModelWithCorners ℝ ℂ ℂ := modelWithCornersSelf ℝ ℂ
  let y : ℂ := (extChartAt I b) b
  have hy : y ∈ (extChartAt I b).target := mem_extChartAt_target b
  have hpoint : (extChartAt I b).symm y = b :=
    (extChartAt I b).left_inv (mem_extChartAt_source b)
  have houtside' : ∀ k : Fin (n - 1),
      (extChartAt I b).symm y ∉ P.closedThinSeamCollar k := by
    simpa only [hpoint] using houtside
  have h := P.gluedCurvatureBoundedInterior_curvatureOperatorAt_lower_bound
    b hi hy houtside'
  dsimp only [I, y] at h
  rw [extChartAt_to_inv] at h
  exact h

#print axioms gluedCurvatureBoundedInterior_chartMetricInner_eq
#print axioms gluedCurvatureBoundedInterior_chartChristoffel_balance
#print axioms gluedCurvatureBoundedInterior_chartChristoffelBilin_eq
#print axioms gluedCurvatureBoundedInterior_chartCurvature_real_angular
#print axioms gluedCurvatureBoundedInterior_curvatureFormAt_real_angular
#print axioms gluedCurvatureBoundedInterior_sectionalCurvature_eq_neg_one
#print axioms gluedCurvatureBoundedInterior_curvatureOperatorAt_lower_bound
#print axioms gluedCurvatureBounded_curvatureOperatorAt_lower_bound_of_interior_outside_closedThinSeamCollars

end
end SystolicGrowth.ExerciseGluingPreparation
