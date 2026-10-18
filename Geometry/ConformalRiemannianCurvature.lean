module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalWarpChartConnection
public import Geometry.CurvatureTwoDimensional
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

@[expose] public section

/-!
# Intrinsic curvature of the actual conformally scaled warped metric

All calculations remain in the ORIGINAL selected chart, using the actual
Christoffel operator already derived from the metric. The mixed derivatives
cancel by genuine Hessian symmetry. The chart curvature is then transported
to the actual Levi-Civita tensor and its two-dimensional all-pair identity.
-/

open Bundle Manifold Riemannian Set Filter
open scoped ContDiff Manifold Topology

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

local instance conformalCurvatureComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by simp [Complex.finrank_real_complex]⟩

private theorem fderiv_complex_mk_apply {r s : ℂ → ℝ} {z : ℂ}
    (hr : DifferentiableAt ℝ r z) (hs : DifferentiableAt ℝ s z) (d : ℂ) :
    fderiv ℝ (fun q => Complex.mk (r q) (s q)) z d =
      Complex.mk (fderiv ℝ r z d) (fderiv ℝ s z d) := by
  have h := Complex.equivRealProdCLM.symm.hasFDerivAt.comp z (hr.hasFDerivAt.prodMk hs.hasFDerivAt)
  have hfun : (fun q => Complex.equivRealProdCLM.symm (r q, s q)) =
      fun q => Complex.mk (r q) (s q) := by
    funext q
    apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply]
  have hd := h.fderiv
  change fderiv ℝ (fun q => Complex.equivRealProdCLM.symm (r q, s q)) z = _ at hd
  rw [hfun] at hd
  have heval := congrArg (fun L : ℂ →L[ℝ] ℂ => L d) hd
  apply Complex.ext
  · simpa [ContinuousLinearMap.comp_apply, Complex.equivRealProdCLM_symm_apply] using congrArg Complex.re heval
  · simpa [ContinuousLinearMap.comp_apply, Complex.equivRealProdCLM_symm_apply] using congrArg Complex.im heval

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]

/-- **Math.** The actual same-atlas conformal metric scales the actual
chart tensor, not a separately defined coordinate model. -/
theorem conformalRiemannianMetric_chartMetricInner
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (u : M → ℝ)
    (hu : ContMDiff (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℝ) ∞ u)
    (α : M) (z a b : ℂ) :
    chartMetricInner (conformalRiemannianMetric g u hu) α z a b =
      Real.exp (2 * u ((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z)) *
        chartMetricInner g α z a b := by
  simp only [chartMetricInner_def, chartGramOnE_def, Tensor.chartGramMatrix_apply]
  change (∑ i, ∑ j, (Real.exp (2 * u ((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z)) *
      g.inner ((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z)
        (Tensor.chartBasisVecFiber α i ((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z))
        (Tensor.chartBasisVecFiber α j ((extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z))) *
      Geodesic.chartCoord i a * Geodesic.chartCoord j b) = _
  simp_rw [mul_assoc, ← Finset.mul_sum]

private theorem conformalPartial_fderiv_symmetry
    (f : ℂ → ℝ) {s : Set ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {z : ℂ} (hz : z ∈ s) :
    fderiv ℝ (conformalPartialImag f) z 1 = fderiv ℝ (conformalPartialReal f) z Complex.I := by
  have hdfSmooth : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hdfSmooth.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have heval (d v : ℂ) : fderiv ℝ (fun q => fderiv ℝ f q v) z d =
      fderiv ℝ (fderiv ℝ f) z d v := by
    rw [fderiv_clm_apply hdf (differentiableAt_const v)]
    simp
  unfold conformalPartialImag conformalPartialReal
  rw [heval, heval]
  exact (hf.contDiffAt (hs.mem_nhds hz)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top)) 1 Complex.I

private theorem chartChristoffel_eval_fderiv
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target) (a b d : ℂ) :
    fderiv ℝ (fun q => Jacobi.chartChristoffelBilin g α q a b) z d =
      fderiv ℝ (Jacobi.chartChristoffelBilin g α) z d a b := by
  have hz' : z ∈ interior (extChartAt (modelWithCornersSelf ℝ ℂ) α).target := by
    rw [(isOpen_extChartAt_target α).interior_eq]
    exact hz
  have hd := Jacobi.differentiableAt_chartChristoffelBilin g α hz'
  have hda := hd.clm_apply (differentiableAt_const a)
  rw [fderiv_clm_apply hda (differentiableAt_const b),
    fderiv_clm_apply hd (differentiableAt_const a)]
  simp

/-- **Math.** The curvature of the ACTUAL chart Christoffel operator of
`exp (2f) * (dx² + W²dy²)`. Its real component contains the warped
Laplacian of `f`; its imaginary component vanishes by Hessian symmetry. -/
theorem conformalWarpChartCurvature_real_imag
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W) (hWpos : ∀ t, 0 < W t)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hmetric : ∀ᶠ q in 𝓝 z, ∀ a b,
      chartMetricInner g α q a b = conformalWarpMetricInner f W q a b) :
    Jacobi.chartCurvature g α z 1 Complex.I Complex.I = Complex.mk
      (-(W z.re * deriv (deriv W) z.re + W z.re * deriv W z.re * conformalPartialReal f z +
        W z.re ^ 2 * fderiv ℝ (conformalPartialReal f) z 1 +
          fderiv ℝ (conformalPartialImag f) z Complex.I)) 0 := by
  let F := Jacobi.chartChristoffelBilin g α
  let X := conformalPartialReal f
  let Y := conformalPartialImag f
  have hopen := isOpen_extChartAt_target (I := modelWithCornersSelf ℝ ℂ) α
  have htarget := hopen.mem_nhds hz
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) (extChartAt (modelWithCornersSelf ℝ ℂ) α).target :=
    hf.fderiv_of_isOpen hopen (by simp)
  have hX : DifferentiableAt ℝ X z := by
    exact ((hdf.clm_apply contDiffOn_const).contDiffAt htarget).differentiableAt (by simp)
  have hY : DifferentiableAt ℝ Y z := by
    exact ((hdf.clm_apply contDiffOn_const).contDiffAt htarget).differentiableAt (by simp)
  have hwD := (hW.differentiable (by simp) z.re).hasDerivAt
  have hW' : ContDiff ℝ ∞ (deriv W) := hW.deriv'
  have hwD' := (hW'.differentiable (by simp) z.re).hasDerivAt
  have hw := hwD.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt
  have hw' := hwD'.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt
  have hrII := ((hw.mul hw').add ((hw.pow 2).mul hX.hasFDerivAt)).neg
  have hII : (fun q => F q Complex.I Complex.I) =ᶠ[𝓝 z]
      fun q => Complex.mk (-(W q.re * deriv W q.re + W q.re ^ 2 * X q)) (Y q) := by
    filter_upwards [htarget, hmetric.eventually_nhds] with q hq hm
    rw [conformalWarpChartChristoffel_eq_of_eventually g α f W hf hW hWpos hq hm]
    apply Complex.ext <;> simp [conformalWarpChristoffel, X, Y]
  have hIIderiv : fderiv ℝ (fun q => F q Complex.I Complex.I) z 1 =
      Complex.mk (-(deriv W z.re ^ 2 + W z.re * deriv (deriv W) z.re +
        2 * W z.re * deriv W z.re * X z + W z.re ^ 2 * fderiv ℝ X z 1))
        (fderiv ℝ Y z 1) := by
    rw [hII.fderiv_eq]
    have hr : DifferentiableAt ℝ (fun q : ℂ => -(W q.re * deriv W q.re + W q.re ^ 2 * X q)) z :=
      hrII.differentiableAt
    rw [fderiv_complex_mk_apply hr hY]
    apply Complex.ext
    · dsimp only
      have hrD := hrII.fderiv
      change fderiv ℝ (fun q : ℂ => -(W q.re * deriv W q.re + W q.re ^ 2 * X q)) z = _ at hrD
      rw [hrD]
      simp [ContinuousLinearMap.comp_apply]
      ring
    · rfl
  have hquot := hwD'.div hwD (hWpos z.re).ne'
  have hquotC := hquot.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt
  have him1I := hX.hasFDerivAt.add hquotC
  have h1I : (fun q => F q 1 Complex.I) =ᶠ[𝓝 z]
      fun q => Complex.mk (Y q) (X q + deriv W q.re / W q.re) := by
    filter_upwards [htarget, hmetric.eventually_nhds] with q hq hm
    rw [conformalWarpChartChristoffel_eq_of_eventually g α f W hf hW hWpos hq hm]
    apply Complex.ext <;> simp [conformalWarpChristoffel, X, Y]
  have h1Ideriv : fderiv ℝ (fun q => F q 1 Complex.I) z Complex.I =
      Complex.mk (fderiv ℝ Y z Complex.I) (fderiv ℝ X z Complex.I) := by
    rw [h1I.fderiv_eq]
    have hi : DifferentiableAt ℝ (fun q : ℂ => X q + deriv W q.re / W q.re) z :=
      him1I.differentiableAt
    rw [fderiv_complex_mk_apply hY hi]
    apply Complex.ext
    · rfl
    · dsimp only
      have hiD := him1I.fderiv
      change fderiv ℝ (fun q : ℂ => X q + deriv W q.re / W q.re) z = _ at hiD
      rw [hiD]
      simp [ContinuousLinearMap.comp_apply]
  have hAt (a b : ℂ) : F z a b = conformalWarpChristoffel f W z a b :=
    conformalWarpChartChristoffel_eq_of_eventually g α f W hf hW hWpos hz hmetric a b
  have hmixed : fderiv ℝ Y z 1 = fderiv ℝ X z Complex.I :=
    conformalPartial_fderiv_symmetry f hopen hf hz
  rw [Jacobi.chartCurvature_def, Jacobi.christoffelCurvature,
    ← chartChristoffel_eval_fderiv g α hz Complex.I Complex.I 1,
    ← chartChristoffel_eval_fderiv g α hz 1 Complex.I Complex.I]
  change fderiv ℝ (fun q => F q Complex.I Complex.I) z 1 -
      fderiv ℝ (fun q => F q 1 Complex.I) z Complex.I +
      F z 1 (F z Complex.I Complex.I) - F z Complex.I (F z 1 Complex.I) = _
  rw [hIIderiv, h1Ideriv, hAt 1 (F z Complex.I Complex.I),
    hAt Complex.I (F z 1 Complex.I), hAt Complex.I Complex.I, hAt 1 Complex.I]
  apply Complex.ext
  · simp [conformalWarpChristoffel, X, Y]
    field_simp [(hWpos z.re).ne']
    ring
  · simp only [Complex.add_im, Complex.sub_im]
    dsimp [conformalWarpChristoffel]
    rw [hmixed]
    dsimp [X, Y]
    field_simp [(hWpos z.re).ne']
    ring

/-- **Math.** The literal numerator derived from the actual connection. -/
def conformalWarpCurvatureNumerator (f : ℂ → ℝ) (W : ℝ → ℝ) (z : ℂ) : ℝ :=
  W z.re * deriv (deriv W) z.re + W z.re * deriv W z.re * conformalPartialReal f z +
    W z.re ^ 2 * fderiv ℝ (conformalPartialReal f) z 1 +
      fderiv ℝ (conformalPartialImag f) z Complex.I

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Transport the derived chart curvature to the ACTUAL
Levi-Civita form on the original tangent bundle, with reversed slots. -/
theorem conformalWarpMetric_curvatureFormAt_chart_basis
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W) (hWpos : ∀ t, 0 < W t)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hmetric : ∀ᶠ q in 𝓝 z, ∀ a b,
      chartMetricInner g α q a b = conformalWarpMetricInner f W q a b) :
    let I := modelWithCornersSelf ℝ ℂ
    let p := (extChartAt I α).symm z
    let τ := trivializationAt ℂ (TangentSpace I) α
    g.leviCivitaConnection.curvatureFormAt g p
      (τ.symmL ℝ p 1) (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p 1) =
        Real.exp (2 * f z) * conformalWarpCurvatureNumerator f W z := by
  let I := modelWithCornersSelf ℝ ℂ
  let p := (extChartAt I α).symm z
  let τ := trivializationAt ℂ (TangentSpace I) α
  have hpSource : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hz
  have hpBase : p ∈ τ.baseSet := hpSource
  have hframe (v : ℂ) :
      (∑ i, Geodesic.chartCoord (E := ℂ) i v • Tensor.chartBasisVecFiber (I := I) α i p) =
        τ.symmL ℝ p v := by
    calc
      _ = ∑ i, Geodesic.chartCoord (E := ℂ) i v • τ.symmL ℝ p (Module.finBasis ℝ ℂ i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Tensor.chartBasisVecFiber]
        exact congrArg (fun w => Geodesic.chartCoord (E := ℂ) i v • w)
          ((Bundle.Trivialization.symmL_apply τ hpBase (Module.finBasis ℝ ℂ i)).symm)
      _ = τ.symmL ℝ p (∑ i, Geodesic.chartCoord (E := ℂ) i v • Module.finBasis ℝ ℂ i) := by
        simp only [map_sum, map_smul]
      _ = τ.symmL ℝ p v := by
        congr 1
        simpa only [Geodesic.chartCoord_def] using (Module.finBasis ℝ ℂ).sum_repr v
  have hbridge := Jacobi.curvatureFormAt_chartFrame g hpSource (1 : ℂ) Complex.I Complex.I (1 : ℂ)
  rw [hframe, hframe, (extChartAt I α).right_inv hz,
    conformalWarpChartCurvature_real_imag g α f W hf hW hWpos hz hmetric] at hbridge
  have hm := hmetric.self_of_nhds
  dsimp only
  rw [hbridge, hm]
  simp [conformalWarpMetricInner, conformalWarpCurvatureNumerator]
  ring

/-- **Math.** The genuine original-coordinate conformal PDE gives the
complete reversed-slot curvature identity on ALL tangent vectors. Its
only geometric inputs are the actual tensor's local form and the literal
PDE; the curvature conclusion is derived, not assumed. -/
theorem conformalWarpMetric_curvatureOperatorAt_eq_of_pde
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M)
    (f : ℂ → ℝ) (W : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hW : ContDiff ℝ ∞ W) (hWpos : ∀ t, 0 < W t)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hmetric : ∀ᶠ q in 𝓝 z, ∀ a b,
      chartMetricInner g α q a b = conformalWarpMetricInner f W q a b)
    (hpde : fderiv ℝ (conformalPartialReal f) z 1 +
        (deriv W z.re / W z.re) * conformalPartialReal f z +
        fderiv ℝ (conformalPartialImag f) z Complex.I / W z.re ^ 2 =
      -(deriv (deriv W) z.re / W z.re) + Real.exp (2 * f z)) :
    let p := (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z
    ∀ x y : TangentSpace (modelWithCornersSelf ℝ ℂ) p,
      g.metricInner p x x * g.metricInner p y y - (g.metricInner p x y) ^ 2 =
        g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x := by
  let I := modelWithCornersSelf ℝ ℂ
  let p := (extChartAt I α).symm z
  let τ := trivializationAt ℂ (TangentSpace I) α
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hpSource : p ∈ (chartAt ℂ α).source := by
    rw [← extChartAt_source I α]
    exact (extChartAt I α).map_target hz
  have hpBase : p ∈ τ.baseSet := hpSource
  let e : Module.Basis (Fin 2) ℝ (TangentSpace I p) :=
    Complex.basisOneI.map (τ.continuousLinearEquivAt ℝ p hpBase).symm.toLinearEquiv
  have he0 : e 0 = τ.symmL ℝ p 1 := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI, Matrix.cons_val_zero,
      ContinuousLinearEquiv.coe_toLinearEquiv, Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have he1 : e 1 = τ.symmL ℝ p Complex.I := by
    simp only [e, Module.Basis.map_apply, Complex.coe_basisOneI, Matrix.cons_val_one,
      Matrix.cons_val_zero, ContinuousLinearEquiv.coe_toLinearEquiv,
      Bundle.Trivialization.symm_continuousLinearEquivAt_eq]
  have hm := hmetric.self_of_nhds
  have hpair (a b : ℂ) : g.metricInner p (τ.symmL ℝ p a) (τ.symmL ℝ p b) =
      conformalWarpMetricInner f W z a b := by
    have h := chartMetricInner_extChartAt_eq_metricInner g α hpSource a b
    rw [(extChartAt I α).right_inv hz, ← Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase a,
      ← Bundle.Trivialization.symmL_apply (R := ℝ) τ hpBase b, hm] at h
    exact h.symm
  have hnum : conformalWarpCurvatureNumerator f W z = Real.exp (2 * f z) * W z.re ^ 2 := by
    have h := congrArg (fun r : ℝ => W z.re ^ 2 * r) hpde
    field_simp [(hWpos z.re).ne'] at h
    unfold conformalWarpCurvatureNumerator
    nlinarith [h]
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g (fun X Y V q => g.koszulDualSection_dual X Y V q)
  have hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have hbaseReverse : g.leviCivitaConnection.curvatureFormAt g p (e 0) (e 1) (e 1) (e 0) =
      wedgeSq (e 0) (e 1) := by
    rw [he0, he1, conformalWarpMetric_curvatureFormAt_chart_basis g α f W hf hW hWpos hz hmetric, hnum]
    change _ = g.metricInner p (τ.symmL ℝ p 1) (τ.symmL ℝ p 1) *
        g.metricInner p (τ.symmL ℝ p Complex.I) (τ.symmL ℝ p Complex.I) -
      g.metricInner p (τ.symmL ℝ p 1) (τ.symmL ℝ p Complex.I) *
        g.metricInner p (τ.symmL ℝ p 1) (τ.symmL ℝ p Complex.I)
    rw [hpair, hpair, hpair]
    simp [conformalWarpMetricInner]
  have hbase : g.leviCivitaConnection.curvatureFormAt g p (e 0) (e 1) (e 0) (e 1) =
      -wedgeSq (e 0) (e 1) := by
    have h := hB.antisymm₃₄ (e 0) (e 1) (e 0) (e 1)
    rw [hbaseReverse] at h
    linarith
  dsimp only
  intro x y
  have hd := hB.diag_eq_det_sq_mul_basis e x y
  rw [hbase] at hd
  have hw := wedgeSq_eq_det_sq_mul_basis e x y
  have hs := hB.antisymm₃₄ x y x y
  change g.metricInner p x x * g.metricInner p y y - (g.metricInner p x y) ^ 2 =
    g.leviCivitaConnection.curvatureFormAt g p x y y x
  have hxy : g.metricInner p x x * g.metricInner p y y - (g.metricInner p x y) ^ 2 = wedgeSq x y := by
    simp only [wedgeSq, pow_two]
    rfl
  rw [hxy]
  nlinarith [hd, hw, hs]

#print axioms conformalRiemannianMetric_chartMetricInner
#print axioms conformalWarpChartCurvature_real_imag
#print axioms conformalWarpMetric_curvatureFormAt_chart_basis
#print axioms conformalWarpMetric_curvatureOperatorAt_eq_of_pde

end

end SystolicGrowth
