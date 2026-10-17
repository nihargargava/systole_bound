module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalRiemannianCurvature
public import Geometry.SmoothWarpConformalCoordinates

@[expose] public section

/-!
# Actual Laplacian under the smooth warped conformal coordinate

The reciprocal-warp coordinate and its constructed inverse convert the
literal Euclidean Laplacian to the original warped-coordinate trace. All
derivatives are genuine Fréchet derivatives of the same smooth function.
-/

open Set Filter Bundle Manifold Riemannian
open scoped ContDiff Topology Manifold

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

/-- **Math.** The genuine complex-plane Laplacian is the trace of the
two literal coordinate partial derivatives. -/
theorem laplacian_complex_eq_conformalPartial_trace {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ ∞ f z) :
    Laplacian.laplacian f z =
      fderiv ℝ (conformalPartialReal f) z 1 +
        fderiv ℝ (conformalPartialImag f) z Complex.I := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  unfold conformalPartialReal conformalPartialImag
  rw [fderiv_clm_apply hdf (differentiableAt_const (1 : ℂ)),
    fderiv_clm_apply hdf (differentiableAt_const Complex.I)]
  simp

/-- **Math.** The Euclidean Laplacian after the ACTUAL inverse conformal
coordinate equals `W² f_tt + W W' f_t + f_θθ` in the original coordinate.
The first and second inverse-radius derivatives are obtained from its
proved derivative `T' = W(T)`, not assumed as extra data. -/
theorem smoothWarpConformalChart_laplacian_comp_symm
    {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t)
    {f : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {z : ℂ} (hz : z ∈ s) :
    let ψ := smoothWarpConformalChart hW.continuous hpos
    Laplacian.laplacian (f ∘ ψ.symm) (ψ z) =
      W z.re ^ 2 * fderiv ℝ (conformalPartialReal f) z 1 +
        W z.re * deriv W z.re * conformalPartialReal f z +
          fderiv ℝ (conformalPartialImag f) z Complex.I := by
  let ψ := smoothWarpConformalChart hW.continuous hpos
  let P : ℂ → ℂ := ψ.symm
  let w : ℂ := ψ z
  let X := conformalPartialReal f
  let Y := conformalPartialImag f
  have hzw : z ∈ ψ.source := by simp [ψ]
  have hw : w ∈ ψ.target := ψ.map_source hzw
  have hp : P w = z := ψ.left_inv hzw
  have hP := smoothWarpConformalChart_symm_hasFDerivAt hW.continuous hpos hw
  have hPsmooth : ContDiffAt ℝ ∞ P w :=
    (smoothWarpConformalChart_symm_contDiffOn hW hpos).contDiffAt (ψ.open_target.mem_nhds hw)
  have hlocal : ∀ᶠ q in 𝓝 w, P q ∈ s := by
    have hmem : P w ∈ s := by rw [hp]; exact hz
    exact hP.continuousAt.eventually (hs.mem_nhds hmem)
  have hdf : ContDiffOn ℝ ∞ (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
  have hX : DifferentiableAt ℝ X z :=
    ((hdf.clm_apply contDiffOn_const).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have hY : DifferentiableAt ℝ Y z :=
    ((hdf.clm_apply contDiffOn_const).contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  have hDreal (q : ℂ) : smoothWarpConformalInverseDerivative hW.continuous hpos q 1 =
      W (P q).re • (1 : ℂ) := by
    apply Complex.ext <;>
      simp [smoothWarpConformalInverseDerivative_apply, smoothWarpConformalFactor,
        P, ψ, smoothWarpConformalChart_symm_apply]
  have hDimag (q : ℂ) : smoothWarpConformalInverseDerivative hW.continuous hpos q Complex.I =
      Complex.I := by simp [smoothWarpConformalInverseDerivative_apply]
  have hreal : conformalPartialReal (f ∘ P) =ᶠ[𝓝 w]
      fun q => W (P q).re * X (P q) := by
    filter_upwards [ψ.open_target.mem_nhds hw, hlocal] with q hq hsq
    have hD := ((hf.contDiffAt (hs.mem_nhds hsq)).differentiableAt (by simp)).hasFDerivAt.comp q
      (smoothWarpConformalChart_symm_hasFDerivAt hW.continuous hpos hq)
    unfold conformalPartialReal
    rw [hD.fderiv]
    simp only [ContinuousLinearMap.comp_apply, hDreal, map_smul, smul_eq_mul]
    rfl
  have himag : conformalPartialImag (f ∘ P) =ᶠ[𝓝 w]
      fun q => Y (P q) := by
    filter_upwards [ψ.open_target.mem_nhds hw, hlocal] with q hq hsq
    have hD := ((hf.contDiffAt (hs.mem_nhds hsq)).differentiableAt (by simp)).hasFDerivAt.comp q
      (smoothWarpConformalChart_symm_hasFDerivAt hW.continuous hpos hq)
    unfold conformalPartialImag
    rw [hD.fderiv]
    simp only [ContinuousLinearMap.comp_apply, hDimag]
    rfl
  have hXat : DifferentiableAt ℝ X (P w) := by rw [hp]; exact hX
  have hYat : DifferentiableAt ℝ Y (P w) := by rw [hp]; exact hY
  have hXP := hXat.hasFDerivAt.comp w hP
  have hYP := hYat.hasFDerivAt.comp w hP
  have hWP := ((hW.differentiable (by simp) (P w).re).hasDerivAt.hasFDerivAt.comp (P w)
    Complex.reCLM.hasFDerivAt).comp w hP
  have hprod := hWP.mul hXP
  have hfsmooth : ContDiffAt ℝ ∞ f (P w) := by rw [hp]; exact hf.contDiffAt (hs.mem_nhds hz)
  have hG : ContDiffAt ℝ ∞ (f ∘ P) w := hfsmooth.comp w hPsmooth
  dsimp only
  change Laplacian.laplacian (f ∘ P) w = _
  rw [laplacian_complex_eq_conformalPartial_trace hG, hreal.fderiv_eq, himag.fderiv_eq]
  have hprodD := hprod.fderiv
  change fderiv ℝ (fun q => W (P q).re * X (P q)) w = _ at hprodD
  have hYPD := hYP.fderiv
  change fderiv ℝ (fun q => Y (P q)) w = _ at hYPD
  rw [hprodD, hYPD]
  simp [ContinuousLinearMap.comp_apply, hDreal, hDimag, hp, X, Y]
  rw [show (W z.re : ℂ) = W z.re • (1 : ℂ) by simp, map_smul]
  simp only [smul_eq_mul]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M] [SigmaCompactSpace M] [T2Space M]

local instance conformalLaplacianComplexFinrankNonzero : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by simp [Complex.finrank_real_complex]⟩

/-- **Math.** A literal Euclidean conformal PDE in an original selected
chart yields the actual constant-curvature tensor on every tangent pair.
This is the `W = 1` case, with its Laplacian trace derived above. -/
theorem conformalEuclideanMetric_curvatureOperatorAt_eq_of_laplacian
    (g : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M) (α : M) (f : ℂ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    {z : ℂ} (hz : z ∈ (extChartAt (modelWithCornersSelf ℝ ℂ) α).target)
    (hmetric : ∀ᶠ q in 𝓝 z, ∀ a b,
      chartMetricInner g α q a b = Real.exp (2 * f q) * (a.re * b.re + a.im * b.im))
    (hpde : Laplacian.laplacian f z = Real.exp (2 * f z)) :
    let p := (extChartAt (modelWithCornersSelf ℝ ℂ) α).symm z
    ∀ x y : TangentSpace (modelWithCornersSelf ℝ ℂ) p,
      g.metricInner p x x * g.metricInner p y y - (g.metricInner p x y) ^ 2 =
        g.metricInner p (g.leviCivitaConnection.curvatureOperatorAt p x y y) x := by
  apply conformalWarpMetric_curvatureOperatorAt_eq_of_pde g α f (fun _ => 1)
    hf contDiff_const (fun _ => by norm_num) hz
  · simpa [conformalWarpMetricInner] using hmetric
  · rw [laplacian_complex_eq_conformalPartial_trace
      (hf.contDiffAt ((isOpen_extChartAt_target α).mem_nhds hz))] at hpde
    simpa using hpde

/-- **Math.** Divide the genuine inverse-coordinate trace identity by
the positive warped area coefficient to recover the original-coordinate
PDE used by the actual curvature computation. -/
theorem smoothWarpConformalChart_pde_to_warped_trace
    {W : ℝ → ℝ} (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t)
    {f : ℂ → ℝ} {s : Set ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s)
    {z : ℂ} (hz : z ∈ s)
    (hpde : Laplacian.laplacian
        (f ∘ (smoothWarpConformalChart hW.continuous hpos).symm)
        (smoothWarpConformalChart hW.continuous hpos z) =
      W z.re ^ 2 * (-(deriv (deriv W) z.re / W z.re) + Real.exp (2 * f z))) :
    fderiv ℝ (conformalPartialReal f) z 1 +
        (deriv W z.re / W z.re) * conformalPartialReal f z +
        fderiv ℝ (conformalPartialImag f) z Complex.I / W z.re ^ 2 =
      -(deriv (deriv W) z.re / W z.re) + Real.exp (2 * f z) := by
  rw [smoothWarpConformalChart_laplacian_comp_symm hW hpos hs hf hz] at hpde
  apply (mul_left_cancel₀ (pow_ne_zero 2 (hpos z.re).ne'))
  convert hpde using 1
  field_simp [(hpos z.re).ne']

#print axioms laplacian_complex_eq_conformalPartial_trace
#print axioms smoothWarpConformalChart_laplacian_comp_symm
#print axioms smoothWarpConformalChart_pde_to_warped_trace
#print axioms conformalEuclideanMetric_curvatureOperatorAt_eq_of_laplacian

end

end SystolicGrowth
