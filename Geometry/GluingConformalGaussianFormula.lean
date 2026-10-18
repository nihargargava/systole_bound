module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingConformalCurvatureAndArea
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

/-!
# The actual conformal-coordinate Gaussian formula

The Euclidean Laplacian is the trace of the genuine second Fréchet
derivative. The inverse-warp derivative identifies it with the intrinsic
Gaussian field of the existing smooth metric.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- **Math.** For a function of the literal real coordinate alone, the
Euclidean complex-plane Laplacian is its actual second real derivative. -/
theorem laplacian_complex_re_of_hasDerivAt
    {f f' : ℝ → ℝ} {z : ℂ} {f'' : ℝ}
    (hf : ∀ᶠ t in 𝓝 z.re, HasDerivAt f (f' t) t)
    (hf' : HasDerivAt f' f'' z.re) :
    Laplacian.laplacian (fun w : ℂ => f w.re) z = f'' := by
  have hderiv : fderiv ℝ (fun w : ℂ => f w.re) =ᶠ[𝓝 z]
      fun w => f' w.re • Complex.reCLM := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually hf] with w hw
    exact (hw.comp_hasFDerivAt w Complex.reCLM.hasFDerivAt).fderiv
  have hsecond := (hf'.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt).smul_const Complex.reCLM
  simp only [Function.comp_def] at hsecond
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hderiv.fderiv_eq, hsecond.fderiv]
  simp

/-- **Math.** The analogous trace identity for a function of the literal
imaginary coordinate. -/
theorem laplacian_complex_im_of_hasDerivAt
    {f f' : ℝ → ℝ} {z : ℂ} {f'' : ℝ}
    (hf : ∀ᶠ t in 𝓝 z.im, HasDerivAt f (f' t) t)
    (hf' : HasDerivAt f' f'' z.im) :
    Laplacian.laplacian (fun w : ℂ => f w.im) z = f'' := by
  have hderiv : fderiv ℝ (fun w : ℂ => f w.im) =ᶠ[𝓝 z]
      fun w => f' w.im • Complex.imCLM := by
    filter_upwards [Complex.continuous_im.continuousAt.eventually hf] with w hw
    exact (hw.comp_hasFDerivAt w Complex.imCLM.hasFDerivAt).fderiv
  have hsecond := (hf'.comp_hasFDerivAt z Complex.imCLM.hasFDerivAt).smul_const Complex.imCLM
  simp only [Function.comp_def] at hsecond
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  dsimp only
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hderiv.fderiv_eq, hsecond.fderiv]
  simp

/-- **Math.** The actual logarithm of the radial conformal coefficient has
first derivative `W'` evaluated at the genuine inverse radius. -/
theorem smoothWarpConformalLogFactor_hasDerivAt {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) {s : ℝ}
    (hs : s ∈ (smoothWarpConformalRadialChart hW.continuous hpos).target) :
    HasDerivAt (fun t => Real.log (smoothWarpConformalFactor hW.continuous hpos t))
      (deriv W ((smoothWarpConformalRadialChart hW.continuous hpos).symm s)) s := by
  let T := (smoothWarpConformalRadialChart hW.continuous hpos).symm
  have hT : HasDerivAt T (W (T s)) s :=
    (smoothWarpConformalRadialChart_symm_hasStrictDerivAt hW.continuous hpos hs).hasDerivAt
  have hfirst := ((hW.differentiable (by simp)).differentiableAt.hasDerivAt.comp s hT).log
    (hpos (T s)).ne'
  simpa only [smoothWarpConformalFactor, T, Function.comp_def,
    mul_div_cancel_right₀ _ (hpos (T s)).ne'] using hfirst

/-- **Math.** The genuine Euclidean Laplacian of the seam log factor is
`W''(T(x)) W(T(x))`, including the image of the smoothing boundaries. -/
theorem smoothWarpConformalLogFactor_laplacian {W : ℝ → ℝ}
    (hW : ContDiff ℝ ∞ W) (hpos : ∀ t, 0 < W t) {z : ℂ}
    (hz : z ∈ (smoothWarpConformalChart hW.continuous hpos).target) :
    Laplacian.laplacian
        (fun w : ℂ => Real.log (smoothWarpConformalFactor hW.continuous hpos w.re)) z =
      deriv (deriv W) ((smoothWarpConformalRadialChart hW.continuous hpos).symm z.re) *
        W ((smoothWarpConformalRadialChart hW.continuous hpos).symm z.re) := by
  have hz' : z.re ∈ (smoothWarpConformalRadialChart hW.continuous hpos).target := by
    simpa only [smoothWarpConformalChart_target, mem_setOf_eq] using hz
  let T := (smoothWarpConformalRadialChart hW.continuous hpos).symm
  have hfirst : ∀ᶠ s in 𝓝 z.re,
      HasDerivAt (fun t => Real.log (smoothWarpConformalFactor hW.continuous hpos t))
        (deriv W (T s)) s := by
    filter_upwards [(smoothWarpConformalRadialChart hW.continuous hpos).open_target.mem_nhds hz']
      with s hs
    exact smoothWarpConformalLogFactor_hasDerivAt hW hpos hs
  have hsecond : HasDerivAt (fun s => deriv W (T s))
      (deriv (deriv W) (T z.re) * W (T z.re)) z.re := by
    have hWd : ContDiff ℝ ∞ (deriv W) := hW.deriv'
    have hd : HasDerivAt (deriv W) (deriv (deriv W) (T z.re)) (T z.re) :=
      (hWd.differentiable (by simp)).differentiableAt.hasDerivAt
    exact hd.comp z.re
      (smoothWarpConformalRadialChart_symm_hasStrictDerivAt hW.continuous hpos hz').hasDerivAt
  exact laplacian_complex_re_of_hasDerivAt (z := z)
    (f := fun t => Real.log (smoothWarpConformalFactor hW.continuous hpos t))
    (f' := fun s => deriv W (T s)) hfirst hsecond

/-- **Math.** The true complex-plane Laplacian of the Poincaré log factor
is its positive conformal area coefficient. -/
theorem poincareConformalLogFactor_laplacian {z : ℂ} (hz : 0 < z.im) :
    Laplacian.laplacian (fun w : ℂ => Real.log (w.im⁻¹)) z = z.im⁻¹ ^ 2 := by
  apply laplacian_complex_im_of_hasDerivAt (z := z)
    (f := fun t => Real.log (t⁻¹)) (f' := fun t => -t⁻¹)
  · filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hz] with t ht
    convert! (Real.hasDerivAt_log ht.ne').neg using 1
    ext x
    exact Real.log_inv x
  · convert! (hasDerivAt_inv hz.ne').neg using 1
    simp

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** In an actual isolated smooth seam conformal chart, the
existing intrinsic Gaussian scalar is `-a⁻² Δ log a` for the literal
Euclidean Laplacian and the SAME coefficient appearing in the tensor. -/
theorem gluedCurvatureBoundedGaussian_conformal_seam_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) {z : ℂ}
    (hz : z ∈ (P.gluedCurvatureBoundedSeamConformalChart k θ).target)
    (hother : ∀ l : Fin (n - 1), l ≠ k →
      (P.gluedCurvatureBoundedSeamConformalChart k θ).symm z ∉ P.thinSeamCollar l) :
    P.gluedCurvatureBoundedGaussian ((P.gluedCurvatureBoundedSeamConformalChart k θ).symm z) =
      -(P.gluedCurvatureBoundedSeamConformalFactor z ^ 2)⁻¹ *
        Laplacian.laplacian (fun w => Real.log (P.gluedCurvatureBoundedSeamConformalFactor w)) z := by
  let e := P.seamAngularComplexChart k θ
  let ψ := P.gluedCurvatureBoundedSeamConformalChange
  let W := P.gluedCurvatureBoundedConformalWarp
  let T := (smoothWarpConformalRadialChart
    P.gluedCurvatureBoundedConformalWarp_contDiff.continuous
    P.gluedCurvatureBoundedConformalWarp_pos).symm
  have hz' : ψ.symm z ∈ e.target := hz.2
  have hb : (P.gluedCurvatureBoundedSeamConformalChart k θ).symm z ∈ e.source :=
    e.map_target hz'
  have hcoord : e ((P.gluedCurvatureBoundedSeamConformalChart k θ).symm z) = ψ.symm z :=
    e.right_inv hz'
  have hre : (ψ.symm z).re = T z.re := by
    simp [ψ, T, gluedCurvatureBoundedSeamConformalChange, smoothWarpConformalChart_symm_apply]
  have hfactor : P.gluedCurvatureBoundedSeamConformalFactor z = W (T z.re) := rfl
  have hLap := smoothWarpConformalLogFactor_laplacian
    P.gluedCurvatureBoundedConformalWarp_contDiff P.gluedCurvatureBoundedConformalWarp_pos hz.1
  change Laplacian.laplacian
    (fun w => Real.log (P.gluedCurvatureBoundedSeamConformalFactor w)) z =
      deriv (deriv W) (T z.re) * W (T z.re) at hLap
  rw [P.gluedCurvatureBoundedGaussian_in_isolated_seam_chart k θ _ hb hother]
  change gluedCurvatureBoundedSeamGaussian P
    (e ((P.gluedCurvatureBoundedSeamConformalChart k θ).symm z)) = _
  rw [hcoord]
  have hW : ContDiff ℝ 2 W := P.gluedCurvatureBoundedConformalWarp_contDiff.of_le (by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  change gluingWarpedGaussianCurvature W ((ψ.symm z).re, (ψ.symm z).im) = _
  rw [gluingWarpedGaussianCurvature_eq hW (P.gluedCurvatureBoundedConformalWarp_pos _),
    hre, hfactor, hLap]
  have hnonzero : W (T z.re) ≠ 0 := (P.gluedCurvatureBoundedConformalWarp_pos _).ne'
  field_simp

/-- **Math.** The same intrinsic conformal formula holds on every actual
unchanged interior chart, with its SAME positive coefficient `1 / Im z`. -/
theorem gluedCurvatureBoundedGaussian_conformal_interior_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ e.target)
    (houtside : ∀ k : Fin (n - 1), e.symm z ∉ P.thinSeamCollar k) :
    P.gluedCurvatureBoundedGaussian (e.symm z) =
      -(z.im⁻¹ ^ 2)⁻¹ * Laplacian.laplacian (fun w : ℂ => Real.log (w.im⁻¹)) z := by
  have hpos := P.gluedInteriorComplexChart_target_im_pos e he hz
  rw [P.gluedCurvatureBoundedGaussian_eq_neg_one_of_outside _ houtside,
    poincareConformalLogFactor_laplacian hpos, neg_mul, inv_mul_cancel₀]
  exact pow_ne_zero _ (inv_ne_zero hpos.ne')

#print axioms gluedCurvatureBoundedGaussian_conformal_seam_chart
#print axioms gluedCurvatureBoundedGaussian_conformal_interior_chart

end ExerciseGluingPreparation

#print axioms laplacian_complex_re_of_hasDerivAt
#print axioms laplacian_complex_im_of_hasDerivAt
#print axioms smoothWarpConformalLogFactor_hasDerivAt
#print axioms smoothWarpConformalLogFactor_laplacian
#print axioms poincareConformalLogFactor_laplacian

end

end SystolicGrowth
