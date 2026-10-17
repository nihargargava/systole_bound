module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarConformalCurvature
public import Geometry.GluingCollarModelMetric

@[expose] public section

/-!
# Native collar length in its actual conformal coordinate

The complex conformal coordinate is based on the constructed inverse-warp
primitive. Its ordinary Euclidean speed, weighted by the actual log factor,
equals the original collar speed. Hence original differentiable curves have
exactly the conformal length, not an assumed metric identification.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SystolicGrowth

/-- The genuine conformal coordinate expressed in the Euclidean complex
plane, whose norm is Euclidean rather than the real-product maximum norm. -/
noncomputable def gluingCollarConformalComplexCoordinate (r : ℝ) (z : ℂ) : ℂ :=
  (gluingCollarConformalRadius r z.re : ℂ) + (z.im : ℂ) * Complex.I

@[simp] theorem gluingCollarConformalComplexCoordinate_re (r : ℝ) (z : ℂ) :
    (gluingCollarConformalComplexCoordinate r z).re =
      gluingCollarConformalRadius r z.re := by
  simp [gluingCollarConformalComplexCoordinate]

/-- The genuine conformal collar chart in the Euclidean complex plane.
Both coordinate changes come from proved open partial homeomorphisms. -/
noncomputable def gluingCollarConformalComplexChart {r : ℝ} (hr : 0 < r) :
    OpenPartialHomeomorph ℂ ℂ :=
  (Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph.trans
    (gluingCollarConformalChart hr)).trans
    Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem gluingCollarConformalComplexChart_apply {r : ℝ} (hr : 0 < r) (z : ℂ) :
    gluingCollarConformalComplexChart hr z = gluingCollarConformalComplexCoordinate r z := by
  simp [gluingCollarConformalComplexChart, gluingCollarConformalComplexCoordinate,
    Complex.equivRealProdCLM_symm_apply]

@[simp] theorem gluingCollarConformalComplexChart_source {r : ℝ} (hr : 0 < r) :
    (gluingCollarConformalComplexChart hr).source = univ := by
  simp [gluingCollarConformalComplexChart]

/-- **Math.** The chart is a genuine open embedding of the unchanged model
plane; its inverse is available on its actual open target, not postulated. -/
theorem gluingCollarConformalComplexCoordinate_isOpenEmbedding {r : ℝ} (hr : 0 < r) :
    Topology.IsOpenEmbedding (gluingCollarConformalComplexCoordinate r) := by
  have heq : (gluingCollarConformalComplexChart hr : ℂ → ℂ) =
      gluingCollarConformalComplexCoordinate r := funext (gluingCollarConformalComplexChart_apply hr)
  rw [← heq]
  exact (gluingCollarConformalComplexChart hr).to_isOpenEmbedding
    (gluingCollarConformalComplexChart_source hr)

/-- The actual coordinate velocity of an original collar tangent vector. -/
noncomputable def gluingCollarConformalComplexVelocity (r : ℝ) (z v : ℂ) : ℂ :=
  ((v.re / gluingCollarWarp r z.re : ℝ) : ℂ) + (v.im : ℂ) * Complex.I

/-- **Math.** The constructed conformal coordinate has the stated velocity
along every genuine differentiable native coordinate curve. -/
theorem gluingCollarConformalComplexCoordinate_comp_hasDerivAt
    {r : ℝ} (hr : 0 < r) {α : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hα : HasDerivAt α v t) :
    HasDerivAt (gluingCollarConformalComplexCoordinate r ∘ α)
      (gluingCollarConformalComplexVelocity r (α t) v) t := by
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hα
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hα
  have hRad := (gluingCollarConformalRadius_hasStrictDerivAt hr (α t).re).hasDerivAt.comp t hRe
  have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hRad).add
    ((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hIm).mul_const Complex.I)
  convert h using 1
  all_goals first
    | rfl
    | simp [gluingCollarConformalComplexVelocity, div_eq_mul_inv, mul_comm]

/-- **Math.** At every original collar point, including the seam, the
native tangent speed is exactly the conformally weighted Euclidean speed. -/
theorem gluingCollarConformalComplexVelocity_speed {r : ℝ} (hr : 0 < r) (z v : ℂ) :
    Real.sqrt (gluingComplexCollarTangentForm r z v v) =
      Real.exp (gluingCollarConformalLogFactor hr (gluingCollarConformalRadius r z.re)) *
        ‖gluingCollarConformalComplexVelocity r z v‖ := by
  have hexp : Real.exp (gluingCollarConformalLogFactor hr
      (gluingCollarConformalRadius r z.re)) = gluingCollarWarp r z.re := by
    rw [gluingCollarConformalLogFactor, gluingCollarConformalRadialChart_left_inv,
      Real.exp_log (gluingCollarWarp_pos hr z.re)]
  rw [hexp]
  have hsq : (gluingCollarWarp r z.re * ‖gluingCollarConformalComplexVelocity r z v‖) ^ 2 =
      gluingComplexCollarTangentForm r z v v := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply,
      gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self]
    simp only [gluingCollarConformalComplexVelocity, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one]
    field_simp [(gluingCollarWarp_pos hr z.re).ne']
    ring
  rw [← hsq, Real.sqrt_sq (mul_nonneg (gluingCollarWarp_pos hr z.re).le (norm_nonneg _))]

/-- **Math.** Exact conformal length of every actual differentiable native
curve. The original length functional and the original curve are retained. -/
theorem gluingCollarModelPathELength_eq_conformal {r : ℝ} (hr : 0 < r)
    {α : ℝ → ℂ} (hα : Differentiable ℝ α) (a b : ℝ) :
    gluingCollarModelPathELength hr α a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.exp (gluingCollarConformalLogFactor hr
            (gluingCollarConformalRadius r (α t).re)) *
          ‖deriv (gluingCollarConformalComplexCoordinate r ∘ α) t‖) := by
  rw [gluingCollarModelPathELength_eq_lintegral]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  rw [(gluingCollarConformalComplexCoordinate_comp_hasDerivAt hr (hα t).hasDerivAt).deriv,
    gluingCollarConformalComplexVelocity_speed hr]

#print axioms gluingCollarConformalComplexCoordinate_comp_hasDerivAt
#print axioms gluingCollarConformalComplexCoordinate_isOpenEmbedding
#print axioms gluingCollarConformalComplexVelocity_speed
#print axioms gluingCollarModelPathELength_eq_conformal

end SystolicGrowth
