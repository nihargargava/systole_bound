module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Geometry.GluingCayleyMetric
public import Geometry.GluingCollarFinWarp
public import Vendored.RiemannDynamics.Hyperbolic.PlaneGeometry.Geodesics.Interpolation

@[expose] public section

/-!
# Fermi coordinates for the finite-curvature fin model

The scaled Fermi map realizes the hyperbolic cylinder model in the upper
half-plane. Its metric pullback and the fin-convexity theorem are separate
obligations; this file starts by constructing the map and proving it is
injective when its scale is positive.
-/

open UpperHalfPlane
open Filter
open scoped UpperHalfPlane ComplexConjugate

namespace SystolicGrowth

/-- The same Fermi map with its upper-half-plane point viewed as a complex
coordinate, so its real differential can be calculated explicitly. -/
noncomputable def gluingFinFermiLift (α : ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.ofReal (Real.exp (α * p.1) * Real.tanh (α * p.2)) +
    Complex.ofReal (Real.exp (α * p.1) / Real.cosh (α * p.2)) * Complex.I

@[simp] theorem gluingFinFermiLift_re (α : ℝ) (p : ℝ × ℝ) :
    (gluingFinFermiLift α p).re = Real.exp (α * p.1) * Real.tanh (α * p.2) := by
  simp only [gluingFinFermiLift, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero]

@[simp] theorem gluingFinFermiLift_im (α : ℝ) (p : ℝ × ℝ) :
    (gluingFinFermiLift α p).im = Real.exp (α * p.1) / Real.cosh (α * p.2) := by
  simp only [gluingFinFermiLift, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, zero_add, add_zero]

/-- A point in the curvature `-λ²` Fermi cylinder, represented in the
curvature `-1` upper half-plane. -/
noncomputable def gluingFinFermiPoint (α t u : ℝ) : ℍ :=
  ⟨gluingFinFermiLift α (t, u), by
    rw [gluingFinFermiLift_im]
    exact div_pos (Real.exp_pos _) (Real.cosh_pos _)⟩

@[simp] theorem gluingFinFermiPoint_re (α t u : ℝ) :
    (gluingFinFermiPoint α t u).re = Real.exp (α * t) * Real.tanh (α * u) := by
  change (gluingFinFermiLift α (t, u)).re = _
  exact gluingFinFermiLift_re α (t, u)

@[simp] theorem gluingFinFermiPoint_im (α t u : ℝ) :
    (gluingFinFermiPoint α t u).im = Real.exp (α * t) / Real.cosh (α * u) := by
  change (gluingFinFermiLift α (t, u)).im = _
  exact gluingFinFermiLift_im α (t, u)

/-- The exact hyperbolic distance formula in scaled Fermi coordinates.  The
radial coordinate measures displacement along the core geodesic, while the
transverse coordinate contributes the `cosh` factors. -/
theorem gluingFinFermiPoint_cosh_dist (α t₁ u₁ t₂ u₂ : ℝ) :
    Real.cosh (dist (gluingFinFermiPoint α t₁ u₁)
      (gluingFinFermiPoint α t₂ u₂)) =
      Real.cosh (α * u₁) * Real.cosh (α * u₂) *
        Real.cosh (α * (t₁ - t₂)) -
          Real.sinh (α * u₁) * Real.sinh (α * u₂) := by
  rw [UpperHalfPlane.cosh_dist']
  simp only [gluingFinFermiPoint_re, gluingFinFermiPoint_im]
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
  have hc₁ : Real.cosh (α * u₁) ≠ 0 := (Real.cosh_pos _).ne'
  have hc₂ : Real.cosh (α * u₂) ≠ 0 := (Real.cosh_pos _).ne'
  have he₁ : Real.exp (α * t₁) ≠ 0 := (Real.exp_pos _).ne'
  have he₂ : Real.exp (α * t₂) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hc₁, hc₂, he₁, he₂]
  rw [show α * (t₁ - t₂) = α * t₁ - α * t₂ by ring, Real.cosh_sub]
  have htime : Real.exp (α * t₁) ^ 2 + Real.exp (α * t₂) ^ 2 =
      2 * Real.exp (α * t₁) * Real.exp (α * t₂) *
        Real.cosh (α * t₁ - α * t₂) := by
    rw [Real.cosh_eq,
      show -(α * t₁ - α * t₂) = α * t₂ - α * t₁ by ring,
      Real.exp_sub, Real.exp_sub]
    field_simp [he₁, he₂]
  have hsq₁ : Real.sinh (α * u₁) ^ 2 + 1 = Real.cosh (α * u₁) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (α * u₁)]
  have hsq₂ : Real.sinh (α * u₂) ^ 2 + 1 = Real.cosh (α * u₂) ^ 2 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq (α * u₂)]
  have hleft :
      (Real.exp (α * t₁) * Real.sinh (α * u₁) * Real.cosh (α * u₂) -
          Real.cosh (α * u₁) * Real.exp (α * t₂) * Real.sinh (α * u₂)) ^ 2 +
        Real.exp (α * t₁) ^ 2 * Real.cosh (α * u₂) ^ 2 +
        Real.cosh (α * u₁) ^ 2 * Real.exp (α * t₂) ^ 2 =
      Real.cosh (α * u₁) ^ 2 * Real.cosh (α * u₂) ^ 2 *
          (Real.exp (α * t₁) ^ 2 + Real.exp (α * t₂) ^ 2) -
        2 * Real.exp (α * t₁) * Real.exp (α * t₂) * Real.cosh (α * u₁) *
          Real.cosh (α * u₂) * Real.sinh (α * u₁) * Real.sinh (α * u₂) := by
    calc
      _ = Real.exp (α * t₁) ^ 2 * Real.cosh (α * u₂) ^ 2 *
            (Real.sinh (α * u₁) ^ 2 + 1) +
          Real.exp (α * t₂) ^ 2 * Real.cosh (α * u₁) ^ 2 *
            (Real.sinh (α * u₂) ^ 2 + 1) -
          2 * Real.exp (α * t₁) * Real.exp (α * t₂) * Real.cosh (α * u₁) *
            Real.cosh (α * u₂) * Real.sinh (α * u₁) * Real.sinh (α * u₂) := by ring
      _ = _ := by rw [hsq₁, hsq₂]; ring
  calc
    _ = Real.cosh (α * u₁) ^ 2 * Real.cosh (α * u₂) ^ 2 *
          (2 * Real.exp (α * t₁) * Real.exp (α * t₂) *
            (Real.cosh (α * t₁) * Real.cosh (α * t₂) -
              Real.sinh (α * t₁) * Real.sinh (α * t₂))) -
        2 * Real.exp (α * t₁) * Real.exp (α * t₂) * Real.cosh (α * u₁) *
          Real.cosh (α * u₂) * Real.sinh (α * u₁) * Real.sinh (α * u₂) := by
      rw [hleft, htime, Real.cosh_sub]
    _ = _ := by ring

/-- With transverse coordinate fixed, moving radially closer to a second
point's radial coordinate strictly decreases the hyperbolic `cosh`-distance.
This quantitative monotonicity can help rule out artificial radial-cap
minimizers when the cross-pair endpoints lie strictly inside the chosen
window. -/
theorem gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt
    {α s t₁ t₂ u v : ℝ} (hα : 0 < α)
    (hcloser : |t₂ - s| < |t₁ - s|) :
    Real.cosh (dist (gluingFinFermiPoint α t₂ u)
      (gluingFinFermiPoint α s v)) <
    Real.cosh (dist (gluingFinFermiPoint α t₁ u)
      (gluingFinFermiPoint α s v)) := by
  rw [gluingFinFermiPoint_cosh_dist, gluingFinFermiPoint_cosh_dist]
  have harg : |α * (t₂ - s)| < |α * (t₁ - s)| := by
    rw [abs_mul, abs_mul, abs_of_pos hα]
    exact mul_lt_mul_of_pos_left hcloser hα
  have hcosh := Real.cosh_lt_cosh.mpr harg
  have hcoef : 0 < Real.cosh (α * u) * Real.cosh (α * v) :=
    mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hdiff : 0 < Real.cosh (α * (t₁ - s)) -
      Real.cosh (α * (t₂ - s)) := sub_pos.mpr hcosh
  have hmul := mul_pos hcoef hdiff
  nlinarith

/-- In particular, with transverse coordinate fixed, moving radially farther
away on one side of the second point strictly increases `cosh`-distance. -/
theorem gluingFinFermiPoint_cosh_dist_strictMono_radial
    {α s t₁ t₂ u v : ℝ} (hα : 0 < α) (hst : s < t₁) (ht : t₁ < t₂) :
    Real.cosh (dist (gluingFinFermiPoint α t₁ u)
      (gluingFinFermiPoint α s v)) <
    Real.cosh (dist (gluingFinFermiPoint α t₂ u)
      (gluingFinFermiPoint α s v)) := by
  apply gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt hα
  rw [abs_of_pos (by linarith : 0 < t₁ - s),
    abs_of_pos (by linarith : 0 < t₂ - s)]
  nlinarith

/-- The explicit real differential of the scaled Fermi map. -/
noncomputable def gluingFinFermiLiftFDeriv (α : ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      ((α * Real.exp (α * p.1) * Real.tanh (α * p.2) : ℝ) +
        Complex.I * (α * Real.exp (α * p.1) / Real.cosh (α * p.2) : ℝ)) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      ((Real.exp (α * p.1) * α / Real.cosh (α * p.2) ^ 2 : ℝ) +
        Complex.I * (-α * Real.exp (α * p.1) * Real.sinh (α * p.2) /
          Real.cosh (α * p.2) ^ 2 : ℝ))

/-- The Fermi map's exact differential on an arbitrary tangent vector. -/
theorem gluingFinFermiLiftFDeriv_apply (α : ℝ) (p v : ℝ × ℝ) :
    gluingFinFermiLiftFDeriv α p v =
      ((α * Real.exp (α * p.1) * Real.tanh (α * p.2) : ℝ) +
          Complex.I * (α * Real.exp (α * p.1) / Real.cosh (α * p.2) : ℝ)) *
          (v.1 : ℂ) +
        ((Real.exp (α * p.1) * α / Real.cosh (α * p.2) ^ 2 : ℝ) +
          Complex.I * (-α * Real.exp (α * p.1) * Real.sinh (α * p.2) /
            Real.cosh (α * p.2) ^ 2 : ℝ)) * (v.2 : ℂ) := by
  simp only [gluingFinFermiLiftFDeriv, add_apply,
    ContinuousLinearMap.smulRight_apply, Complex.real_smul]
  change (v.1 : ℂ) * _ + (v.2 : ℂ) * _ = _
  ring

private theorem gluingFinFermiTanh_hasDerivAt (α u : ℝ) :
  HasDerivAt (fun x : ℝ => Real.tanh (α * x))
      (α / Real.cosh (α * u) ^ 2) u := by
  have hx : HasDerivAt (fun x : ℝ => α * x) α u :=
    by simpa using (hasDerivAt_id u).const_mul α
  have h := hx.sinh.div hx.cosh (Real.cosh_pos (α * u)).ne'
  have hcoeff :
      (Real.cosh (α * u) * α * Real.cosh (α * u) -
        Real.sinh (α * u) * (Real.sinh (α * u) * α)) /
          Real.cosh (α * u) ^ 2 = α / Real.cosh (α * u) ^ 2 := by
    calc
      _ = α * (Real.cosh (α * u) ^ 2 - Real.sinh (α * u) ^ 2) /
          Real.cosh (α * u) ^ 2 := by ring
      _ = α / Real.cosh (α * u) ^ 2 := by
        rw [Real.cosh_sq_sub_sinh_sq]
        ring
  rw [hcoeff] at h
  simpa only [Real.tanh_eq_sinh_div_cosh, Pi.div_apply] using! h

private theorem gluingFinFermiSech_hasDerivAt (α u : ℝ) :
  HasDerivAt (fun x : ℝ => 1 / Real.cosh (α * x))
      (-α * Real.sinh (α * u) / Real.cosh (α * u) ^ 2) u := by
  have hx : HasDerivAt (fun x : ℝ => α * x) α u :=
    by simpa using (hasDerivAt_id u).const_mul α
  have h := (hasDerivAt_const u (1 : ℝ)).div hx.cosh
    (Real.cosh_pos (α * u)).ne'
  have hcoeff :
      (0 * Real.cosh (α * u) - 1 * (Real.sinh (α * u) * α)) /
          Real.cosh (α * u) ^ 2 =
        -α * Real.sinh (α * u) / Real.cosh (α * u) ^ 2 := by ring
  rw [hcoeff] at h
  exact h

/-- The complex Fermi coordinate has its ordinary differential given by the
two coordinate derivatives in the radial and transverse directions. -/
theorem gluingFinFermiLift_hasFDerivAt (α : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (gluingFinFermiLift α) (gluingFinFermiLiftFDeriv α p) p := by
  let dExp : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (α * Real.exp (α * p.1))
  let dTanh : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (α / Real.cosh (α * p.2) ^ 2)
  let dSech : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (-α * Real.sinh (α * p.2) / Real.cosh (α * p.2) ^ 2)
  have hExp1 : HasDerivAt (fun x : ℝ => Real.exp (α * x))
      (α * Real.exp (α * p.1)) p.1 := by
    have hArg : HasDerivAt (fun x : ℝ => α * x) α p.1 := by
      simpa [mul_comm] using (hasDerivAt_id p.1).const_mul α
    convert (Real.hasDerivAt_exp (α * p.1)).comp p.1 hArg using 1 <;>
      first | rfl | ring
  have hExp := hExp1.comp_hasFDerivAt p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hTanh := (gluingFinFermiTanh_hasDerivAt α p.2).comp_hasFDerivAt p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hSech := (gluingFinFermiSech_hasDerivAt α p.2).comp_hasFDerivAt p
    (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hExp' : HasFDerivAt (fun q : ℝ × ℝ => Real.exp (α * q.1)) dExp p := by
    exact hExp.congr_fderiv (g' := dExp) (by
      apply ContinuousLinearMap.ext
      intro v
      simp [dExp, ContinuousLinearMap.smulRight_apply]
      ring)
  have hTanh' : HasFDerivAt (fun q : ℝ × ℝ => Real.tanh (α * q.2)) dTanh p := by
    exact hTanh.congr_fderiv (g' := dTanh) (by
      apply ContinuousLinearMap.ext
      intro v
      simp [dTanh, ContinuousLinearMap.smulRight_apply]
      ring)
  have hSech' : HasFDerivAt (fun q : ℝ × ℝ => 1 / Real.cosh (α * q.2)) dSech p := by
    exact hSech.congr_fderiv (g' := dSech) (by
      apply ContinuousLinearMap.ext
      intro v
      simp [dSech, ContinuousLinearMap.smulRight_apply]
      ring)
  let dRe : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (α * Real.exp (α * p.1) * Real.tanh (α * p.2)) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (Real.exp (α * p.1) * α / Real.cosh (α * p.2) ^ 2)
  let dIm : (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
        (α * Real.exp (α * p.1) / Real.cosh (α * p.2)) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (-α * Real.exp (α * p.1) * Real.sinh (α * p.2) /
          Real.cosh (α * p.2) ^ 2)
  have hRe : HasFDerivAt (fun q : ℝ × ℝ =>
      Real.exp (α * q.1) * Real.tanh (α * q.2)) dRe p := by
    have h := hExp'.mul hTanh'
    exact h.congr_fderiv (g' := dRe) (by
      apply ContinuousLinearMap.ext
      intro v
      simp [dRe, dExp, dTanh, ContinuousLinearMap.smulRight_apply]
      ring)
  have hIm : HasFDerivAt (fun q : ℝ × ℝ =>
      Real.exp (α * q.1) * (1 / Real.cosh (α * q.2))) dIm p := by
    have h := hExp'.mul hSech'
    exact h.congr_fderiv (g' := dIm) (by
      apply ContinuousLinearMap.ext
      intro v
      simp [dIm, dExp, dSech, ContinuousLinearMap.smulRight_apply]
      ring)
  have hReC := (Complex.ofRealCLM.hasFDerivAt).comp p hRe
  have hImC := ((Complex.ofRealCLM.hasFDerivAt).comp p hIm).mul_const Complex.I
  have h := hReC.add hImC
  have hEq : gluingFinFermiLift α =
      ((⇑Complex.ofRealCLM ∘ fun q : ℝ × ℝ =>
        Real.exp (α * q.1) * Real.tanh (α * q.2)) +
        fun q : ℝ × ℝ =>
          (⇑Complex.ofRealCLM ∘ fun q : ℝ × ℝ =>
            Real.exp (α * q.1) * (1 / Real.cosh (α * q.2))) q * Complex.I) := by
    funext q
    change gluingFinFermiLift α q =
      Complex.ofReal (Real.exp (α * q.1) * Real.tanh (α * q.2)) +
        Complex.ofReal (Real.exp (α * q.1) * (1 / Real.cosh (α * q.2))) * Complex.I
    simp [gluingFinFermiLift]
    rfl
  have hLift := h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hEq)
  exact hLift.congr_fderiv (g' := gluingFinFermiLiftFDeriv α p) (by
    apply ContinuousLinearMap.ext
    intro v
    simp [gluingFinFermiLiftFDeriv, dRe, dIm,
      ContinuousLinearMap.smulRight_apply, Complex.real_smul]
    ring)

private theorem gluingFinFermiComplexVector_re (a b c d x y : ℝ) :
    (((a : ℂ) + Complex.I * b) * x + ((c : ℂ) + Complex.I * d) * y).re =
      a * x + c * y := by
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero]

private theorem gluingFinFermiComplexVector_im (a b c d x y : ℝ) :
    (((a : ℂ) + Complex.I * b) * x + ((c : ℂ) + Complex.I * d) * y).im =
      b * x + d * y := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add]
  ring

private theorem gluingFinFermi_mul_conj_re (z w : ℂ) :
    (z * conj w).re = z.re * w.re + z.im * w.im := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The scaled Fermi coordinates pull the Poincaré metric back to the
curvature `-α²` cylinder metric. This is the exact ambient-model metric
identity needed by the finite-fins argument. -/
theorem gluingFinFermiLift_fderiv_tangentForm_pullback
    (α : ℝ) (p v w : ℝ × ℝ) :
    gluingHalfPlaneTangentForm (gluingFinFermiPoint α p.1 p.2)
        (fderiv ℝ (gluingFinFermiLift α) p v)
        (fderiv ℝ (gluingFinFermiLift α) p w) =
      α ^ 2 * (Real.cosh (α * p.2) ^ 2 * v.1 * w.1 + v.2 * w.2) := by
  rw [(gluingFinFermiLift_hasFDerivAt α p).fderiv]
  have hc : Real.cosh (α * p.2) ≠ 0 := (Real.cosh_pos _).ne'
  have he : Real.exp (α * p.1) ≠ 0 := (Real.exp_pos _).ne'
  have hFrame (x y : ℝ) :
      (gluingFinFermiLiftFDeriv α p (x, y)).re =
          α * Real.exp (α * p.1) * Real.tanh (α * p.2) * x +
            (Real.exp (α * p.1) * α / Real.cosh (α * p.2) ^ 2) * y ∧
      (gluingFinFermiLiftFDeriv α p (x, y)).im =
          (α * Real.exp (α * p.1) / Real.cosh (α * p.2)) * x +
            (-α * Real.exp (α * p.1) * Real.sinh (α * p.2) /
              Real.cosh (α * p.2) ^ 2) * y := by
    constructor
    · rw [gluingFinFermiLiftFDeriv_apply]
      exact gluingFinFermiComplexVector_re _ _ _ _ _ _
    · rw [gluingFinFermiLiftFDeriv_apply]
      exact gluingFinFermiComplexVector_im _ _ _ _ _ _
  have hv := hFrame v.1 v.2
  have hw := hFrame w.1 w.2
  rw [gluingHalfPlaneTangentForm, gluingFinFermiPoint_im]
  rw [gluingFinFermi_mul_conj_re]
  have hvRe : (gluingFinFermiLiftFDeriv α p v).re =
      α * Real.exp (α * p.1) * Real.tanh (α * p.2) * v.1 +
        Real.exp (α * p.1) * α / Real.cosh (α * p.2) ^ 2 * v.2 := by
    simpa only [Prod.eta] using hv.1
  have hvIm : (gluingFinFermiLiftFDeriv α p v).im =
      α * Real.exp (α * p.1) / Real.cosh (α * p.2) * v.1 +
        -α * Real.exp (α * p.1) * Real.sinh (α * p.2) /
          Real.cosh (α * p.2) ^ 2 * v.2 := by
    simpa only [Prod.eta] using hv.2
  have hwRe : (gluingFinFermiLiftFDeriv α p w).re =
      α * Real.exp (α * p.1) * Real.tanh (α * p.2) * w.1 +
        Real.exp (α * p.1) * α / Real.cosh (α * p.2) ^ 2 * w.2 := by
    simpa only [Prod.eta] using hw.1
  have hwIm : (gluingFinFermiLiftFDeriv α p w).im =
      α * Real.exp (α * p.1) / Real.cosh (α * p.2) * w.1 +
        -α * Real.exp (α * p.1) * Real.sinh (α * p.2) /
          Real.cosh (α * p.2) ^ 2 * w.2 := by
    simpa only [Prod.eta] using hw.2
  rw [hvRe, hvIm, hwRe, hwIm]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp [hc, he]
  have hcs := Real.cosh_sq_sub_sinh_sq (α * p.2)
  linear_combination -(α ^ 2 * Real.cosh (α * p.2) ^ 2 * v.1 * w.1) * hcs -
    (α ^ 2 * v.2 * w.2) * hcs

/-- The pointwise Poincare speed of the scaled Fermi differential is exactly
the scale `|α|` times its cylinder speed. This is the local identity needed
to compare ambient fin path costs with hyperbolic length. -/
theorem gluingFinFermiLift_fderiv_speed
    (α : ℝ) (p v : ℝ × ℝ) :
    ‖fderiv ℝ (gluingFinFermiLift α) p v‖ /
        (gluingFinFermiPoint α p.1 p.2).im =
      |α| * Real.sqrt (Real.cosh (α * p.2) ^ 2 * v.1 ^ 2 + v.2 ^ 2) := by
  let w := fderiv ℝ (gluingFinFermiLift α) p v
  have hpull := gluingFinFermiLift_fderiv_tangentForm_pullback α p v v
  have hform : gluingHalfPlaneTangentForm (gluingFinFermiPoint α p.1 p.2)
      w w = ‖w‖ ^ 2 / (gluingFinFermiPoint α p.1 p.2).im ^ 2 := by
    simp only [gluingHalfPlaneTangentForm, Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  rw [hform] at hpull
  have him : 0 < (gluingFinFermiPoint α p.1 p.2).im :=
    (gluingFinFermiPoint α p.1 p.2).im_pos
  have hq : 0 ≤ Real.cosh (α * p.2) ^ 2 * v.1 ^ 2 + v.2 ^ 2 := by
    positivity
  have hmul : ‖w‖ ^ 2 = (gluingFinFermiPoint α p.1 p.2).im ^ 2 *
      (α ^ 2 * (Real.cosh (α * p.2) ^ 2 * v.1 ^ 2 + v.2 ^ 2)) := by
    have hh := (div_eq_iff (pow_ne_zero 2 him.ne')).mp hpull
    nlinarith [hh]
  have hsq :
      (‖w‖ / (gluingFinFermiPoint α p.1 p.2).im) ^ 2 =
        (|α| * Real.sqrt (Real.cosh (α * p.2) ^ 2 * v.1 ^ 2 + v.2 ^ 2)) ^ 2 := by
    rw [div_pow, mul_pow, sq_abs, Real.sq_sqrt hq]
    field_simp [(gluingFinFermiPoint α p.1 p.2).im_pos.ne']
    nlinarith [hmul]
  have hleft : 0 ≤ ‖w‖ / (gluingFinFermiPoint α p.1 p.2).im :=
    div_nonneg (norm_nonneg _) him.le
  have hright : 0 ≤ |α| * Real.sqrt
      (Real.cosh (α * p.2) ^ 2 * v.1 ^ 2 + v.2 ^ 2) := by positivity
  nlinarith

/-- The ratio of the real and imaginary coordinates recovers `sinh (λu)`;
this separates the transverse Fermi coordinate from the dilation along the
central geodesic. -/
theorem gluingFinFermiPoint_re_div_im (α t u : ℝ) :
    (gluingFinFermiPoint α t u).re / (gluingFinFermiPoint α t u).im =
      Real.sinh (α * u) := by
  rw [gluingFinFermiPoint_re, gluingFinFermiPoint_im, Real.tanh_eq_sinh_div_cosh]
  have he : Real.exp (α * t) ≠ 0 := (Real.exp_pos _).ne'
  have hc : Real.cosh (α * u) ≠ 0 := (Real.cosh_pos _).ne'
  field_simp

/-- Recover the transverse Fermi coordinate from a point of the upper
half-plane. The positive scale hypothesis is needed only for division. -/
noncomputable def gluingFinFermiTransverseCoord (α : ℝ) (z : ℍ) : ℝ :=
  Real.arsinh (z.re / z.im) / α

/-- Recover the radial Fermi coordinate from the logarithmic modulus in the
upper half-plane. -/
noncomputable def gluingFinFermiRadialCoord (α : ℝ) (z : ℍ) : ℝ :=
  Real.log ‖(z : ℂ)‖ / α

/-- The inverse transverse coordinate recovers `u` on the scaled Fermi map. -/
theorem gluingFinFermiTransverseCoord_point {α t u : ℝ} (hα : 0 < α) :
    gluingFinFermiTransverseCoord α (gluingFinFermiPoint α t u) = u := by
  rw [gluingFinFermiTransverseCoord, gluingFinFermiPoint_re_div_im,
    Real.arsinh_sinh]
  field_simp [hα.ne']

/-- The hyperbolic tangent of the transverse Fermi coordinate is the real
coordinate divided by the Euclidean norm. -/
theorem gluingFinFermiTransverseCoord_tanh {α : ℝ} (hα : 0 < α) (z : ℍ) :
    Real.tanh (α * gluingFinFermiTransverseCoord α z) =
      z.re / ‖(z : ℂ)‖ := by
  unfold gluingFinFermiTransverseCoord
  have hscale : α * (Real.arsinh (z.re / z.im) / α) =
      Real.arsinh (z.re / z.im) := by
    field_simp
  rw [hscale, Real.tanh_arsinh]
  have hsqrt : Real.sqrt (1 + (z.re / z.im) ^ 2) =
      ‖(z : ℂ)‖ / z.im := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    field_simp [z.im_ne_zero]
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  rw [hsqrt]
  field_simp [z.im_ne_zero, norm_pos_iff.mpr z.ne_zero]

/-- On a Euclidean circle centered on the real axis, the transverse Fermi
coordinate's hyperbolic tangent is an explicit function of radial norm. -/
theorem gluingFinFermiCircle_tanh_eq_radius_formula {α c ρ : ℝ}
    (hα : 0 < α) (hc : c ≠ 0) (z : ℍ)
    (hcircle : (z.re - c) ^ 2 + z.im ^ 2 = ρ ^ 2) :
    Real.tanh (α * gluingFinFermiTransverseCoord α z) =
      (‖(z : ℂ)‖ + (c ^ 2 - ρ ^ 2) / ‖(z : ℂ)‖) / (2 * c) := by
  rw [gluingFinFermiTransverseCoord_tanh hα z]
  have hnormSq : ‖(z : ℂ)‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hbalance : ‖(z : ℂ)‖ ^ 2 + c ^ 2 - ρ ^ 2 = 2 * c * z.re := by
    rw [hnormSq]
    nlinarith [hcircle]
  have hn : ‖(z : ℂ)‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr z.ne_zero)
  field_simp [hc, hn]
  nlinarith [hbalance]

/-- Reparameterizing the circle formula by radial Fermi coordinate gives a
two-exponential expression, whose second derivative is immediate. -/
theorem gluingFinFermiCircle_tanh_eq_exp_formula {α c ρ : ℝ}
    (hα : 0 < α) (hc : c ≠ 0) (z : ℍ)
    (hcircle : (z.re - c) ^ 2 + z.im ^ 2 = ρ ^ 2) :
    Real.tanh (α * gluingFinFermiTransverseCoord α z) =
      (Real.exp (α * gluingFinFermiRadialCoord α z) +
        (c ^ 2 - ρ ^ 2) * Real.exp (-(α * gluingFinFermiRadialCoord α z))) /
        (2 * c) := by
  have hnorm : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hexp : Real.exp (α * gluingFinFermiRadialCoord α z) = ‖(z : ℂ)‖ := by
    rw [gluingFinFermiRadialCoord]
    have harg : α * (Real.log ‖(z : ℂ)‖ / α) = Real.log ‖(z : ℂ)‖ := by
      field_simp [hα.ne']
    rw [harg, Real.exp_log hnorm]
  rw [gluingFinFermiCircle_tanh_eq_radius_formula hα hc z hcircle,
    Real.exp_neg, hexp]
  field_simp [hc, hnorm.ne']

/-- The radial-parameter expression for the transverse hyperbolic tangent on
a circle geodesic. -/
noncomputable def gluingFinFermiCircleTanhGraph (α c ρ t : ℝ) : ℝ :=
  (Real.exp (α * t) + (c ^ 2 - ρ ^ 2) * Real.exp (-α * t)) / (2 * c)

/-- Its explicit first derivative. -/
noncomputable def gluingFinFermiCircleTanhGraphDeriv
    (α c ρ t : ℝ) : ℝ :=
  (α * Real.exp (α * t) - α * (c ^ 2 - ρ ^ 2) * Real.exp (-α * t)) /
    (2 * c)

/-- The transverse coordinate of the circle geodesic, expressed as a graph over its
radial Fermi coordinate. -/
noncomputable def gluingFinFermiCircleTransverseGraph
    (α c ρ t : ℝ) : ℝ :=
  Real.artanh (gluingFinFermiCircleTanhGraph α c ρ t) / α

/-- The slope of the transverse graph over the radial coordinate. -/
noncomputable def gluingFinFermiCircleTransverseGraphSlope
    (α c ρ t : ℝ) : ℝ :=
  gluingFinFermiCircleTanhGraphDeriv α c ρ t /
    (α * (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2))

private theorem gluingFinFermiArtanh_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 1) :
    HasDerivAt Real.artanh (1 / (1 - x ^ 2)) x := by
  have hplus : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
    simpa using (hasDerivAt_id x).const_add 1
  have hminus : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub 1
  have hminus_ne : 1 - x ≠ 0 := ne_of_gt (by linarith [hx.2])
  have hratio := hplus.div hminus hminus_ne
  have hratio_pos : 0 < (1 + x) / (1 - x) :=
    div_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hlog := hratio.log (ne_of_gt hratio_pos)
  have hformula : Real.artanh =ᶠ[nhds x]
      (fun y : ℝ => 1 / 2 * Real.log ((1 + y) / (1 - y))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [Real.artanh_eq_half_log ⟨hy.1.le, hy.2.le⟩]
  have h := hlog.const_mul (1 / 2)
  have h' := h.congr_of_eventuallyEq hformula
  have hplus_ne : 1 + x ≠ 0 := ne_of_gt (by linarith [hx.1])
  have hsq_ne : 1 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
  have hcoeff : 1 / (1 - x ^ 2) =
      1 / 2 * ((1 * (1 - x) - (1 + x) * (-1)) / (1 - x) ^ 2 /
        ((1 + x) / (1 - x))) := by
    field_simp [hminus_ne, hplus_ne, hsq_ne]
    ring
  exact h'.congr_deriv hcoeff.symm

private theorem gluingFinFermiExpLinear_hasDerivAt (a t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (a * s))
      (a * Real.exp (a * t)) t := by
  have harg : HasDerivAt (fun s : ℝ => a * s) a t := by
    simpa [mul_comm] using (hasDerivAt_id t).const_mul a
  convert (Real.hasDerivAt_exp (a * t)).comp t harg using 1 <;>
    first | rfl | ring

/-- The second-derivative term in the graph equation for a geodesic in the
scaled Fermi metric `du² + cosh(αu)² dt²`. -/
noncomputable def gluingFinFermiGraphAcceleration (α u p : ℝ) : ℝ :=
  α * Real.cosh (α * u) * Real.sinh (α * u) +
    2 * α * p ^ 2 * Real.tanh (α * u)

/-- The transverse Fermi coordinate of a vertical upper-half-plane geodesic,
written as a graph over its radial coordinate. -/
noncomputable def gluingFinFermiVerticalTanhGraph
    (α x t : ℝ) : ℝ := x * Real.exp (-α * t)

/-- The derivative of the vertical geodesic's rational-tanh graph. -/
noncomputable def gluingFinFermiVerticalTanhGraphDeriv
    (α x t : ℝ) : ℝ := -α * x * Real.exp (-α * t)

/-- The vertical geodesic's transverse graph in scaled Fermi coordinates. -/
noncomputable def gluingFinFermiVerticalTransverseGraph
    (α x t : ℝ) : ℝ :=
  Real.artanh (gluingFinFermiVerticalTanhGraph α x t) / α

/-- The vertical geodesic's slope with respect to radial Fermi coordinate. -/
noncomputable def gluingFinFermiVerticalTransverseGraphSlope
    (α x t : ℝ) : ℝ :=
  gluingFinFermiVerticalTanhGraphDeriv α x t /
    (α * (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2))

theorem gluingFinFermiVerticalTanhGraph_hasDerivAt {α x t : ℝ} :
    HasDerivAt (gluingFinFermiVerticalTanhGraph α x)
      (gluingFinFermiVerticalTanhGraphDeriv α x t) t := by
  have he := gluingFinFermiExpLinear_hasDerivAt (-α) t
  have h := he.const_mul x
  have hgraph : gluingFinFermiVerticalTanhGraph α x =ᶠ[nhds t]
      (fun s : ℝ => x * Real.exp (-α * s)) := by
    filter_upwards [] with s
    rfl
  have hcoeff : x * (-α * Real.exp (-α * t)) =
      gluingFinFermiVerticalTanhGraphDeriv α x t := by
    dsimp [gluingFinFermiVerticalTanhGraphDeriv]
    ring
  exact h.congr_of_eventuallyEq hgraph |>.congr_deriv hcoeff

theorem gluingFinFermiVerticalTanhGraphDeriv_hasDerivAt {α x t : ℝ} :
    HasDerivAt (gluingFinFermiVerticalTanhGraphDeriv α x)
      (α ^ 2 * gluingFinFermiVerticalTanhGraph α x t) t := by
  have he := gluingFinFermiExpLinear_hasDerivAt (-α) t
  have h := he.const_mul (-α * x)
  have hgraph : gluingFinFermiVerticalTanhGraphDeriv α x =ᶠ[nhds t]
      (fun s : ℝ => (-α * x) * Real.exp (-α * s)) := by
    filter_upwards [] with s
    rfl
  have hcoeff : (-α * x) * (-α * Real.exp (-α * t)) =
      α ^ 2 * gluingFinFermiVerticalTanhGraph α x t := by
    dsimp [gluingFinFermiVerticalTanhGraph]
    ring
  exact h.congr_of_eventuallyEq hgraph |>.congr_deriv hcoeff

theorem gluingFinFermiVerticalTransverseGraph_hasDerivAt
    {α x t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiVerticalTanhGraph α x t ∈ Set.Ioo (-1) 1) :
    HasDerivAt (gluingFinFermiVerticalTransverseGraph α x)
      (gluingFinFermiVerticalTanhGraphDeriv α x t /
        (α * (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2))) t := by
  have hq' := gluingFinFermiVerticalTanhGraph_hasDerivAt (α := α) (x := x)
    (t := t)
  have hArt := (gluingFinFermiArtanh_hasDerivAt hq).comp t hq'
  have h := hArt.div_const α
  have hden : 1 - gluingFinFermiVerticalTanhGraph α x t ^ 2 ≠ 0 := by
    have hleft := hq.1
    have hright := hq.2
    nlinarith
  have hcoeff :
      (1 / (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2) *
        gluingFinFermiVerticalTanhGraphDeriv α x t) / α =
      gluingFinFermiVerticalTanhGraphDeriv α x t /
        (α * (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2)) := by
    field_simp [hα, hden]
  exact h.congr_deriv hcoeff

theorem gluingFinFermiVerticalTransverseGraphSlope_hasDerivAt
    {α x t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiVerticalTanhGraph α x t ∈ Set.Ioo (-1) 1) :
    HasDerivAt (gluingFinFermiVerticalTransverseGraphSlope α x)
      (α * gluingFinFermiVerticalTanhGraph α x t /
          (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2) +
        2 * α * gluingFinFermiVerticalTanhGraph α x t *
          gluingFinFermiVerticalTransverseGraphSlope α x t ^ 2) t := by
  let q : ℝ → ℝ := gluingFinFermiVerticalTanhGraph α x
  let q' : ℝ → ℝ := gluingFinFermiVerticalTanhGraphDeriv α x
  have hqfun := gluingFinFermiVerticalTanhGraph_hasDerivAt
    (α := α) (x := x) (t := t)
  have hqderiv := gluingFinFermiVerticalTanhGraphDeriv_hasDerivAt
    (α := α) (x := x) (t := t)
  have hqfun' : HasDerivAt q (q' t) t := by simpa [q, q'] using hqfun
  have hqderiv' : HasDerivAt q' (α ^ 2 * q t) t := by
    simpa [q, q'] using hqderiv
  have hsq_ne : 1 - q t ^ 2 ≠ 0 := by
    have hleft := hq.1
    have hright := hq.2
    dsimp [q]
    nlinarith
  have hden_ne : α * (1 - q t ^ 2) ≠ 0 := mul_ne_zero hα hsq_ne
  have hsq := hqfun'.mul hqfun'
  have hden0 := (hsq.const_sub (1 : ℝ)).const_mul α
  have hdenEv : (fun y : ℝ => α * (1 - (q * q) y)) =ᶠ[nhds t]
      (fun s : ℝ => α * (1 - q s ^ 2)) :=
    Filter.Eventually.of_forall fun s => by simp [pow_two]
  have hden : HasDerivAt (fun s : ℝ => α * (1 - q s ^ 2))
      (-(2 * α * q t * q' t)) t := by
    have hdenCoeff : α * -(q' t * q t + q t * q' t) =
        -(2 * α * q t * q' t) := by ring
    exact hden0.congr_of_eventuallyEq hdenEv.symm |>.congr_deriv hdenCoeff
  have hquot := hqderiv'.div hden hden_ne
  have hquotEv : (q' / fun s : ℝ => α * (1 - q s ^ 2)) =ᶠ[nhds t]
      (fun s : ℝ => q' s / (α * (1 - q s ^ 2))) :=
    Filter.Eventually.of_forall fun s => rfl
  have hquot' : HasDerivAt
      (fun s : ℝ => q' s / (α * (1 - q s ^ 2)))
      ((α ^ 2 * q t * (α * (1 - q t ^ 2)) -
        q' t * (-(2 * α * q t * q' t))) /
        (α * (1 - q t ^ 2)) ^ 2) t := by
    exact hquot.congr_of_eventuallyEq hquotEv |>.congr_deriv rfl
  have hcoeff :
      (α ^ 2 * q t * (α * (1 - q t ^ 2)) -
        q' t * (-(2 * α * q t * q' t))) /
        (α * (1 - q t ^ 2)) ^ 2 =
      α * q t / (1 - q t ^ 2) +
        2 * α * q t * (q' t / (α * (1 - q t ^ 2))) ^ 2 := by
    field_simp [hα, hsq_ne]
    ring
  have hquot'' := hquot'.congr_deriv hcoeff
  change HasDerivAt
    (fun s => q' s / (α * (1 - q s ^ 2))) _ t
  exact hquot''

theorem gluingFinFermiVerticalTransverseGraphSlope_acceleration
    {α x t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiVerticalTanhGraph α x t ∈ Set.Ioo (-1) 1) :
    HasDerivAt (gluingFinFermiVerticalTransverseGraphSlope α x)
      (gluingFinFermiGraphAcceleration α
        (gluingFinFermiVerticalTransverseGraph α x t)
        (gluingFinFermiVerticalTransverseGraphSlope α x t)) t := by
  have hderiv := gluingFinFermiVerticalTransverseGraphSlope_hasDerivAt hα hq
  have hαt : α * gluingFinFermiVerticalTransverseGraph α x t =
      Real.artanh (gluingFinFermiVerticalTanhGraph α x t) := by
    dsimp [gluingFinFermiVerticalTransverseGraph]
    field_simp [hα]
  have hcoshsinh :
      Real.cosh (Real.artanh (gluingFinFermiVerticalTanhGraph α x t)) *
        Real.sinh (Real.artanh (gluingFinFermiVerticalTanhGraph α x t)) =
      gluingFinFermiVerticalTanhGraph α x t /
        (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2) := by
    rw [Real.cosh_artanh hq, Real.sinh_artanh hq]
    have hpos : 0 < 1 - gluingFinFermiVerticalTanhGraph α x t ^ 2 := by
      have hleft := hq.1
      have hright := hq.2
      nlinarith
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hpos.le]
    simp
  have htanh := Real.tanh_artanh hq
  have hcoeff :
      α * gluingFinFermiVerticalTanhGraph α x t /
          (1 - gluingFinFermiVerticalTanhGraph α x t ^ 2) +
        2 * α * gluingFinFermiVerticalTanhGraph α x t *
          gluingFinFermiVerticalTransverseGraphSlope α x t ^ 2 =
      gluingFinFermiGraphAcceleration α
        (gluingFinFermiVerticalTransverseGraph α x t)
        (gluingFinFermiVerticalTransverseGraphSlope α x t) := by
    rw [gluingFinFermiGraphAcceleration, hαt]
    rw [mul_assoc (α : ℝ)
      (Real.cosh (Real.artanh (gluingFinFermiVerticalTanhGraph α x t)))
      (Real.sinh (Real.artanh (gluingFinFermiVerticalTanhGraph α x t)))]
    rw [hcoshsinh, htanh]
    ring
  exact hderiv.congr_deriv hcoeff

theorem gluingFinFermiVerticalTransverseGraph_second_derivative
    {α x t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiVerticalTanhGraph α x t ∈ Set.Ioo (-1) 1) :
    deriv (deriv (gluingFinFermiVerticalTransverseGraph α x)) t =
      gluingFinFermiGraphAcceleration α
        (gluingFinFermiVerticalTransverseGraph α x t)
        (gluingFinFermiVerticalTransverseGraphSlope α x t) := by
  have hqcont : ContinuousAt (gluingFinFermiVerticalTanhGraph α x) t :=
    (gluingFinFermiVerticalTanhGraph_hasDerivAt (α := α) (x := x)
      (t := t)).continuousAt
  have hqevent : ∀ᶠ s in nhds t,
      gluingFinFermiVerticalTanhGraph α x s ∈ Set.Ioo (-1) 1 :=
    hqcont.eventually (isOpen_Ioo.mem_nhds hq)
  have hderivEq :
      deriv (gluingFinFermiVerticalTransverseGraph α x) =ᶠ[nhds t]
        gluingFinFermiVerticalTransverseGraphSlope α x := by
    filter_upwards [hqevent] with s hqs
    exact (gluingFinFermiVerticalTransverseGraph_hasDerivAt (t := s)
      hα hqs).deriv
  have hacc := gluingFinFermiVerticalTransverseGraphSlope_acceleration hα hq
  exact hacc.congr_of_eventuallyEq hderivEq |>.deriv

/-- The vertical graph's rational-tanh coordinate at the radial coordinate of
a point is exactly its real coordinate divided by its Euclidean norm. -/
theorem gluingFinFermiVerticalTanhGraph_eq_coord
    {α x : ℝ} (hα : 0 < α) (z : ℍ) (hre : z.re = x) :
    gluingFinFermiVerticalTanhGraph α x
        (gluingFinFermiRadialCoord α z) =
      Real.tanh (α * gluingFinFermiTransverseCoord α z) := by
  have hnorm : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hexp :
      Real.exp (α * gluingFinFermiRadialCoord α z) = ‖(z : ℂ)‖ := by
    rw [gluingFinFermiRadialCoord]
    have harg : α * (Real.log ‖(z : ℂ)‖ / α) = Real.log ‖(z : ℂ)‖ := by
      field_simp [hα.ne']
    rw [harg, Real.exp_log hnorm]
  have hq : gluingFinFermiVerticalTanhGraph α x
        (gluingFinFermiRadialCoord α z) =
      Real.tanh (α * gluingFinFermiTransverseCoord α z) := by
    change x * Real.exp (-α * gluingFinFermiRadialCoord α z) = _
    calc
      _ = x * Real.exp (-(α * gluingFinFermiRadialCoord α z)) := by
        have harg : -α * gluingFinFermiRadialCoord α z =
            -(α * gluingFinFermiRadialCoord α z) := by ring
        rw [harg]
      _ = x / Real.exp (α * gluingFinFermiRadialCoord α z) := by
        rw [Real.exp_neg]
        rw [div_eq_mul_inv]
      _ = z.re / ‖(z : ℂ)‖ := by rw [hre, hexp]
      _ = _ := gluingFinFermiTransverseCoord_tanh hα z |>.symm
  exact hq

/-- The explicit vertical graph agrees with the actual transverse Fermi
coordinate at every point on the vertical line with real coordinate `x`. -/
theorem gluingFinFermiVerticalTransverseGraph_eq_coord
    {α x : ℝ} (hα : 0 < α) (z : ℍ) (hre : z.re = x) :
    gluingFinFermiVerticalTransverseGraph α x
        (gluingFinFermiRadialCoord α z) =
      gluingFinFermiTransverseCoord α z := by
  have hq := gluingFinFermiVerticalTanhGraph_eq_coord hα z hre
  calc
    gluingFinFermiVerticalTransverseGraph α x
        (gluingFinFermiRadialCoord α z) =
      Real.artanh (gluingFinFermiVerticalTanhGraph α x
        (gluingFinFermiRadialCoord α z)) / α := rfl
    _ = Real.artanh (Real.tanh
        (α * gluingFinFermiTransverseCoord α z)) / α := by rw [hq]
    _ = gluingFinFermiTransverseCoord α z := by
      rw [Real.artanh_tanh]
      field_simp [hα.ne']

/-- The circle transverse-tangent graph has the displayed derivative. -/
theorem gluingFinFermiCircleTanhGraph_hasDerivAt {α c ρ : ℝ}
    (t : ℝ) :
    HasDerivAt (gluingFinFermiCircleTanhGraph α c ρ)
      (gluingFinFermiCircleTanhGraphDeriv α c ρ t) t := by
  have hpos := gluingFinFermiExpLinear_hasDerivAt α t
  have hneg := gluingFinFermiExpLinear_hasDerivAt (-α) t
  have hgraph : gluingFinFermiCircleTanhGraph α c ρ =
      (fun x : ℝ =>
        ((fun y : ℝ => Real.exp (α * y)) +
          (fun y => (c ^ 2 - ρ ^ 2) * Real.exp (-α * y))) x / (2 * c)) := by
    funext x
    rfl
  have hderiv : gluingFinFermiCircleTanhGraphDeriv α c ρ t =
      (α * Real.exp (α * t) +
        (c ^ 2 - ρ ^ 2) * (-α * Real.exp (-α * t))) / (2 * c) := by
    simp [gluingFinFermiCircleTanhGraphDeriv]
    ring
  have hev : gluingFinFermiCircleTanhGraph α c ρ =ᶠ[nhds t]
      (fun x : ℝ => ((fun y : ℝ => Real.exp (α * y)) +
        (fun y => (c ^ 2 - ρ ^ 2) * Real.exp (-α * y))) x / (2 * c)) :=
    Filter.Eventually.of_forall fun x => congrFun hgraph x
  exact ((hpos.add (hneg.const_mul (c ^ 2 - ρ ^ 2))).div_const (2 * c))
    |>.congr_of_eventuallyEq hev |>.congr_deriv hderiv.symm

/-- The first derivative itself has derivative `α²` times the graph. -/
theorem gluingFinFermiCircleTanhGraphDeriv_hasDerivAt {α c ρ : ℝ}
    (t : ℝ) :
    HasDerivAt (gluingFinFermiCircleTanhGraphDeriv α c ρ)
      (α ^ 2 * gluingFinFermiCircleTanhGraph α c ρ t) t := by
  have hpos := (gluingFinFermiExpLinear_hasDerivAt α t).const_mul α
  have hneg := (gluingFinFermiExpLinear_hasDerivAt (-α) t).const_mul
    (-(α * (c ^ 2 - ρ ^ 2)))
  have hgraph : gluingFinFermiCircleTanhGraphDeriv α c ρ =
      (fun x : ℝ =>
        ((fun y : ℝ => α * Real.exp (α * y)) +
          (fun y => -(α * (c ^ 2 - ρ ^ 2)) * Real.exp (-α * y))) x /
          (2 * c)) := by
    funext x
    dsimp [gluingFinFermiCircleTanhGraphDeriv]
    ring
  have hderiv : α ^ 2 * gluingFinFermiCircleTanhGraph α c ρ t =
      (α * (α * Real.exp (α * t)) +
        -(α * (c ^ 2 - ρ ^ 2)) * (-α * Real.exp (-α * t))) /
          (2 * c) := by
    simp [gluingFinFermiCircleTanhGraph]
    ring
  have hev : gluingFinFermiCircleTanhGraphDeriv α c ρ =ᶠ[nhds t]
      (fun x => ((fun y : ℝ => α * Real.exp (α * y)) +
        (fun y => -(α * (c ^ 2 - ρ ^ 2)) * Real.exp (-α * y))) x / (2 * c)) :=
    Filter.Eventually.of_forall fun x => congrFun hgraph x
  exact ((hpos.add hneg).div_const (2 * c)).congr_of_eventuallyEq hev
    |>.congr_deriv hderiv.symm

/-- Differentiate the circle graph's transverse Fermi coordinate wherever the circle lies
strictly inside the range of `tanh`. -/
theorem gluingFinFermiCircleTransverseGraph_hasDerivAt
    {α c ρ t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1) :
    HasDerivAt (gluingFinFermiCircleTransverseGraph α c ρ)
      (gluingFinFermiCircleTanhGraphDeriv α c ρ t /
        (α * (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2))) t := by
  have hq' := gluingFinFermiCircleTanhGraph_hasDerivAt (α := α) (c := c)
    (ρ := ρ) t
  have hArt := (gluingFinFermiArtanh_hasDerivAt hq).comp t hq'
  have h := hArt.div_const α
  have hden : 1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2 ≠ 0 := by
    have hleft := hq.1
    have hright := hq.2
    nlinarith
  have hcoeff :
      (1 / (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2) *
        gluingFinFermiCircleTanhGraphDeriv α c ρ t) / α =
      gluingFinFermiCircleTanhGraphDeriv α c ρ t /
        (α * (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2)) := by
    field_simp [hα, hden]
  exact h.congr_deriv hcoeff

/-- Differentiate the transverse graph slope. This is the rational-tanh form of
the Fermi-coordinate geodesic acceleration equation. -/
theorem gluingFinFermiCircleTransverseGraphSlope_hasDerivAt
    {α c ρ t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1) :
    HasDerivAt (gluingFinFermiCircleTransverseGraphSlope α c ρ)
      (α * gluingFinFermiCircleTanhGraph α c ρ t /
          (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2) +
        2 * α * gluingFinFermiCircleTanhGraph α c ρ t *
          gluingFinFermiCircleTransverseGraphSlope α c ρ t ^ 2) t := by
  let q : ℝ → ℝ := gluingFinFermiCircleTanhGraph α c ρ
  let q' : ℝ → ℝ := gluingFinFermiCircleTanhGraphDeriv α c ρ
  have hqfun := gluingFinFermiCircleTanhGraph_hasDerivAt
    (α := α) (c := c) (ρ := ρ) t
  have hqderiv := gluingFinFermiCircleTanhGraphDeriv_hasDerivAt (α := α)
    (c := c) (ρ := ρ) t
  have hqfun' : HasDerivAt q (q' t) t := by
    simpa [q, q'] using hqfun
  have hqderiv' : HasDerivAt q' (α ^ 2 * q t) t := by
    simpa [q, q'] using hqderiv
  have hsq_ne : 1 - q t ^ 2 ≠ 0 := by
    have hleft := hq.1
    have hright := hq.2
    dsimp [q]
    nlinarith
  have hden_ne : α * (1 - q t ^ 2) ≠ 0 := mul_ne_zero hα hsq_ne
  have hsq := hqfun'.mul hqfun'
  have hden0 := (hsq.const_sub (1 : ℝ)).const_mul α
  have hdenEv : (fun y : ℝ => α * (1 - (q * q) y)) =ᶠ[nhds t]
      (fun s : ℝ => α * (1 - q s ^ 2)) :=
    Filter.Eventually.of_forall fun s => by simp [pow_two]
  have hden : HasDerivAt (fun s : ℝ => α * (1 - q s ^ 2))
      (-(2 * α * q t * q' t)) t := by
    have hdenCoeff : α * -(q' t * q t + q t * q' t) =
        -(2 * α * q t * q' t) := by ring
    exact hden0.congr_of_eventuallyEq hdenEv.symm |>.congr_deriv hdenCoeff
  have hquot := hqderiv'.div hden hden_ne
  have hquotEv : (q' / fun s : ℝ => α * (1 - q s ^ 2)) =ᶠ[nhds t]
      (fun s : ℝ => q' s / (α * (1 - q s ^ 2))) :=
    Filter.Eventually.of_forall fun s => rfl
  have hquot' : HasDerivAt
      (fun s : ℝ => q' s / (α * (1 - q s ^ 2)))
      ((α ^ 2 * q t * (α * (1 - q t ^ 2)) -
        q' t * (-(2 * α * q t * q' t))) /
        (α * (1 - q t ^ 2)) ^ 2) t := by
    exact hquot.congr_of_eventuallyEq hquotEv |>.congr_deriv rfl
  have hcoeff :
      (α ^ 2 * q t * (α * (1 - q t ^ 2)) -
        q' t * (-(2 * α * q t * q' t))) /
        (α * (1 - q t ^ 2)) ^ 2 =
      α * q t / (1 - q t ^ 2) +
        2 * α * q t * (q' t / (α * (1 - q t ^ 2))) ^ 2 := by
    field_simp [hα, hsq_ne]
    ring
  have hquot'' := hquot'.congr_deriv hcoeff
  change HasDerivAt
    (fun s : ℝ => q' s / (α * (1 - q s ^ 2))) _ t
  exact hquot''

/-- The complex norm of the Fermi image depends only on its radial coordinate. -/
theorem gluingFinFermiPoint_norm (α t u : ℝ) :
    ‖(gluingFinFermiPoint α t u : ℂ)‖ = Real.exp (α * t) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    gluingFinFermiPoint_re, gluingFinFermiPoint_im]
  have hcosh : Real.cosh (α * u) ≠ 0 := (Real.cosh_pos _).ne'
  have hid : Real.tanh (α * u) ^ 2 +
      (1 / Real.cosh (α * u)) ^ 2 = 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq (α * u)]
  have hsquare : Real.exp (α * t) * Real.tanh (α * u) *
      (Real.exp (α * t) * Real.tanh (α * u)) +
      (Real.exp (α * t) / Real.cosh (α * u)) *
        (Real.exp (α * t) / Real.cosh (α * u)) = Real.exp (α * t) ^ 2 := by
    calc
      _ = Real.exp (α * t) ^ 2 *
          (Real.tanh (α * u) ^ 2 + (1 / Real.cosh (α * u)) ^ 2) := by
            field_simp [hcosh]
      _ = _ := by rw [hid, mul_one]
  rw [hsquare]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The radial inverse coordinate recovers `t` on the scaled Fermi map. -/
theorem gluingFinFermiRadialCoord_point {α t u : ℝ} (hα : 0 < α) :
    gluingFinFermiRadialCoord α (gluingFinFermiPoint α t u) = t := by
  rw [gluingFinFermiRadialCoord, gluingFinFermiPoint_norm, Real.log_exp]
  field_simp [hα.ne']

/-- The Euclidean squared norm of a semicircle point, expanded in its center
and angular coordinate. -/
theorem gluingFinFermiCircPoint_normSq (c r u : ℝ) (hr : 0 < r) :
    Complex.normSq
        (Vendored.RiemannDynamics.circPoint c r u hr : ℍ) =
      c ^ 2 + r ^ 2 + 2 * c * r * Real.cos
        (Vendored.RiemannDynamics.circAngle u) := by
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im,
    Vendored.RiemannDynamics.circPoint_re, Vendored.RiemannDynamics.circPoint_im]
  nlinarith [Real.sin_sq_add_cos_sq (Vendored.RiemannDynamics.circAngle u)]

/-- Moving forward along a semicircle centered to the right of the imaginary
axis decreases the logarithmic radial coordinate. -/
theorem gluingFinFermiRadialCoord_circPoint_antitone {α c r : ℝ}
    (hα : 0 < α) (hc : 0 ≤ c) (hr : 0 < r) :
    Antitone (fun u : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.circPoint c r u hr)) := by
  intro u v huv
  have hθ : Vendored.RiemannDynamics.circAngle u ≤
      Vendored.RiemannDynamics.circAngle v :=
    Vendored.RiemannDynamics.circAngle_mono huv
  have huθ : Vendored.RiemannDynamics.circAngle u ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (Vendored.RiemannDynamics.circAngle_mem u).1,
      le_of_lt (Vendored.RiemannDynamics.circAngle_mem u).2⟩
  have hvθ : Vendored.RiemannDynamics.circAngle v ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (Vendored.RiemannDynamics.circAngle_mem v).1,
      le_of_lt (Vendored.RiemannDynamics.circAngle_mem v).2⟩
  have hcos := Real.antitoneOn_cos huθ hvθ hθ
  have hnormSq : Complex.normSq
      (Vendored.RiemannDynamics.circPoint c r v hr : ℂ) ≤
      Complex.normSq
        (Vendored.RiemannDynamics.circPoint c r u hr : ℂ) := by
    rw [gluingFinFermiCircPoint_normSq c r v hr,
      gluingFinFermiCircPoint_normSq c r u hr]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc) hr.le)
      (sub_nonneg.mpr hcos)]
  have hnorm : ‖(Vendored.RiemannDynamics.circPoint c r v hr : ℂ)‖ ≤
      ‖(Vendored.RiemannDynamics.circPoint c r u hr : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    exact Real.sqrt_le_sqrt hnormSq
  have hpos : 0 < ‖(Vendored.RiemannDynamics.circPoint c r v hr : ℂ)‖ :=
    norm_pos_iff.mpr (Vendored.RiemannDynamics.circPoint c r v hr).ne_zero
  have hlog := Real.log_le_log hpos hnorm
  exact div_le_div_of_nonneg_right hlog hα.le

/-- Moving forward along a semicircle centered to the left of the imaginary
axis increases the logarithmic radial coordinate. -/
theorem gluingFinFermiRadialCoord_circPoint_monotone {α c r : ℝ}
    (hα : 0 < α) (hc : c ≤ 0) (hr : 0 < r) :
    Monotone (fun u : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.circPoint c r u hr)) := by
  intro u v huv
  have hθ : Vendored.RiemannDynamics.circAngle u ≤
      Vendored.RiemannDynamics.circAngle v :=
    Vendored.RiemannDynamics.circAngle_mono huv
  have huθ : Vendored.RiemannDynamics.circAngle u ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (Vendored.RiemannDynamics.circAngle_mem u).1,
      le_of_lt (Vendored.RiemannDynamics.circAngle_mem u).2⟩
  have hvθ : Vendored.RiemannDynamics.circAngle v ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt (Vendored.RiemannDynamics.circAngle_mem v).1,
      le_of_lt (Vendored.RiemannDynamics.circAngle_mem v).2⟩
  have hcos := Real.antitoneOn_cos huθ hvθ hθ
  have hnormSq : Complex.normSq
      (Vendored.RiemannDynamics.circPoint c r u hr : ℂ) ≤
      Complex.normSq
        (Vendored.RiemannDynamics.circPoint c r v hr : ℂ) := by
    rw [gluingFinFermiCircPoint_normSq c r u hr,
      gluingFinFermiCircPoint_normSq c r v hr]
    have hcoef : 2 * c * r ≤ 0 := by nlinarith [hc, hr]
    have hterm := mul_nonpos_of_nonpos_of_nonneg hcoef
      (sub_nonneg.mpr hcos)
    nlinarith
  have hnorm : ‖(Vendored.RiemannDynamics.circPoint c r u hr : ℂ)‖ ≤
      ‖(Vendored.RiemannDynamics.circPoint c r v hr : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    exact Real.sqrt_le_sqrt hnormSq
  have hpos : 0 < ‖(Vendored.RiemannDynamics.circPoint c r u hr : ℂ)‖ :=
    norm_pos_iff.mpr (Vendored.RiemannDynamics.circPoint c r u hr).ne_zero
  have hlog := Real.log_le_log hpos hnorm
  exact div_le_div_of_nonneg_right hlog hα.le

/-- At fixed real part, increasing the imaginary part increases the logarithmic
radial coordinate. -/
theorem gluingFinFermiRadialCoord_mono_of_im {α : ℝ} (hα : 0 < α)
    {z w : ℍ} (hre : z.re = w.re) (him : z.im ≤ w.im) :
    gluingFinFermiRadialCoord α z ≤ gluingFinFermiRadialCoord α w := by
  have hnormSq : Complex.normSq (z : ℂ) ≤ Complex.normSq (w : ℂ) := by
    rw [Complex.normSq_apply, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hre]
    nlinarith [mul_nonneg (sub_nonneg.mpr him)
      (by positivity : 0 ≤ w.im + z.im)]
  have hnorm : ‖(z : ℂ)‖ ≤ ‖(w : ℂ)‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    exact Real.sqrt_le_sqrt hnormSq
  have hpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hlog := Real.log_le_log hpos hnorm
  exact div_le_div_of_nonneg_right hlog hα.le

/-- Radial height varies monotonically along every vertical hyperbolic
geodesic interpolation. -/
theorem gluingFinFermiRadialCoord_geodInterp_vertical_mono_or_anti
    {α : ℝ} (hα : 0 < α) (a b : ℍ) (hre : a.re = b.re) :
    Monotone (fun t : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b t)) ∨
    Antitone (fun t : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b t)) := by
  let la := Real.log a.im
  let lb := Real.log b.im
  have himag (t : ℝ) :
      (Vendored.RiemannDynamics.geodInterp a b t).im =
        Real.exp ((1 - t) * la + t * lb) := by
    rw [Vendored.RiemannDynamics.geodInterp_vertical hre]
    rfl
  have hreal (t : ℝ) :
      (Vendored.RiemannDynamics.geodInterp a b t).re = a.re := by
    rw [Vendored.RiemannDynamics.geodInterp_vertical hre]
    rfl
  rcases le_total la lb with hab | hba
  · left
    intro s t hst
    have hparam : (1 - s) * la + s * lb ≤ (1 - t) * la + t * lb := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hab)]
    have him : (Vendored.RiemannDynamics.geodInterp a b s).im ≤
        (Vendored.RiemannDynamics.geodInterp a b t).im := by
      rw [himag s, himag t]
      exact Real.exp_le_exp.mpr hparam
    exact gluingFinFermiRadialCoord_mono_of_im hα
      ((hreal s).trans (hreal t).symm) him
  · right
    intro s t hst
    have hparam : (1 - t) * la + t * lb ≤ (1 - s) * la + s * lb := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr hba)]
    have him : (Vendored.RiemannDynamics.geodInterp a b t).im ≤
        (Vendored.RiemannDynamics.geodInterp a b s).im := by
      rw [himag t, himag s]
      exact Real.exp_le_exp.mpr hparam
    exact gluingFinFermiRadialCoord_mono_of_im hα
      ((hreal t).trans (hreal s).symm) him

/-- The radial coordinate varies monotonically, in one direction or the other,
along every semicircular hyperbolic geodesic interpolation. -/
theorem gluingFinFermiRadialCoord_geodInterp_circle_mono_or_anti
    {α : ℝ} (hα : 0 < α) (a b : ℍ) (hne : a.re ≠ b.re) :
    Monotone (fun t : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b t)) ∨
    Antitone (fun t : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b t)) := by
  let c := Vendored.RiemannDynamics.geodCenter a b
  let r := Vendored.RiemannDynamics.geodRadius a b
  let u₀ := Vendored.RiemannDynamics.circCoord c a
  let u₁ := Vendored.RiemannDynamics.circCoord c b
  have hr : 0 < r := Vendored.RiemannDynamics.geodRadius_pos a b
  have hform (t : ℝ) :
      gluingFinFermiRadialCoord α (Vendored.RiemannDynamics.geodInterp a b t) =
        gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.circPoint c r ((1 - t) * u₀ + t * u₁) hr) := by
    rw [Vendored.RiemannDynamics.geodInterp_circle (by simpa using hne)]
  rcases le_total u₀ u₁ with h₀₁ | h₁₀
  · have hparam : Monotone (fun t : ℝ => (1 - t) * u₀ + t * u₁) := by
      intro s t hst
      dsimp
      nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr h₀₁)]
    rcases le_total 0 c with hc | hc
    · right
      intro s t hst
      calc
        _ = gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - t) * u₀ + t * u₁) hr) := hform t
        _ ≤ gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - s) * u₀ + s * u₁) hr) :=
              gluingFinFermiRadialCoord_circPoint_antitone hα hc hr (hparam hst)
        _ = _ := (hform s).symm
    · left
      intro s t hst
      calc
        _ = gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - s) * u₀ + s * u₁) hr) := hform s
        _ ≤ gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - t) * u₀ + t * u₁) hr) :=
              gluingFinFermiRadialCoord_circPoint_monotone hα hc hr (hparam hst)
        _ = _ := (hform t).symm
  · have hparam : Antitone (fun t : ℝ => (1 - t) * u₀ + t * u₁) := by
      intro s t hst
      dsimp
      nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr h₁₀)]
    rcases le_total 0 c with hc | hc
    · left
      intro s t hst
      calc
        _ = gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - s) * u₀ + s * u₁) hr) := hform s
        _ ≤ gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - t) * u₀ + t * u₁) hr) :=
              (gluingFinFermiRadialCoord_circPoint_antitone hα hc hr) (hparam hst)
        _ = _ := (hform t).symm
    · right
      intro s t hst
      calc
        _ = gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - t) * u₀ + t * u₁) hr) := hform t
        _ ≤ gluingFinFermiRadialCoord α
            (Vendored.RiemannDynamics.circPoint c r ((1 - s) * u₀ + s * u₁) hr) :=
              (gluingFinFermiRadialCoord_circPoint_monotone hα hc hr) (hparam hst)
        _ = _ := (hform s).symm

/-- The radial Fermi coordinate is monotone in one of the two orientations
along every hyperbolic geodesic interpolation in the upper half-plane. -/
theorem gluingFinFermiRadialCoord_geodInterp_mono_or_anti
    {α : ℝ} (hα : 0 < α) (a b : ℍ) :
    Monotone (fun t : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b t)) ∨
    Antitone (fun t : ℝ => gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b t)) := by
  by_cases hre : a.re = b.re
  · exact gluingFinFermiRadialCoord_geodInterp_vertical_mono_or_anti hα a b hre
  · exact gluingFinFermiRadialCoord_geodInterp_circle_mono_or_anti hα a b hre

/-- Positive-scale Fermi coordinates are injective. -/
theorem gluingFinFermiPoint_injective {α : ℝ} (hα : 0 < α) :
    Function.Injective (fun p : ℝ × ℝ => gluingFinFermiPoint α p.1 p.2) := by
  intro p q hpq
  change gluingFinFermiPoint α p.1 p.2 =
    gluingFinFermiPoint α q.1 q.2 at hpq
  have hratio :
      (gluingFinFermiPoint α p.1 p.2).re /
          (gluingFinFermiPoint α p.1 p.2).im =
        (gluingFinFermiPoint α q.1 q.2).re /
          (gluingFinFermiPoint α q.1 q.2).im := by
    exact congrArg (fun z : ℍ => z.re / z.im) hpq
  have hsinh : Real.sinh (α * p.2) = Real.sinh (α * q.2) := by
    rw [← gluingFinFermiPoint_re_div_im α p.1 p.2,
      ← gluingFinFermiPoint_re_div_im α q.1 q.2]
    exact hratio
  have hu_mul : α * p.2 = α * q.2 := Real.sinh_injective hsinh
  have hu : p.2 = q.2 := mul_left_cancel₀ hα.ne' hu_mul
  have him := congrArg UpperHalfPlane.im hpq
  rw [gluingFinFermiPoint_im, gluingFinFermiPoint_im, hu] at him
  have hexp : Real.exp (α * p.1) = Real.exp (α * q.1) := by
    have hc : Real.cosh (α * q.2) ≠ 0 := (Real.cosh_pos _).ne'
    field_simp [hc] at him
    exact him
  have ht_mul : α * p.1 = α * q.1 := Real.exp_injective hexp
  have ht : p.1 = q.1 := mul_left_cancel₀ hα.ne' ht_mul
  exact Prod.ext ht hu

/-- The rational-tanh graph equation is exactly the Fermi-coordinate geodesic
acceleration equation. -/
theorem gluingFinFermiCircleTransverseGraphSlope_acceleration
    {α c ρ t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1) :
    HasDerivAt (gluingFinFermiCircleTransverseGraphSlope α c ρ)
      (gluingFinFermiGraphAcceleration α
        (gluingFinFermiCircleTransverseGraph α c ρ t)
        (gluingFinFermiCircleTransverseGraphSlope α c ρ t)) t := by
  have hderiv := gluingFinFermiCircleTransverseGraphSlope_hasDerivAt hα hq
  have hαt : α * gluingFinFermiCircleTransverseGraph α c ρ t =
      Real.artanh (gluingFinFermiCircleTanhGraph α c ρ t) := by
    dsimp [gluingFinFermiCircleTransverseGraph]
    field_simp [hα]
  have hcoshsinh :
      Real.cosh (Real.artanh (gluingFinFermiCircleTanhGraph α c ρ t)) *
        Real.sinh (Real.artanh (gluingFinFermiCircleTanhGraph α c ρ t)) =
      gluingFinFermiCircleTanhGraph α c ρ t /
        (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2) := by
    rw [Real.cosh_artanh hq, Real.sinh_artanh hq]
    have hpos : 0 < 1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2 := by
      have hleft := hq.1
      have hright := hq.2
      nlinarith
    rw [div_mul_div_comm, ← pow_two, Real.sq_sqrt hpos.le]
    simp
  have htanh := Real.tanh_artanh hq
  have hcoeff :
      α * gluingFinFermiCircleTanhGraph α c ρ t /
          (1 - gluingFinFermiCircleTanhGraph α c ρ t ^ 2) +
        2 * α * gluingFinFermiCircleTanhGraph α c ρ t *
          gluingFinFermiCircleTransverseGraphSlope α c ρ t ^ 2 =
      gluingFinFermiGraphAcceleration α
        (gluingFinFermiCircleTransverseGraph α c ρ t)
        (gluingFinFermiCircleTransverseGraphSlope α c ρ t) := by
    rw [gluingFinFermiGraphAcceleration, hαt]
    rw [mul_assoc (α : ℝ)
      (Real.cosh (Real.artanh (gluingFinFermiCircleTanhGraph α c ρ t)))
      (Real.sinh (Real.artanh (gluingFinFermiCircleTanhGraph α c ρ t)))]
    rw [hcoshsinh, htanh]
    ring
  exact hderiv.congr_deriv hcoeff

/-- The actual second derivative of the circle graph is its Fermi acceleration. -/
theorem gluingFinFermiCircleTransverseGraph_second_derivative
    {α c ρ t : ℝ} (hα : α ≠ 0)
    (hq : gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1) :
    deriv (deriv (gluingFinFermiCircleTransverseGraph α c ρ)) t =
      gluingFinFermiGraphAcceleration α
        (gluingFinFermiCircleTransverseGraph α c ρ t)
        (gluingFinFermiCircleTransverseGraphSlope α c ρ t) := by
  have hqcont : ContinuousAt (gluingFinFermiCircleTanhGraph α c ρ) t :=
    (gluingFinFermiCircleTanhGraph_hasDerivAt t).continuousAt
  have hqevent : ∀ᶠ s in nhds t,
      gluingFinFermiCircleTanhGraph α c ρ s ∈ Set.Ioo (-1) 1 :=
    hqcont.eventually (isOpen_Ioo.mem_nhds hq)
  have hderivEq : deriv (gluingFinFermiCircleTransverseGraph α c ρ) =ᶠ[nhds t]
      gluingFinFermiCircleTransverseGraphSlope α c ρ := by
    filter_upwards [hqevent] with s hqs
    exact (gluingFinFermiCircleTransverseGraph_hasDerivAt (t := s) hα hqs).deriv
  have hacc := gluingFinFermiCircleTransverseGraphSlope_acceleration hα hq
  exact hacc.congr_of_eventuallyEq hderivEq |>.deriv

/-- The explicit transverse graph on a hyperbolic circle is the actual Fermi
transverse coordinate of each point, when parameterized by radial coordinate. -/
theorem gluingFinFermiCircleTransverseGraph_eq_coord
    {α c ρ : ℝ} (hα : 0 < α) (hc : c ≠ 0) (z : ℍ)
    (hcircle : (z.re - c) ^ 2 + z.im ^ 2 = ρ ^ 2) :
    gluingFinFermiCircleTransverseGraph α c ρ
        (gluingFinFermiRadialCoord α z) = gluingFinFermiTransverseCoord α z := by
  have hformula := gluingFinFermiCircle_tanh_eq_exp_formula hα hc z hcircle
  have hqeq : gluingFinFermiCircleTanhGraph α c ρ
      (gluingFinFermiRadialCoord α z) =
      Real.tanh (α * gluingFinFermiTransverseCoord α z) := by
    simpa [gluingFinFermiCircleTanhGraph, neg_mul] using hformula.symm
  have hq : gluingFinFermiCircleTanhGraph α c ρ
      (gluingFinFermiRadialCoord α z) ∈ Set.Ioo (-1) 1 := by
    rw [hqeq]
    exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  calc
    gluingFinFermiCircleTransverseGraph α c ρ
        (gluingFinFermiRadialCoord α z) =
      Real.artanh (gluingFinFermiCircleTanhGraph α c ρ
        (gluingFinFermiRadialCoord α z)) / α := rfl
    _ = Real.artanh (Real.tanh
        (α * gluingFinFermiTransverseCoord α z)) / α := by rw [hqeq]
    _ = gluingFinFermiTransverseCoord α z := by
      rw [Real.artanh_tanh]
      field_simp [hα.ne']

/-- On a semicircular hyperbolic interpolation with nonzero center, the actual
Fermi coordinates lie on the explicit transverse graph over radial coordinate. -/
theorem gluingFinFermiTransverseCoord_geodInterp_circle_graph
    {α : ℝ} (hα : 0 < α) {a b : ℍ} (hre : a.re ≠ b.re)
    (hc : Vendored.RiemannDynamics.geodCenter a b ≠ 0) (s : ℝ) :
    gluingFinFermiTransverseCoord α
        (Vendored.RiemannDynamics.geodInterp a b s) =
      gluingFinFermiCircleTransverseGraph α
        (Vendored.RiemannDynamics.geodCenter a b)
        (Vendored.RiemannDynamics.geodRadius a b)
        (gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b s)) := by
  let c := Vendored.RiemannDynamics.geodCenter a b
  let r := Vendored.RiemannDynamics.geodRadius a b
  let u := (1 - s) * Vendored.RiemannDynamics.circCoord c a +
    s * Vendored.RiemannDynamics.circCoord c b
  have hr : 0 < r := Vendored.RiemannDynamics.geodRadius_pos a b
  have hparam : Vendored.RiemannDynamics.geodInterp a b s =
      Vendored.RiemannDynamics.circPoint c r u hr := by
    dsimp [c, r, u]
    exact Vendored.RiemannDynamics.geodInterp_circle (by simpa using hre) s
  have hcircle :
      ((Vendored.RiemannDynamics.geodInterp a b s).re - c) ^ 2 +
        (Vendored.RiemannDynamics.geodInterp a b s).im ^ 2 = r ^ 2 := by
    rw [hparam, Vendored.RiemannDynamics.circPoint_re,
      Vendored.RiemannDynamics.circPoint_im]
    nlinarith [Real.sin_sq_add_cos_sq (Vendored.RiemannDynamics.circAngle u)]
  simpa [c, r] using
    (gluingFinFermiCircleTransverseGraph_eq_coord hα hc
      (Vendored.RiemannDynamics.geodInterp a b s) hcircle).symm

/-- The explicit circle graph stays in the range of `artanh` at every radial
coordinate attained by the corresponding hyperbolic interpolation. -/
theorem gluingFinFermiCircleTanhGraph_geodInterp_mem
    {α : ℝ} (hα : 0 < α) {a b : ℍ} (hre : a.re ≠ b.re)
    (hc : Vendored.RiemannDynamics.geodCenter a b ≠ 0) (s : ℝ) :
    gluingFinFermiCircleTanhGraph α
        (Vendored.RiemannDynamics.geodCenter a b)
        (Vendored.RiemannDynamics.geodRadius a b)
        (gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b s)) ∈ Set.Ioo (-1) 1 := by
  let c := Vendored.RiemannDynamics.geodCenter a b
  let ρ := Vendored.RiemannDynamics.geodRadius a b
  let u := (1 - s) * Vendored.RiemannDynamics.circCoord c a +
    s * Vendored.RiemannDynamics.circCoord c b
  have hρ : 0 < ρ := Vendored.RiemannDynamics.geodRadius_pos a b
  have hparam : Vendored.RiemannDynamics.geodInterp a b s =
      Vendored.RiemannDynamics.circPoint c ρ u hρ := by
    dsimp [c, ρ, u]
    exact Vendored.RiemannDynamics.geodInterp_circle (by simpa using hre) s
  have hcircle :
      ((Vendored.RiemannDynamics.geodInterp a b s).re - c) ^ 2 +
        (Vendored.RiemannDynamics.geodInterp a b s).im ^ 2 = ρ ^ 2 := by
    rw [hparam, Vendored.RiemannDynamics.circPoint_re,
      Vendored.RiemannDynamics.circPoint_im]
    nlinarith [Real.sin_sq_add_cos_sq (Vendored.RiemannDynamics.circAngle u)]
  have hformula := gluingFinFermiCircle_tanh_eq_exp_formula hα hc
    (Vendored.RiemannDynamics.geodInterp a b s) hcircle
  have hq : gluingFinFermiCircleTanhGraph α c ρ
      (gluingFinFermiRadialCoord α
        (Vendored.RiemannDynamics.geodInterp a b s)) =
      Real.tanh (α * gluingFinFermiTransverseCoord α
        (Vendored.RiemannDynamics.geodInterp a b s)) := by
    simpa [c, ρ, gluingFinFermiCircleTanhGraph, neg_mul] using hformula.symm
  change gluingFinFermiCircleTanhGraph α c ρ
      (gluingFinFermiRadialCoord α
        (Vendored.RiemannDynamics.geodInterp a b s)) ∈ Set.Ioo (-1) 1
  rw [hq]
  exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩

/-- The angular coordinate on the centered semicircle has transverse Fermi
coordinate equal to minus its arc-length parameter, up to the scale. -/
theorem gluingFinFermiTransverseCoord_circPoint_center_zero
    {α r v : ℝ} (hα : 0 < α) (hr : 0 < r) :
    gluingFinFermiTransverseCoord α
      (Vendored.RiemannDynamics.circPoint 0 r v hr) = -v / α := by
  have hnormSq : ‖(Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, gluingFinFermiCircPoint_normSq]
    norm_num
  have hnorm : ‖(Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)‖ = r := by
    nlinarith [norm_nonneg (Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)]
  have hcos : Real.cos (Vendored.RiemannDynamics.circAngle v) = -Real.tanh v := by
    let q := Real.exp v
    have hcosq : Real.cos (Real.arctan q) ^ 2 = 1 / (1 + q ^ 2) :=
      Real.cos_sq_arctan q
    have hsinq : Real.sin (Real.arctan q) ^ 2 = q ^ 2 / (1 + q ^ 2) := by
      rw [Real.sin_arctan]
      rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + q ^ 2)]
    have hcosdouble : Real.cos (2 * Real.arctan q) =
        (1 - q ^ 2) / (1 + q ^ 2) := by
      rw [Real.cos_two_mul, hcosq]
      field_simp [show 1 + q ^ 2 ≠ 0 by positivity]
      ring
    have htanh : Real.tanh v = (q ^ 2 - 1) / (q ^ 2 + 1) := by
      rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
      dsimp [q]
      rw [Real.exp_neg]
      have he : Real.exp v ≠ 0 := (Real.exp_pos v).ne'
      field_simp [he]
    rw [Vendored.RiemannDynamics.circAngle, hcosdouble, htanh]
    ring
  have hratio : (Vendored.RiemannDynamics.circPoint 0 r v hr).re /
      ‖(Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)‖ =
        -Real.tanh v := by
    rw [Vendored.RiemannDynamics.circPoint_re, hnorm]
    simp only [zero_add]
    rw [hcos]
    field_simp [hr.ne']
  apply mul_left_cancel₀ hα.ne'
  apply Real.tanh_injective
  calc
    Real.tanh (α * gluingFinFermiTransverseCoord α
        (Vendored.RiemannDynamics.circPoint 0 r v hr)) = _ := by
      exact gluingFinFermiTransverseCoord_tanh hα _
    _ = Real.tanh (-v) := by rw [hratio, Real.tanh_neg]
    _ = Real.tanh (α * (-v / α)) := by
      have harg : α * (-v / α) = -v := by field_simp [hα.ne']
      rw [harg]

/-- A centered semicircle has constant radial Fermi coordinate. -/
theorem gluingFinFermiRadialCoord_circPoint_center_zero
    {α r v : ℝ} (hr : 0 < r) :
    gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.circPoint 0 r v hr) = Real.log r / α := by
  have hnormSq : ‖(Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, gluingFinFermiCircPoint_normSq]
    norm_num
  have hnorm : ‖(Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)‖ = r := by
    nlinarith [norm_nonneg (Vendored.RiemannDynamics.circPoint 0 r v hr : ℂ)]
  rw [gluingFinFermiRadialCoord, hnorm]

/-- On a semicircle centered at zero, the Fermi path is a straight segment in
the transverse coordinate at fixed radial coordinate. -/
theorem gluingFinFermiCoord_geodInterp_center_zero
    {α : ℝ} (hα : 0 < α) {a b : ℍ} (hre : a.re ≠ b.re)
    (hc : Vendored.RiemannDynamics.geodCenter a b = 0) (s : ℝ) :
    gluingFinFermiRadialCoord α (Vendored.RiemannDynamics.geodInterp a b s) =
        Real.log (Vendored.RiemannDynamics.geodRadius a b) / α ∧
      gluingFinFermiTransverseCoord α (Vendored.RiemannDynamics.geodInterp a b s) =
        (1 - s) * gluingFinFermiTransverseCoord α a +
          s * gluingFinFermiTransverseCoord α b := by
  let r := Vendored.RiemannDynamics.geodRadius a b
  let u₀ := Vendored.RiemannDynamics.circCoord 0 a
  let u₁ := Vendored.RiemannDynamics.circCoord 0 b
  have hr : 0 < r := Vendored.RiemannDynamics.geodRadius_pos a b
  have hradA : ‖(a : ℂ) - (0 : ℂ)‖ = r := by
    dsimp [r, Vendored.RiemannDynamics.geodRadius]
    rw [hc]
    simp
  have hradB : ‖(b : ℂ) - (0 : ℂ)‖ = r := by
    have h := Vendored.RiemannDynamics.norm_sub_geodCenter hre
    simpa [r, hc] using h
  have ha : Vendored.RiemannDynamics.circPoint 0 r u₀ hr = a := by
    dsimp [u₀]
    exact Vendored.RiemannDynamics.circPoint_circCoord
      hr hradA
  have hb : Vendored.RiemannDynamics.circPoint 0 r u₁ hr = b := by
    dsimp [u₁]
    exact Vendored.RiemannDynamics.circPoint_circCoord hr hradB
  have hpath : Vendored.RiemannDynamics.geodInterp a b s =
      Vendored.RiemannDynamics.circPoint 0 r ((1 - s) * u₀ + s * u₁) hr := by
    rw [Vendored.RiemannDynamics.geodInterp_circle (by simpa using hre)]
    simp [r, u₀, u₁, hc]
  have hcoordA : gluingFinFermiTransverseCoord α a = -u₀ / α := by
    rw [← ha]
    exact gluingFinFermiTransverseCoord_circPoint_center_zero hα hr
  have hcoordB : gluingFinFermiTransverseCoord α b = -u₁ / α := by
    rw [← hb]
    exact gluingFinFermiTransverseCoord_circPoint_center_zero hα hr
  constructor
  · rw [hpath]
    simpa [r] using gluingFinFermiRadialCoord_circPoint_center_zero hr
  · rw [hpath]
    rw [gluingFinFermiTransverseCoord_circPoint_center_zero hα hr, hcoordA, hcoordB]
    field_simp [hα.ne']
    ring

/-- On a centered semicircle, the upper fin condition is preserved along the
geodesic: the radial Fermi coordinate, hence the fin height, is constant and
the transverse coordinate is the affine interpolation of its endpoint
values. -/
theorem gluingFinFermi_upperFin_geodInterp_center_zero
    {α ε r : ℝ} {a b : ℍ} (hα : 0 < α)
    (hre : a.re ≠ b.re)
    (hc : Vendored.RiemannDynamics.geodCenter a b = 0)
    (hA : ε * gluingCollarWarp r (gluingFinFermiRadialCoord α a) ≤
      gluingFinFermiTransverseCoord α a)
    (hB : ε * gluingCollarWarp r (gluingFinFermiRadialCoord α b) ≤
      gluingFinFermiTransverseCoord α b)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    ε * gluingCollarWarp r
        (gluingFinFermiRadialCoord α (Vendored.RiemannDynamics.geodInterp a b s)) ≤
      gluingFinFermiTransverseCoord α (Vendored.RiemannDynamics.geodInterp a b s) := by
  let q := Real.log (Vendored.RiemannDynamics.geodRadius a b) / α
  have hcoords := gluingFinFermiCoord_geodInterp_center_zero hα hre hc s
  have hradA : gluingFinFermiRadialCoord α a = q := by
    simpa [q, Vendored.RiemannDynamics.geodInterp_zero] using
      (gluingFinFermiCoord_geodInterp_center_zero hα hre hc (0 : ℝ)).1
  have hradB : gluingFinFermiRadialCoord α b = q := by
    simpa [q, Vendored.RiemannDynamics.geodInterp_one] using
      (gluingFinFermiCoord_geodInterp_center_zero hα hre hc (1 : ℝ)).1
  have huA : ε * gluingCollarWarp r q ≤ gluingFinFermiTransverseCoord α a := by
    rw [← hradA]
    exact hA
  have huB : ε * gluingCollarWarp r q ≤ gluingFinFermiTransverseCoord α b := by
    rw [← hradB]
    exact hB
  have hcoeffA : 0 ≤ 1 - s := by linarith [hs.2]
  have hcoeffB : 0 ≤ s := hs.1
  have hlin : ε * gluingCollarWarp r q ≤
      (1 - s) * gluingFinFermiTransverseCoord α a +
        s * gluingFinFermiTransverseCoord α b := by
    calc
      _ = (1 - s) * (ε * gluingCollarWarp r q) +
          s * (ε * gluingCollarWarp r q) := by ring
      _ ≤ (1 - s) * gluingFinFermiTransverseCoord α a +
          s * gluingFinFermiTransverseCoord α b :=
        add_le_add (mul_le_mul_of_nonneg_left huA hcoeffA)
          (mul_le_mul_of_nonneg_left huB hcoeffB)
  rw [hcoords.1]
  exact hlin.trans_eq hcoords.2.symm

/-- The radial Fermi coordinate is continuous on the upper half-plane. -/
theorem continuous_gluingFinFermiRadialCoord (α : ℝ) :
    Continuous (gluingFinFermiRadialCoord α) := by
  have hnorm : Continuous (fun z : ℍ => ‖(z : ℂ)‖) :=
    continuous_norm.comp UpperHalfPlane.continuous_coe
  have hnonzero : ∀ z : ℍ, ‖(z : ℂ)‖ ≠ 0 := fun z =>
    (norm_pos_iff.mpr z.ne_zero).ne'
  have hlog := hnorm.log hnonzero
  change Continuous (fun z : ℍ => Real.log ‖(z : ℂ)‖ / α)
  exact hlog.div_const α

/-- The transverse Fermi coordinate is continuous on the upper half-plane. -/
theorem continuous_gluingFinFermiTransverseCoord (α : ℝ) :
    Continuous (gluingFinFermiTransverseCoord α) := by
  have hcoe : Continuous (fun z : ℍ => (z : ℂ)) := UpperHalfPlane.continuous_coe
  have hre := Complex.continuous_re.comp hcoe
  have him := Complex.continuous_im.comp hcoe
  have him_ne : ∀ z : ℍ, z.im ≠ 0 := fun z => z.im_pos.ne'
  have hquot : Continuous (fun z : ℍ => z.re / z.im) := hre.div him him_ne
  change Continuous (fun z : ℍ => Real.arsinh (z.re / z.im) / α)
  exact (Real.continuous_arsinh.comp hquot).div_const α

/-- Every radial coordinate between the endpoints of a hyperbolic interpolation
is attained on the interpolation segment. This is the interval-coverage bridge
needed to use the circle graph as a geodesic graph, rather than only pointwise
along a separately parameterized circle. -/
theorem exists_geodInterp_param_of_radial_mem_uIcc
    {α : ℝ} (hα : 0 < α) (a b : ℍ) {x : ℝ}
    (hx : x ∈ Set.uIcc (gluingFinFermiRadialCoord α a)
      (gluingFinFermiRadialCoord α b)) :
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      gluingFinFermiRadialCoord α (Vendored.RiemannDynamics.geodInterp a b s) = x := by
  let f : ℝ → ℝ := fun s => gluingFinFermiRadialCoord α
    (Vendored.RiemannDynamics.geodInterp a b s)
  have hfcont : Continuous f := by
    dsimp [f]
    exact (continuous_gluingFinFermiRadialCoord α).comp
      (Vendored.RiemannDynamics.continuous_geodInterp.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id)) )
  have hf0 : f 0 = gluingFinFermiRadialCoord α a := by
    simp [f, Vendored.RiemannDynamics.geodInterp_zero]
  have hf1 : f 1 = gluingFinFermiRadialCoord α b := by
    simp [f, Vendored.RiemannDynamics.geodInterp_one]
  have hIVT := intermediate_value_Icc (a := (0 : ℝ)) (b := 1)
    (by norm_num : (0 : ℝ) ≤ 1) hfcont.continuousOn
  rcases gluingFinFermiRadialCoord_geodInterp_mono_or_anti hα a b with hm | hm
  · have h01 : f 0 ≤ f 1 := by
      exact hm (by norm_num)
    have hxu : x ∈ Set.uIcc (f 0) (f 1) := by
      simpa [hf0, hf1] using hx
    have hx' : x ∈ Set.Icc (f 0) (f 1) := by
      rcases Set.mem_uIcc.mp hxu with h | h
      · exact h
      · exact ⟨le_trans h01 h.1, le_trans h.2 h01⟩
    rcases hIVT hx' with ⟨s, hs, hfs⟩
    exact ⟨s, hs, hfs⟩
  · have h10 : f 1 ≤ f 0 := by
      exact hm (by norm_num)
    have hxu : x ∈ Set.uIcc (f 0) (f 1) := by
      simpa [hf0, hf1] using hx
    have hx' : x ∈ Set.Icc (f 1) (f 0) := by
      rcases Set.mem_uIcc.mp hxu with h | h
      · exact ⟨le_trans h10 h.1, le_trans h.2 h10⟩
      · exact h
    have hIVT' := intermediate_value_Icc' (a := (0 : ℝ)) (b := 1)
      (by norm_num : (0 : ℝ) ≤ 1) hfcont.continuousOn
    rcases hIVT' hx' with ⟨s, hs, hfs⟩
    exact ⟨s, hs, hfs⟩

/-- Differentiate the Fermi-coordinate geodesic acceleration with respect to
height. -/
theorem gluingFinFermiGraphAcceleration_hasDerivAt (α u p : ℝ) :
    HasDerivAt (fun x : ℝ => gluingFinFermiGraphAcceleration α x p)
      (α ^ 2 * (Real.cosh (α * u) ^ 2 + Real.sinh (α * u) ^ 2) +
        2 * α ^ 2 * p ^ 2 / Real.cosh (α * u) ^ 2) u := by
  have harg : HasDerivAt (fun x : ℝ => α * x) α u := by
    simpa using (hasDerivAt_id u).const_mul α
  have hcosh := harg.cosh
  have hsinh := harg.sinh
  have hprod := (hcosh.mul hsinh).const_mul α
  have htanh := (gluingFinFermiTanh_hasDerivAt α u).const_mul (2 * α * p ^ 2)
  have hsum : HasDerivAt
      (fun x : ℝ => α * Real.cosh (α * x) * Real.sinh (α * x) +
        2 * α * p ^ 2 * Real.tanh (α * x))
      (α * (Real.sinh (α * u) * α * Real.sinh (α * u) +
        Real.cosh (α * u) * (Real.cosh (α * u) * α)) +
        2 * α * p ^ 2 * (α / Real.cosh (α * u) ^ 2)) u := by
    exact (hprod.add htanh).congr_of_eventuallyEq (by
      filter_upwards [] with x
      dsimp
      ring)
  convert hsum using 1
  · rfl
  · rw [div_eq_mul_inv]
    ring

/-- For positive scale, the graph acceleration is strictly increasing in its
height argument, at every fixed slope. -/
theorem gluingFinFermiGraphAcceleration_strictMono_height {α p : ℝ}
    (hα : 0 < α) :
    StrictMono (fun u : ℝ => gluingFinFermiGraphAcceleration α u p) := by
  apply strictMono_of_deriv_pos
  intro u
  rw [(gluingFinFermiGraphAcceleration_hasDerivAt α u p).deriv]
  positivity

/-- A negative second derivative at a stationary point rules out a minimum.
The proof turns the negative second derivative into a strictly negative first
derivative immediately to the right, then applies the mean value theorem on a
short interval contained in the original minimizing interval. -/
theorem gluingFinFermi_no_negative_interior_min
    {H : ℝ → ℝ} {a b x : ℝ}
    (hx : x ∈ Set.Ioo a b)
    (hcont : ContinuousOn H (Set.Icc a b))
    (hmin : ∀ y ∈ Set.Icc a b, H x ≤ H y)
    (hderiv : deriv H x = 0)
    (hsecond : deriv (deriv H) x < 0) : False := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_neg
    (f := deriv H) hsecond hderiv
  have hsign' : ∀ᶠ z in nhdsWithin x {x}ᶜ,
      SignType.sign (deriv H z) = SignType.sign (x - z) :=
    hsign.filter_mono nhdsWithin_le_nhds
  have hright := deriv_neg_right_of_sign_deriv hsign'
  obtain ⟨y, hy, hsub⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset (a := x) (u' := b) hx.2).mp hright
  have hxy : x < y := hy.1
  have hyb : y ≤ b := hy.2
  have hxyImage : Set.Icc x y ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hx.1.le hyb
  have hcont' : ContinuousOn H (Set.Icc x y) := hcont.mono hxyImage
  have hderivneg : ∀ z ∈ interior (Set.Icc x y), deriv H z < 0 := by
    intro z hz
    have hz' : z ∈ Set.Ioo x y := by
      simpa only [interior_Icc] using hz
    exact hsub hz'
  have hanti : StrictAntiOn H (Set.Icc x y) :=
    strictAntiOn_of_deriv_neg (convex_Icc x y) hcont' hderivneg
  have hdrop : H y < H x := hanti
    ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy
  have hyab : y ∈ Set.Icc a b := ⟨hx.1.le.trans hxy.le, hyb⟩
  linarith [hmin y hyab]

/-- At a negative contact, the geodesic graph's second derivative is strictly
smaller than the fin graph's second derivative: use equality of the slopes,
the geodesic acceleration equation, and the fin acceleration inequality. -/
theorem gluingFinFermiGraph_secondDerivative_gap
    {α φ f p φ₂ f₂ : ℝ} (hα : 0 < α) (hφf : φ < f)
    (hφ₂ : φ₂ = gluingFinFermiGraphAcceleration α φ p)
    (hf₂ : gluingFinFermiGraphAcceleration α f p ≤ f₂) :
    φ₂ < f₂ := by
  have hmono : StrictMono (fun u : ℝ => gluingFinFermiGraphAcceleration α u p) :=
    gluingFinFermiGraphAcceleration_strictMono_height (α := α) (p := p) hα
  have hstrict := hmono hφf
  change gluingFinFermiGraphAcceleration α φ p <
    gluingFinFermiGraphAcceleration α f p at hstrict
  rw [← hφ₂] at hstrict
  exact lt_of_lt_of_le hstrict hf₂

/-- At a smooth point below the actual scaled collar fin, a circle-geodesic
graph with matching slope has strictly smaller second derivative than the
fin. This is the concrete differential-comparison step used at a negative
interior minimum of their difference. -/
theorem gluingFinFermiProfile_secondDerivative_gap
    {α c ρ r ε t : ℝ} (hα : 0 < α)
    (hq : gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1)
    (hbelow : gluingFinFermiCircleTransverseGraph α c ρ t <
      ε * gluingCollarWarp r t)
    (hslope : gluingFinFermiCircleTransverseGraphSlope α c ρ t =
      ε * deriv (gluingCollarWarp r) t)
    (hacc : gluingFinFermiGraphAcceleration α
        (ε * gluingCollarWarp r t)
        (ε * deriv (gluingCollarWarp r) t) ≤
      deriv (deriv (fun s => ε * gluingCollarWarp r s)) t) :
    deriv (deriv (gluingFinFermiCircleTransverseGraph α c ρ)) t <
      deriv (deriv (fun s => ε * gluingCollarWarp r s)) t := by
  apply gluingFinFermiGraph_secondDerivative_gap hα hbelow
    (gluingFinFermiCircleTransverseGraph_second_derivative hα.ne' hq)
  simpa only [hslope] using hacc

/-- A circle-geodesic graph cannot dip below the actual scaled fin on an
interval lying entirely to one side of the seam, provided the finite
acceleration inequality holds there. The proof chooses a negative minimum;
equal slopes and strict acceleration comparison contradict its negative
second derivative. -/
theorem gluingFinFermiCircleGraph_ge_profile_of_acceleration
    {α c ρ r ε a b : ℝ} (hα : 0 < α) (hab : a ≤ b)
    (hq : ∀ t ∈ Set.Icc a b,
      gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1)
    (hside : ∀ t ∈ Set.Icc a b, t ≠ 0)
    (hleft : ε * gluingCollarWarp r a ≤
      gluingFinFermiCircleTransverseGraph α c ρ a)
    (hright : ε * gluingCollarWarp r b ≤
      gluingFinFermiCircleTransverseGraph α c ρ b)
    (hacc : ∀ t ∈ Set.Icc a b,
      gluingFinFermiGraphAcceleration α
          (ε * gluingCollarWarp r t)
          (ε * deriv (gluingCollarWarp r) t) ≤
        deriv (deriv (fun s => ε * gluingCollarWarp r s)) t) :
    ∀ t ∈ Set.Icc a b,
      ε * gluingCollarWarp r t ≤
        gluingFinFermiCircleTransverseGraph α c ρ t := by
  classical
  let φ := gluingFinFermiCircleTransverseGraph α c ρ
  let F := fun t => ε * gluingCollarWarp r t
  let H := fun t => φ t - F t
  have hcontH : ContinuousOn H (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    change ContinuousAt (fun s => φ s - F s) t
    exact (gluingFinFermiCircleTransverseGraph_hasDerivAt
      hα.ne' (hq t ht)).continuousAt.sub
        ((gluingCollarWarp_continuous r).continuousAt.const_mul ε)
  intro t ht
  by_contra hnot
  have hbelow : H t < 0 := by
    dsimp [H, F, φ] at hnot ⊢
    linarith
  obtain ⟨x, hx, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hcontH
  have hxneg : H x < 0 := lt_of_le_of_lt (hmin ht) hbelow
  have hxa : a < x := by
    by_contra h
    have hEq : x = a := le_antisymm (le_of_not_gt h) hx.1
    rw [hEq] at hxneg
    have hleft' : 0 ≤ H a := by
      dsimp [H, F, φ]
      linarith
    linarith
  have hxb : x < b := by
    by_contra h
    have hEq : x = b := le_antisymm hx.2 (le_of_not_gt h)
    rw [hEq] at hxneg
    have hright' : 0 ≤ H b := by
      dsimp [H, F, φ]
      linarith
    linarith
  have hxIoo : x ∈ Set.Ioo a b := ⟨hxa, hxb⟩
  have hxne : x ≠ 0 := hside x hx
  have hFderiv : HasDerivAt F (ε * deriv (gluingCollarWarp r) x) x := by
    simpa [F] using (gluingCollarWarp_hasDerivAt_of_ne r hxne).const_mul ε
  have hφderiv : HasDerivAt φ
      (gluingFinFermiCircleTransverseGraphSlope α c ρ x) x := by
    simpa [φ, gluingFinFermiCircleTransverseGraphSlope] using
      gluingFinFermiCircleTransverseGraph_hasDerivAt hα.ne' (hq x hx)
  have hHderiv : HasDerivAt H
      (gluingFinFermiCircleTransverseGraphSlope α c ρ x -
        ε * deriv (gluingCollarWarp r) x) x := by
    change HasDerivAt (fun s => φ s - F s) _ x
    exact hφderiv.sub hFderiv
  have hlocal : IsLocalMin H x := hmin.localize.isLocalMin
    (Icc_mem_nhds hxIoo.1 hxIoo.2)
  have hderivzero : deriv H x = 0 := hlocal.deriv_eq_zero
  have hderivEq := hHderiv.deriv
  have hslope : gluingFinFermiCircleTransverseGraphSlope α c ρ x =
      ε * deriv (gluingCollarWarp r) x := by
    dsimp [H] at hderivEq
    linarith
  have hgap := gluingFinFermiProfile_secondDerivative_gap hα
    (hq x hx) (by
      have : H x < 0 := hxneg
      dsimp [H, φ, F] at this ⊢
      linarith) hslope (hacc x hx)
  have hgap' : deriv (deriv φ) x <
      deriv (deriv F) x := by
    simpa [φ, F] using hgap
  have hgraphTwice : HasDerivAt (deriv φ)
      (gluingFinFermiGraphAcceleration α
        (φ x) (gluingFinFermiCircleTransverseGraphSlope α c ρ x)) x := by
    have hqcont : ContinuousAt (gluingFinFermiCircleTanhGraph α c ρ) x :=
      (gluingFinFermiCircleTanhGraph_hasDerivAt x).continuousAt
    have hqevent : ∀ᶠ s in nhds x,
        gluingFinFermiCircleTanhGraph α c ρ s ∈ Set.Ioo (-1) 1 :=
      hqcont.eventually (isOpen_Ioo.mem_nhds (hq x hx))
    have hderivEq : deriv φ =ᶠ[nhds x]
        gluingFinFermiCircleTransverseGraphSlope α c ρ := by
      filter_upwards [hqevent] with s hqs
      exact (gluingFinFermiCircleTransverseGraph_hasDerivAt
        hα.ne' hqs).deriv
    simpa [φ] using
      (gluingFinFermiCircleTransverseGraphSlope_acceleration
        hα.ne' (hq x hx)).congr_of_eventuallyEq hderivEq
  have hFtwice : HasDerivAt (deriv F) (ε * gluingCollarWarp r x) x := by
    have h := (gluingCollarWarp_hasDerivAt_deriv r hxne).const_mul ε
    simpa [F, deriv_const_mul_field ε] using h
  have hderivHEq : deriv H =ᶠ[nhds x]
      (fun s => gluingFinFermiCircleTransverseGraphSlope α c ρ s -
        ε * deriv (gluingCollarWarp r) s) := by
    have hqcont : ContinuousAt (gluingFinFermiCircleTanhGraph α c ρ) x :=
      (gluingFinFermiCircleTanhGraph_hasDerivAt x).continuousAt
    have hqevent : ∀ᶠ s in nhds x,
        gluingFinFermiCircleTanhGraph α c ρ s ∈ Set.Ioo (-1) 1 :=
      hqcont.eventually (isOpen_Ioo.mem_nhds (hq x hx))
    have hsideevent : ∀ᶠ s in nhds x, s ≠ 0 := eventually_ne_nhds hxne
    filter_upwards [hqevent, hsideevent] with s hqs hs
    have hφs : HasDerivAt φ
        (gluingFinFermiCircleTransverseGraphSlope α c ρ s) s := by
      simpa [φ, gluingFinFermiCircleTransverseGraphSlope] using
        gluingFinFermiCircleTransverseGraph_hasDerivAt hα.ne' hqs
    have hFs : HasDerivAt F
        (ε * deriv (gluingCollarWarp r) s) s := by
      simpa [F] using (gluingCollarWarp_hasDerivAt_of_ne r hs).const_mul ε
    have hHs := hφs.sub hFs
    change deriv (fun u => φ u - F u) s = _
    exact hHs.deriv
  have hHtwice :=
    (gluingFinFermiCircleTransverseGraphSlope_acceleration hα.ne'
      (hq x hx)).sub ((gluingCollarWarp_hasDerivAt_deriv r hxne).const_mul ε)
  have hsecond := hHtwice.congr_of_eventuallyEq hderivHEq
  have hsecondneg : deriv (deriv H) x < 0 := by
    have hgraphEq := gluingFinFermiCircleTransverseGraph_second_derivative
      hα.ne' (hq x hx)
    have hwarpEq := gluingCollarFinWarp_scaled_second_deriv_eq ε r hxne
    rw [hgraphEq, hwarpEq] at hgap'
    rw [hsecond.deriv]
    exact sub_neg.mpr hgap'
  exact gluingFinFermi_no_negative_interior_min hxIoo hcontH
    (fun y hy => hmin hy) hderivzero hsecondneg

/-- On a bounded collar window, the actual scaled fin profile satisfies the
geodesic-acceleration differential inequality with its classical second
derivative, away from the seam. -/
theorem gluingCollarFinWarp_uniform_Fermi_second_deriv_bound
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ∀ t ∈ Set.Icc (-R) R, t ≠ 0 →
        gluingFinFermiGraphAcceleration (Real.sqrt (1 - ε))
            (ε * gluingCollarWarp r t)
            (ε * deriv (gluingCollarWarp r) t) ≤
          deriv (deriv (fun s => ε * gluingCollarWarp r s)) t := by
  obtain ⟨ε, hε, hε', hacc⟩ :=
    gluingCollarFinWarp_uniform_boundary_acceleration hr hR
  refine ⟨ε, hε, hε', ?_⟩
  intro t ht ht0
  rw [gluingCollarFinWarp_scaled_second_deriv_eq ε r ht0]
  simpa [gluingFinFermiGraphAcceleration, mul_assoc, mul_pow] using hacc t ht ht0

/-- Every sufficiently fine dyadic fin scale obeys the actual Fermi graph
acceleration bound on a fixed bounded window. This is the scale-compatible
input needed to apply the smooth-side profile comparison to the AB04
approximating sequence. -/
theorem gluingCollarFinWarp_dyadic_Fermi_second_deriv_bound
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ t ∈ Set.Icc (-R) R, t ≠ 0 →
        gluingFinFermiGraphAcceleration
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
              ((1 / 2 : ℝ) ^ n * gluingCollarWarp r t)
              ((1 / 2 : ℝ) ^ n * deriv (gluingCollarWarp r) t) ≤
          deriv (deriv (fun s => (1 / 2 : ℝ) ^ n * gluingCollarWarp r s)) t := by
  obtain ⟨N, hN⟩ := gluingCollarFinWarp_dyadic_boundary_estimate_eventually hr hR
  let N' : ℕ := max N 2
  refine ⟨N', le_max_right N 2, fun n hn t ht ht0 => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left N 2) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right N 2) hn
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := by
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    dsimp [ε]
    norm_num at hpow ⊢
    nlinarith
  have hacc := gluingCollarFinWarp_boundary_estimate_implies_acceleration
    hr hε hε' (hN n hnN)
  rw [gluingCollarFinWarp_scaled_second_deriv_eq ε r ht0]
  convert hacc t ht ht0 using 1
  all_goals norm_num [ε, gluingFinFermiGraphAcceleration]
  all_goals ring_nf

/-- A differentiable graph cannot have a local minimum of its difference with
the fin at the seam: the fin has a strictly positive slope jump there. -/
theorem gluingFinFermiGraph_no_seam_local_min
    {ε r : ℝ} (hε : 0 < ε) {φ : ℝ → ℝ} {p : ℝ}
    (hφderiv : HasDerivAt φ p 0) :
    ¬ IsLocalMin (fun t => φ t - ε * gluingCollarWarp r t) 0 := by
  intro hmin
  let H := fun t => φ t - ε * gluingCollarWarp r t
  have hleftF : HasDerivWithinAt (fun t => ε * gluingCollarWarp r t)
      (-ε * Real.cosh r) (Set.Iic 0) 0 := by
    simpa only [show ε * (-Real.cosh r) = -ε * Real.cosh r by ring] using
      (gluingCollarWarp_hasDerivWithinAt_zero_left r).const_mul ε
  have hrightF : HasDerivWithinAt (fun t => ε * gluingCollarWarp r t)
      (ε * Real.cosh r) (Set.Ici 0) 0 := by
    exact (gluingCollarWarp_hasDerivWithinAt_zero_right r).const_mul ε
  have hleftH : HasDerivWithinAt H (p - (-ε * Real.cosh r))
      (Set.Iic 0) 0 := by
    change HasDerivWithinAt (fun t => φ t - ε * gluingCollarWarp r t) _ _ _
    exact hφderiv.hasDerivWithinAt.sub hleftF
  have hrightH : HasDerivWithinAt H (p - ε * Real.cosh r)
      (Set.Ici 0) 0 := by
    change HasDerivWithinAt (fun t => φ t - ε * gluingCollarWarp r t) _ _ _
    exact hφderiv.hasDerivWithinAt.sub hrightF
  have hleftDir : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic 0) 0 := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (0 : ℝ) + t • (-1 : ℝ) ∈ Set.Iic 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Iic, zero_add, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (by norm_num)
    exact hevent.frequently
  have hrightDir : (1 : ℝ) ∈ posTangentConeAt (Set.Ici 0) 0 := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (0 : ℝ) + t • (1 : ℝ) ∈ Set.Ici 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ici, zero_add, smul_eq_mul]
      exact mul_nonneg (le_of_lt ht) (by norm_num)
    exact hevent.frequently
  have hleftSign := (hmin.on (Set.Iic 0)).hasFDerivWithinAt_nonneg
    hleftH.hasFDerivWithinAt hleftDir
  have hrightSign := (hmin.on (Set.Ici 0)).hasFDerivWithinAt_nonneg
    hrightH.hasFDerivWithinAt hrightDir
  have hleftSign' : p - (-ε * Real.cosh r) ≤ 0 := by
    have hleftSign'' : 0 ≤ -(p - (-ε * Real.cosh r)) := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hleftSign
    linarith
  have hrightSign' : 0 ≤ p - ε * Real.cosh r := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hrightSign
  have hjump : p - ε * Real.cosh r - (p - (-ε * Real.cosh r)) < 0 := by
    rw [show p - ε * Real.cosh r - (p - (-ε * Real.cosh r)) =
      -2 * (ε * Real.cosh r) by ring]
    have hpos : 0 < 2 * (ε * Real.cosh r) :=
      mul_pos (by norm_num) (mul_pos hε (Real.cosh_pos r))
    nlinarith
  linarith

/-- The positive slope jump of the actual fin excludes a local minimum of
`circleGraph - ε * warp` at the seam. A local minimum forces the left
one-sided derivative to be nonpositive and the right one to be nonnegative,
whereas the fin's upward jump makes the difference's jump strictly negative. -/
theorem gluingFinFermiCircleGraph_no_seam_local_min
    {α c ρ ε r : ℝ} (hα : 0 < α) (hε : 0 < ε)
    (hq : gluingFinFermiCircleTanhGraph α c ρ 0 ∈ Set.Ioo (-1) 1) :
    ¬ IsLocalMin
      (fun t => gluingFinFermiCircleTransverseGraph α c ρ t -
        ε * gluingCollarWarp r t) 0 := by
  intro hmin
  let φ := gluingFinFermiCircleTransverseGraph α c ρ
  let H := fun t => φ t - ε * gluingCollarWarp r t
  let d := gluingFinFermiCircleTransverseGraphSlope α c ρ 0
  have hφderiv : HasDerivAt φ d 0 := by
    simpa [φ, d, gluingFinFermiCircleTransverseGraphSlope] using
      gluingFinFermiCircleTransverseGraph_hasDerivAt hα.ne' hq
  have hleftF : HasDerivWithinAt (fun t => ε * gluingCollarWarp r t)
      (-ε * Real.cosh r) (Set.Iic 0) 0 := by
    simpa only [show ε * (-Real.cosh r) = -ε * Real.cosh r by ring] using
      (gluingCollarWarp_hasDerivWithinAt_zero_left r).const_mul ε
  have hrightF : HasDerivWithinAt (fun t => ε * gluingCollarWarp r t)
      (ε * Real.cosh r) (Set.Ici 0) 0 := by
    exact (gluingCollarWarp_hasDerivWithinAt_zero_right r).const_mul ε
  have hleftH : HasDerivWithinAt H (d - (-ε * Real.cosh r)) (Set.Iic 0) 0 := by
    change HasDerivWithinAt (fun t => φ t - ε * gluingCollarWarp r t) _ _ _
    exact hφderiv.hasDerivWithinAt.sub hleftF
  have hrightH : HasDerivWithinAt H (d - ε * Real.cosh r) (Set.Ici 0) 0 := by
    change HasDerivWithinAt (fun t => φ t - ε * gluingCollarWarp r t) _ _ _
    exact hφderiv.hasDerivWithinAt.sub hrightF
  have hleftDir : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic 0) 0 := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (0 : ℝ) + t • (-1 : ℝ) ∈ Set.Iic 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Iic, zero_add, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht) (by norm_num)
    exact hevent.frequently
  have hrightDir : (1 : ℝ) ∈ posTangentConeAt (Set.Ici 0) 0 := by
    apply mem_posTangentConeAt_of_frequently_mem
    have hevent : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (0 : ℝ) + t • (1 : ℝ) ∈ Set.Ici 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_Ici, zero_add, smul_eq_mul]
      exact mul_nonneg (le_of_lt ht) (by norm_num)
    exact hevent.frequently
  have hleftSign := (hmin.on (Set.Iic 0)).hasFDerivWithinAt_nonneg
    hleftH.hasFDerivWithinAt hleftDir
  have hrightSign := (hmin.on (Set.Ici 0)).hasFDerivWithinAt_nonneg
    hrightH.hasFDerivWithinAt hrightDir
  have hleftSign' : d - (-ε * Real.cosh r) ≤ 0 := by
    have hleftSign'' : 0 ≤ -(d - (-ε * Real.cosh r)) := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hleftSign
    linarith
  have hrightSign' : 0 ≤ d - ε * Real.cosh r := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hrightSign
  have hjump : d - ε * Real.cosh r - (d - (-ε * Real.cosh r)) < 0 := by
    rw [show d - ε * Real.cosh r - (d - (-ε * Real.cosh r)) =
      -2 * (ε * Real.cosh r) by ring]
    have hpos : 0 < 2 * (ε * Real.cosh r) :=
      mul_pos (by norm_num) (mul_pos hε (Real.cosh_pos r))
    nlinarith
  linarith

/-- Full bounded-interval fin comparison, including the seam. Away from zero,
the smooth acceleration comparison excludes a negative interior minimum; at
zero, the positive profile slope jump excludes a local minimum directly. -/
theorem gluingFinFermiCircleGraph_ge_profile_of_acceleration_with_seam
    {α c ρ r ε a b : ℝ} (hα : 0 < α) (hε : 0 < ε) (hab : a ≤ b)
    (hq : ∀ t ∈ Set.Icc a b,
      gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1)
    (hleft : ε * gluingCollarWarp r a ≤
      gluingFinFermiCircleTransverseGraph α c ρ a)
    (hright : ε * gluingCollarWarp r b ≤
      gluingFinFermiCircleTransverseGraph α c ρ b)
    (hacc : ∀ t ∈ Set.Icc a b, t ≠ 0 →
      gluingFinFermiGraphAcceleration α
          (ε * gluingCollarWarp r t)
          (ε * deriv (gluingCollarWarp r) t) ≤
        deriv (deriv (fun s => ε * gluingCollarWarp r s)) t) :
    ∀ t ∈ Set.Icc a b,
      ε * gluingCollarWarp r t ≤
        gluingFinFermiCircleTransverseGraph α c ρ t := by
  classical
  let φ := gluingFinFermiCircleTransverseGraph α c ρ
  let F := fun t => ε * gluingCollarWarp r t
  let H := fun t => φ t - F t
  have hcontH : ContinuousOn H (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    change ContinuousAt (fun s => φ s - F s) t
    exact (gluingFinFermiCircleTransverseGraph_hasDerivAt
      hα.ne' (hq t ht)).continuousAt.sub
        ((gluingCollarWarp_continuous r).continuousAt.const_mul ε)
  intro t ht
  by_contra hnot
  have hbelow : H t < 0 := by
    dsimp [H, F, φ] at hnot ⊢
    linarith
  obtain ⟨x, hx, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hcontH
  have hxneg : H x < 0 := lt_of_le_of_lt (hmin ht) hbelow
  have hxa : a < x := by
    by_contra h
    have hEq : x = a := le_antisymm (le_of_not_gt h) hx.1
    rw [hEq] at hxneg
    have hleft' : 0 ≤ H a := by
      dsimp [H, F, φ]
      linarith
    linarith
  have hxb : x < b := by
    by_contra h
    have hEq : x = b := le_antisymm hx.2 (le_of_not_gt h)
    rw [hEq] at hxneg
    have hright' : 0 ≤ H b := by
      dsimp [H, F, φ]
      linarith
    linarith
  have hxIoo : x ∈ Set.Ioo a b := ⟨hxa, hxb⟩
  have hlocal : IsLocalMin H x := hmin.localize.isLocalMin
    (Icc_mem_nhds hxIoo.1 hxIoo.2)
  by_cases hxne : x ≠ 0
  · have hFderiv : HasDerivAt F (ε * deriv (gluingCollarWarp r) x) x := by
      simpa [F] using (gluingCollarWarp_hasDerivAt_of_ne r hxne).const_mul ε
    have hφderiv : HasDerivAt φ
        (gluingFinFermiCircleTransverseGraphSlope α c ρ x) x := by
      simpa [φ, gluingFinFermiCircleTransverseGraphSlope] using
        gluingFinFermiCircleTransverseGraph_hasDerivAt hα.ne' (hq x hx)
    have hHderiv : HasDerivAt H
        (gluingFinFermiCircleTransverseGraphSlope α c ρ x -
          ε * deriv (gluingCollarWarp r) x) x := by
      change HasDerivAt (fun s => φ s - F s) _ x
      exact hφderiv.sub hFderiv
    have hderivzero : deriv H x = 0 := hlocal.deriv_eq_zero
    have hderivEq := hHderiv.deriv
    have hslope : gluingFinFermiCircleTransverseGraphSlope α c ρ x =
        ε * deriv (gluingCollarWarp r) x := by
      dsimp [H] at hderivEq
      linarith
    have hgap := gluingFinFermiProfile_secondDerivative_gap hα
      (hq x hx) (by
        have : H x < 0 := hxneg
        dsimp [H, φ, F] at this ⊢
        linarith) hslope (hacc x hx hxne)
    have hgap' : deriv (deriv φ) x < deriv (deriv F) x := by
      simpa [φ, F] using hgap
    have hderivHEq : deriv H =ᶠ[nhds x]
        (fun s => gluingFinFermiCircleTransverseGraphSlope α c ρ s -
          ε * deriv (gluingCollarWarp r) s) := by
      have hqcont : ContinuousAt (gluingFinFermiCircleTanhGraph α c ρ) x :=
        (gluingFinFermiCircleTanhGraph_hasDerivAt x).continuousAt
      have hqevent : ∀ᶠ s in nhds x,
          gluingFinFermiCircleTanhGraph α c ρ s ∈ Set.Ioo (-1) 1 :=
        hqcont.eventually (isOpen_Ioo.mem_nhds (hq x hx))
      have hsideevent : ∀ᶠ s in nhds x, s ≠ 0 := eventually_ne_nhds hxne
      filter_upwards [hqevent, hsideevent] with s hqs hs
      have hφs : HasDerivAt φ
          (gluingFinFermiCircleTransverseGraphSlope α c ρ s) s := by
        simpa [φ, gluingFinFermiCircleTransverseGraphSlope] using
          gluingFinFermiCircleTransverseGraph_hasDerivAt hα.ne' hqs
      have hFs : HasDerivAt F
          (ε * deriv (gluingCollarWarp r) s) s := by
        simpa [F] using (gluingCollarWarp_hasDerivAt_of_ne r hs).const_mul ε
      change deriv (fun u => φ u - F u) s = _
      exact (hφs.sub hFs).deriv
    have hsecond :=
      (gluingFinFermiCircleTransverseGraphSlope_acceleration hα.ne'
        (hq x hx)).sub ((gluingCollarWarp_hasDerivAt_deriv r hxne).const_mul ε)
      |>.congr_of_eventuallyEq hderivHEq
    have hsecondneg : deriv (deriv H) x < 0 := by
      have hgraphEq := gluingFinFermiCircleTransverseGraph_second_derivative
        hα.ne' (hq x hx)
      have hwarpEq := gluingCollarFinWarp_scaled_second_deriv_eq ε r hxne
      rw [hgraphEq, hwarpEq] at hgap'
      rw [hsecond.deriv]
      exact sub_neg.mpr hgap'
    exact gluingFinFermi_no_negative_interior_min hxIoo hcontH
      (fun y hy => hmin hy) hderivzero hsecondneg
  · have hx0 : x = 0 := not_ne_iff.mp hxne
    have hlocal0 : IsLocalMin
        (fun s => gluingFinFermiCircleTransverseGraph α c ρ s -
          ε * gluingCollarWarp r s) 0 := by
      simpa [H, φ, F, hx0] using hlocal
    have hq0 : gluingFinFermiCircleTanhGraph α c ρ 0 ∈ Set.Ioo (-1) 1 := by
      simpa [hx0] using hq x hx
    exact (gluingFinFermiCircleGraph_no_seam_local_min hα hε
      hq0) hlocal0

/-- Any geodesic graph satisfying the Fermi acceleration equation stays above
the scaled fin on a bounded interval when the fin's acceleration dominates.
This abstract form also covers vertical upper-half-plane geodesics. -/
theorem gluingFinFermiGraph_ge_profile_of_acceleration_with_seam
    {α r ε a b : ℝ} (hα : 0 < α) (hε : 0 < ε) (hab : a ≤ b)
    (φ p : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc a b, HasDerivAt φ (p t) t)
    (hp : ∀ t ∈ Set.Icc a b,
      HasDerivAt p
        (gluingFinFermiGraphAcceleration α (φ t) (p t)) t)
    (hleft : ε * gluingCollarWarp r a ≤ φ a)
    (hright : ε * gluingCollarWarp r b ≤ φ b)
    (hacc : ∀ t ∈ Set.Icc a b, t ≠ 0 →
      gluingFinFermiGraphAcceleration α
          (ε * gluingCollarWarp r t)
          (ε * deriv (gluingCollarWarp r) t) ≤
        deriv (deriv (fun s => ε * gluingCollarWarp r s)) t) :
    ∀ t ∈ Set.Icc a b, ε * gluingCollarWarp r t ≤ φ t := by
  classical
  let F : ℝ → ℝ := fun t => ε * gluingCollarWarp r t
  let H : ℝ → ℝ := fun t => φ t - F t
  have hcontH : ContinuousOn H (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    change ContinuousAt (fun s => φ s - F s) t
    exact (hφ t ht).continuousAt.sub
      ((gluingCollarWarp_continuous r).continuousAt.const_mul ε)
  intro t ht
  by_contra hnot
  have hbelow : H t < 0 := by
    dsimp [H, F] at hnot ⊢
    linarith
  obtain ⟨x, hx, hmin⟩ :=
    isCompact_Icc.exists_isMinOn ⟨a, le_rfl, hab⟩ hcontH
  have hxneg : H x < 0 := lt_of_le_of_lt (hmin ht) hbelow
  have hxa : a < x := by
    by_contra h
    have hEq : x = a := le_antisymm (le_of_not_gt h) hx.1
    rw [hEq] at hxneg
    have hleft' : 0 ≤ H a := by dsimp [H, F]; linarith
    linarith
  have hxb : x < b := by
    by_contra h
    have hEq : x = b := le_antisymm hx.2 (le_of_not_gt h)
    rw [hEq] at hxneg
    have hright' : 0 ≤ H b := by dsimp [H, F]; linarith
    linarith
  have hxIoo : x ∈ Set.Ioo a b := ⟨hxa, hxb⟩
  have hlocal : IsLocalMin H x := hmin.localize.isLocalMin
    (Icc_mem_nhds hxIoo.1 hxIoo.2)
  by_cases hxne : x ≠ 0
  · have hFderiv : HasDerivAt F (ε * deriv (gluingCollarWarp r) x) x := by
      simpa [F] using (gluingCollarWarp_hasDerivAt_of_ne r hxne).const_mul ε
    have hHderiv : HasDerivAt H (p x - ε * deriv (gluingCollarWarp r) x) x := by
      change HasDerivAt (fun s => φ s - F s) _ x
      exact (hφ x hx).sub hFderiv
    have hderivzero : deriv H x = 0 := hlocal.deriv_eq_zero
    have hderivEq := hHderiv.deriv
    have hslope : p x = ε * deriv (gluingCollarWarp r) x := by
      dsimp [H] at hderivEq
      linarith
    have hbelow' : φ x < ε * gluingCollarWarp r x := by
      have : H x < 0 := hxneg
      dsimp [H, F] at this ⊢
      linarith
    have hgap := gluingFinFermiGraph_secondDerivative_gap hα hbelow' rfl
      (by simpa only [hslope] using hacc x hx hxne)
    rw [gluingCollarFinWarp_scaled_second_deriv_eq ε r hxne] at hgap
    have hgap' :
        gluingFinFermiGraphAcceleration α (φ x) (p x) <
          ε * gluingCollarWarp r x := by
      rw [hslope]
      exact hgap
    have hderivHEq : deriv H =ᶠ[nhds x]
        (fun s => p s - ε * deriv (gluingCollarWarp r) s) := by
      filter_upwards [Ioo_mem_nhds hxa hxb, eventually_ne_nhds hxne]
        with s hs hsz
      have hsIcc : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.le⟩
      have hFs : HasDerivAt F (ε * deriv (gluingCollarWarp r) s) s := by
        simpa [F] using
          (gluingCollarWarp_hasDerivAt_of_ne r hsz).const_mul ε
      change deriv (fun u => φ u - F u) s = _
      exact (hφ s hsIcc).sub hFs |>.deriv
    have hsecondAt : HasDerivAt (deriv H)
        (gluingFinFermiGraphAcceleration α (φ x) (p x) -
          ε * gluingCollarWarp r x) x := by
      have h := (hp x hx).sub
        ((gluingCollarWarp_hasDerivAt_deriv r hxne).const_mul ε)
      exact h.congr_of_eventuallyEq hderivHEq
    have hsecondneg : deriv (deriv H) x < 0 := by
      have hEq := hsecondAt.deriv
      rw [hEq]
      exact sub_neg.mpr hgap'
    exact gluingFinFermi_no_negative_interior_min hxIoo hcontH
      (fun y hy => hmin hy) hderivzero hsecondneg
  · have hx0 : x = 0 := not_ne_iff.mp hxne
    have hlocal0 : IsLocalMin
        (fun s => φ s - ε * gluingCollarWarp r s) 0 := by
      simpa [H, F, hx0] using hlocal
    have hφ0 : HasDerivAt φ (p 0) 0 := by
      apply hφ 0
      simpa [hx0] using hx
    exact (gluingFinFermiGraph_no_seam_local_min hε hφ0) hlocal0

/-- A vertical hyperbolic geodesic's transverse graph stays above the fin
profile on bounded intervals, including when the interval crosses the seam. -/
theorem gluingFinFermiVerticalGraph_ge_profile_of_acceleration_with_seam
    {α x r ε a b : ℝ} (hα : 0 < α) (hε : 0 < ε) (hab : a ≤ b)
    (hq : ∀ t ∈ Set.Icc a b,
      gluingFinFermiVerticalTanhGraph α x t ∈ Set.Ioo (-1) 1)
    (hleft : ε * gluingCollarWarp r a ≤
      gluingFinFermiVerticalTransverseGraph α x a)
    (hright : ε * gluingCollarWarp r b ≤
      gluingFinFermiVerticalTransverseGraph α x b)
    (hacc : ∀ t ∈ Set.Icc a b, t ≠ 0 →
      gluingFinFermiGraphAcceleration α
          (ε * gluingCollarWarp r t)
          (ε * deriv (gluingCollarWarp r) t) ≤
        deriv (deriv (fun s => ε * gluingCollarWarp r s)) t) :
    ∀ t ∈ Set.Icc a b,
      ε * gluingCollarWarp r t ≤
        gluingFinFermiVerticalTransverseGraph α x t := by
  apply gluingFinFermiGraph_ge_profile_of_acceleration_with_seam
    hα hε hab (gluingFinFermiVerticalTransverseGraph α x)
      (gluingFinFermiVerticalTransverseGraphSlope α x)
  · intro t ht
    exact gluingFinFermiVerticalTransverseGraph_hasDerivAt hα.ne' (hq t ht)
  · intro t ht
    exact gluingFinFermiVerticalTransverseGraphSlope_acceleration
      hα.ne' (hq t ht)
  · exact hleft
  · exact hright
  · exact hacc

/-- If the fin acceleration dominates on the radial interval of a vertical
hyperbolic geodesic, then the geodesic segment stays in the upper fin. -/
theorem gluingFinFermi_upperFin_geodInterp_vertical_of_acceleration
    {α ε r : ℝ} (hα : 0 < α) (hε : 0 < ε)
    {a b : ℍ} (hre : a.re = b.re)
    (hA : ε * gluingCollarWarp r
        (gluingFinFermiRadialCoord α a) ≤
      gluingFinFermiTransverseCoord α a)
    (hB : ε * gluingCollarWarp r
        (gluingFinFermiRadialCoord α b) ≤
      gluingFinFermiTransverseCoord α b)
    (hacc : ∀ t ∈ Set.uIcc (gluingFinFermiRadialCoord α a)
        (gluingFinFermiRadialCoord α b), t ≠ 0 →
      gluingFinFermiGraphAcceleration α
          (ε * gluingCollarWarp r t)
          (ε * deriv (gluingCollarWarp r) t) ≤
        deriv (deriv (fun s => ε * gluingCollarWarp r s)) t)
    {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
    ε * gluingCollarWarp r
        (gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b s)) ≤
      gluingFinFermiTransverseCoord α
        (Vendored.RiemannDynamics.geodInterp a b s) := by
  let ta := gluingFinFermiRadialCoord α a
  let tb := gluingFinFermiRadialCoord α b
  have hq : ∀ t ∈ Set.uIcc ta tb,
      gluingFinFermiVerticalTanhGraph α a.re t ∈ Set.Ioo (-1) 1 := by
    intro t ht
    obtain ⟨u, hu, hrad⟩ :=
      exists_geodInterp_param_of_radial_mem_uIcc hα a b (by simpa [ta, tb] using ht)
    have hreal : (Vendored.RiemannDynamics.geodInterp a b u).re = a.re := by
      rw [Vendored.RiemannDynamics.geodInterp_vertical hre]
      rfl
    have hcoord := gluingFinFermiVerticalTanhGraph_eq_coord hα
      (Vendored.RiemannDynamics.geodInterp a b u) hreal
    rw [hrad] at hcoord
    rw [hcoord]
    exact ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  have hleft : ε * gluingCollarWarp r ta ≤
      gluingFinFermiVerticalTransverseGraph α a.re ta := by
    simpa [ta] using (hA.trans_eq
      (gluingFinFermiVerticalTransverseGraph_eq_coord hα a rfl).symm)
  have hright : ε * gluingCollarWarp r tb ≤
      gluingFinFermiVerticalTransverseGraph α a.re tb := by
    have hcoord := gluingFinFermiVerticalTransverseGraph_eq_coord hα b hre.symm
    simpa [tb] using hB.trans_eq hcoord.symm
  have hprofile : ∀ t ∈ Set.uIcc ta tb,
      ε * gluingCollarWarp r t ≤
        gluingFinFermiVerticalTransverseGraph α a.re t := by
    rcases le_total ta tb with htab | htba
    ·
      have hdom : ∀ t ∈ Set.Icc ta tb,
          gluingFinFermiVerticalTanhGraph α a.re t ∈ Set.Ioo (-1) 1 :=
        fun t ht => hq t (by simpa only [ta, tb, Set.uIcc_of_le htab] using ht)
      have hbound : ∀ t ∈ Set.Icc ta tb, t ≠ 0 →
          gluingFinFermiGraphAcceleration α
              (ε * gluingCollarWarp r t)
              (ε * deriv (gluingCollarWarp r) t) ≤
            deriv (deriv (fun v => ε * gluingCollarWarp r v)) t := by
        intro t ht ht0
        exact hacc t (by simpa only [ta, tb, Set.uIcc_of_le htab] using ht) ht0
      intro t ht
      exact gluingFinFermiVerticalGraph_ge_profile_of_acceleration_with_seam
        hα hε htab hdom hleft hright hbound t
          (by simpa only [ta, tb, Set.uIcc_of_le htab] using ht)
    · have hdom (t : ℝ) (ht : t ∈ Set.Icc tb ta) :
          gluingFinFermiVerticalTanhGraph α a.re t ∈ Set.Ioo (-1) 1 :=
        hq t (Set.mem_uIcc.mpr (Or.inr ht))
      have hbound (t : ℝ) (ht : t ∈ Set.Icc tb ta) (ht0 : t ≠ 0) :
          gluingFinFermiGraphAcceleration α
              (ε * gluingCollarWarp r t)
              (ε * deriv (gluingCollarWarp r) t) ≤
            deriv (deriv (fun v => ε * gluingCollarWarp r v)) t :=
        hacc t (Set.mem_uIcc.mpr (Or.inr ht)) ht0
      intro t ht
      have ht' : t ∈ Set.Icc tb ta := by
        rcases Set.mem_uIcc.mp ht with h | h
        · exact ⟨le_trans htba h.1, h.2.trans htba⟩
        · exact h
      exact gluingFinFermiVerticalGraph_ge_profile_of_acceleration_with_seam
        hα hε htba hdom hright hleft hbound t
          ht'
  have hradInterp := gluingFinFermiRadialCoord_geodInterp_mono_or_anti hα a b
  have h0 : gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b 0) = ta := by
    simp [ta, Vendored.RiemannDynamics.geodInterp_zero]
  have h1 : gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b 1) = tb := by
    simp [tb, Vendored.RiemannDynamics.geodInterp_one]
  have hradIcc : gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b s) ∈ Set.uIcc ta tb := by
    rcases hradInterp with hm | hm
    · have h0 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 0) = ta := by
        simp [ta, Vendored.RiemannDynamics.geodInterp_zero]
      have h1 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 1) = tb := by
        simp [tb, Vendored.RiemannDynamics.geodInterp_one]
      apply Set.mem_uIcc.mpr
      left
      exact ⟨by rw [← h0]; exact hm hs.1,
        by rw [← h1]; exact hm hs.2⟩
    · have h0 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 0) = ta := by
        simp [ta, Vendored.RiemannDynamics.geodInterp_zero]
      have h1 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 1) = tb := by
        simp [tb, Vendored.RiemannDynamics.geodInterp_one]
      apply Set.mem_uIcc.mpr
      right
      exact ⟨by rw [← h1]; exact hm hs.2,
        by rw [← h0]; exact hm hs.1⟩
  have hprof := hprofile _ hradIcc
  have hreal : (Vendored.RiemannDynamics.geodInterp a b s).re = a.re := by
    rw [Vendored.RiemannDynamics.geodInterp_vertical hre]
    rfl
  have hcoord := gluingFinFermiVerticalTransverseGraph_eq_coord hα
    (Vendored.RiemannDynamics.geodInterp a b s) hreal
  simpa only [hcoord] using hprof

/-- On a fixed radial window, every sufficiently fine dyadic fin is geodesically
convex along vertical upper-half-plane geodesics. -/
theorem eventually_gluingFinFermi_upperFin_geodInterp_vertical
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ a b : ℍ,
      a.re = b.re →
      gluingFinFermiRadialCoord (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a ∈
        Set.Icc (-R) R →
      gluingFinFermiRadialCoord (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b ∈
        Set.Icc (-R) R →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a) ≤
        gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b) ≤
        gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 : ℝ) ^ n * gluingCollarWarp r
            (gluingFinFermiRadialCoord
              (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
              (Vendored.RiemannDynamics.geodInterp a b s)) ≤
          gluingFinFermiTransverseCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
            (Vendored.RiemannDynamics.geodInterp a b s) := by
  obtain ⟨N, hN2, hacc⟩ := gluingCollarFinWarp_dyadic_Fermi_second_deriv_bound hr hR
  refine ⟨N, hN2, fun n hn a b hre ha hb hA hB s hs => ?_⟩
  have hn2 : 2 ≤ n := hN2.trans hn
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  let α : ℝ := Real.sqrt (1 - ε)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := by
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    dsimp [ε]
    norm_num at hpow ⊢
    nlinarith
  have hα : 0 < α := by
    dsimp [α]
    exact Real.sqrt_pos.2 (by linarith)
  have hbound : ∀ t ∈ Set.uIcc
      (gluingFinFermiRadialCoord α a) (gluingFinFermiRadialCoord α b),
      t ≠ 0 →
      gluingFinFermiGraphAcceleration α
          (ε * gluingCollarWarp r t)
          (ε * deriv (gluingCollarWarp r) t) ≤
        deriv (deriv (fun v => ε * gluingCollarWarp r v)) t := by
    intro t ht ht0
    have htWindow : t ∈ Set.Icc (-R) R := by
      rcases Set.mem_uIcc.mp ht with hta | hta
      · exact ⟨ha.1.trans hta.1, hta.2.trans hb.2⟩
      · exact ⟨hb.1.trans hta.1, hta.2.trans ha.2⟩
    simpa [ε, α, gluingFinFermiGraphAcceleration] using hacc n hn t htWindow ht0
  exact gluingFinFermi_upperFin_geodInterp_vertical_of_acceleration
    hα hε hre hA hB hbound hs

/-- The actual circle graph stays above every sufficiently fine dyadic fin
profile on a bounded interval, even when the interval crosses the seam. -/
theorem eventually_gluingFinFermiCircleGraph_ge_dyadic_profile
    {r R a b : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hab : a ≤ b)
    (ha : -R ≤ a) (hb : b ≤ R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ c ρ : ℝ,
      (∀ t ∈ Set.Icc a b,
        gluingFinFermiCircleTanhGraph
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ t ∈ Set.Ioo (-1) 1) →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r a ≤
        gluingFinFermiCircleTransverseGraph
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ a →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r b ≤
        gluingFinFermiCircleTransverseGraph
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ b →
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) ^ n * gluingCollarWarp r t ≤
          gluingFinFermiCircleTransverseGraph
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ t := by
  obtain ⟨N, hN2, hacc⟩ := gluingCollarFinWarp_dyadic_Fermi_second_deriv_bound hr hR
  refine ⟨N, fun n hn c ρ hq hleft hright t ht => ?_⟩
  have hn2 : 2 ≤ n := hN2.trans hn
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := by
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    dsimp [ε]
    norm_num at hpow ⊢
    nlinarith
  have hα : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.2 (by linarith)
  have hcmp := gluingFinFermiCircleGraph_ge_profile_of_acceleration_with_seam
    hα hε hab hq hleft hright (by
      intro s hs hs0
      exact hacc n hn s
        ⟨ha.trans hs.1, hs.2.trans hb⟩ hs0)
  exact hcmp t ht

/-- The circular graph comparison has a dyadic threshold uniform over every
subinterval of the same bounded radial window. This stronger packaging is what
allows the endpoints to vary with the chosen hyperbolic geodesic. -/
theorem eventually_gluingFinFermiCircleGraph_ge_dyadic_profile_uniform
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ a b c ρ : ℝ,
      -R ≤ a → a ≤ b → b ≤ R →
      (∀ t ∈ Set.Icc a b,
        gluingFinFermiCircleTanhGraph
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ t ∈ Set.Ioo (-1) 1) →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r a ≤
        gluingFinFermiCircleTransverseGraph
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ a →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r b ≤
        gluingFinFermiCircleTransverseGraph
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ b →
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) ^ n * gluingCollarWarp r t ≤
          gluingFinFermiCircleTransverseGraph
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) c ρ t := by
  obtain ⟨N, hN2, hacc⟩ := gluingCollarFinWarp_dyadic_Fermi_second_deriv_bound hr hR
  refine ⟨N, hN2, fun n hn a b c ρ hlow hab hhigh hq hleft hright t ht => ?_⟩
  have hn2 : 2 ≤ n := hN2.trans hn
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := by
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    dsimp [ε]
    norm_num at hpow ⊢
    nlinarith
  have hα : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.2 (by linarith)
  have hbound : ∀ s ∈ Set.Icc a b, s ≠ 0 →
      gluingFinFermiGraphAcceleration (Real.sqrt (1 - ε))
          (ε * gluingCollarWarp r s)
          (ε * deriv (gluingCollarWarp r) s) ≤
        deriv (deriv (fun v => ε * gluingCollarWarp r v)) s := by
    intro s hs hs0
    have hsWindow : s ∈ Set.Icc (-R) R :=
      ⟨hlow.trans hs.1, hs.2.trans hhigh⟩
    simpa [ε, gluingFinFermiGraphAcceleration] using hacc n hn s hsWindow hs0
  exact gluingFinFermiCircleGraph_ge_profile_of_acceleration_with_seam
    hα hε hab hq hleft hright hbound t ht

/-- On a fixed radial window, every sufficiently fine dyadic fin is geodesically
convex along non-centered circular hyperbolic geodesics. The threshold is
uniform in the circle and in the radial subinterval swept by its endpoints. -/
theorem eventually_gluingFinFermi_upperFin_geodInterp_circle_nonzeroCenter
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ a b : ℍ,
      a.re ≠ b.re →
      Vendored.RiemannDynamics.geodCenter a b ≠ 0 →
      gluingFinFermiRadialCoord (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a ∈
        Set.Icc (-R) R →
      gluingFinFermiRadialCoord (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b ∈
        Set.Icc (-R) R →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a) ≤
        gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b) ≤
        gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 : ℝ) ^ n * gluingCollarWarp r
            (gluingFinFermiRadialCoord
              (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
              (Vendored.RiemannDynamics.geodInterp a b s)) ≤
          gluingFinFermiTransverseCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
            (Vendored.RiemannDynamics.geodInterp a b s) := by
  obtain ⟨N', hN'2, hprofile⟩ :=
    eventually_gluingFinFermiCircleGraph_ge_dyadic_profile_uniform hr hR
  refine ⟨max N' 2, le_max_right _ _, ?_⟩
  intro n hn a b hre hc ha hb hA hB s hs
  have hnN' : N' ≤ n := le_trans (le_max_left N' 2) hn
  have hn2 : 2 ≤ n := le_trans (le_max_right N' 2) hn
  let ε : ℝ := (1 / 2 : ℝ) ^ n
  let α : ℝ := Real.sqrt (1 - ε)
  let ta : ℝ := gluingFinFermiRadialCoord α a
  let tb : ℝ := gluingFinFermiRadialCoord α b
  let c : ℝ := Vendored.RiemannDynamics.geodCenter a b
  let ρ : ℝ := Vendored.RiemannDynamics.geodRadius a b
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε' : ε < 1 / 2 := by
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    dsimp [ε]
    norm_num at hpow ⊢
    nlinarith
  have hα : 0 < α := by
    dsimp [α]
    exact Real.sqrt_pos.2 (by linarith)
  have hta : -R ≤ ta := by simpa only [ta, α, ε] using ha.1
  have hta' : ta ≤ R := by simpa only [ta, α, ε] using ha.2
  have htb' : -R ≤ tb := by simpa only [tb, α, ε] using hb.1
  have htb : tb ≤ R := by simpa only [tb, α, ε] using hb.2
  have hgraphA : gluingFinFermiTransverseCoord α a =
      gluingFinFermiCircleTransverseGraph α c ρ ta := by
    simpa only [ta, c, ρ, Vendored.RiemannDynamics.geodInterp_zero] using
      gluingFinFermiTransverseCoord_geodInterp_circle_graph hα hre hc 0
  have hgraphB : gluingFinFermiTransverseCoord α b =
      gluingFinFermiCircleTransverseGraph α c ρ tb := by
    simpa only [tb, c, ρ, Vendored.RiemannDynamics.geodInterp_one] using
      gluingFinFermiTransverseCoord_geodInterp_circle_graph hα hre hc 1
  have hleft : ε * gluingCollarWarp r ta ≤
      gluingFinFermiCircleTransverseGraph α c ρ ta := by
    simpa only [ta, ε, α] using hA.trans_eq hgraphA
  have hright : ε * gluingCollarWarp r tb ≤
      gluingFinFermiCircleTransverseGraph α c ρ tb := by
    simpa only [tb, ε, α] using hB.trans_eq hgraphB
  have hq : ∀ t ∈ Set.Icc (min ta tb) (max ta tb),
      gluingFinFermiCircleTanhGraph α c ρ t ∈ Set.Ioo (-1) 1 := by
    intro t ht
    have htU : t ∈ Set.uIcc ta tb := by
      rcases le_total ta tb with htab | htba
      · apply Set.mem_uIcc.mpr
        left
        simpa [min_eq_left htab, max_eq_right htab] using ht
      · apply Set.mem_uIcc.mpr
        right
        simpa [min_eq_right htba, max_eq_left htba] using ht
    obtain ⟨u, hu, hrad⟩ := exists_geodInterp_param_of_radial_mem_uIcc hα a b htU
    have hmem := gluingFinFermiCircleTanhGraph_geodInterp_mem hα hre hc u
    rw [hrad] at hmem
    simpa only [c, ρ] using hmem
  have hprof := hprofile n hnN' (min ta tb) (max ta tb) c ρ
  have hleftSorted : ε * gluingCollarWarp r (min ta tb) ≤
      gluingFinFermiCircleTransverseGraph α c ρ (min ta tb) := by
    rcases le_total ta tb with htab | htba
    · simpa [ε, α, min_eq_left htab] using hleft
    · simpa [ε, α, min_eq_right htba] using hright
  have hrightSorted : ε * gluingCollarWarp r (max ta tb) ≤
      gluingFinFermiCircleTransverseGraph α c ρ (max ta tb) := by
    rcases le_total ta tb with htab | htba
    · simpa [ε, α, max_eq_right htab] using hright
    · simpa [ε, α, max_eq_left htba] using hleft
  have hprof' := hprof (le_min hta htb') min_le_max
    (max_le hta' htb) hq hleftSorted hrightSorted
  have hradMono := gluingFinFermiRadialCoord_geodInterp_circle_mono_or_anti
    hα a b hre
  have hradIcc : gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b s) ∈ Set.uIcc ta tb := by
    rcases hradMono with hm | hm
    · apply Set.mem_uIcc.mpr
      left
      have h0 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 0) = ta := by
        simp [ta, α, ε, Vendored.RiemannDynamics.geodInterp_zero]
      have h1 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 1) = tb := by
        simp [tb, α, ε, Vendored.RiemannDynamics.geodInterp_one]
      exact ⟨by rw [← h0]; exact hm hs.1,
        by rw [← h1]; exact hm hs.2⟩
    · apply Set.mem_uIcc.mpr
      right
      have h0 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 0) = ta := by
        simp [ta, α, ε, Vendored.RiemannDynamics.geodInterp_zero]
      have h1 : gluingFinFermiRadialCoord α
          (Vendored.RiemannDynamics.geodInterp a b 1) = tb := by
        simp [tb, α, ε, Vendored.RiemannDynamics.geodInterp_one]
      exact ⟨by rw [← h1]; exact hm hs.2,
        by rw [← h0]; exact hm hs.1⟩
  have htIcc : gluingFinFermiRadialCoord α
      (Vendored.RiemannDynamics.geodInterp a b s) ∈
        Set.Icc (min ta tb) (max ta tb) := by
    rcases Set.mem_uIcc.mp hradIcc with h | h
    · exact ⟨(min_le_left ta tb).trans h.1,
        h.2.trans (le_max_right ta tb)⟩
    · exact ⟨(min_le_right ta tb).trans h.1,
        h.2.trans (le_max_left ta tb)⟩
  have hbound := hprof' _ htIcc
  have hgraph := gluingFinFermiTransverseCoord_geodInterp_circle_graph
    hα hre hc s
  have hresult : ε * gluingCollarWarp r
      (gluingFinFermiRadialCoord α
        (Vendored.RiemannDynamics.geodInterp a b s)) ≤
      gluingFinFermiTransverseCoord α
        (Vendored.RiemannDynamics.geodInterp a b s) := by
    exact hbound.trans_eq hgraph.symm
  simpa only [ε, α] using hresult

/-- On a fixed radial window, all sufficiently fine dyadic upper fins are
geodesically convex along every upper-half-plane geodesic. The proof splits the
vertical, centered-circle, and non-centered-circle cases. -/
theorem eventually_gluingFinFermi_upperFin_geodInterp
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ a b : ℍ,
      gluingFinFermiRadialCoord (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a ∈
        Set.Icc (-R) R →
      gluingFinFermiRadialCoord (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b ∈
        Set.Icc (-R) R →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a) ≤
        gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) a →
      (1 / 2 : ℝ) ^ n * gluingCollarWarp r
          (gluingFinFermiRadialCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b) ≤
        gluingFinFermiTransverseCoord
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) b →
      ∀ s ∈ Set.Icc (0 : ℝ) 1,
        (1 / 2 : ℝ) ^ n * gluingCollarWarp r
            (gluingFinFermiRadialCoord
              (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
              (Vendored.RiemannDynamics.geodInterp a b s)) ≤
          gluingFinFermiTransverseCoord
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n))
            (Vendored.RiemannDynamics.geodInterp a b s) := by
  obtain ⟨Nv, hNv2, hver⟩ :=
    eventually_gluingFinFermi_upperFin_geodInterp_vertical hr hR
  obtain ⟨Nc, hNc2, hcir⟩ :=
    eventually_gluingFinFermi_upperFin_geodInterp_circle_nonzeroCenter hr hR
  refine ⟨max Nv Nc, le_trans hNv2 (le_max_left Nv Nc), ?_⟩
  intro n hn a b ha hb hA hB s hs
  have hnV : Nv ≤ n := le_trans (le_max_left Nv Nc) hn
  have hnC : Nc ≤ n := le_trans (le_max_right Nv Nc) hn
  have hn2 : 2 ≤ n := le_trans hNv2 hnV
  have hα : 0 < Real.sqrt (1 - (1 / 2 : ℝ) ^ n) := by
    apply Real.sqrt_pos.2
    have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
    norm_num at hpow
    nlinarith
  by_cases hre : a.re = b.re
  · exact hver n hnV a b hre ha hb hA hB s hs
  · by_cases hc : Vendored.RiemannDynamics.geodCenter a b = 0
    · exact gluingFinFermi_upperFin_geodInterp_center_zero hα hre hc hA hB hs
    · exact hcir n hnC a b hre hc ha hb hA hB s hs

#print axioms gluingFinFermiLift_hasFDerivAt
#print axioms gluingFinFermiLift_fderiv_tangentForm_pullback
#print axioms gluingFinFermiLift_fderiv_speed
#print axioms gluingFinFermiPoint_cosh_dist
#print axioms gluingFinFermiPoint_cosh_dist_strictMono_radial_of_abs_sub_lt
#print axioms gluingFinFermiPoint_cosh_dist_strictMono_radial
#print axioms gluingFinFermiPoint_injective
#print axioms gluingFinFermiTransverseCoord_point
#print axioms gluingFinFermiTransverseCoord_tanh
#print axioms gluingFinFermiCircle_tanh_eq_radius_formula
#print axioms gluingFinFermiCircle_tanh_eq_exp_formula
#print axioms gluingFinFermiCircleTanhGraph_hasDerivAt
#print axioms gluingFinFermiCircleTanhGraphDeriv_hasDerivAt
#print axioms gluingFinFermiCircleTransverseGraph_hasDerivAt
#print axioms gluingFinFermiCircleTransverseGraphSlope_hasDerivAt
#print axioms gluingFinFermiCircleTransverseGraphSlope_acceleration
#print axioms gluingFinFermiCircleTransverseGraph_second_derivative
#print axioms gluingFinFermiCircleTransverseGraph_eq_coord
#print axioms gluingFinFermiTransverseCoord_geodInterp_circle_graph
#print axioms gluingFinFermiTransverseCoord_circPoint_center_zero
#print axioms gluingFinFermiRadialCoord_circPoint_center_zero
#print axioms gluingFinFermiCoord_geodInterp_center_zero
#print axioms gluingFinFermi_upperFin_geodInterp_center_zero
#print axioms continuous_gluingFinFermiRadialCoord
#print axioms continuous_gluingFinFermiTransverseCoord
#print axioms exists_geodInterp_param_of_radial_mem_uIcc
#print axioms gluingFinFermiRadialCoord_point
#print axioms gluingFinFermiRadialCoord_circPoint_antitone
#print axioms gluingFinFermiRadialCoord_circPoint_monotone
#print axioms gluingFinFermiRadialCoord_mono_of_im
#print axioms gluingFinFermiRadialCoord_geodInterp_vertical_mono_or_anti
#print axioms gluingFinFermiRadialCoord_geodInterp_circle_mono_or_anti
#print axioms gluingFinFermiRadialCoord_geodInterp_mono_or_anti
#print axioms gluingFinFermiGraphAcceleration_strictMono_height
#print axioms gluingFinFermi_no_negative_interior_min
#print axioms gluingFinFermiGraph_secondDerivative_gap
#print axioms gluingFinFermiProfile_secondDerivative_gap
#print axioms gluingFinFermiCircleGraph_ge_profile_of_acceleration
#print axioms gluingCollarFinWarp_uniform_Fermi_second_deriv_bound
#print axioms gluingCollarFinWarp_dyadic_Fermi_second_deriv_bound
#print axioms gluingFinFermiCircleGraph_no_seam_local_min
#print axioms gluingFinFermiCircleGraph_ge_profile_of_acceleration_with_seam
#print axioms eventually_gluingFinFermiCircleGraph_ge_dyadic_profile
#print axioms gluingFinFermiVerticalTanhGraph_hasDerivAt
#print axioms gluingFinFermiVerticalTanhGraphDeriv_hasDerivAt
#print axioms gluingFinFermiVerticalTransverseGraph_hasDerivAt
#print axioms gluingFinFermiVerticalTransverseGraphSlope_hasDerivAt
#print axioms gluingFinFermiVerticalTransverseGraphSlope_acceleration
#print axioms gluingFinFermiVerticalTransverseGraph_second_derivative
#print axioms gluingFinFermiVerticalTanhGraph_eq_coord
#print axioms gluingFinFermiVerticalTransverseGraph_eq_coord
#print axioms gluingFinFermiGraph_no_seam_local_min
#print axioms gluingFinFermiGraph_ge_profile_of_acceleration_with_seam
#print axioms gluingFinFermiVerticalGraph_ge_profile_of_acceleration_with_seam
#print axioms gluingFinFermi_upperFin_geodInterp_vertical_of_acceleration
#print axioms eventually_gluingFinFermi_upperFin_geodInterp_vertical
#print axioms eventually_gluingFinFermi_upperFin_geodInterp_circle_nonzeroCenter
#print axioms eventually_gluingFinFermi_upperFin_geodInterp
#print axioms eventually_gluingFinFermiCircleGraph_ge_dyadic_profile_uniform

end SystolicGrowth
