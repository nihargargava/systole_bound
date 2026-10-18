module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingDeckMetric
public import Vendored.RiemannDynamics.Hyperbolic.PlaneGeometry.TriangleArea
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Genuine smooth segments realizing hyperbolic distance

Actual determinant-one transformations normalize the two endpoints to a
vertical line. A log-linear exponential-height curve, transported back by
the inverse transformation, realizes the Poincare distance with constant
coordinate speed. The construction also controls every intermediate point.
-/

open Set MeasureTheory UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups ENNReal

namespace SystolicGrowth

set_option backward.isDefEq.respectTransparency false

/-- Exponential-height parametrization of a vertical hyperbolic line. -/
noncomputable def hyperbolicVerticalSegment (a u v t : ℝ) : ℂ :=
  (a : ℂ) + (Real.exp ((1 - t) * u + t * v) : ℂ) * Complex.I

@[simp] theorem hyperbolicVerticalSegment_im (a u v t : ℝ) :
    (hyperbolicVerticalSegment a u v t).im = Real.exp ((1 - t) * u + t * v) := by
  simp only [hyperbolicVerticalSegment, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
    mul_zero, add_zero, zero_add]

theorem hyperbolicVerticalSegment_im_pos (a u v t : ℝ) :
    0 < (hyperbolicVerticalSegment a u v t).im := by
  simp only [hyperbolicVerticalSegment_im]
  exact Real.exp_pos _

theorem hyperbolicVerticalSegment_contDiff (a u v : ℝ) :
    ContDiff ℝ 1 (hyperbolicVerticalSegment a u v) := by
  unfold hyperbolicVerticalSegment
  apply contDiff_const.add
  have hlin : ContDiff ℝ 1 (fun t : ℝ => (1 - t) * u + t * v) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp hlin)).mul contDiff_const

set_option backward.isDefEq.respectTransparency false in
theorem hyperbolicVerticalSegment_hasDerivAt (a u v t : ℝ) :
    HasDerivAt (hyperbolicVerticalSegment a u v)
      ((Real.exp ((1 - t) * u + t * v) * (v - u) : ℝ) * Complex.I) t := by
  have h : HasDerivAt (fun s : ℝ => (1 - s) * u + s * v) (v - u) t := by
    convert!
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const u).add
        ((hasDerivAt_id t).mul_const v) using 1
    simp only [zero_sub, one_mul, neg_mul, neg_add_eq_sub]
  exact
    ((h.exp.ofReal_comp).mul_const Complex.I).const_add (a : ℂ)

theorem hyperbolicVerticalSegment_speed (a u v t : ℝ) :
    ‖deriv (hyperbolicVerticalSegment a u v) t‖ /
      (hyperbolicVerticalSegment a u v t).im = |v - u| := by
  rw [(hyperbolicVerticalSegment_hasDerivAt a u v t).deriv,
    hyperbolicVerticalSegment_im, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

/-- Genuine determinant-one derivative invariance of Poincare speed. -/
theorem gluingDeckComplexDeriv_poincare_speed (γ : SL(2, ℝ)) (z : ℍ) (v : ℂ) :
    ‖gluingDeckComplexDerivEquiv γ (z : ℂ) z.im_pos v‖ / (γ • z : ℍ).im =
      ‖v‖ / z.im := by
  have hd : ‖(γ 1 0 : ℂ) * (z : ℂ) + (γ 1 1 : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gluingDeckComplex_denom_ne_zero γ z.im_pos)
  rw [gluingDeckComplexDerivEquiv_apply, norm_mul, gluingDeckComplexDeriv,
    norm_div, norm_one, norm_pow, gluingDeckComplex_im_smul]
  field_simp [hd, z.im_pos.ne']

/-- Every endpoint pair has an actual special-linear vertical normalization. -/
theorem exists_hyperbolic_vertical_normalization (z w : ℍ) :
    ∃ γ : SL(2, ℝ), (γ • z : ℍ).re = (γ • w : ℍ).re := by
  by_cases h : z.re = w.re
  · exact ⟨1, by simpa only [one_smul] using h⟩
  · obtain ⟨γ, hz, hw⟩ := Vendored.RiemannDynamics.exists_smul_re_eq_zero h
    exact ⟨γ, hz.trans hw.symm⟩

/-- The native half-plane lift of the explicit exponential vertical curve. -/
noncomputable def hyperbolicVerticalSegmentPoint (a u v t : ℝ) : ℍ :=
  ⟨hyperbolicVerticalSegment a u v t, hyperbolicVerticalSegment_im_pos a u v t⟩

@[simp] theorem hyperbolicVerticalSegmentPoint_re (a u v t : ℝ) :
    (hyperbolicVerticalSegmentPoint a u v t).re = a := by
  simp only [hyperbolicVerticalSegmentPoint, UpperHalfPlane.mk_re,
    hyperbolicVerticalSegment, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp] theorem hyperbolicVerticalSegmentPoint_im (a u v t : ℝ) :
    (hyperbolicVerticalSegmentPoint a u v t).im = Real.exp ((1 - t) * u + t * v) :=
  hyperbolicVerticalSegment_im a u v t

theorem hyperbolicVerticalSegmentPoint_dist (a u v s t : ℝ) :
    dist (hyperbolicVerticalSegmentPoint a u v s)
      (hyperbolicVerticalSegmentPoint a u v t) = |s - t| * |v - u| := by
  rw [UpperHalfPlane.dist_of_re_eq (by simp), hyperbolicVerticalSegmentPoint_im,
    hyperbolicVerticalSegmentPoint_im, Real.log_exp, Real.log_exp, Real.dist_eq]
  have h : ((1 - s) * u + s * v) - ((1 - t) * u + t * v) =
      (s - t) * (v - u) := by ring
  rw [h, abs_mul]

theorem hyperbolicVerticalSegmentPoint_zero (z w : ℍ) :
    hyperbolicVerticalSegmentPoint z.re (Real.log z.im) (Real.log w.im) 0 = z := by
  apply UpperHalfPlane.ext_re_im
  · simp
  · simp only [hyperbolicVerticalSegmentPoint_im, sub_zero, one_mul, zero_mul,
      add_zero, Real.exp_log z.im_pos]

theorem hyperbolicVerticalSegmentPoint_one (z w : ℍ) (h : z.re = w.re) :
    hyperbolicVerticalSegmentPoint z.re (Real.log z.im) (Real.log w.im) 1 = w := by
  apply UpperHalfPlane.ext_re_im
  · simpa using h
  · simp only [hyperbolicVerticalSegmentPoint_im, sub_self, zero_mul, one_mul,
      zero_add, Real.exp_log w.im_pos]

/-- An actual smooth upper-half-plane segment has constant Poincare speed
equal to the endpoint distance and realizes that distance at every time. -/
theorem exists_hyperbolic_constantSpeed_segment (z w : ℍ) :
    ∃ α : ℝ → ℂ, ContDiff ℝ 1 α ∧ (∀ t, 0 < (α t).im) ∧
      α 0 = (z : ℂ) ∧ α 1 = (w : ℂ) ∧
      (∀ t, ‖deriv α t‖ / (α t).im = dist z w) ∧
      (∀ s t, dist (UpperHalfPlane.ofComplex (α s))
        (UpperHalfPlane.ofComplex (α t)) = |s - t| * dist z w) := by
  obtain ⟨γ, hγ⟩ := exists_hyperbolic_vertical_normalization z w
  let z' : ℍ := γ • z
  let w' : ℍ := γ • w
  let β := hyperbolicVerticalSegment z'.re (Real.log z'.im) (Real.log w'.im)
  let p := hyperbolicVerticalSegmentPoint z'.re (Real.log z'.im) (Real.log w'.im)
  let α := gluingDeckComplex γ⁻¹ ∘ β
  have hβ : ContDiff ℝ 1 β := hyperbolicVerticalSegment_contDiff _ _ _
  have hcoe (t : ℝ) : α t = ((γ⁻¹ • p t : ℍ) : ℂ) :=
    gluingDeckComplex_coe γ⁻¹ (p t)
  have him (t : ℝ) : 0 < (α t).im := by
    rw [hcoe]
    exact (γ⁻¹ • p t : ℍ).im_pos
  have hsmooth : ContDiff ℝ 1 α := by
    apply contDiff_iff_contDiffAt.mpr
    intro t
    exact ((gluingDeckComplex_contDiffAt γ⁻¹
      (hyperbolicVerticalSegment_im_pos _ _ _ t)).of_le (by simp)).comp t hβ.contDiffAt
  have h0 : α 0 = (z : ℂ) := by
    rw [hcoe]
    dsimp only [p]
    rw [hyperbolicVerticalSegmentPoint_zero]
    simp only [z', inv_smul_smul]
  have h1 : α 1 = (w : ℂ) := by
    rw [hcoe]
    dsimp only [p]
    rw [hyperbolicVerticalSegmentPoint_one z' w' hγ]
    simp only [w', inv_smul_smul]
  have hscale : |Real.log w'.im - Real.log z'.im| = dist z w := by
    rw [← dist_smul γ z w, UpperHalfPlane.dist_of_re_eq hγ, Real.dist_eq,
      abs_sub_comm]
  have hspeed (t : ℝ) : ‖deriv α t‖ / (α t).im = dist z w := by
    have hd := (gluingDeckComplex_hasFDerivAt_equiv γ⁻¹ (p t).im_pos).comp_hasDerivAt t
      (hyperbolicVerticalSegment_hasDerivAt _ _ _ t)
    have hderiv : deriv α t = gluingDeckComplexDerivEquiv γ⁻¹ (p t)
        (p t).im_pos (deriv β t) := by
      rw [(hyperbolicVerticalSegment_hasDerivAt _ _ _ t).deriv]
      exact hd.deriv
    rw [hderiv, hcoe, UpperHalfPlane.coe_im]
    exact (gluingDeckComplexDeriv_poincare_speed γ⁻¹ (p t) (deriv β t)).trans
      ((hyperbolicVerticalSegment_speed _ _ _ t).trans hscale)
  have hdist (s t : ℝ) : dist (UpperHalfPlane.ofComplex (α s))
      (UpperHalfPlane.ofComplex (α t)) = |s - t| * dist z w := by
    rw [hcoe, hcoe, UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply,
      dist_smul, hyperbolicVerticalSegmentPoint_dist, hscale]
  exact ⟨α, hsmooth, him, h0, h1, hspeed, hdist⟩

/-- Smooth curves with exact Poincare length between arbitrary endpoints.
The intermediate-point bound is part of the same genuine construction. -/
theorem exists_hyperbolic_length_realizing_segment (z w : ℍ) :
    ∃ α : ℝ → ℂ, ContDiff ℝ 1 α ∧ (∀ t, 0 < (α t).im) ∧
      α 0 = (z : ℂ) ∧ α 1 = (w : ℂ) ∧
      (∫⁻ t in Icc (0 : ℝ) 1,
        ENNReal.ofReal (‖deriv α t‖ / (α t).im)) = edist z w ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        dist z (UpperHalfPlane.ofComplex (α t)) = t * dist z w) := by
  obtain ⟨α, hsmooth, him, h0, h1, hspeed, hdist⟩ :=
    exists_hyperbolic_constantSpeed_segment z w
  refine ⟨α, hsmooth, him, h0, h1, ?_, ?_⟩
  · simp only [hspeed, MeasureTheory.setLIntegral_const, Real.volume_Icc,
      sub_zero, ENNReal.ofReal_one, mul_one, ← edist_dist]
  · intro t ht
    simpa only [h0, UpperHalfPlane.ofComplex_apply, zero_sub, abs_neg,
      abs_of_nonneg ht.1] using hdist 0 t

#print axioms hyperbolicVerticalSegment_contDiff
#print axioms hyperbolicVerticalSegment_speed
#print axioms gluingDeckComplexDeriv_poincare_speed
#print axioms exists_hyperbolic_vertical_normalization
#print axioms exists_hyperbolic_constantSpeed_segment
#print axioms exists_hyperbolic_length_realizing_segment

end SystolicGrowth
