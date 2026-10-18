module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronScalarContour
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# The scalar Perron jump across the pole

The quotient `(exp (L*z)-1)/z` extends holomorphically across zero as a
`dslope`. Its integral around a symmetric rectangle therefore vanishes.
Separating the reciprocal term gives the jump between positive- and
negative-frequency vertical contours, without deforming a circle into
the rectangle or treating the pole as holomorphic.
-/

open Filter MeasureTheory

namespace SystolicGrowth.CookMagyarCircle

/-- The symmetric vertical reciprocal integral is a real arctangent.
Both the strict positive abscissa and the exact `-H..H` endpoints matter. -/
theorem integral_perronVerticalInv_eq_two_arctan
    (σ H : ℝ) (hσ : 0 < σ) :
    (∫ t in -H..H, (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)) =
      ((2 * Real.arctan (H / σ) : ℝ) : ℂ) := by
  have hden (t : ℝ) : σ ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hnorm (t : ℝ) :
      Complex.normSq ((σ : ℂ) + Complex.I * (t : ℂ)) = σ ^ 2 + t ^ 2 := by
    simpa only [mul_comm Complex.I] using Complex.normSq_add_mul_I σ t
  have hpoint (t : ℝ) :
      (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) =
        (((σ / (σ ^ 2 + t ^ 2)) : ℝ) : ℂ) -
          Complex.I * (((t / (σ ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.inv_re, hnorm, Complex.mul_re]
      norm_cast
      simp
    · simp [Complex.inv_im, hnorm, Complex.mul_im]
      norm_cast
      ring
  have hcontR : Continuous (fun t : ℝ => σ / (σ ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hcontI : Continuous (fun t : ℝ => t / (σ ^ 2 + t ^ 2)) := by
    fun_prop (disch := exact hden _)
  have hcontRC : Continuous (fun t : ℝ => (((σ / (σ ^ 2 + t ^ 2)) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hcontR
  have hcontIC : Continuous (fun t : ℝ =>
      Complex.I * (((t / (σ ^ 2 + t ^ 2)) : ℝ) : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp hcontI)
  have hodd : (∫ t in -H..H, t / (σ ^ 2 + t ^ 2)) = 0 := by
    have hneg := intervalIntegral.integral_comp_neg
      (f := fun t : ℝ => t / (σ ^ 2 + t ^ 2)) (a := -H) (b := H)
    simp only [neg_neg] at hneg
    have hpointNeg (t : ℝ) :
        -t / (σ ^ 2 + (-t) ^ 2) = -(t / (σ ^ 2 + t ^ 2)) := by ring
    simp_rw [hpointNeg] at hneg
    rw [intervalIntegral.integral_neg] at hneg
    linarith
  have hreal :
      (∫ t in -H..H, σ / (σ ^ 2 + t ^ 2)) =
        2 * Real.arctan (H / σ) := by
    rw [integral_div_sq_add_sq]
    rw [show -H / σ = -(H / σ) by ring, Real.arctan_neg]
    ring
  calc
    (∫ t in -H..H, (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)) =
        ∫ t in -H..H,
          (((σ / (σ ^ 2 + t ^ 2)) : ℝ) : ℂ) -
            Complex.I * (((t / (σ ^ 2 + t ^ 2)) : ℝ) : ℂ) := by
              apply intervalIntegral.integral_congr
              intro t _
              exact hpoint t
    _ = _ := by
      rw [intervalIntegral.integral_sub
        (hcontRC.intervalIntegrable _ _)
        (hcontIC.intervalIntegrable _ _),
        intervalIntegral.integral_ofReal,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal,
        hreal, hodd]
      simp

/-- The entire extension of `(exp (L*z)-1)/z` at the removable point `0`. -/
noncomputable def perronRegularizedContourIntegrand (L : ℝ) (z : ℂ) : ℂ :=
  dslope (fun w : ℂ => Complex.exp ((L : ℂ) * w)) 0 z

theorem perronRegularizedContourIntegrand_eq_of_ne
    (L : ℝ) (z : ℂ) (hz : z ≠ 0) :
    perronRegularizedContourIntegrand L z =
      (Complex.exp ((L : ℂ) * z) - 1) / z := by
  simp [perronRegularizedContourIntegrand, dslope_of_ne _ hz, slope_def_field]

/-- The removable quotient is holomorphic even on a rectangle crossing
zero. This is why rectangular Cauchy--Goursat applies to it. -/
theorem differentiable_perronRegularizedContourIntegrand (L : ℝ) :
    Differentiable ℂ (perronRegularizedContourIntegrand L) := by
  have h : DifferentiableOn ℂ (perronRegularizedContourIntegrand L) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ))
      (by simp)).2 (by
        intro z hz
        fun_prop)
  exact differentiableOn_univ.mp h

/-- A horizontal edge of the regularized rectangle has a uniform `1/|t|`
bound. The upper real coordinate `σ` controls its exponential numerator. -/
theorem norm_perronRegularizedContourIntegrand_horizontal_le
    (L σ u t : ℝ) (hL : 0 < L) (hu : u ≤ σ) (ht : 0 < |t|) :
    ‖perronRegularizedContourIntegrand L
      ((u : ℂ) + Complex.I * (t : ℂ))‖ ≤
        (Real.exp (L * σ) + 1) / |t| := by
  let z : ℂ := (u : ℂ) + Complex.I * (t : ℂ)
  have hz : z ≠ 0 := by
    apply ne_of_apply_ne Complex.im
    simpa [z] using (abs_pos.mp ht)
  have hden : |t| ≤ ‖z‖ := by
    simpa [z] using Complex.abs_im_le_norm z
  have hnum : ‖Complex.exp ((L : ℂ) * z) - 1‖ ≤
      Real.exp (L * σ) + 1 := by
    calc
      ‖Complex.exp ((L : ℂ) * z) - 1‖ ≤
          ‖Complex.exp ((L : ℂ) * z)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp (L * u) + 1 := by simp [Complex.norm_exp, z]
      _ ≤ Real.exp (L * σ) + 1 := by
        linarith [Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hu hL.le)]
  calc
    ‖perronRegularizedContourIntegrand L z‖ =
        ‖Complex.exp ((L : ℂ) * z) - 1‖ / ‖z‖ := by
          rw [perronRegularizedContourIntegrand_eq_of_ne L z hz, norm_div]
    _ ≤ (Real.exp (L * σ) + 1) / ‖z‖ := by
          exact (div_le_div_iff_of_pos_right (lt_of_lt_of_le ht hden)).mpr hnum
    _ ≤ (Real.exp (L * σ) + 1) / |t| := by
          exact div_le_div_of_nonneg_left (by positivity) ht hden

/-- Quantitative vanishing bound for either horizontal side of the
cross-zero rectangle. -/
theorem norm_integral_perronRegularized_horizontal_le
    (L σ t : ℝ) (hL : 0 < L) (hσ : 0 < σ) (ht : 0 < |t|) :
    ‖∫ u in -σ..σ, perronRegularizedContourIntegrand L
      ((u : ℂ) + Complex.I * (t : ℂ))‖ ≤
        ((Real.exp (L * σ) + 1) / |t|) * (2 * σ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -σ) (b := σ) (C := (Real.exp (L * σ) + 1) / |t|)
    (f := fun u : ℝ => perronRegularizedContourIntegrand L
      ((u : ℂ) + Complex.I * (t : ℂ))) (by
      intro u hu
      have hu' : u ∈ Set.Ioc (-σ) σ := by
        simpa only [Set.uIoc_of_le (by linarith : -σ ≤ σ)] using hu
      exact norm_perronRegularizedContourIntegrand_horizontal_le
        L σ u t hL hu'.2 ht)
  simpa [abs_of_pos (by linarith : 0 < σ + σ), two_mul] using h

private theorem tendsto_integral_perronRegularized_horizontal_top
    (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) :
    Filter.Tendsto (fun H : ℝ =>
      ∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + Complex.I * (H : ℂ))) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let C : ℝ := (Real.exp (L * σ) + 1) * (2 * σ)
  have hbound : ∀ᶠ H : ℝ in Filter.atTop,
      ‖∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + Complex.I * (H : ℂ))‖ ≤ C / H := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with H hH
    calc
      _ ≤ ((Real.exp (L * σ) + 1) / |H|) * (2 * σ) :=
        norm_integral_perronRegularized_horizontal_le L σ H hL hσ
          (by simpa [abs_of_pos hH] using hH)
      _ = C / H := by simp [C, abs_of_pos hH]; ring
  have hzero : Filter.Tendsto (fun H : ℝ => C / H) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul C)
  exact squeeze_zero' (Filter.Eventually.of_forall fun H => norm_nonneg _)
    hbound hzero

private theorem tendsto_integral_perronRegularized_horizontal_bottom
    (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) :
    Filter.Tendsto (fun H : ℝ =>
      ∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + Complex.I * (-H : ℂ))) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let C : ℝ := (Real.exp (L * σ) + 1) * (2 * σ)
  have hbound : ∀ᶠ H : ℝ in Filter.atTop,
      ‖∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + Complex.I * (-H : ℂ))‖ ≤ C / H := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with H hH
    calc
      _ ≤ ((Real.exp (L * σ) + 1) / |-H|) * (2 * σ) := by
        simpa only [Complex.ofReal_neg] using
          norm_integral_perronRegularized_horizontal_le L σ (-H) hL hσ
            (by simpa [abs_neg, abs_of_pos hH] using hH)
      _ = C / H := by simp [C, abs_neg, abs_of_pos hH]; ring
  have hzero : Filter.Tendsto (fun H : ℝ => C / H) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul C)
  exact squeeze_zero' (Filter.Eventually.of_forall fun H => norm_nonneg _)
    hbound hzero

/-- Reflection of the vertical phase integral converts a negative
abscissa to a positive abscissa with the opposite frequency. -/
theorem perronPhaseTruncation_neg_abscissa
    (σ L H : ℝ) :
    perronPhaseTruncation (-σ) L H =
      -perronPhaseTruncation σ (-L) H := by
  unfold perronPhaseTruncation
  let f : ℝ → ℂ := fun t =>
    ((((-σ : ℝ) : ℂ) + Complex.I * (t : ℂ))⁻¹) *
      Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))
  have hcomp := intervalIntegral.integral_comp_neg (f := f) (a := -H) (b := H)
  simp only [neg_neg] at hcomp
  change (∫ t in -H..H, f t) = _
  rw [← hcomp]
  have hpoint (t : ℝ) :
      f (-t) = -
        (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹ *
          Complex.exp ((Complex.I * ((-L : ℝ) : ℂ)) * (t : ℂ))) := by
    have hden : (((-σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
        -((σ : ℂ) + Complex.I * (t : ℂ)) := by push_cast; ring
    have hexp : (Complex.I * (L : ℂ)) * ((-t : ℝ) : ℂ) =
        (Complex.I * ((-L : ℝ) : ℂ)) * (t : ℂ) := by push_cast; ring
    simp only [f, hden, hexp, inv_neg]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg]

/-- A regularized vertical side is the ordinary exponential contour minus
the reciprocal vertical integral. -/
theorem integral_perronRegularized_vertical
    (L s H : ℝ) (hs : s ≠ 0) :
    (∫ t in -H..H, perronRegularizedContourIntegrand L
      ((s : ℂ) + Complex.I * (t : ℂ))) =
      (Real.exp (L * s) : ℂ) * perronPhaseTruncation s L H -
        ∫ t in -H..H, (((s : ℂ) + Complex.I * (t : ℂ))⁻¹) := by
  have hzne (t : ℝ) : (s : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    apply ne_of_apply_ne Complex.re
    simpa using hs
  have hpoint (t : ℝ) :
      perronRegularizedContourIntegrand L
        ((s : ℂ) + Complex.I * (t : ℂ)) =
      perronContourIntegrand L ((s : ℂ) + Complex.I * (t : ℂ)) -
        (((s : ℂ) + Complex.I * (t : ℂ))⁻¹) := by
    rw [perronRegularizedContourIntegrand_eq_of_ne L _ (hzne t)]
    simp [perronContourIntegrand, sub_div, one_div]
  simp_rw [hpoint]
  have hcont1 : Continuous (fun t : ℝ =>
      perronContourIntegrand L ((s : ℂ) + Complex.I * (t : ℂ))) := by
    unfold perronContourIntegrand
    fun_prop (disch := exact hzne _)
  have hcont2 : Continuous (fun t : ℝ =>
      (((s : ℂ) + Complex.I * (t : ℂ))⁻¹)) := by
    fun_prop (disch := exact hzne _)
  rw [intervalIntegral.integral_sub
    (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _),
    integral_perronContourIntegrand_vertical]

/-- Reflection changes the sign of the reciprocal vertical side. -/
theorem integral_perronVerticalInv_neg_abscissa (σ H : ℝ) :
    (∫ t in -H..H, ((((-σ : ℝ) : ℂ) + Complex.I * (t : ℂ))⁻¹)) =
      -(∫ t in -H..H, (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)) := by
  have h := intervalIntegral.integral_comp_neg
    (f := fun t : ℝ => ((((-σ : ℝ) : ℂ) + Complex.I * (t : ℂ))⁻¹))
    (a := -H) (b := H)
  simp only [neg_neg] at h
  rw [← h]
  have hpoint (t : ℝ) :
      ((((-σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ))⁻¹) =
        -((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)) := by
    have hden : (((-σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
        -((σ : ℂ) + Complex.I * (t : ℂ)) := by push_cast; ring
    rw [hden, inv_neg]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_neg]

/-- The exact counterclockwise reciprocal boundary integral of a rectangle
crossing the real pole at zero; this is a finite-height identity. -/
theorem perronReciprocal_crossZero_rectangle
    (a b H : ℝ) (ha : a < 0) (hb : 0 < b) (hH : 0 < H) :
    ((∫ u in a..b, (((u : ℂ) + (-H : ℂ) * Complex.I)⁻¹)) -
      (∫ u in a..b, (((u : ℂ) + (H : ℂ) * Complex.I)⁻¹)) +
      Complex.I • (∫ t in -H..H, (((b : ℂ) + (t : ℂ) * Complex.I)⁻¹)) -
      Complex.I • (∫ t in -H..H, (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹))) =
        (2 * Real.pi * Complex.I : ℂ) := by
  have hright :
      (∫ t in -H..H, (((b : ℂ) + (t : ℂ) * Complex.I)⁻¹)) =
        ((2 * Real.arctan (H / b) : ℝ) : ℂ) := by
    simpa only [mul_comm Complex.I] using
      integral_perronVerticalInv_eq_two_arctan b H hb
  have hleft :
      (∫ t in -H..H, (((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)) =
        ((2 * Real.arctan (H / a) : ℝ) : ℂ) := by
    have h := integral_perronVerticalInv_neg_abscissa (-a) H
    rw [integral_perronVerticalInv_eq_two_arctan (-a) H (neg_pos.mpr ha)] at h
    simpa only [neg_neg, div_neg, Real.arctan_neg, mul_neg,
      Complex.ofReal_neg, mul_comm Complex.I] using h
  have hbottom : Continuous (fun u : ℝ =>
      (((u : ℂ) + (-H : ℂ) * Complex.I)⁻¹)) := by
    apply Continuous.inv₀
    · fun_prop
    · intro u heq
      have h := congrArg Complex.im heq
      simp at h
      linarith
  have htop : Continuous (fun u : ℝ =>
      (((u : ℂ) + (H : ℂ) * Complex.I)⁻¹)) := by
    apply Continuous.inv₀
    · fun_prop
    · intro u heq
      have h := congrArg Complex.im heq
      simp at h
      linarith
  have hpoint (u : ℝ) :
      (((u : ℂ) + (-H : ℂ) * Complex.I)⁻¹) -
        (((u : ℂ) + (H : ℂ) * Complex.I)⁻¹) =
      Complex.I * (((2 * (H / (H ^ 2 + u ^ 2))) : ℝ) : ℂ) := by
    apply Complex.ext
    all_goals
      simp only [Complex.sub_re, Complex.sub_im, Complex.inv_re, Complex.inv_im,
        Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, Complex.neg_re, Complex.neg_im, zero_mul, mul_zero,
        mul_one, one_mul, add_zero, zero_add, sub_zero, neg_zero]
      ring
  have hhorizontal :
      (∫ u in a..b, (((u : ℂ) + (-H : ℂ) * Complex.I)⁻¹)) -
        (∫ u in a..b, (((u : ℂ) + (H : ℂ) * Complex.I)⁻¹)) =
      Complex.I * ((2 * (Real.arctan (b / H) - Real.arctan (a / H)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_sub
      (hbottom.intervalIntegrable _ _) (htop.intervalIntegrable _ _)]
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_const_mul, integral_div_sq_add_sq]
  have hrightAngle : Real.arctan (H / b) = Real.pi / 2 - Real.arctan (b / H) := by
    have h := Real.arctan_inv_of_pos (div_pos hb hH)
    simpa only [inv_div] using h
  have hleftAngle : Real.arctan (H / a) = -(Real.pi / 2) - Real.arctan (a / H) := by
    have h := Real.arctan_inv_of_neg (div_neg_of_neg_of_pos ha hH)
    simpa only [inv_div] using h
  rw [hhorizontal, hright, hleft, hrightAngle, hleftAngle]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

#print axioms perronReciprocal_crossZero_rectangle

/-- Translation of the finite-height kernel to any real pole. -/
theorem perronReciprocal_realPole_rectangle
    (σL σR β H : ℝ) (hleft : σL < β) (hright : β < σR) (hH : 0 < H) :
    ((∫ u in σL..σR, (((u : ℂ) + (-H : ℂ) * Complex.I - (β : ℂ))⁻¹)) -
      (∫ u in σL..σR, (((u : ℂ) + (H : ℂ) * Complex.I - (β : ℂ))⁻¹)) +
      Complex.I • (∫ t in -H..H,
        (((σR : ℂ) + (t : ℂ) * Complex.I - (β : ℂ))⁻¹)) -
      Complex.I • (∫ t in -H..H,
        (((σL : ℂ) + (t : ℂ) * Complex.I - (β : ℂ))⁻¹))) =
        (2 * Real.pi * Complex.I : ℂ) := by
  have hpoint (u t : ℝ) :
      (((u : ℂ) + (t : ℂ) * Complex.I - (β : ℂ))⁻¹) =
        (((u - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹ := by
    congr 1
    push_cast
    ring
  have hhorizontal (t : ℝ) :
      (∫ u in σL..σR, ((((u - β : ℝ) : ℂ) + (t : ℂ) * Complex.I)⁻¹)) =
      ∫ u in σL - β..σR - β, (((u : ℂ) + (t : ℂ) * Complex.I)⁻¹) :=
    intervalIntegral.integral_comp_sub_right
      (fun u : ℝ => (((u : ℂ) + (t : ℂ) * Complex.I)⁻¹)) β
  simp_rw [← Complex.ofReal_neg, hpoint]
  rw [hhorizontal (-H), hhorizontal H]
  simpa only [Complex.ofReal_neg] using
    perronReciprocal_crossZero_rectangle (σL - β) (σR - β) H
    (by linarith) (by linarith) hH

#print axioms perronReciprocal_realPole_rectangle

/-- The entire quotient has zero integral around the rectangle crossing
the deleted pole of the original Perron integrand. -/
theorem perronRegularized_crossZero_rectangle (L σ H : ℝ) :
    ((∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + (-H : ℂ) * Complex.I)) -
      (∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + (H : ℂ) * Complex.I)) +
      Complex.I • (∫ t in -H..H, perronRegularizedContourIntegrand L
        ((σ : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I • (∫ t in -H..H, perronRegularizedContourIntegrand L
        (((-σ : ℝ) : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
  let z : ℂ := ⟨-σ, -H⟩
  let w : ℂ := ⟨σ, H⟩
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronRegularizedContourIntegrand L) z w
    ((differentiable_perronRegularizedContourIntegrand L).differentiableOn)
  simpa [z, w] using h

private theorem integral_perronRegularized_vertical_right
    (L s H : ℝ) (hs : s ≠ 0) :
    (∫ t in -H..H, perronRegularizedContourIntegrand L
      ((s : ℂ) + (t : ℂ) * Complex.I)) =
      (Real.exp (L * s) : ℂ) * perronPhaseTruncation s L H -
        ∫ t in -H..H, (((s : ℂ) + Complex.I * (t : ℂ))⁻¹) := by
  convert integral_perronRegularized_vertical L s H hs using 1
  congr 1
  funext t
  congr 1
  ring_nf

private theorem integral_perronRegularized_vertical_left
    (L σ H : ℝ) (hσ : 0 < σ) :
    (∫ t in -H..H, perronRegularizedContourIntegrand L
      (((-σ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      -(Real.exp (-(L * σ)) : ℂ) * perronPhaseTruncation σ (-L) H +
        ∫ t in -H..H, (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) := by
  rw [integral_perronRegularized_vertical_right L (-σ) H (by linarith),
    perronPhaseTruncation_neg_abscissa,
    integral_perronVerticalInv_neg_abscissa]
  simp only [mul_neg, sub_neg_eq_add, mul_neg]
  congr 1
  ring_nf

/-- The reciprocal side tends to `π`, exactly the half-circle contribution
at the pole. -/
theorem tendsto_integral_perronVerticalInv
    (σ : ℝ) (hσ : 0 < σ) :
    Filter.Tendsto (fun H : ℝ =>
      ∫ t in -H..H, (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹))
      Filter.atTop (nhds (Real.pi : ℂ)) := by
  have harg : Filter.Tendsto (fun H : ℝ => H / σ) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const hσ tendsto_id
  have hatan : Filter.Tendsto (fun H : ℝ => Real.arctan (H / σ))
      Filter.atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
  have hreal : Filter.Tendsto (fun H : ℝ => 2 * Real.arctan (H / σ))
      Filter.atTop (nhds Real.pi) := by
    convert hatan.const_mul 2 using 1
    ring_nf
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hcomplex using 1
  · funext H
    exact integral_perronVerticalInv_eq_two_arctan σ H hσ

/-- The cross-zero jump of the two infinite-height scalar contours. The
residue is isolated as the difference of the two reciprocal vertical sides. -/
theorem perronPhaseContourLimit_crossZero_jump
    (σ L : ℝ) (hσ : 0 < σ) (hL : 0 < L) :
    (Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L +
      (Real.exp (-(L * σ)) : ℂ) * perronPhaseContourLimit σ (-L) =
        (2 * Real.pi : ℂ) := by
  have hB : Filter.Tendsto (fun H : ℝ =>
      ∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + (-H : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    convert tendsto_integral_perronRegularized_horizontal_bottom L σ hL hσ using 1
    funext H
    congr 1
    funext u
    congr 1
    ring
  have hT : Filter.Tendsto (fun H : ℝ =>
      ∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + (H : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    convert tendsto_integral_perronRegularized_horizontal_top L σ hL hσ using 1
    funext H
    congr 1
    funext u
    congr 1
    ring
  let B : ℝ → ℂ := fun H =>
    ∫ t in -H..H, (((σ : ℂ) + Complex.I * (t : ℂ))⁻¹)
  let F : ℝ → ℂ := fun H =>
    ((∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + (-H : ℂ) * Complex.I)) -
      (∫ u in -σ..σ, perronRegularizedContourIntegrand L
        ((u : ℂ) + (H : ℂ) * Complex.I)) +
      Complex.I • ((Real.exp (L * σ) : ℂ) * perronPhaseTruncation σ L H - B H) -
      Complex.I • (-(Real.exp (-(L * σ)) : ℂ) *
        perronPhaseTruncation σ (-L) H + B H))
  have hrect (H : ℝ) : F H = 0 := by
    dsimp [F]
    have h := perronRegularized_crossZero_rectangle L σ H
    rw [integral_perronRegularized_vertical_right L σ H hσ.ne',
      integral_perronRegularized_vertical_left L σ H hσ] at h
    exact h
  have hInv : Filter.Tendsto B Filter.atTop (nhds (Real.pi : ℂ)) :=
    tendsto_integral_perronVerticalInv σ hσ
  have hPpos : Filter.Tendsto
      (fun H : ℝ => (Real.exp (L * σ) : ℂ) * perronPhaseTruncation σ L H)
      Filter.atTop
      (nhds ((Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L)) :=
    (tendsto_perronPhaseTruncation σ L hσ hL.ne').const_mul _
  have hPneg : Filter.Tendsto
      (fun H : ℝ => (Real.exp (-(L * σ)) : ℂ) * perronPhaseTruncation σ (-L) H)
      Filter.atTop
      (nhds ((Real.exp (-(L * σ)) : ℂ) * perronPhaseContourLimit σ (-L))) :=
    (tendsto_perronPhaseTruncation σ (-L) hσ (by linarith)).const_mul _
  have hlim0 := ((hB.sub hT).add ((hPpos.sub hInv).const_smul Complex.I)).sub
    ((hPneg.neg.add hInv).const_smul Complex.I)
  have hlim : Filter.Tendsto F Filter.atTop
      (nhds (((0 : ℂ) - 0 +
        Complex.I • ((Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L -
          (Real.pi : ℂ))) -
        Complex.I • (-(Real.exp (-(L * σ)) : ℂ) *
          perronPhaseContourLimit σ (-L) + (Real.pi : ℂ)))) := by
    simpa only [F, B, neg_mul] using hlim0
  have hzero : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have heq : F = fun _ => (0 : ℂ) := funext hrect
    rw [heq]
    exact tendsto_const_nhds
  have hval := tendsto_nhds_unique hlim hzero
  simp only [sub_zero, zero_add] at hval
  have hmul : (Complex.I : ℂ) *
      ((Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L +
        (Real.exp (-(L * σ)) : ℂ) * perronPhaseContourLimit σ (-L) -
        (2 * Real.pi : ℂ)) = 0 := by
    convert hval using 1; simp [smul_eq_mul]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero)

/-- Positive-frequency scalar Perron contour value. The zero on the
negative-frequency side is the separately proved pole-free shift theorem. -/
theorem perronPhaseContourLimit_eq_of_pos
    (σ L : ℝ) (hσ : 0 < σ) (hL : 0 < L) :
    perronPhaseContourLimit σ L =
      ((2 * Real.pi * Real.exp (-σ * L) : ℝ) : ℂ) := by
  have hjump := perronPhaseContourLimit_crossZero_jump σ L hσ hL
  rw [perronPhaseContourLimit_eq_zero_of_neg σ (-L) hσ (by linarith),
    mul_zero, add_zero] at hjump
  have hExp : (Real.exp (L * σ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (L * σ)
  have hproduct : (Real.exp (L * σ) : ℂ) *
      ((2 * Real.pi * Real.exp (-σ * L) : ℝ) : ℂ) =
        (2 * Real.pi : ℂ) := by
    norm_cast
    rw [show -σ * L = -(L * σ) by ring]
    calc
      Real.exp (L * σ) * (2 * Real.pi * Real.exp (-(L * σ))) =
          (Real.exp (L * σ) * Real.exp (-(L * σ))) * (2 * Real.pi) := by ring
      _ = 2 * Real.pi := by rw [← Real.exp_add]; simp
  exact (mul_left_cancel₀ hExp) (hjump.trans hproduct.symm)

/-- P08: restoring the scalar amplitude turns the phase-contour value into
the inclusive half-integer Perron indicator. The value is unnormalized. -/
theorem perronHalfInteger_amplitude_mul_contourLimit
    (m k : ℕ) (σ : ℝ) (hk : 0 < k) (hσ : 0 < σ) :
    (((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
        perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) =
      if k ≤ m then (2 * Real.pi : ℂ) else 0 := by
  let x : ℝ := (m : ℝ) + 1 / 2
  let y : ℝ := x / (k : ℝ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hy : 0 < y := div_pos hx hkR
  change ((y ^ σ : ℝ) : ℂ) * perronPhaseContourLimit σ (Real.log y) =
    if k ≤ m then (2 * Real.pi : ℂ) else 0
  by_cases hkm : k ≤ m
  · have hkx : (k : ℝ) < x := (perronHalfInteger_lt_iff m k).2 hkm
    have hlog : 0 < Real.log y := Real.log_pos ((one_lt_div hkR).2 hkx)
    rw [if_pos hkm, perronPhaseContourLimit_eq_of_pos σ (Real.log y) hσ hlog]
    norm_cast
    rw [Real.rpow_def_of_pos hy]
    calc
      Real.exp (Real.log y * σ) *
          (2 * Real.pi * Real.exp (-σ * Real.log y)) =
          (Real.exp (Real.log y * σ) *
            Real.exp (-σ * Real.log y)) * (2 * Real.pi) := by ring
      _ = 2 * Real.pi := by
        rw [← Real.exp_add]
        rw [show Real.log y * σ + -σ * Real.log y = 0 by ring]
        simp
  · have hmk : m + 1 ≤ k := by omega
    have hmkR : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hmk
    have hxk : x < (k : ℝ) := by dsimp [x]; linarith
    have hlog : Real.log y < 0 :=
      Real.log_neg hy ((div_lt_one hkR).2 hxk)
    rw [if_neg hkm, perronPhaseContourLimit_eq_zero_of_neg σ (Real.log y) hσ hlog,
      mul_zero]

#print axioms integral_perronVerticalInv_eq_two_arctan
#print axioms perronRegularizedContourIntegrand_eq_of_ne
#print axioms differentiable_perronRegularizedContourIntegrand
#print axioms norm_perronRegularizedContourIntegrand_horizontal_le
#print axioms norm_integral_perronRegularized_horizontal_le
#print axioms perronPhaseTruncation_neg_abscissa
#print axioms integral_perronRegularized_vertical
#print axioms integral_perronVerticalInv_neg_abscissa
#print axioms perronRegularized_crossZero_rectangle
#print axioms tendsto_integral_perronVerticalInv
#print axioms perronPhaseContourLimit_crossZero_jump
#print axioms perronPhaseContourLimit_eq_of_pos
#print axioms perronHalfInteger_amplitude_mul_contourLimit

end SystolicGrowth.CookMagyarCircle
