module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronOscillatoryKernel
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-!
# A pole-free rectangular shift of the scalar Perron contour

For real frequency `L`, the holomorphic function `exp (L*z) / z` has no pole
on a positive real strip. Cauchy--Goursat identifies its vertical integrals
up to the two horizontal edges. This is the contour-shift ingredient for the
negative-frequency (`x/k < 1`) branch of the scalar Perron formula. A shift
across zero requires a separate pole/residue argument.

Source: Montgomery--Vaughan, *Multiplicative Number Theory I*, Section 5.1,
proof of Theorem 5.2, especially the `y ≤ 1/2` contour (printed pp. 139--140).
-/

namespace SystolicGrowth.CookMagyarCircle

open MeasureTheory

/-- The holomorphic integrand behind the scalar Perron contour, written in
the exponential coordinate `L = log y`. -/
noncomputable def perronContourIntegrand (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((L : ℂ) * z) / z

/-- The scalar contour integrand is holomorphic on every closed strip in the
positive half-plane. -/
theorem differentiableOn_perronContourIntegrand_positiveStrip
    (L σ R H : ℝ) (hσ : 0 < σ) (hσR : σ ≤ R) :
    DifferentiableOn ℂ (perronContourIntegrand L)
      (Set.uIcc σ R ×ℂ Set.uIcc (-H) H) := by
  intro z hz
  have hzre : z.re ∈ Set.uIcc σ R := (Complex.mem_reProdIm.mp hz).1
  have hσz : σ ≤ z.re := by
    rw [Set.uIcc_of_le hσR] at hzre
    exact hzre.1
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos (lt_of_lt_of_le hσ hσz)
  have hdiff : DifferentiableAt ℂ (perronContourIntegrand L) z := by
    unfold perronContourIntegrand
    fun_prop (disch := exact hz0)
  exact hdiff.differentiableWithinAt

/-- Cauchy--Goursat on the rectangle with real coordinates `σ,R` and
imaginary coordinates `-H,H`, wholly to the right of the pole. -/
theorem perronContour_positiveStrip_rectangle
    (L σ R H : ℝ) (hσ : 0 < σ) (hσR : σ ≤ R) :
    ((∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + (-H : ℂ) * Complex.I)) -
      (∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + (H : ℂ) * Complex.I)) +
      Complex.I • (∫ t in -H..H, perronContourIntegrand L
        ((R : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I • (∫ t in -H..H, perronContourIntegrand L
        ((σ : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
  let z : ℂ := ⟨σ, -H⟩
  let w : ℂ := ⟨R, H⟩
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronContourIntegrand L) z w
    (differentiableOn_perronContourIntegrand_positiveStrip L σ R H hσ hσR)
  simpa [z, w] using h

/-- A vertical side of the rectangle is an exponential amplitude times
the oscillatory phase kernel. -/
theorem perronContourIntegrand_vertical (L σ t : ℝ) :
    perronContourIntegrand L ((σ : ℂ) + Complex.I * (t : ℂ)) =
      (Real.exp (L * σ) : ℂ) *
        ((((σ : ℂ) + Complex.I * (t : ℂ))⁻¹) *
          Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))) := by
  unfold perronContourIntegrand
  rw [mul_add, Complex.exp_add]
  have hreal : Complex.exp ((L : ℂ) * (σ : ℂ)) = (Real.exp (L * σ) : ℂ) := by
    norm_cast
  rw [hreal]
  ring_nf

/-- The vertical side is exactly the project’s symmetric phase truncation,
with its real exponential amplitude restored. -/
theorem integral_perronContourIntegrand_vertical (L σ H : ℝ) :
    (∫ t in -H..H, perronContourIntegrand L
      ((σ : ℂ) + Complex.I * (t : ℂ))) =
      (Real.exp (L * σ) : ℂ) * perronPhaseTruncation σ L H := by
  simp_rw [perronContourIntegrand_vertical]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- For a nonpositive frequency, the scalar contour integrand on a
horizontal edge is controlled by its value at the left real coordinate. -/
theorem norm_perronContourIntegrand_horizontal_le (L σ u t : ℝ)
    (hL : L ≤ 0) (hσu : σ ≤ u) (ht : 0 < |t|) :
    ‖perronContourIntegrand L ((u : ℂ) + Complex.I * (t : ℂ))‖ ≤
      Real.exp (L * σ) / |t| := by
  have hden : |t| ≤ ‖(u : ℂ) + Complex.I * (t : ℂ)‖ := by
    simpa using Complex.abs_im_le_norm ((u : ℂ) + Complex.I * (t : ℂ))
  have hLu : L * u ≤ L * σ := mul_le_mul_of_nonpos_left hσu hL
  have hnum : Real.exp (L * u) ≤ Real.exp (L * σ) := Real.exp_le_exp.mpr hLu
  calc
    ‖perronContourIntegrand L ((u : ℂ) + Complex.I * (t : ℂ))‖
        = Real.exp (L * u) / ‖(u : ℂ) + Complex.I * (t : ℂ)‖ := by
          simp [perronContourIntegrand, Complex.norm_exp]
    _ ≤ Real.exp (L * σ) / ‖(u : ℂ) + Complex.I * (t : ℂ)‖ := by
          exact (div_le_div_iff_of_pos_right (lt_of_lt_of_le ht hden)).mpr hnum
    _ ≤ Real.exp (L * σ) / |t| := by
          exact div_le_div_of_nonneg_left (Real.exp_nonneg _) ht hden

/-- The two horizontal edges in a fixed positive strip vanish as contour
height grows; this is their quantitative `1 / |t|` bound. -/
theorem norm_integral_perronContourIntegrand_horizontal_le (L σ R t : ℝ)
    (hL : L ≤ 0) (hσR : σ ≤ R) (ht : 0 < |t|) :
    ‖∫ u in σ..R, perronContourIntegrand L
      ((u : ℂ) + Complex.I * (t : ℂ))‖ ≤
      (Real.exp (L * σ) / |t|) * (R - σ) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := σ) (b := R) (C := Real.exp (L * σ) / |t|)
    (f := fun u : ℝ => perronContourIntegrand L
      ((u : ℂ) + Complex.I * (t : ℂ))) (by
      intro u hu
      have hu' : u ∈ Set.Ioc σ R := by simpa only [Set.uIoc_of_le hσR] using hu
      exact norm_perronContourIntegrand_horizontal_le L σ u t hL hu'.1.le ht)
  simpa [abs_of_nonneg (sub_nonneg.mpr hσR)] using h

private theorem tendsto_integral_perronContour_horizontal_top
    (L σ R : ℝ) (hL : L ≤ 0) (hσR : σ ≤ R) :
    Filter.Tendsto (fun H : ℝ =>
      ∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + Complex.I * (H : ℂ))) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let C : ℝ := Real.exp (L * σ) * (R - σ)
  have hbound : ∀ᶠ H : ℝ in Filter.atTop,
      ‖∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + Complex.I * (H : ℂ))‖ ≤ C / H := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with H hH
    have ht : 0 < |H| := by simpa [abs_of_pos hH] using hH
    calc
      _ ≤ (Real.exp (L * σ) / |H|) * (R - σ) :=
        norm_integral_perronContourIntegrand_horizontal_le L σ R H hL hσR ht
      _ = C / H := by simp [C, abs_of_pos hH]; ring
  have hzero : Filter.Tendsto (fun H : ℝ => C / H) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul C)
  exact squeeze_zero' (Filter.Eventually.of_forall fun H => norm_nonneg _)
    hbound hzero

private theorem tendsto_integral_perronContour_horizontal_bottom
    (L σ R : ℝ) (hL : L ≤ 0) (hσR : σ ≤ R) :
    Filter.Tendsto (fun H : ℝ =>
      ∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + Complex.I * (-H : ℂ))) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  let C : ℝ := Real.exp (L * σ) * (R - σ)
  have hbound : ∀ᶠ H : ℝ in Filter.atTop,
      ‖∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + Complex.I * (-H : ℂ))‖ ≤ C / H := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with H hH
    have ht : 0 < |-H| := by simpa [abs_neg, abs_of_pos hH] using hH
    calc
      _ ≤ (Real.exp (L * σ) / |-H|) * (R - σ) := by
        simpa using
          norm_integral_perronContourIntegrand_horizontal_le L σ R (-H) hL hσR ht
      _ = C / H := by simp [C, abs_neg, abs_of_pos hH]; ring
  have hzero : Filter.Tendsto (fun H : ℝ => C / H) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul C)
  exact squeeze_zero' (Filter.Eventually.of_forall fun H => norm_nonneg _)
    hbound hzero

private theorem integral_perronContourIntegrand_vertical_right (L σ H : ℝ) :
    (∫ t in -H..H, perronContourIntegrand L
      ((σ : ℂ) + (t : ℂ) * Complex.I)) =
      (Real.exp (L * σ) : ℂ) * perronPhaseTruncation σ L H := by
  convert integral_perronContourIntegrand_vertical L σ H using 1
  congr 1
  funext t
  congr 1
  ring

/-- Shifting the infinite-height scalar contour between two positive
abscissae does not change the value after its exponential amplitude is
restored. The horizontal edges vanish by the proved `1/H` estimate. -/
theorem perronPhaseContourLimit_abscissa_shift_of_neg
    (L σ R : ℝ) (hL : L < 0) (hσ : 0 < σ) (hσR : σ ≤ R) :
    (Real.exp (L * R) : ℂ) * perronPhaseContourLimit R L =
      (Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L := by
  have hB : Filter.Tendsto (fun H : ℝ =>
      ∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + (-H : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    convert tendsto_integral_perronContour_horizontal_bottom L σ R hL.le hσR using 1
    funext H
    congr 1
    funext u
    congr 1
    ring
  have hT : Filter.Tendsto (fun H : ℝ =>
      ∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + (H : ℂ) * Complex.I)) Filter.atTop (nhds 0) := by
    convert tendsto_integral_perronContour_horizontal_top L σ R hL.le hσR using 1
    funext H
    congr 1
    funext u
    congr 1
    ring
  let F : ℝ → ℂ := fun H =>
    ((∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + (-H : ℂ) * Complex.I)) -
      (∫ u in σ..R, perronContourIntegrand L
        ((u : ℂ) + (H : ℂ) * Complex.I)) +
      Complex.I • ((Real.exp (L * R) : ℂ) * perronPhaseTruncation R L H) -
      Complex.I • ((Real.exp (L * σ) : ℂ) * perronPhaseTruncation σ L H))
  have hrect (H : ℝ) : F H = 0 := by
    dsimp [F]
    have h := perronContour_positiveStrip_rectangle L σ R H hσ hσR
    rw [integral_perronContourIntegrand_vertical_right L R H,
      integral_perronContourIntegrand_vertical_right L σ H] at h
    exact h
  have hVR : Filter.Tendsto
      (fun H : ℝ => (Real.exp (L * R) : ℂ) * perronPhaseTruncation R L H)
      Filter.atTop
      (nhds ((Real.exp (L * R) : ℂ) * perronPhaseContourLimit R L)) :=
    (tendsto_perronPhaseTruncation R L (lt_of_lt_of_le hσ hσR) hL.ne).const_mul _
  have hVσ : Filter.Tendsto
      (fun H : ℝ => (Real.exp (L * σ) : ℂ) * perronPhaseTruncation σ L H)
      Filter.atTop
      (nhds ((Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L)) :=
    (tendsto_perronPhaseTruncation σ L hσ hL.ne).const_mul _
  have hlim0 := ((hB.sub hT).add (hVR.const_smul Complex.I)).sub
    (hVσ.const_smul Complex.I)
  have hlim : Filter.Tendsto F Filter.atTop
      (nhds ((0 : ℂ) - 0 + Complex.I • ((Real.exp (L * R) : ℂ) *
          perronPhaseContourLimit R L) -
        Complex.I • ((Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L))) := by
    simpa only [F] using hlim0
  have hzero : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have heq : F = fun _ => (0 : ℂ) := funext hrect
    rw [heq]
    exact tendsto_const_nhds
  have hval := tendsto_nhds_unique hlim hzero
  simp only [sub_zero, zero_add] at hval
  have hmul : (Complex.I : ℂ) *
      ((Real.exp (L * R) : ℂ) * perronPhaseContourLimit R L -
        (Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L) = 0 := by
    simpa [smul_eq_mul, mul_sub] using hval
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero)

/- TASK-SLOT PERRON-NEGATIVE (COMPLETE): P01, P02, P03, P04 are proved below,
in dependency order. They are reference patterns, not open assignments.
P01 bounds the height-one truncation; P02 bounds the infinite limit for R ≥ 1;
P03 sends the exponentially weighted negative-frequency limit to zero;
P04 uses the proved abscissa shift to evaluate that limit. No new placeholders.
The positive-frequency value is proved separately in PerronResidueJump.lean. -/

/-- P01: a height-one phase contour is bounded uniformly in its frequency
when the real abscissa is at least one. -/
theorem norm_perronPhaseTruncation_one_le_two
    (R L : ℝ) (hR : 1 ≤ R) :
    ‖perronPhaseTruncation R L 1‖ ≤ 2 := by
  have hpoint (t : ℝ) :
      ‖((((R : ℂ) + Complex.I * (t : ℂ))⁻¹) *
          Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ)))‖ ≤ 1 := by
    have hRnorm : R ≤ ‖(R : ℂ) + Complex.I * (t : ℂ)‖ := by
      simpa using Complex.re_le_norm ((R : ℂ) + Complex.I * (t : ℂ))
    have hden : (1 : ℝ) ≤ ‖(R : ℂ) + Complex.I * (t : ℂ)‖ :=
      hR.trans hRnorm
    have hphase :
        ‖Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, norm_inv, hphase, mul_one]
    exact inv_le_one_of_one_le₀ hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 : ℝ)) (b := 1) (C := 1)
    (f := fun t : ℝ => (((R : ℂ) + Complex.I * (t : ℂ))⁻¹) *
      Complex.exp ((Complex.I * (L : ℂ)) * (t : ℂ)))
    (fun t _ => hpoint t)
  norm_num at h
  simpa [perronPhaseTruncation] using h

/-- P02: the infinite-height phase contour is uniformly bounded on real
abscissae at least one, for a fixed nonzero frequency. -/
theorem norm_perronPhaseContourLimit_abscissa_ge_one_le
    (R L : ℝ) (hR : 1 ≤ R) (hL : L ≠ 0) :
    ‖perronPhaseContourLimit R L‖ ≤ 18 / |L| + 2 := by
  have hRpos : 0 < R := by linarith
  have htail :
      ‖perronPhaseContourLimit R L - perronPhaseTruncation R L 1‖ ≤
        18 / |L| := by
    simpa only [one_mul] using
      norm_perronPhaseContourLimit_sub_truncation_le R L 1 hRpos hL (by norm_num)
  have htriangle :
      ‖perronPhaseContourLimit R L‖ ≤
        ‖perronPhaseContourLimit R L - perronPhaseTruncation R L 1‖ +
          ‖perronPhaseTruncation R L 1‖ := by
    calc
      ‖perronPhaseContourLimit R L‖ =
          ‖(perronPhaseContourLimit R L - perronPhaseTruncation R L 1) +
            perronPhaseTruncation R L 1‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  exact htriangle.trans (add_le_add htail (norm_perronPhaseTruncation_one_le_two R L hR))

/-- P03: for a negative frequency, the exponentially weighted contour
limit vanishes as the abscissa moves to the right. -/
theorem tendsto_weighted_perronPhaseContourLimit_of_neg
    (L : ℝ) (hL : L < 0) :
    Filter.Tendsto
      (fun R : ℝ => (Real.exp (L * R) : ℂ) * perronPhaseContourLimit R L)
      Filter.atTop (nhds 0) := by
  have hdecay : Filter.Tendsto
      (fun R : ℝ => Real.exp (L * R) * (18 / |L| + 2))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.tendsto_exp_atBot.comp
        ((Filter.tendsto_id : Filter.Tendsto (fun R : ℝ => R) Filter.atTop Filter.atTop).const_mul_atTop_of_neg hL)).mul_const (18 / |L| + 2)
  have hbound : ∀ᶠ R : ℝ in Filter.atTop,
      ‖(Real.exp (L * R) : ℂ) * perronPhaseContourLimit R L‖ ≤
        Real.exp (L * R) * (18 / |L| + 2) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (norm_perronPhaseContourLimit_abscissa_ge_one_le R L hR hL.ne)
      (Real.exp_nonneg _)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hdecay

/-- P04: the infinite-height phase contour vanishes at negative frequency. -/
theorem perronPhaseContourLimit_eq_zero_of_neg
    (σ L : ℝ) (hσ : 0 < σ) (hL : L < 0) :
    perronPhaseContourLimit σ L = 0 := by
  have hevent :
      (fun R : ℝ => (Real.exp (L * R) : ℂ) * perronPhaseContourLimit R L) =ᶠ[Filter.atTop]
        (fun _ : ℝ => (Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L) := by
    filter_upwards [Filter.eventually_ge_atTop σ] with R hσR
    exact perronPhaseContourLimit_abscissa_shift_of_neg L σ R hL hσ hσR
  have hconst : Filter.Tendsto
      (fun _ : ℝ => (Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L)
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' hevent (tendsto_weighted_perronPhaseContourLimit_of_neg L hL)
  have hzero : (Real.exp (L * σ) : ℂ) * perronPhaseContourLimit σ L = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  have hExp : (Real.exp (L * σ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.exp_ne_zero (L * σ)
  exact (mul_eq_zero.mp hzero).resolve_left hExp

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.differentiableOn_perronContourIntegrand_positiveStrip
#print axioms SystolicGrowth.CookMagyarCircle.perronContour_positiveStrip_rectangle
#print axioms SystolicGrowth.CookMagyarCircle.perronContourIntegrand_vertical
#print axioms SystolicGrowth.CookMagyarCircle.integral_perronContourIntegrand_vertical
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronContourIntegrand_horizontal_le
#print axioms SystolicGrowth.CookMagyarCircle.norm_integral_perronContourIntegrand_horizontal_le
#print axioms SystolicGrowth.CookMagyarCircle.perronPhaseContourLimit_abscissa_shift_of_neg
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronPhaseTruncation_one_le_two
#print axioms SystolicGrowth.CookMagyarCircle.norm_perronPhaseContourLimit_abscissa_ge_one_le
#print axioms SystolicGrowth.CookMagyarCircle.tendsto_weighted_perronPhaseContourLimit_of_neg
#print axioms SystolicGrowth.CookMagyarCircle.perronPhaseContourLimit_eq_zero_of_neg
