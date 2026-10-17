module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarWarp
public import Geometry.GluingCollarCurveIntegrability
public import Geometry.GluingCollarAdmissibleMetric
public import Geometry.LipschitzCoordinateCalculus
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-!
# Clamping radial collar coordinates

The radial clamp leaves the angular coordinate unchanged, is nonexpanding in
the ordinary complex metric, and decreases the collar warping coefficient.
-/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace SystolicGrowth

/-- Clamp a real coordinate to the symmetric interval `[-R, R]`. -/
noncomputable def gluingCollarClampReal (R t : ℝ) : ℝ := max (-R) (min R t)

/-- Clamp the signed radial coordinate and retain the angular coordinate. -/
noncomputable def gluingCollarClamp (R : ℝ) (z : ℂ) : ℂ :=
  ⟨gluingCollarClampReal R z.re, z.im⟩

private theorem gluingCollarClampReal_abs_le {R t : ℝ} (hR : 0 ≤ R) :
    |gluingCollarClampReal R t| ≤ |t| := by
  by_cases hleft : t < -R
  · rw [gluingCollarClampReal, min_eq_right (le_of_lt (by linarith : t < R)),
      max_eq_left (le_of_lt hleft)]
    rw [abs_of_nonpos (by linarith : -R ≤ 0)]
    rw [abs_of_neg (by linarith : t < 0)]
    linarith
  · by_cases hright : R < t
    · rw [gluingCollarClampReal, min_eq_left (le_of_lt hright),
        max_eq_right (by linarith : -R ≤ R)]
      rw [abs_of_nonneg hR, abs_of_pos (by linarith : 0 < t)]
      linarith
    · have hlow : -R ≤ t := le_of_not_gt hleft
      have hupp : t ≤ R := le_of_not_gt hright
      rw [gluingCollarClampReal, min_eq_right hupp, max_eq_right hlow]

theorem gluingCollarClampReal_lipschitz {R : ℝ} :
    LipschitzWith 1 (gluingCollarClampReal R) := by
  change LipschitzWith 1 (fun x : ℝ => max (-R) (min R x))
  simpa only [Function.id_def, min_comm] using
    (LipschitzWith.id.min_const R).const_max (-R)

/-- Radial clamping does not increase ordinary complex distance. -/
theorem gluingCollarClamp_lipschitz (R : ℝ) :
    LipschitzWith 1 (gluingCollarClamp R) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro z w
  have hclamp := (gluingCollarClampReal_lipschitz (R := R)).dist_le_mul z.re w.re
  change dist (gluingCollarClamp R z) (gluingCollarClamp R w) ≤
    (1 : ℝ≥0) * dist z w
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  simp only [gluingCollarClamp]
  have habs : |gluingCollarClampReal R z.re - gluingCollarClampReal R w.re| ≤
      |z.re - w.re| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hclamp
  have hsq : (gluingCollarClampReal R z.re - gluingCollarClampReal R w.re) ^ 2 ≤
      (z.re - w.re) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (gluingCollarClampReal R z.re -
      gluingCollarClampReal R w.re)) (abs_nonneg (z.re - w.re))).mpr habs
    simpa only [sq_abs] using h
  have him : (z.im - w.im) ^ 2 ≤ (z.im - w.im) ^ 2 := le_rfl
  simpa only [NNReal.coe_one, one_mul] using
    (Real.sqrt_le_sqrt (add_le_add hsq him))

/-- The ordinary-coordinate radial clamp is continuous. -/
theorem gluingCollarClamp_continuous (R : ℝ) : Continuous (gluingCollarClamp R) :=
  (gluingCollarClamp_lipschitz R).continuous

/-- Clamping a radial coordinate decreases the collar warp. -/
theorem gluingCollarWarp_clamp_le (r R t : ℝ) (hR : 0 ≤ R) :
    gluingCollarWarp r (gluingCollarClampReal R t) ≤ gluingCollarWarp r t := by
  unfold gluingCollarWarp
  apply Real.sinh_le_sinh.mpr
  have habs := gluingCollarClampReal_abs_le (R := R) (t := t) hR
  linarith

/-- Radial clamping contracts the derivative of every interval-Lipschitz
curve almost everywhere, including at preimages of the clamp corners. -/
theorem gluingCollarClamp_deriv_abs_le_ae {R : ℝ} {u : ℝ → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u (Icc 0 1)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 1),
      |deriv (fun s => gluingCollarClampReal R (u s)) t| ≤ |deriv u t| := by
  let v : ℝ → ℝ := fun s => gluingCollarClampReal R (u s)
  have hv : LipschitzOnWith K v (Icc 0 1) := by
    simpa only [v, Function.comp_def, one_mul] using
      (gluingCollarClampReal_lipschitz (R := R)).comp_lipschitzOnWith hu
  have huIcc : LipschitzOnWith K u (uIcc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using hu
  have hvIcc : LipschitzOnWith K v (uIcc 0 1) := by
    simpa only [uIcc_of_le zero_le_one] using hv
  have huAC := huIcc.absolutelyContinuousOnInterval
  have hvAC := hvIcc.absolutelyContinuousOnInterval
  filter_upwards [ae_restrict_of_ae huAC.ae_differentiableAt,
    ae_restrict_of_ae hvAC.ae_differentiableAt,
    ae_restrict_mem measurableSet_Icc] with t hdu hdv ht
  have ht' : t ∈ uIcc 0 1 := by
    simpa only [uIcc_of_le zero_le_one] using ht
  have hdu' := hdu ht'
  have hdv' := hdv ht'
  have hslope : ∀ s : ℝ, |slope v t s| ≤ |slope u t s| := by
    intro s
    by_cases hst : s = t
    · subst s
      simp [slope]
    · have hdist := (gluingCollarClampReal_lipschitz (R := R)).dist_le_mul
        (u s) (u t)
      have hdist' : |v s - v t| ≤ |u s - u t| := by
        simpa only [v, Real.dist_eq, NNReal.coe_one, one_mul] using hdist
      have hden : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
      rw [slope_def_field, slope_def_field, abs_div, abs_div]
      exact (div_le_div_iff_of_pos_right hden).2 hdist'
  have hlim := le_of_tendsto_of_tendsto
    (hdv'.hasDerivAt.tendsto_slope.abs) (hdu'.hasDerivAt.tendsto_slope.abs)
    (Filter.Eventually.of_forall hslope)
  exact hlim

/-- The actual collar tangent speed decreases almost everywhere under radial
clamping of any ordinary-coordinate Lipschitz curve. -/
theorem gluingCollarClamp_speed_le_ae {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    {K : ℝ≥0} {α : ℝ → ℂ} (hα : LipschitzOnWith K α (Icc 0 1)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 1),
      Real.sqrt (gluingComplexCollarTangentForm r
        (gluingCollarClamp R (α t))
        (deriv (fun s => gluingCollarClamp R (α s)) t)
        (deriv (fun s => gluingCollarClamp R (α s)) t)) ≤
      Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)) := by
  let β : ℝ → ℂ := fun s => gluingCollarClamp R (α s)
  have hβ : LipschitzOnWith K β (Icc 0 1) := by
    simpa only [β, Function.comp_def, one_mul] using
      (gluingCollarClamp_lipschitz R).comp_lipschitzOnWith hα
  have hαre : LipschitzOnWith K (fun s => (α s).re) (Icc 0 1) := by
    simpa [Function.comp_def] using
      (RCLike.lipschitzWith_re (K := ℂ)).comp_lipschitzOnWith hα
  have hαcomp := lipschitzCoordinate_deriv_components_ae zero_le_one hα
  have hβcomp := lipschitzCoordinate_deriv_components_ae zero_le_one hβ
  have hrad := gluingCollarClamp_deriv_abs_le_ae (R := R) hαre
  change ∀ᵐ t ∂volume.restrict (Icc 0 1),
    Real.sqrt (gluingComplexCollarTangentForm r (β t)
      (deriv β t) (deriv β t)) ≤
    Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))
  filter_upwards [hαcomp, hβcomp, hrad] with t hαd hβd hrad
  have hwarp := gluingCollarWarp_clamp_le r R (α t).re hR
  have hwarpPos := gluingCollarWarp_pos hr (α t).re
  have hwarpClampPos := gluingCollarWarp_pos hr (gluingCollarClampReal R (α t).re)
  have hrad' : |deriv (fun s => (β s).re) t| ≤
      |deriv (fun s => (α s).re) t| := by
    simpa [β, gluingCollarClamp] using hrad
  have hradSq :
      (deriv (fun s => (β s).re) t) ^ 2 ≤ (deriv (fun s => (α s).re) t) ^ 2 := by
    have h := (sq_le_sq₀
      (abs_nonneg (deriv (fun s => (β s).re) t))
      (abs_nonneg (deriv (fun s => (α s).re) t))).2 hrad'
    simpa only [sq_abs] using h
  have hwarpSq :
      gluingCollarWarp r (β t).re ^ 2 ≤ gluingCollarWarp r (α t).re ^ 2 := by
    change gluingCollarWarp r (gluingCollarClampReal R (α t).re) ^ 2 ≤ _
    exact (sq_le_sq₀ hwarpClampPos.le hwarpPos.le).2 hwarp
  have himEq : deriv (fun s => (β s).im) t = deriv (fun s => (α s).im) t := by
    have heq : (fun s => (β s).im) = fun s => (α s).im := by
      funext s
      simp [β, gluingCollarClamp]
    rw [heq]
  have hquad :
      (deriv (fun s => (β s).re) t) ^ 2 +
          gluingCollarWarp r (β t).re ^ 2 * (deriv (fun s => (β s).im) t) ^ 2 ≤
        (deriv (fun s => (α s).re) t) ^ 2 +
          gluingCollarWarp r (α t).re ^ 2 * (deriv (fun s => (α s).im) t) ^ 2 := by
    rw [himEq]
    exact add_le_add hradSq
      (mul_le_mul_of_nonneg_right hwarpSq (sq_nonneg _))
  have hsimp (z : ℂ) (v : ℂ) :
      gluingComplexCollarTangentForm r z v v =
        (v.re) ^ 2 + gluingCollarWarp r z.re ^ 2 * (v.im) ^ 2 := by
    rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self]
  change Real.sqrt (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t)) ≤ _
  rw [hsimp, hsimp]
  rw [hβd.1, hβd.2, hαd.1, hαd.2]
  exact Real.sqrt_le_sqrt hquad

/-- Radial clamping contracts the actual weighted length of every
ordinary-coordinate Lipschitz collar curve. -/
theorem gluingCollarClamp_length_le {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    {K : ℝ≥0} {α : ℝ → ℂ} (hα : LipschitzOnWith K α (Icc 0 1)) :
    (∫ t in (0 : ℝ)..1, Real.sqrt (gluingComplexCollarTangentForm r
      (gluingCollarClamp R (α t))
      (deriv (fun s => gluingCollarClamp R (α s)) t)
      (deriv (fun s => gluingCollarClamp R (α s)) t))) ≤
    ∫ t in (0 : ℝ)..1,
      Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)) := by
  let β : ℝ → ℂ := fun s => gluingCollarClamp R (α s)
  have hβ : LipschitzOnWith K β (Icc 0 1) := by
    simpa only [β, Function.comp_def, one_mul] using
      (gluingCollarClamp_lipschitz R).comp_lipschitzOnWith hα
  have hβint := gluingCollarCurve_speed_intervalIntegrable hr zero_le_one hβ
  have hαint := gluingCollarCurve_speed_intervalIntegrable hr zero_le_one hα
  have hspeed : (fun t => Real.sqrt
      (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) ≤ᵐ[
        volume.restrict (Icc 0 1)] (fun t => Real.sqrt
      (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
    filter_upwards [gluingCollarClamp_speed_le_ae hr hR hα] with t ht
    simpa only [β] using ht
  simpa only [β] using
    intervalIntegral.integral_mono_ae_restrict zero_le_one hβint hαint hspeed

/-- The radial clamp is nonexpanding for the actual native collar distance.
The proof contracts every admissible weighted curve and then takes the
defining infimum; it does not infer metric contraction from coordinate
Lipschitz continuity alone. -/
theorem gluingCollarClamp_nativeEDist_le {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (z w : ℂ) :
    gluingCollarModelEDist hr (gluingCollarClamp R z) (gluingCollarClamp R w) ≤
      gluingCollarModelEDist hr z w := by
  rw [← gluingCollarAdmissibleEDist_eq_native hr
      (gluingCollarClamp R z) (gluingCollarClamp R w),
    ← gluingCollarAdmissibleEDist_eq_native hr z w]
  unfold gluingCollarAdmissibleEDist
  refine le_iInf fun α => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun hLip => ?_
  obtain ⟨K, hK⟩ := hLip
  let β : ℝ → ℂ := fun s => gluingCollarClamp R (α s)
  have hβ : LipschitzOnWith K β (Icc 0 1) := by
    simpa only [β, Function.comp_def, one_mul] using
      (gluingCollarClamp_lipschitz R).comp_lipschitzOnWith hK
  have hβ0 : β 0 = gluingCollarClamp R z := by simp [β, h0]
  have hβ1 : β 1 = gluingCollarClamp R w := by simp [β, h1]
  have hspeed : (fun t => Real.sqrt
      (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) ≤ᵐ[
        volume.restrict (Icc 0 1)] (fun t => Real.sqrt
      (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
    filter_upwards [gluingCollarClamp_speed_le_ae hr hR hK] with t ht
    simpa only [β] using ht
  have hlen : (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (Real.sqrt (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t)))) ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
      (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
    apply lintegral_mono_ae
    filter_upwards [hspeed] with t ht
    exact ENNReal.ofReal_le_ofReal ht
  calc
    _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) := by
      exact gluingCollarAdmissibleEDist_le_warp_length r hβ0 hβ1 hβ
    _ ≤ _ := hlen

#print axioms gluingCollarClamp_lipschitz
#print axioms gluingCollarClamp_continuous
#print axioms gluingCollarWarp_clamp_le
#print axioms gluingCollarClamp_deriv_abs_le_ae
#print axioms gluingCollarClamp_speed_le_ae
#print axioms gluingCollarClamp_length_le
#print axioms gluingCollarClamp_nativeEDist_le

end SystolicGrowth
