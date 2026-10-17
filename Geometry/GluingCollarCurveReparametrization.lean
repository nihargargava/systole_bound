module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLipschitzLength
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-!
# Affine normalization of Lipschitz collar-coordinate curves

Affine normalization sends every ordered compact parameter interval to the
unit interval and preserves its actual weighted speed integral. Ordinary
complex Lipschitz continuity and derivatives remain separate from the native
collar metric. The zero-length interval is included; neither endpoint
differentiability nor C¹ regularity of admissible curves is assumed.
-/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace SystolicGrowth

/-- The ordinary affine normalization of the parameter interval. -/
noncomputable def gluingCollarNormalizeCurve (a b : ℝ) (α : ℝ → ℂ) (t : ℝ) : ℂ :=
  α (a + (b - a) * t)

@[simp] theorem gluingCollarNormalizeCurve_zero (a b : ℝ) (α : ℝ → ℂ) :
    gluingCollarNormalizeCurve a b α 0 = α a := by simp [gluingCollarNormalizeCurve]

@[simp] theorem gluingCollarNormalizeCurve_one (a b : ℝ) (α : ℝ → ℂ) :
    gluingCollarNormalizeCurve a b α 1 = α b := by simp [gluingCollarNormalizeCurve]

private theorem normalize_parameter_mem {a b t : ℝ} (hab : a ≤ b)
    (ht : t ∈ Icc 0 1) : a + (b - a) * t ∈ Icc a b := by
  have hd := sub_nonneg.mpr hab
  have hlo := mul_nonneg hd ht.1
  have hhi := mul_le_mul_of_nonneg_left ht.2 hd
  constructor <;> nlinarith

/-- Every interval-Lipschitz coordinate curve normalizes to an ordinary
Lipschitz curve on the unit interval, with the actual rescaled constant. -/
theorem gluingCollarNormalizeCurve_lipschitzOnWith {a b : ℝ} {K : ℝ≥0}
    {α : ℝ → ℂ} (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    LipschitzOnWith (K * Real.toNNReal (b - a))
      (gluingCollarNormalizeCurve a b α) (Icc 0 1) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  have hd := sub_nonneg.mpr hab
  have h := hα.dist_le_mul (a + (b - a) * s) (normalize_parameter_mem hab hs)
    (a + (b - a) * t) (normalize_parameter_mem hab ht)
  have hsub : (a + (b - a) * s) - (a + (b - a) * t) = (b - a) * (s - t) := by ring
  simp only [Real.dist_eq, hsub, abs_mul, abs_of_nonneg hd] at h
  simpa only [gluingCollarNormalizeCurve, NNReal.coe_mul, Real.coe_toNNReal _ hd,
    Real.dist_eq, mul_assoc] using h

/-- Affine composition respects the actual totalized derivative, even at
nondifferentiable points and for a zero interval. -/
theorem gluingCollarNormalizeCurve_deriv (a b : ℝ) (α : ℝ → ℂ) (t : ℝ) :
    deriv (gluingCollarNormalizeCurve a b α) t =
      (b - a) • deriv α (a + (b - a) * t) := by
  unfold gluingCollarNormalizeCurve
  rw [deriv_comp_mul_left (b - a) (fun s => α (a + s)) t,
    deriv_comp_const_add α a]

private theorem normalized_speed {a b : ℝ} (hab : a ≤ b) (r : ℝ)
    (α : ℝ → ℂ) (t : ℝ) :
    Real.sqrt (gluingComplexCollarTangentForm r (gluingCollarNormalizeCurve a b α t)
      (deriv (gluingCollarNormalizeCurve a b α) t)
      (deriv (gluingCollarNormalizeCurve a b α) t)) =
      (b - a) * Real.sqrt (gluingComplexCollarTangentForm r (α (a + (b - a) * t))
        (deriv α (a + (b - a) * t)) (deriv α (a + (b - a) * t))) := by
  rw [← gluingCollarFrozenVelocity_norm, gluingCollarNormalizeCurve_deriv,
    map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab),
    gluingCollarFrozenVelocity_norm]
  rfl

/-- Actual weighted real length is preserved under affine normalization.
This identity needs no differentiability or integrability premise because
the affine derivative and substitution formulas are unconditional. -/
theorem gluingCollarNormalizeCurve_integral_speed {a b : ℝ} (hab : a ≤ b)
    (r : ℝ) (α : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..1, Real.sqrt (gluingComplexCollarTangentForm r
      (gluingCollarNormalizeCurve a b α t) (deriv (gluingCollarNormalizeCurve a b α) t)
        (deriv (gluingCollarNormalizeCurve a b α) t))) =
      ∫ t in a..b, Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t)) := by
  simp_rw [normalized_speed hab]
  rw [intervalIntegral.integral_const_mul]
  simpa only [smul_eq_mul, mul_zero, add_zero, mul_one,
    show a + (b - a) = b by ring] using
    intervalIntegral.smul_integral_comp_add_mul
      (fun t => Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)))
      (b - a) a (a := (0 : ℝ)) (b := 1)

/-- The closed-interval extended weighted integral is also unchanged for
every Lipschitz coordinate curve, including a degenerate parameter interval. -/
theorem gluingCollarNormalizeCurve_lintegral_speed {r a b : ℝ} (hr : 0 < r)
    {K : ℝ≥0} {α : ℝ → ℂ} (hab : a ≤ b) (hα : LipschitzOnWith K α (Icc a b)) :
    (∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (gluingComplexCollarTangentForm r
      (gluingCollarNormalizeCurve a b α t) (deriv (gluingCollarNormalizeCurve a b α) t)
        (deriv (gluingCollarNormalizeCurve a b α) t)))) =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t))) := by
  have hnorm := gluingCollarNormalizeCurve_lipschitzOnWith hab hα
  have hi := gluingCollarCurve_speed_intervalIntegrable hr hab hα
  have hn := gluingCollarCurve_speed_intervalIntegrable hr zero_le_one hnorm
  have heq {c d : ℝ} {β : ℝ → ℂ} (hcd : c ≤ d)
      (hint : IntervalIntegrable (fun t => Real.sqrt
        (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) volume c d) :
      ENNReal.ofReal (∫ t in c..d, Real.sqrt
        (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) =
          ∫⁻ t in Icc c d, ENNReal.ofReal (Real.sqrt
            (gluingComplexCollarTangentForm r (β t) (deriv β t) (deriv β t))) := by
    rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp hint)
      (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg _))
  rw [← heq zero_le_one hn, ← heq hab hi,
    gluingCollarNormalizeCurve_integral_speed hab]

/-- Native collar distance is bounded by genuine weighted length on every
ordered interval. Lipschitz continuity refers only to ambient coordinates. -/
theorem gluingCollarModelMetric_dist_le_interval_lipschitz_length {r a b : ℝ}
    (hr : 0 < r) {K : ℝ≥0} {α : ℝ → ℂ} (hab : a ≤ b)
    (hα : LipschitzOnWith K α (Icc a b)) :
    @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α a) (α b) ≤
      ∫ t in a..b, Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t)) := by
  have h := gluingCollarModelMetric_dist_le_lipschitz_length hr
    (gluingCollarNormalizeCurve_lipschitzOnWith hab hα)
  rw [gluingCollarNormalizeCurve_zero, gluingCollarNormalizeCurve_one,
    gluingCollarNormalizeCurve_integral_speed hab] at h
  exact h

/-- Extended native collar distance obeys the same actual weighted bound
on every ordered compact parameter interval. -/
theorem gluingCollarModelEDist_le_interval_lipschitz_warp_length {r a b : ℝ}
    (hr : 0 < r) {K : ℝ≥0} {α : ℝ → ℂ} (hab : a ≤ b)
    (hα : LipschitzOnWith K α (Icc a b)) :
    gluingCollarModelEDist hr (α a) (α b) ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
        (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  have h := gluingCollarModelEDist_le_lipschitz_warp_length hr
    (gluingCollarNormalizeCurve_lipschitzOnWith hab hα)
  rw [gluingCollarNormalizeCurve_zero, gluingCollarNormalizeCurve_one,
    gluingCollarNormalizeCurve_lintegral_speed hr hab hα] at h
  exact h

#print axioms gluingCollarNormalizeCurve_deriv
#print axioms gluingCollarNormalizeCurve_integral_speed
#print axioms gluingCollarNormalizeCurve_lintegral_speed
#print axioms gluingCollarModelMetric_dist_le_interval_lipschitz_length
#print axioms gluingCollarModelEDist_le_interval_lipschitz_warp_length

end SystolicGrowth
