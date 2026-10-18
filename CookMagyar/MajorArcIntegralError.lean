module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MajorArcMeasure

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.CookMagyarArcs

/-! # Uniform major-arc integration errors

The major arcs lie in the unit fundamental interval and have volume at most
`2(Q+1)^2 Q/N³`. Thus a uniform pointwise approximation can be integrated
with either a unit-volume or the sharper cubic-scale measure factor. The
arithmetic approximation and model integral remain separate obligations.
-/

/-- The clipped major arcs have real volume at most one. -/
theorem majorArcs_volume_real_le_one (N Q : ℕ) :
    volume.real (majorArcs N Q) ≤ 1 := by
  have hmono : volume (majorArcs N Q) ≤ volume (Set.Icc (0 : ℝ) 1) :=
    measure_mono (majorArcs_subset_Icc N Q)
  have htop : volume (Set.Icc (0 : ℝ) 1) ≠ ∞ := by simp
  have hreal := ENNReal.toReal_mono htop hmono
  simpa [Measure.real] using hreal

/-- The direct integral error is the pointwise error times arc volume. -/
theorem norm_cubicMajorArcIntegral_sub_model_le_mul_volume
    (n N T Q : ℕ) (model : ℝ → ℂ)
    (hmodel : IntegrableOn model (majorArcs N Q))
    {E : ℝ}
    (hpoint : ∀ alpha ∈ majorArcs N Q,
      ‖cubicIntegrand n N T alpha - model alpha‖ ≤ E) :
    ‖cubicMajorArcIntegral n N T Q -
        ∫ alpha in majorArcs N Q, model alpha‖ ≤
      E * volume.real (majorArcs N Q) := by
  have hfin : volume (majorArcs N Q) < ∞ := by
    calc
      volume (majorArcs N Q) ≤ volume (Set.Icc (0 : ℝ) 1) :=
        measure_mono (majorArcs_subset_Icc N Q)
      _ < ∞ := by simp
  have hnorm :
      ‖∫ alpha in majorArcs N Q,
          (cubicIntegrand n N T alpha - model alpha)‖ ≤
        E * volume.real (majorArcs N Q) :=
    norm_setIntegral_le_of_norm_le_const hfin hpoint
  calc
    ‖cubicMajorArcIntegral n N T Q -
        ∫ alpha in majorArcs N Q, model alpha‖ =
        ‖∫ alpha in majorArcs N Q,
            (cubicIntegrand n N T alpha - model alpha)‖ := by
      rw [integral_sub (cubicIntegrand_integrableOn_majorArcs n N T Q) hmodel]
      rfl
    _ ≤ E * volume.real (majorArcs N Q) := hnorm

/-- The unit-interval bound gives no loss in a uniform pointwise error. -/
theorem norm_cubicMajorArcIntegral_sub_model_le
    (n N T Q : ℕ) (model : ℝ → ℂ)
    (hmodel : IntegrableOn model (majorArcs N Q))
    {E : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ alpha ∈ majorArcs N Q,
      ‖cubicIntegrand n N T alpha - model alpha‖ ≤ E) :
    ‖cubicMajorArcIntegral n N T Q -
        ∫ alpha in majorArcs N Q, model alpha‖ ≤ E := by
  calc
    ‖cubicMajorArcIntegral n N T Q -
        ∫ alpha in majorArcs N Q, model alpha‖ ≤
      E * volume.real (majorArcs N Q) :=
        norm_cubicMajorArcIntegral_sub_model_le_mul_volume
          n N T Q model hmodel hpoint
    _ ≤ E := by
      have hvol := majorArcs_volume_real_le_one N Q
      nlinarith

/-- The sharper circle-volume bound preserves the cubic `N⁻³` factor. -/
theorem norm_cubicMajorArcIntegral_sub_model_le_count_mul_radius
    (n N T Q : ℕ) (model : ℝ → ℂ)
    (hmodel : IntegrableOn model (majorArcs N Q))
    {E : ℝ} (hE : 0 ≤ E)
    (hpoint : ∀ alpha ∈ majorArcs N Q,
      ‖cubicIntegrand n N T alpha - model alpha‖ ≤ E) :
    ‖cubicMajorArcIntegral n N T Q -
        ∫ alpha in majorArcs N Q, model alpha‖ ≤
      E * (((Q + 1 : ℕ) ^ 2 : ℝ) * (2 * cubicArcRadius N Q)) := by
  calc
    ‖cubicMajorArcIntegral n N T Q -
        ∫ alpha in majorArcs N Q, model alpha‖ ≤
      E * volume.real (majorArcs N Q) :=
        norm_cubicMajorArcIntegral_sub_model_le_mul_volume
          n N T Q model hmodel hpoint
    _ ≤ E * (((Q + 1 : ℕ) ^ 2 : ℝ) * (2 * cubicArcRadius N Q)) :=
      mul_le_mul_of_nonneg_left
        (volume_real_majorArcs_le_center_count_mul_radius N Q) hE

end SystolicGrowth.CookMagyarArcs
