module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarSmoothWarp
public import Geometry.GluingCollarWarpRegularity
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-!
# Uniform first-derivative control for actual collar smoothing

The explicit positive square root controls the smooth derivative independently
of the smoothing parameter. Both the genuine smooth derivative and Lean's
totalized derivative of the original warp obey the same compact-window bound.
The bounds give actual supremum and integral estimates for cutoff errors.
-/

open Set MeasureTheory

namespace SystolicGrowth

private theorem abs_sinh_le_cosh (t : ℝ) : |Real.sinh t| ≤ Real.cosh t := by
  nlinarith [Real.cosh_sq t, sq_abs (Real.sinh t), abs_nonneg (Real.sinh t), Real.cosh_pos t]

/-- The actual square-root quotient has absolute value at most one for every parameter. -/
theorem gluingCollarSmoothWarp_sinh_div_root_abs_le_one (ε t : ℝ) :
    |Real.sinh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)| ≤ 1 := by
  have hroot : |Real.sinh t| ≤ Real.sqrt (Real.sinh t ^ 2 + ε ^ 2) := by
    have h := Real.sqrt_le_sqrt
      (le_add_of_nonneg_right (a := Real.sinh t ^ 2) (sq_nonneg ε))
    rwa [Real.sqrt_sq_eq_abs] at h
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hzero : Real.sqrt (Real.sinh t ^ 2 + ε ^ 2) = 0
  · simp [hzero]
  · exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hzero))).mpr hroot

/-- A tighter pointwise derivative bound holds for all positive smoothing parameters. -/
theorem gluingCollarSmoothWarp_deriv_abs_le_point {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (t : ℝ) :
    |deriv (gluingCollarSmoothWarp r ε) t| ≤ Real.cosh (r + |t|) := by
  have hquotient := gluingCollarSmoothWarp_sinh_div_root_abs_le_one ε t
  have hsinh := Real.sinh_pos_iff.mpr hr
  rw [gluingCollarSmoothWarp_deriv r hε]
  calc
    |Real.sinh r * Real.sinh t + Real.cosh r *
        (Real.sinh t * Real.cosh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2))| ≤
      |Real.sinh r * Real.sinh t| + |Real.cosh r *
        (Real.sinh t * Real.cosh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2))| := abs_add_le _ _
    _ = Real.sinh r * |Real.sinh t| + Real.cosh r *
        (|Real.sinh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)| * Real.cosh t) := by
      rw [show Real.sinh t * Real.cosh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2) =
        (Real.sinh t / Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)) * Real.cosh t by ring]
      simp only [abs_mul, abs_of_pos hsinh, abs_of_pos (Real.cosh_pos r),
        abs_of_pos (Real.cosh_pos t)]
    _ ≤ Real.sinh r * |Real.sinh t| + Real.cosh r * Real.cosh t := by
      gcongr
      exact (mul_le_mul_of_nonneg_right hquotient (Real.cosh_pos t).le).trans_eq (one_mul _)
    _ = Real.cosh (r + |t|) := by
      rw [Real.cosh_add, Real.cosh_abs, ← Real.abs_sinh]
      ring

/-- The actual smooth derivative is uniformly bounded on the full compact window. -/
theorem gluingCollarSmoothWarp_deriv_abs_le_window {r ε R t : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hR : 0 ≤ R) (ht : t ∈ Icc (-R) R) :
    |deriv (gluingCollarSmoothWarp r ε) t| ≤ Real.cosh (r + R) := by
  apply (gluingCollarSmoothWarp_deriv_abs_le_point hr hε t).trans
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_pos (add_pos_of_pos_of_nonneg hr (abs_nonneg t)),
    abs_of_pos (add_pos_of_pos_of_nonneg hr hR)]
  linarith [abs_le.mpr ht]

private theorem cosh_add_le_cosh_factor {r R : ℝ} (hr : 0 < r) :
    Real.cosh (r + R) ≤ (Real.sinh r + Real.cosh r) * Real.cosh R := by
  rw [Real.cosh_add]
  have hsinh := Real.sinh_pos_iff.mpr hr
  have hR : Real.sinh R ≤ Real.cosh R := (le_abs_self _).trans (abs_sinh_le_cosh R)
  nlinarith

theorem gluingCollarSmoothWarp_deriv_abs_le_cosh_factor {r ε R t : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hR : 0 ≤ R) (ht : t ∈ Icc (-R) R) :
    |deriv (gluingCollarSmoothWarp r ε) t| ≤
      (Real.sinh r + Real.cosh r) * Real.cosh R :=
  (gluingCollarSmoothWarp_deriv_abs_le_window hr hε hR ht).trans
    (cosh_add_le_cosh_factor hr)

/-- The original derivative has the identical window bound, including its totalized value at
the genuine corner. The underlying native proof handles both smooth branches and zero. -/
theorem gluingCollarWarp_deriv_abs_le_positive_radius {r R t : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (ht : t ∈ Icc (-R) R) :
    |deriv (gluingCollarWarp r) t| ≤ Real.cosh (r + R) := by
  simpa only [abs_of_pos hr] using gluingCollarWarp_deriv_abs_le_all r hR ht

theorem gluingCollarWarp_deriv_abs_le_cosh_factor {r R t : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (ht : t ∈ Icc (-R) R) :
    |deriv (gluingCollarWarp r) t| ≤ (Real.sinh r + Real.cosh r) * Real.cosh R :=
  (gluingCollarWarp_deriv_abs_le_positive_radius hr hR ht).trans
    (cosh_add_le_cosh_factor hr)

/-- The actual continuous smooth derivative is integrable on every compact radial window. -/
theorem gluingCollarSmoothWarp_deriv_integrableOn (r : ℝ) {ε : ℝ}
    (hε : 0 < ε) (R : ℝ) :
    IntegrableOn (deriv (gluingCollarSmoothWarp r ε)) (Icc (-R) R) :=
  (gluingCollarSmoothWarp_contDiff r hε 1).continuous_deriv_one.continuousOn.integrableOn_compact
    isCompact_Icc

/-- The original totalized derivative is measurable and genuinely integrable on the same
window; no false continuity at the seam is used. -/
theorem gluingCollarWarp_deriv_integrableOn {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    IntegrableOn (deriv (gluingCollarWarp r)) (Icc (-R) R) := by
  letI : IsFiniteMeasure (volume.restrict (Icc (-R) R)) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt isCompact_Icc.measure_lt_top)
  apply (integrable_const (Real.cosh (r + R))).mono'
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa only [Real.norm_eq_abs] using gluingCollarWarp_deriv_abs_le_positive_radius hr hR ht

theorem gluingCollarSmoothWarp_deriv_sup_norm_le_window {r ε R : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hR : 0 ≤ R) :
    (⨆ t : Icc (-R) R, ‖deriv (gluingCollarSmoothWarp r ε) t.1‖) ≤ Real.cosh (r + R) := by
  letI : Nonempty (Icc (-R) R) := ⟨⟨0, by constructor <;> linarith⟩⟩
  apply ciSup_le
  intro t
  simpa only [Real.norm_eq_abs] using gluingCollarSmoothWarp_deriv_abs_le_window hr hε hR t.2

theorem gluingCollarWarp_deriv_sup_norm_le_window {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) :
    (⨆ t : Icc (-R) R, ‖deriv (gluingCollarWarp r) t.1‖) ≤ Real.cosh (r + R) := by
  letI : Nonempty (Icc (-R) R) := ⟨⟨0, by constructor <;> linarith⟩⟩
  apply ciSup_le
  intro t
  simpa only [Real.norm_eq_abs] using gluingCollarWarp_deriv_abs_le_positive_radius hr hR t.2

private theorem window_integral_abs_le {f : ℝ → ℝ} {R K : ℝ} (hR : 0 ≤ R)
    (hi : IntegrableOn f (Icc (-R) R)) (hb : ∀ t ∈ Icc (-R) R, |f t| ≤ K) :
    (∫ t in Icc (-R) R, |f t|) ≤ K * (2 * R) := by
  have habs : IntegrableOn (fun t => |f t|) (Icc (-R) R) := by
    change Integrable (fun t => |f t|) (volume.restrict (Icc (-R) R))
    simpa only [Real.norm_eq_abs] using hi.norm
  have hc : IntegrableOn (fun _ : ℝ => K) (Icc (-R) R) :=
    integrableOn_const (ne_of_lt isCompact_Icc.measure_lt_top)
  calc
    (∫ t in Icc (-R) R, |f t|) ≤ ∫ _t in Icc (-R) R, K :=
      setIntegral_mono_on habs hc measurableSet_Icc hb
    _ = K * (2 * R) := by
      rw [setIntegral_const, measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R), smul_eq_mul]
      ring

theorem gluingCollarSmoothWarp_deriv_abs_integral_le {r ε R : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ t in Icc (-R) R, |deriv (gluingCollarSmoothWarp r ε) t|) ≤
      Real.cosh (r + R) * (2 * R) :=
  window_integral_abs_le hR (gluingCollarSmoothWarp_deriv_integrableOn r hε R)
    (fun _ ht => gluingCollarSmoothWarp_deriv_abs_le_window hr hε hR ht)

theorem gluingCollarWarp_deriv_abs_integral_le {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) :
    (∫ t in Icc (-R) R, |deriv (gluingCollarWarp r) t|) ≤
      Real.cosh (r + R) * (2 * R) :=
  window_integral_abs_le hR (gluingCollarWarp_deriv_integrableOn hr hR)
    (fun _ ht => gluingCollarWarp_deriv_abs_le_positive_radius hr hR ht)

/-- Both genuine derivative estimates also uniformly control the cutoff's derivative-error
term, including the actual seam. -/
theorem gluingCollarSmoothWarp_deriv_sub_warp_deriv_abs_le_window {r ε R t : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hR : 0 ≤ R) (ht : t ∈ Icc (-R) R) :
    |deriv (gluingCollarSmoothWarp r ε) t - deriv (gluingCollarWarp r) t| ≤
      2 * Real.cosh (r + R) := by
  calc
    |deriv (gluingCollarSmoothWarp r ε) t - deriv (gluingCollarWarp r) t| ≤
        |deriv (gluingCollarSmoothWarp r ε) t| + |deriv (gluingCollarWarp r) t| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (deriv (gluingCollarSmoothWarp r ε) t) (-deriv (gluingCollarWarp r) t)
    _ ≤ Real.cosh (r + R) + Real.cosh (r + R) :=
      add_le_add (gluingCollarSmoothWarp_deriv_abs_le_window hr hε hR ht)
        (gluingCollarWarp_deriv_abs_le_positive_radius hr hR ht)
    _ = 2 * Real.cosh (r + R) := by ring

#print axioms gluingCollarSmoothWarp_deriv_abs_le_window
#print axioms gluingCollarWarp_deriv_abs_le_positive_radius
#print axioms gluingCollarSmoothWarp_deriv_integrableOn
#print axioms gluingCollarWarp_deriv_integrableOn
#print axioms gluingCollarSmoothWarp_deriv_sup_norm_le_window
#print axioms gluingCollarSmoothWarp_deriv_abs_integral_le
#print axioms gluingCollarSmoothWarp_deriv_sub_warp_deriv_abs_le_window

end SystolicGrowth
