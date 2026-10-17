module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronKernelLeaf
public import CookMagyar.PerronCoefficientSeries
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.LSeries.Dirichlet

@[expose] public section

/-!
# Absolute series exchange on a finite Perron contour

Positive indices avoid the zero term of the Dirichlet series. Pointwise
domination gives a summable family of integral norms on the finite interval;
the Bochner integral can then be interchanged with the coefficient series.
-/

open MeasureTheory

namespace SystolicGrowth.CookMagyarCircle

/-- Uniform domination of one coefficient-weighted scalar contour term. -/
theorem norm_coefficient_perronScalarKernel_le
    (a : ℂ) (x σ t : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k) (hσ : 0 < σ) :
    ‖a * perronScalarKernel x k σ t‖ ≤
      (x ^ σ / σ) * (‖a‖ / (k : ℝ) ^ σ) := by
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left
    (norm_perronScalarKernel_le x σ t k hx hk hσ) (norm_nonneg a)
  calc
    _ ≤ ‖a‖ * ((x / (k : ℝ)) ^ σ / σ) := h
    _ = _ := by rw [Real.div_rpow hx.le (Nat.cast_nonneg k)]; ring

/-- An absolutely convergent coefficient series may be integrated termwise
on every finite positive-abscissa Perron contour. -/
theorem integral_tsum_perronScalarKernel
    (a : ℕ → ℂ) (x σ H : ℝ) (hx : 0 < x) (hσ : 0 < σ) (hH : 0 ≤ H)
    (ha : Summable (fun k : ℕ =>
      ‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ))) :
    (∫ t in -H..H, ∑' k : ℕ, a (k + 1) * perronScalarKernel x (k + 1) σ t) =
      ∑' k : ℕ, a (k + 1) *
        (∫ t in -H..H, perronScalarKernel x (k + 1) σ t) := by
  let F : ℕ → ℝ → ℂ := fun k t => a (k + 1) * perronScalarKernel x (k + 1) σ t
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-H) H)
  have horder : -H ≤ H := by linarith
  have hFint (k : ℕ) : Integrable (F k) μ := by
    have hc : Continuous (F k) :=
      (continuous_perronScalarKernel x σ (k + 1) hx (by omega) hσ).const_mul _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le horder).mp
      (hc.intervalIntegrable (-H) H)
  have hbound (k : ℕ) :
      (∫ t, ‖F k t‖ ∂μ) ≤
        (2 * H * (x ^ σ / σ)) * (‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ)) := by
    have hpoint (t : ℝ) : ‖F k t‖ ≤
        (x ^ σ / σ) * (‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ)) :=
      norm_coefficient_perronScalarKernel_le _ x σ t (k + 1) hx (by omega) hσ
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -H) (b := H)
      (C := (x ^ σ / σ) * (‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ)))
      (f := fun t : ℝ => ‖F k t‖) (by
        intro t _
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpoint t)
    change (∫ t in Set.Ioc (-H) H, ‖F k t‖) ≤ _
    rw [← intervalIntegral.integral_of_le horder]
    calc
      _ ≤ ‖∫ t in -H..H, ‖F k t‖‖ := by exact le_abs_self _
      _ ≤ _ := by
        convert hi using 1
        rw [abs_of_nonneg (by linarith : 0 ≤ H - -H)]
        ring
  have hFsum : Summable (fun k : ℕ => ∫ t, ‖F k t‖ ∂μ) :=
    Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun t => norm_nonneg (F k t))) hbound
      (ha.mul_left (2 * H * (x ^ σ / σ)))
  have hexchange := integral_tsum_of_summable_integral_norm hFint hFsum
  have hinterval :
      (∫ t in -H..H, ∑' k : ℕ, F k t) =
        ∑' k : ℕ, ∫ t in -H..H, F k t := by
    simpa only [intervalIntegral.integral_of_le horder, μ] using hexchange.symm
  simpa only [F, intervalIntegral.integral_const_mul] using hinterval

/- TASK-SLOT PERRON-INTEGRAL-SUMMABILITY (COMPLETE): P10 is proved below. -/

/-- Positive-index scalar contour integrals form a summable family whenever
their absolute Dirichlet coefficients are summable. -/
theorem summable_integral_perronScalarKernel
    (a : ℕ → ℂ) (x σ H : ℝ) (hx : 0 < x) (hσ : 0 < σ) (hH : 0 ≤ H)
    (ha : Summable (fun k : ℕ =>
      ‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ))) :
    Summable (fun k : ℕ => a (k + 1) *
      (∫ t in -H..H, perronScalarKernel x (k + 1) σ t)) := by
  apply (ha.mul_left (2 * H * (x ^ σ / σ))).of_norm_bounded
  intro k
  rw [← intervalIntegral.integral_const_mul]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -H) (b := H)
    (C := (x ^ σ / σ) * (‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ)))
    (f := fun t : ℝ => a (k + 1) * perronScalarKernel x (k + 1) σ t) (by
      intro t _
      exact norm_coefficient_perronScalarKernel_le _ x σ t (k + 1) hx (by omega) hσ)
  calc
    _ ≤ ((x ^ σ / σ) * (‖a (k + 1)‖ / (((k + 1 : ℕ) : ℝ) ^ σ))) *
        |H - -H| := hi
    _ = _ := by
      rw [abs_of_nonneg (by linarith : 0 ≤ H - -H)]
      ring

/-- The twisted von Mangoldt coefficients have the absolute convergence
required for termwise integration on a near-one Perron contour. -/
theorem summable_twisted_vonMangoldt_rpow_norm
    (q : ℕ) (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    Summable (fun k : ℕ =>
      ‖χ (k + 1) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)‖ /
        (((k + 1 : ℕ) : ℝ) ^ σ)) := by
  have hΛ := (vonMangoldt_rpow_series_summable_and_tsum_le σ hσ hσ₂).1
  have hshift : Summable (fun k : ℕ =>
      ArithmeticFunction.vonMangoldt (k + 1) / (((k + 1 : ℕ) : ℝ) ^ σ)) :=
    (summable_nat_add_iff 1).mpr hΛ
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hshift
  intro k
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) σ)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (χ.norm_le_one (k + 1))
    (ArithmeticFunction.vonMangoldt_nonneg (n := k + 1))

/-- Positive real bases let the scalar kernel be factored into its exact
Dirichlet-series power and contour multiplier. -/
theorem perronScalarKernel_eq_dirichletFactor
    (x σ t : ℝ) (k : ℕ) (hx : 0 < x) (hk : 0 < k) :
    perronScalarKernel x k σ t =
      (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
        (k : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
        ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkcomplex : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hkpow : (k : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hkcomplex)
  have hmul : (x : ℂ) ^ s =
      (((x / (k : ℝ) : ℝ) : ℂ) ^ s) * (k : ℂ) ^ s := by
    have h := Complex.mul_cpow_ofReal_nonneg (div_pos hx hkreal).le hkreal.le s
    have hbase : ((x / (k : ℝ) : ℝ) : ℂ) * ((k : ℝ) : ℂ) = (x : ℂ) := by
      rw [← Complex.ofReal_mul, div_mul_cancel₀ _ hkreal.ne']
    rw [hbase] at h
    simpa only [Complex.ofReal_natCast] using h
  have hratio : (((x / (k : ℝ) : ℝ) : ℂ) ^ s) = (x : ℂ) ^ s / (k : ℂ) ^ s :=
    (eq_div_iff hkpow).mpr hmul.symm
  exact congrArg (fun z : ℂ => z / s) hratio

/-- Expanding the L-series gives exactly the positive-index scalar kernels,
including the original contour denominator. -/
theorem LSeries_perron_integrand_eq_tsum
    (a : ℕ → ℂ) (x σ t : ℝ) (hx : 0 < x)
    (ha : LSeriesSummable a ((σ : ℂ) + Complex.I * (t : ℂ))) :
    LSeries a ((σ : ℂ) + Complex.I * (t : ℂ)) *
        (x : ℂ) ^ ((σ : ℂ) + Complex.I * (t : ℂ)) /
          ((σ : ℂ) + Complex.I * (t : ℂ)) =
      ∑' k : ℕ, a (k + 1) * perronScalarKernel x (k + 1) σ t := by
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  have hshift : Summable (fun k : ℕ => a (k + 1) / (k + 1 : ℂ) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr ha
    simpa only [LSeries.term, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Nat.cast_add, Nat.cast_one] using h
  have hseries : LSeries a s = ∑' k : ℕ, a (k + 1) / (k + 1 : ℂ) ^ s := by
    have h := ha.sum_add_tsum_nat_add 1
    simpa [LSeries, LSeries.term, s] using h.symm
  change LSeries a s * (x : ℂ) ^ s / s = _
  rw [hseries]
  calc
    _ = (∑' k : ℕ, a (k + 1) / (k + 1 : ℂ) ^ s) * ((x : ℂ) ^ s / s) := by ring
    _ = ∑' k : ℕ, (a (k + 1) / (k + 1 : ℂ) ^ s) * ((x : ℂ) ^ s / s) :=
      (hshift.tsum_mul_right _).symm
    _ = _ := by
      apply tsum_congr
      intro k
      rw [perronScalarKernel_eq_dirichletFactor x σ t (k + 1) hx (by omega)]
      change _ = a (k + 1) * ((x : ℂ) ^ s / ((k + 1 : ℕ) : ℂ) ^ s / s)
      push_cast
      ring

/-- The analytic L-series contour integral is exactly the termwise scalar
Perron integral for the twisted von Mangoldt coefficients. -/
theorem integral_twisted_LSeries_perron_eq_tsum
    (q : ℕ) (χ : DirichletCharacter ℂ q) (x σ H : ℝ)
    (hx : 0 < x) (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hH : 0 ≤ H) :
    (∫ t in -H..H,
      let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
      LSeries (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) s *
        (x : ℂ) ^ s / s) =
      ∑' k : ℕ, (χ (k + 1) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)) *
        (∫ t in -H..H, perronScalarKernel x (k + 1) σ t) := by
  have hpoint (t : ℝ) :
      (let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
       LSeries (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) s *
         (x : ℂ) ^ s / s) =
        ∑' k : ℕ, (χ (k + 1) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)) *
          perronScalarKernel x (k + 1) σ t := by
    have hs : 1 < ((σ : ℂ) + Complex.I * (t : ℂ)).re := by simpa using hσ
    have hsum : LSeriesSummable
        (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ))
        ((σ : ℂ) + Complex.I * (t : ℂ)) := by
      simpa only [Pi.mul_def] using
        DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
    simpa only [Nat.cast_add, Nat.cast_one] using
      LSeries_perron_integrand_eq_tsum
        (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) x σ t hx hsum
  simp_rw [hpoint]
  have habs : Summable (fun k : ℕ =>
      ‖χ ((k + 1 : ℕ) : ZMod q) * (ArithmeticFunction.vonMangoldt (k + 1) : ℂ)‖ /
        (((k + 1 : ℕ) : ℝ) ^ σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      summable_twisted_vonMangoldt_rpow_norm q χ σ hσ hσ₂
  simpa only [Nat.cast_add, Nat.cast_one] using
    integral_tsum_perronScalarKernel
      (fun k : ℕ => χ k * (ArithmeticFunction.vonMangoldt k : ℂ)) x σ H hx
      (by linarith) hH habs

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.integral_tsum_perronScalarKernel
#print axioms SystolicGrowth.CookMagyarCircle.summable_integral_perronScalarKernel
#print axioms SystolicGrowth.CookMagyarCircle.summable_twisted_vonMangoldt_rpow_norm
#print axioms SystolicGrowth.CookMagyarCircle.LSeries_perron_integrand_eq_tsum
#print axioms SystolicGrowth.CookMagyarCircle.integral_twisted_LSeries_perron_eq_tsum
