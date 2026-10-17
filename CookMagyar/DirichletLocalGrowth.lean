module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SiegelCharacterBounds
public import Mathlib.NumberTheory.ZetaValues

@[expose] public section

/-!
# Actual local growth and center lower bounds for Dirichlet L-functions

The Abel continuation estimate bounds a nonprincipal `L`-function on each
closed disk centered at `2+iτ`. At its center, the actual inverse Dirichlet
series has coefficients `χ(n)μ(n)` of norm at most one. The convergent
inverse-square sum gives a positive lower norm bound independent of both
the modulus and the height. These are inputs for local zero counting and
logarithmic-derivative estimates, not an assumed zero-free region.
-/

open scoped BigOperators LSeries.notation

namespace SystolicGrowth.CookMagyarCircle

variable {q : ℕ} [NeZero q]

/-- Polynomial local growth on the actual closed disk at height `τ`. -/
theorem dirichlet_LFunction_norm_le_shifted_disk
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) {s : ℂ}
    (hs : s ∈ Metric.closedBall (2 + (τ : ℂ) * Complex.I) (3 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 7 * (q : ℝ) * (|τ| + 2) := by
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  have hcre : c.re = 2 := by simp [c, Complex.mul_re]
  have hdist : ‖s - c‖ ≤ (3 / 2 : ℝ) :=
    by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hre : 1 / 2 ≤ s.re := by
    have h : 2 - s.re ≤ ‖s - c‖ := by
      calc
        2 - s.re = (c - s).re := by simp only [Complex.sub_re, hcre]
        _ ≤ ‖c - s‖ := Complex.re_le_norm _
        _ = ‖s - c‖ := norm_sub_rev _ _
    linarith
  have hc : ‖c‖ ≤ 2 + |τ| := by
    calc
      _ ≤ ‖(2 : ℂ)‖ + ‖(τ : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖s‖ ≤ 7 / 2 + |τ| := by
    calc
      ‖s‖ = ‖s - c + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖s - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 7 / 2 + |τ| := by linarith
  have hq : (0 : ℝ) ≤ q := by positivity
  have hheight : 0 ≤ |τ| := abs_nonneg _
  apply (siegel_LFunction_norm_le χ hχ (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < s.re)).mpr
  have hnum : ‖s‖ * (q : ℝ) ≤ (7 * (q : ℝ) * (|τ| + 2)) * (1 / 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hnorm hq, mul_nonneg hq hheight]
  exact hnum.trans (mul_le_mul_of_nonneg_left hre (by positivity))

private theorem LSeries_norm_le_four_of_coeff_norm_le_one
    {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : s.re = 2) :
    ‖LSeries f s‖ ≤ 4 := by
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) (by rw [hs]; norm_num)
  have hterm (n : ℕ) : ‖LSeries.term f s n‖ ≤ (1 : ℝ) / (n : ℝ) ^ 2 := by
    rw [LSeries.norm_term_eq, hs, Real.rpow_two]
    by_cases hn : n = 0
    · simp [hn]
    · rw [if_neg hn]
      exact div_le_div_of_nonneg_right (hf n) (sq_nonneg _)
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
      hsum.norm.tsum_le_tsum hterm hasSum_zeta_two.summable
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 4 := by
      nlinarith [(sq_le_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 4)).mpr Real.pi_le_four]

/-- A uniform positive lower norm at `Re(s)=2`, derived from the actual
Möbius-twisted inverse series. It is independent of both `q` and `τ`. -/
theorem dirichlet_LFunction_center_norm_lower
    (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (2 + (τ : ℂ) * Complex.I)‖ := by
  let s : ℂ := 2 + (τ : ℂ) * Complex.I
  let f : ℕ → ℂ := fun n => χ (n : ZMod q) * (ArithmeticFunction.moebius n : ℂ)
  have hre : s.re = 2 := by simp [s, Complex.mul_re]
  have hcoeff (n : ℕ) : ‖f n‖ ≤ 1 := by
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    dsimp only [f]
    rw [norm_mul]
    exact (mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one).trans_eq (by ring)
  have hbound : ‖LSeries f s‖ ≤ 4 := LSeries_norm_le_four_of_coeff_norm_le_one hcoeff hre
  have hprod : DirichletCharacter.LFunction χ s * LSeries f s = 1 := by
    rw [χ.LFunction_eq_LSeries (by rw [hre]; norm_num)]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ (by rw [hre]; norm_num)
  have hnorm : ‖DirichletCharacter.LFunction χ s‖ * ‖LSeries f s‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hprod
  have hmul := mul_le_mul_of_nonneg_left hbound (norm_nonneg (DirichletCharacter.LFunction χ s))
  change (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ s‖
  nlinarith

#print axioms dirichlet_LFunction_norm_le_shifted_disk
#print axioms dirichlet_LFunction_center_norm_lower

end SystolicGrowth.CookMagyarCircle
