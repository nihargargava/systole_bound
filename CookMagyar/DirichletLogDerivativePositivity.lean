module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import CookMagyar.APCharacterBridge
public import CookMagyar.DirichletLocalFactorization
public import CookMagyar.SiegelRealCharacterProduct
public import CookMagyar.ZetaLogDerivativeNearOne
public import Vendored.PrimeNumberTheoremAnd.StrongPNT

@[expose] public section

/-!
# De la Vallée Poussin positivity for actual Dirichlet L-functions

The polynomial `3 + 4 cos θ + cos (2 θ)` is nonnegative. Its complex
form remains nonnegative throughout the closed unit disc, which also
handles the zero values of imprimitive Dirichlet characters: in that case
the two twisted terms vanish and the untwisted coefficient is `3`.

Absolute convergence of the actual von Mangoldt series for `σ > 1`
transfers the termwise inequality to the logarithmic derivatives of zeta,
`L(χ)` and `L(χ²)`. No zero-free-region assumption is used.
-/

open scoped LSeries.notation

namespace SystolicGrowth.CookMagyarMajorArc

open Metric Set
open SystolicGrowth.CookMagyarCircle

/-- The classical trigonometric polynomial used in the zero-free argument. -/
theorem deLaValleePoussin_trigonometric_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (Real.cos θ + 1)]

/-- The complex form also covers character values equal to zero. -/
theorem deLaValleePoussin_complex_nonneg (z : ℂ) (hz : ‖z‖ ≤ 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have hnorm : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have hsq : ‖z‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hz 2
    rw [← Complex.normSq_eq_norm_sq] at hsq
    simpa only [Complex.normSq_apply, sq, one_mul] using hsq
  simp only [pow_two, Complex.mul_re]
  nlinarith [sq_nonneg (z.re + 1)]

private theorem twisted_vonMangoldt_term_factor
    {q : ℕ} (χ : DirichletCharacter ℂ q) (σ τ : ℝ)
    {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
      ((σ : ℂ) + (τ : ℂ) * Complex.I) n =
      ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) *
        (χ n / (n : ℂ) ^ ((τ : ℂ) * Complex.I)) := by
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ (by exact_mod_cast hn)]
  simp only [Pi.mul_apply, Complex.ofReal_div]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
  simp only [Complex.ofReal_natCast]
  ring

/-- Every actual von Mangoldt coefficient gives a nonnegative contribution,
including at nonunits where `χ n = 0`. -/
theorem deLaValleePoussin_vonMangoldt_term_nonneg
    {q : ℕ} (χ : DirichletCharacter ℂ q) (σ τ : ℝ) (n : ℕ) :
    0 ≤ (3 * LSeries.term ↗ArithmeticFunction.vonMangoldt (σ : ℂ) n +
      4 * LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
        ((σ : ℂ) + (τ : ℂ) * Complex.I) n +
      LSeries.term (↗(χ ^ 2) * ↗ArithmeticFunction.vonMangoldt)
        ((σ : ℂ) + 2 * (τ : ℂ) * Complex.I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let a : ℝ := ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ
  let z : ℂ := χ n / (n : ℂ) ^ ((τ : ℂ) * Complex.I)
  have ha : 0 ≤ a := div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  have hz : ‖z‖ ≤ 1 := by
    dsimp [z]
    rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simpa using χ.norm_le_one (n : ZMod q)
  have hbase : LSeries.term ↗ArithmeticFunction.vonMangoldt (σ : ℂ) n = (a : ℂ) := by
    rw [LSeries.term_of_ne_zero hn]
    dsimp [a]
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
    simp only [Complex.ofReal_natCast]
  have htwist : LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt)
      ((σ : ℂ) + (τ : ℂ) * Complex.I) n = (a : ℂ) * z :=
    twisted_vonMangoldt_term_factor χ σ τ hn
  have hsquare : LSeries.term (↗(χ ^ 2) * ↗ArithmeticFunction.vonMangoldt)
      ((σ : ℂ) + 2 * (τ : ℂ) * Complex.I) n = (a : ℂ) * z ^ 2 := by
    have hphase : (n : ℂ) ^ (2 * (τ : ℂ) * Complex.I) =
        ((n : ℂ) ^ ((τ : ℂ) * Complex.I)) ^ 2 := by
      rw [mul_assoc, Complex.cpow_ofNat_mul]
    have hfactor := twisted_vonMangoldt_term_factor (χ ^ 2) σ (2 * τ) hn
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hfactor
    rw [hfactor, hphase, MulChar.pow_apply' χ two_ne_zero]
    dsimp [z]
    rw [div_pow]
  rw [hbase, htwist, hsquare]
  have hreal : (3 * (a : ℂ) + 4 * ((a : ℂ) * z) + (a : ℂ) * z ^ 2).re =
      a * (3 + 4 * z.re + (z ^ 2).re) := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    norm_num
    ring
  rw [hreal]
  exact mul_nonneg ha (deLaValleePoussin_complex_nonneg z hz)

/-- Absolute convergence transfers the coefficient inequality to the three
actual von Mangoldt L-series. -/
theorem deLaValleePoussin_vonMangoldt_LSeries_nonneg
    {q : ℕ} (χ : DirichletCharacter ℂ q) (σ τ : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * LSeries ↗ArithmeticFunction.vonMangoldt (σ : ℂ) +
      4 * LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt)
        ((σ : ℂ) + (τ : ℂ) * Complex.I) +
      LSeries (↗(χ ^ 2) * ↗ArithmeticFunction.vonMangoldt)
        ((σ : ℂ) + 2 * (τ : ℂ) * Complex.I)).re := by
  have hσ0 : 1 < (σ : ℂ).re := hσ
  have hσ1 : 1 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simpa using hσ
  have hσ2 : 1 < ((σ : ℂ) + 2 * (τ : ℂ) * Complex.I).re := by simpa using hσ
  have h0 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hσ0).hasSum
  have h1 := (χ.LSeriesSummable_twist_vonMangoldt hσ1).hasSum
  have h2 := ((χ ^ 2).LSeriesSummable_twist_vonMangoldt hσ2).hasSum
  have hsum := ((h0.mul_left (3 : ℂ)).add (h1.mul_left (4 : ℂ))).add h2
  have hre := Complex.hasSum_re hsum
  dsimp only [LSeries]
  rw [← hre.tsum_eq]
  exact tsum_nonneg (deLaValleePoussin_vonMangoldt_term_nonneg χ σ τ)

/-- The actual de la Vallée Poussin logarithmic-derivative inequality on
`σ > 1`, for any character of any positive level, primitive or not. -/
theorem deLaValleePoussin_logDeriv_nonneg
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ τ : ℝ) (hσ : 1 < σ) :
    0 ≤ (3 * (-logDeriv riemannZeta (σ : ℂ)) +
      4 * (-logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (τ : ℂ) * Complex.I)) +
      (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + 2 * (τ : ℂ) * Complex.I))).re := by
  have hσ0 : 1 < (σ : ℂ).re := hσ
  have hσ1 : 1 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simpa using hσ
  have hσ2 : 1 < ((σ : ℂ) + 2 * (τ : ℂ) * Complex.I).re := by simpa using hσ
  have h := deLaValleePoussin_vonMangoldt_LSeries_nonneg χ σ τ hσ
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ0,
    χ.LSeries_twist_vonMangoldt_eq hσ1,
    (χ ^ 2).LSeries_twist_vonMangoldt_eq hσ2] at h
  simpa only [logDeriv_apply, neg_div,
    χ.deriv_LFunction_eq_deriv_LSeries hσ1, χ.LFunction_eq_LSeries hσ1,
    (χ ^ 2).deriv_LFunction_eq_deriv_LSeries hσ2,
    (χ ^ 2).LFunction_eq_LSeries hσ2] using h

/-- An actual zero of a Dirichlet L-function cannot lie to the right of the
line `Re s = 1`, by its equality with the absolutely convergent Dirichlet
series there. -/
theorem dirichlet_LFunction_zero_re_le_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hz : DirichletCharacter.LFunction χ z = 0) : z.re ≤ 1 := by
  by_contra h
  have hσ : 1 < z.re := lt_of_not_ge h
  have hne : DirichletCharacter.LFunction χ z ≠ 0 := by
    rw [χ.LFunction_eq_LSeries hσ]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hσ
  exact hne hz

private theorem dirichlet_LFunction_local_divisor_sum_bounds
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) :
    (0 ≤ ∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
          ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) ∧
    (∀ z ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
      DirichletCharacter.LFunction χ z = 0 →
      ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) z : ℤ) : ℂ) /
            ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re) ≤
        ∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
              ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re))) := by
  classical
  let U : Set ℂ := ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)
  let D : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U
  obtain ⟨hfinite, hnonneg, g, hg, hgz, hfactor⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ τ
  have hfU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U := by
    intro u hu
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt u
  have horder : ∀ u : U,
      meromorphicOrderAt (DirichletCharacter.LFunction χ) u ≠ ⊤ := by
    intro u
    rw [(hfU u.1 u.2).meromorphicOrderAt_eq]
    exact fun h => dirichlet_LFunction_analyticOrderAt_ne_top χ hχ u.1
      (ENat.map_eq_top_iff.mp h)
  have hzeroSet := hfU.meromorphicNFOn.zero_set_eq_divisor_support horder
  have hterm (u : ℂ) (hu : D u ≠ 0) :
      0 ≤ ((((D u : ℤ) : ℂ) / ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) := by
    have huSupport : u ∈ Function.support D := by
      simp only [Function.mem_support, ne_eq]
      exact hu
    have huZero : u ∈ U ∧ DirichletCharacter.LFunction χ u = 0 := by
      change u ∈ Function.support (MeromorphicOn.divisor
        (DirichletCharacter.LFunction χ) U) at huSupport
      rw [← hzeroSet] at huSupport
      exact huSupport
    have hreu : u.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ huZero.2
    have hgap : 0 < (((σ : ℂ) + (τ : ℂ) * Complex.I) - u).re := by
      simp
      linarith
    have hden : 0 < Complex.normSq ((σ : ℂ) + (τ : ℂ) * Complex.I - u) := by
      apply Complex.normSq_pos.mpr
      intro hzero
      have hzeroRe := congrArg Complex.re hzero
      rw [show (((σ : ℂ) + (τ : ℂ) * Complex.I - u).re) = σ - u.re by simp] at hzeroRe
      simp at hzeroRe
      linarith
    have hD : 0 ≤ (D u : ℝ) := by exact_mod_cast hnonneg u
    rw [Complex.div_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, zero_div]
    simpa using div_nonneg (mul_nonneg hD hgap.le) hden.le
  have hsum :
      (∑ᶠ u : ℂ,
        (((D u : ℤ) : ℂ) / ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) =
      ∑ u ∈ hfinite.toFinset,
        (((D u : ℤ) : ℂ) / ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      apply hu
      simp [hzero]
    exact (Set.Finite.mem_toFinset hfinite).mpr hDu
  have hsum_nonneg : 0 ≤ ∑ᶠ u : ℂ,
      (((D u : ℤ) : ℂ) / ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re := by
    rw [hsum]
    exact Finset.sum_nonneg fun u hu => hterm u (Set.Finite.mem_toFinset hfinite |>.mp hu)
  refine ⟨?_, ?_⟩
  · exact hsum_nonneg
  · intro z hzU hz
    have hzSupport : z ∈ Function.support D := by
      change z ∈ Function.support (MeromorphicOn.divisor
        (DirichletCharacter.LFunction χ) U)
      rw [← hzeroSet]
      exact ⟨hzU, hz⟩
    have hzD : D z ≠ 0 := by
      simpa [Function.mem_support] using hzSupport
    have hzFin : z ∈ hfinite.toFinset :=
      (Set.Finite.mem_toFinset hfinite).mpr hzD
    rw [hsum]
    exact Finset.single_le_sum
      (fun u hu => hterm u ((Set.Finite.mem_toFinset hfinite).mp hu)) hzFin

/-- The actual local divisor contribution has nonnegative real part on the
right of the line `Re s = 1`. It is a finite sum over the actual zeros in the
factorization disk. -/
theorem dirichlet_LFunction_local_divisor_sum_nonneg
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) :
    0 ≤ ∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
          ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) :=
  (dirichlet_LFunction_local_divisor_sum_bounds χ hχ τ σ hσ).1

/-- The local divisor sum dominates the contribution of any specified actual
zero in the factorization disk, retaining its multiplicity as a nonnegative
term. -/
theorem dirichlet_LFunction_local_divisor_sum_ge_zero_term
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) (z : ℂ)
    (hzU : z ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
    (hz : DirichletCharacter.LFunction χ z = 0) :
    ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) z : ℤ) : ℂ) /
          ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re) ≤
      ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) :=
  (dirichlet_LFunction_local_divisor_sum_bounds χ hχ τ σ hσ).2 z hzU hz

/-- At an actual zero, its integer divisor multiplicity is positive, hence at
least one. Therefore the local divisor sum also dominates the unweighted
reciprocal term used in the classical zero-free argument. -/
theorem dirichlet_LFunction_local_divisor_sum_ge_reciprocal
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) (z : ℂ)
    (hzU : z ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
    (hz : DirichletCharacter.LFunction χ z = 0) :
    (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re ≤
      ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) := by
  classical
  let U : Set ℂ := ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)
  let D : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U
  obtain ⟨_, hnonneg, _, _, _, _⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ τ
  have hfU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U := by
    intro u hu
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt u
  have horder : ∀ u : U,
      meromorphicOrderAt (DirichletCharacter.LFunction χ) u ≠ ⊤ := by
    intro u
    rw [(hfU u.1 u.2).meromorphicOrderAt_eq]
    exact fun h => dirichlet_LFunction_analyticOrderAt_ne_top χ hχ u.1
      (ENat.map_eq_top_iff.mp h)
  have hzeroSet := hfU.meromorphicNFOn.zero_set_eq_divisor_support horder
  have hzSupport : z ∈ Function.support D := by
    change z ∈ Function.support (MeromorphicOn.divisor
      (DirichletCharacter.LFunction χ) U)
    rw [← hzeroSet]
    exact ⟨hzU, hz⟩
  have hzD : D z ≠ 0 := by
    simpa [Function.mem_support] using hzSupport
  have hDpos : (1 : ℝ) ≤ (D z : ℝ) := by
    have hDnonneg : 0 ≤ D z := by exact_mod_cast hnonneg z
    have hDint : (0 : ℤ) < D z := lt_of_le_of_ne hDnonneg (Ne.symm hzD)
    exact_mod_cast hDint
  let w : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I - z
  have hwre : 0 < w.re := by
    dsimp [w]
    simp
    linarith [dirichlet_LFunction_zero_re_le_one χ hz]
  have hwnorm : 0 < Complex.normSq w := by
    apply Complex.normSq_pos.mpr
    intro hw
    have hwre0 : w.re = 0 := by simp [hw]
    exact (ne_of_gt hwre) hwre0
  have hrecip : 0 < (1 / w).re := by
    rw [one_div, Complex.inv_re]
    exact div_pos hwre hwnorm
  have hterm :
      ((((D z : ℤ) : ℂ) / w).re) = (D z : ℝ) * (1 / w).re := by
    dsimp [w]
    rw [Complex.div_re, one_div, Complex.inv_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul]
    ring
  have hchosen : (1 / w).re ≤ (D z : ℝ) * (1 / w).re := by
    have hmul := mul_le_mul_of_nonneg_right hDpos hrecip.le
    simpa using hmul
  calc
    (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re = (1 / w).re := by rfl
    _ ≤ (D z : ℝ) * (1 / w).re := hchosen
    _ = ((((D z : ℤ) : ℂ) / ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re) := by
      rw [← hterm]
    _ ≤ ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re) :=
      dirichlet_LFunction_local_divisor_sum_ge_zero_term χ hχ τ σ hσ z hzU hz

private theorem dirichlet_remainder_size_ratio_log
    {q : ℕ} [NeZero q] (τ J : ℝ) :
    Real.log ((7 * (q : ℝ) * (|τ| + 2) / (1 / 4 : ℝ) ^ J) /
        ((1 / 4 : ℝ) * (5 / 4 : ℝ) ^ (-J))) =
      Real.log (28 * (q : ℝ) * (|τ| + 2)) + J * Real.log 5 := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  have hM : 0 < 7 * (q : ℝ) * (|τ| + 2) := by positivity
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  have hbase : (0 : ℝ) < 5 / 4 := by norm_num
  have hpowQuarter : 0 < (1 / 4 : ℝ) ^ J := Real.rpow_pos_of_pos hquarter J
  have hpowBase : 0 < (5 / 4 : ℝ) ^ (-J) := Real.rpow_pos_of_pos hbase (-J)
  have hlogFive : Real.log (5 / 4 : ℝ) - Real.log (1 / 4 : ℝ) = Real.log 5 := by
    rw [← Real.log_div hbase.ne' hquarter.ne']
    norm_num
  have hlogB : Real.log (28 * (q : ℝ) * (|τ| + 2)) =
      Real.log (7 * (q : ℝ) * (|τ| + 2)) - Real.log (1 / 4 : ℝ) := by
    rw [← Real.log_div hM.ne' hquarter.ne']
    congr 1
    ring
  rw [Real.log_div (div_pos hM hpowQuarter).ne' (mul_pos hquarter hpowBase).ne',
    Real.log_div hM.ne' hpowQuarter.ne',
    Real.log_mul hquarter.ne' hpowBase.ne',
    Real.log_rpow hquarter J, Real.log_rpow hbase (-J), hlogB, ← hlogFive]
  ring


private theorem dirichlet_remainder_logDeriv_bound
    {q : ℕ} [NeZero q] (τ : ℝ) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)))
    (hgne : ∀ z ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ), g z ≠ 0)
    (hupper : ∀ z ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ),
      ‖g z‖ ≤ 7 * (q : ℝ) * (|τ| + 2) /
        (1 / 4 : ℝ) ^ (Real.log (28 * (q : ℝ) * (|τ| + 2)) /
          Real.log (6 / 5 : ℝ)))
    (hcenter : (1 / 4 : ℝ) * (5 / 4 : ℝ) ^
      (-(Real.log (28 * (q : ℝ) * (|τ| + 2)) /
        Real.log (6 / 5 : ℝ))) ≤ ‖g (2 + (τ : ℂ) * Complex.I)‖) :
    ∀ z ∈ closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ),
      ‖logDeriv g z‖ ≤
        (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
          (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
  let J : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) /
    Real.log (6 / 5 : ℝ)
  let k : ℝ := 1 + Real.log 5 / Real.log (6 / 5 : ℝ)
  have hk : 1 ≤ k := by
    dsimp [k]
    have h5 := (Real.log_pos (by norm_num : (1 : ℝ) < 5)).le
    have h65 := (Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)).le
    exact le_add_of_nonneg_right (div_nonneg h5 h65)
  have hbound := norm_logDeriv_le_of_analyticOnNhd_nonzero_centerBound
      (R := 5 / 4) (r := 6 / 5)
      (M := 7 * (q : ℝ) * (|τ| + 2) / (1 / 4 : ℝ) ^ J)
      (m := (1 / 4 : ℝ) * (5 / 4 : ℝ) ^ (-J))
      (by norm_num) (by norm_num) (by norm_num)
      hg hgne hupper (by positivity) hcenter
  intro z hz
  have hzBound := hbound z hz
  rw [dirichlet_remainder_size_ratio_log τ J] at hzBound
  calc
    _ ≤ 4 * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + J * Real.log 5 + 1) *
        (6 / 5 + (5 / 4 - 6 / 5) / 3) /
          (((5 / 4 - 6 / 5) / 3) * (5 / 4 - (6 / 5 + (5 / 4 - 6 / 5) / 3))) := hzBound
    _ = 8760 * (k * Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
      dsimp [J, k]
      ring
    _ ≤ 8760 * (k * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      nlinarith
    _ = _ := by dsimp [k]; ring


/-- The actual local logarithmic derivative differs from its finite zero sum
by a uniformly logarithmic remainder, derived from the proved growth, Jensen
count, center lower bound and analytic quotient. No zero-free region is assumed. -/
theorem norm_dirichlet_LFunction_local_logDeriv_sub_divisor_sum_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ)
    {s : ℂ} (hs : s ∈ closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ))
    (hsne : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖logDeriv (DirichletCharacter.LFunction χ) s -
        ∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
              (s - u)‖ ≤
      (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
  obtain ⟨g, hg, hgne, hfactor, hlog⟩ :=
    exists_dirichlet_LFunction_local_factorization_logDeriv χ hχ τ
  obtain ⟨g₀, _, _, hfactor₀, hcenter₀⟩ :=
    exists_dirichlet_LFunction_local_factorization_center_lower χ hχ τ
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  have hc : c ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ) :=
    mem_ball_self (by norm_num)
  have hφne : (∏ᶠ u : ℂ, (c - u) ^
      MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u) ≠ 0 := by
    intro hzero
    have hlower := dirichlet_LFunction_center_norm_lower χ τ
    change (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ c‖ at hlower
    rw [hfactor c hc, hzero, zero_mul, norm_zero] at hlower
    norm_num at hlower
  have hcenterEq : g c = g₀ c :=
    mul_left_cancel₀ hφne ((hfactor c hc).symm.trans (hfactor₀ c hc))
  have hcenter : (1 / 4 : ℝ) * (5 / 4 : ℝ) ^
      (-(Real.log (28 * (q : ℝ) * (|τ| + 2)) /
        Real.log (6 / 5 : ℝ))) ≤ ‖g (2 + (τ : ℂ) * Complex.I)‖ := by
    change _ ≤ ‖g c‖
    rw [hcenterEq]
    exact hcenter₀
  have hupper := dirichlet_LFunction_local_remainder_norm_le χ hχ τ g hg hfactor
  have hbound := dirichlet_remainder_logDeriv_bound τ g hg hgne hupper hcenter s hs
  have hsU : s ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ) :=
    (closedBall_subset_ball (by norm_num : (6 / 5 : ℝ) < 5 / 4)) hs
  calc
    _ = ‖logDeriv g s‖ := by
      congr 1
      rw [hlog s hsU hsne]
      ring
    _ ≤ _ := hbound

#print axioms norm_dirichlet_LFunction_local_logDeriv_sub_divisor_sum_le

private theorem neg_re_dirichlet_local_logDeriv_le_sub_divisor
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ)
    {s : ℂ} (hs : s ∈ closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ))
    (hsne : DirichletCharacter.LFunction χ s ≠ 0) :
    (-logDeriv (DirichletCharacter.LFunction χ) s).re ≤
      (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) -
      ∑ᶠ u : ℂ,
        (((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            (s - u)).re := by
  classical
  let D : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
    (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
  let S : ℂ := ∑ᶠ u : ℂ, (D u : ℂ) / (s - u)
  have hfinite : D.HasFiniteSupport :=
    (exists_dirichlet_LFunction_local_factorization χ hχ τ).1
  have hterms : (fun u : ℂ => (D u : ℂ) / (s - u)).HasFiniteSupport := by
    apply hfinite.subset
    intro u hu
    by_contra hzero
    exact hu (by simp [Function.mem_support] at hzero; simp [hzero])
  have hmap : S.re = ∑ᶠ u : ℂ, ((D u : ℂ) / (s - u)).re :=
    Complex.reAddGroupHom.map_finsum hterms
  have hnorm := norm_dirichlet_LFunction_local_logDeriv_sub_divisor_sum_le
    χ hχ τ hs hsne
  have hreal := Complex.re_le_norm (S - logDeriv (DirichletCharacter.LFunction χ) s)
  rw [Complex.sub_re, norm_sub_rev] at hreal
  change ‖logDeriv (DirichletCharacter.LFunction χ) s - S‖ ≤ _ at hnorm
  change (-logDeriv (DirichletCharacter.LFunction χ) s).re ≤ _ -
    ∑ᶠ u : ℂ, ((D u : ℂ) / (s - u)).re
  rw [← hmap, Complex.neg_re]
  linarith

private theorem dirichlet_right_strip_mem_closedBall (τ σ : ℝ)
    (hσ : 1 < σ) (hσupper : σ ≤ 11 / 10) :
    (σ : ℂ) + (τ : ℂ) * Complex.I ∈
      closedBall (2 + (τ : ℂ) * Complex.I) (6 / 5 : ℝ) := by
  rw [mem_closedBall, dist_eq_norm]
  have hsub : (σ : ℂ) + (τ : ℂ) * Complex.I -
      (2 + (τ : ℂ) * Complex.I) = ((σ - 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith

/-- Nonprincipal negative logarithmic derivatives have a uniform real-part
upper bound immediately to the right of `1`; all local zero terms help. -/
theorem neg_re_dirichlet_LFunction_logDeriv_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) (hσupper : σ ≤ 11 / 10) :
    (-logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
      (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
  have hsre : 1 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simpa using hσ
  have hsne : DirichletCharacter.LFunction χ
      ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    rw [χ.LFunction_eq_LSeries hsre]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hsre
  have hbound := neg_re_dirichlet_local_logDeriv_le_sub_divisor χ hχ τ
    (dirichlet_right_strip_mem_closedBall τ σ hσ hσupper) hsne
  have hnonneg := dirichlet_LFunction_local_divisor_sum_nonneg χ hχ τ σ hσ
  linarith

/-- Retain the reciprocal contribution of a specified actual zero in the
real-part upper bound used by the de la Vallée Poussin contradiction. -/
theorem neg_re_dirichlet_LFunction_logDeriv_le_sub_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) (hσupper : σ ≤ 11 / 10) (z : ℂ)
    (hzU : z ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
    (hz : DirichletCharacter.LFunction χ z = 0) :
    (-logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
      (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
        (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) -
      (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re := by
  have hsre : 1 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simpa using hσ
  have hsne : DirichletCharacter.LFunction χ
      ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 := by
    rw [χ.LFunction_eq_LSeries hsre]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hsre
  have hbound := neg_re_dirichlet_local_logDeriv_le_sub_divisor χ hχ τ
    (dirichlet_right_strip_mem_closedBall τ σ hσ hσupper) hsne
  have hzero := dirichlet_LFunction_local_divisor_sum_ge_reciprocal χ hχ τ σ hσ z hzU hz
  linarith

set_option maxHeartbeats 0 in
/-- Nonreal Dirichlet characters have a uniform zero-free region obtained by
combining de la Vallée Poussin positivity with the local divisor estimate.
The quantitative remainder is bounded by the zero-free disk estimate in
`DirichletLocalFactorization`; the exceptional real-character branch is
handled separately. -/
theorem dirichlet_LFunction_zero_free_nonreal_character :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ^ 2 ≠ 1 → ∀ z : ℂ,
        DirichletCharacter.LFunction χ z = 0 →
          z.re ≤ 1 - c / (Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1) := by
  obtain ⟨dZeta, Cz, hdZeta, hCz, hζ⟩ := exists_neg_logDeriv_riemannZeta_real_upper_bound
  let K : ℝ := 8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))
  let a : ℝ := min dZeta (min (1 / 100) (1 / (100 * (K + Cz + 1))))
  let c : ℝ := a / 10
  have hKpos : 0 < K := by
    dsimp [K]
    have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hKnonneg : 0 ≤ K := hKpos.le
  have haPos : 0 < a := by
    dsimp [a]
    apply lt_min hdZeta
    apply lt_min (by norm_num)
    positivity
  have haLedZeta : a ≤ dZeta := by dsimp [a]; exact min_le_left _ _
  have haLeOneHundredth : a ≤ 1 / 100 := by
    dsimp [a]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have haLeSmall : a ≤ 1 / (100 * (K + Cz + 1)) := by
    dsimp [a]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hcPos : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hcPos, ?_⟩
  intro q hq χ hχsq z hz
  let B : ℝ := 28 * (q : ℝ) * (|z.im| + 2)
  let ell : ℝ := Real.log B + 1
  let σ : ℝ := 1 + a / ell
  by_contra hgood
  have hβnot : 1 - c / ell < z.re := lt_of_not_ge hgood
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hqge : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hBge : 1 ≤ B := by
    dsimp [B]
    have ht : 2 ≤ |z.im| + 2 := by have := abs_nonneg z.im; linarith
    nlinarith [hqge, ht]
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hBge
  have hLge : 1 ≤ ell := by
    change 1 ≤ Real.log B + 1
    have := Real.log_nonneg hBge
    linarith
  have hLpos : 0 < ell := lt_of_lt_of_le zero_lt_one hLge
  have hχ : χ ≠ 1 := by
    intro h
    apply hχsq
    rw [h]
    simp
  have hβle : z.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hz
  have hσ : 1 < σ := by
    dsimp [σ]
    have : 0 < a / ell := div_pos haPos hLpos
    linarith
  have hσupper : σ ≤ 11 / 10 := by
    dsimp [σ]
    have haL : a / ell ≤ 1 / 100 := by
      rw [div_le_iff₀ hLpos]
      nlinarith [haLeOneHundredth, hLge]
    linarith
  have hσδ : σ ≤ 1 + dZeta := by
    dsimp [σ]
    have haL : a / ell ≤ a := by
      rw [div_le_iff₀ hLpos]
      nlinarith [haPos, hLge]
    linarith [haLedZeta]
  have hζσ := hζ σ hσ hσδ
  have hχ2bound := neg_re_dirichlet_LFunction_logDeriv_le (χ ^ 2) hχsq
    (2 * z.im) σ hσ hσupper
  have hB2le : 28 * (q : ℝ) * (|2 * z.im| + 2) ≤ 2 * B := by
    dsimp [B]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [abs_nonneg z.im]
  have hlogB2 : Real.log (28 * (q : ℝ) * (|2 * z.im| + 2)) ≤ Real.log B + 1 := by
    have harg2 : 0 < 28 * (q : ℝ) * (|2 * z.im| + 2) := by positivity
    calc
      Real.log (28 * (q : ℝ) * (|2 * z.im| + 2)) ≤ Real.log (2 * B) :=
        Real.log_le_log harg2 hB2le
      _ = Real.log 2 + Real.log B := Real.log_mul (by norm_num) hBpos.ne'
      _ = Real.log B + Real.log 2 := by ring
      _ ≤ Real.log B + 1 := by
        have hlog2 : Real.log 2 ≤ 1 := by
          calc
            Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
            _ = 1 := by norm_num
        simpa [add_comm] using add_le_add_left hlog2 (Real.log B)
      _ = 1 + Real.log B := by ring
      _ = Real.log B + 1 := by ring
  have hχ2bound' :
      (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + 2 * (z.im : ℂ) * Complex.I)).re ≤ 2 * K * ell := by
    have hraw := hχ2bound
    dsimp [K] at hraw ⊢
    dsimp [B, ell] at hlogB2
    have hlogbound : Real.log (28 * (q : ℝ) * (|2 * z.im| + 2)) + 1 ≤ 2 * ell := by
      dsimp [ell]
      linarith
    have hraw' :
        (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
          ((σ : ℂ) + 2 * (z.im : ℂ) * Complex.I)).re ≤
        (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
          (Real.log (28 * (q : ℝ) * (|2 * z.im| + 2)) + 1) := by
      have harg : (σ : ℂ) + (2 * z.im : ℝ) * Complex.I =
          (σ : ℂ) + 2 * (z.im : ℂ) * Complex.I := by
        push_cast
        ring
      rw [harg] at hraw
      exact hraw
    calc
      _ ≤ (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) *
          (Real.log (28 * (q : ℝ) * (|2 * z.im| + 2)) + 1) := hraw'
      _ ≤ 2 * (8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))) * ell := by
        have hKnonneg' : 0 ≤ 8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ)) := by
          dsimp [K] at hKnonneg
          exact hKnonneg
        nlinarith [mul_le_mul_of_nonneg_left hlogbound hKnonneg']
  have hzrepr : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hzRe : ((z.re : ℂ) + (z.im : ℂ) * Complex.I).re = z.re := by simp
  have hzIm : ((z.re : ℂ) + (z.im : ℂ) * Complex.I).im = z.im := by simp
  have hzCenter : dist z (2 + (z.im : ℂ) * Complex.I) = 2 - z.re := by
    have hdiff : z - (2 + (z.im : ℂ) * Complex.I) = ((z.re - 2 : ℝ) : ℂ) := by
      rw [hzrepr]
      rw [hzIm]
      rw [hzRe]
      push_cast
      ring
    rw [dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  have hzU : z ∈ ball (2 + (z.im : ℂ) * Complex.I) (5 / 4 : ℝ) := by
    rw [Metric.mem_ball, hzCenter]
    have hcSmall : c / ell ≤ 1 / 1000 := by
      dsimp [c]
      rw [div_le_iff₀ hLpos]
      nlinarith [haLeOneHundredth]
    have hβ : 1 - c / ell < z.re := hβnot
    linarith
  have hχbound := neg_re_dirichlet_LFunction_logDeriv_le_sub_zero χ hχ
    z.im σ hσ hσupper z hzU hz
  have hdenom : (σ : ℂ) + (z.im : ℂ) * Complex.I - z = ((σ - z.re : ℝ) : ℂ) := by
    rw [hzrepr]
    rw [hzRe, hzIm]
    push_cast
    ring
  have hrecipChar :
      (1 / ((σ : ℂ) + (z.im : ℂ) * Complex.I - z)).re = 1 / (σ - z.re) := by
    rw [hdenom]
    rw [Complex.div_re]
    simp only [Complex.one_re, Complex.one_im, zero_mul, Complex.ofReal_re]
    rw [Complex.normSq_ofReal]
    have hx : σ - z.re ≠ 0 := by linarith [hσ, hβle]
    field_simp [hx]
    ring
  rw [hrecipChar] at hχbound
  have hpos := deLaValleePoussin_logDeriv_nonneg χ σ z.im hσ
  have hzetaBound : -(logDeriv riemannZeta (σ : ℂ)).re ≤ ell / a + Cz := by
    have hrecip : 1 / (σ - 1) = ell / a := by
      dsimp [σ]
      field_simp [ne_of_gt haPos]
      ring
    rw [hrecip] at hζσ
    exact hζσ
  have hineq : 4 / (σ - z.re) ≤ (3 / a + 3 * Cz + 6 * K) * ell := by
    have hpos' : 0 ≤ 3 * (-(logDeriv riemannZeta (σ : ℂ)).re) +
        4 * (-(logDeriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (z.im : ℂ) * Complex.I))).re +
        (-(logDeriv (DirichletCharacter.LFunction (χ ^ 2))
          ((σ : ℂ) + 2 * (z.im : ℂ) * Complex.I))).re := by
      simpa [Complex.add_re, Complex.mul_re] using hpos
    have hχbound' :
        (-(logDeriv (DirichletCharacter.LFunction χ)
          ((σ : ℂ) + (z.im : ℂ) * Complex.I))).re ≤ K * ell - 1 / (σ - z.re) := by
      dsimp [K, ell, B]
      exact hχbound
    have hcore : 4 / (σ - z.re) ≤ 3 * (ell / a + Cz) + 6 * K * ell := by
      have hsumUpper :
          3 * (-(logDeriv riemannZeta (σ : ℂ)).re) +
            4 * (-(logDeriv (DirichletCharacter.LFunction χ)
              ((σ : ℂ) + (z.im : ℂ) * Complex.I))).re +
            (-(logDeriv (DirichletCharacter.LFunction (χ ^ 2))
              ((σ : ℂ) + 2 * (z.im : ℂ) * Complex.I))).re ≤
            3 * (ell / a + Cz) + 4 * (K * ell - 1 / (σ - z.re)) + 2 * K * ell := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hzetaBound (by norm_num)
          · exact mul_le_mul_of_nonneg_left hχbound' (by norm_num)
        · exact hχ2bound'
      have hupper : 0 ≤ 3 * (ell / a + Cz) +
          4 * (K * ell - 1 / (σ - z.re)) + 2 * K * ell :=
        le_trans hpos' hsumUpper
      have hupper' : 0 ≤ 3 * (ell / a + Cz) + 6 * K * ell - 4 / (σ - z.re) := by
        calc
          _ = 3 * (ell / a + Cz) +
              4 * (K * ell - 1 / (σ - z.re)) + 2 * K * ell := by ring
          _ ≥ 0 := hupper
      linarith [hupper']
    have hCL : Cz ≤ Cz * ell := by nlinarith [hCz.le, hLge]
    have hcoeffUpper : 3 * (ell / a + Cz) + 6 * K * ell ≤
        (3 / a + 3 * Cz + 6 * K) * ell := by
      have ha_ne : a ≠ 0 := ne_of_gt haPos
      rw [show ell / a = (1 / a) * ell by field_simp [ha_ne]]
      calc
        _ = (3 / a + 6 * K) * ell + 3 * Cz := by ring
        _ ≤ (3 / a + 6 * K) * ell + 3 * Cz * ell := by
          have h3CL := mul_le_mul_of_nonneg_left hCL (by norm_num : (0 : ℝ) ≤ 3)
          nlinarith [h3CL]
        _ = (3 / a + 3 * Cz + 6 * K) * ell := by ring
    exact hcore.trans hcoeffUpper
  have hgapPos : 0 < σ - z.re := by linarith
  have hgapSmall : σ - z.re < (a + c) / ell := by
    rw [lt_div_iff₀ hLpos]
    have hβnot' := mul_lt_mul_of_pos_right hβnot hLpos
    have hβnot'' : ell - c < z.re * ell := by
      field_simp [ne_of_gt hLpos] at hβnot'
      nlinarith [hβnot']
    dsimp [σ]
    field_simp [ne_of_gt hLpos]
    nlinarith [hβnot'']
  have hcontradiction : False := by
    have hrecip : 1 / ((a + c) / ell) < 1 / (σ - z.re) :=
      one_div_lt_one_div_of_lt hgapPos hgapSmall
    have hcoeff : 3 / a + 3 * Cz + 6 * K < 4 / (a + c) := by
      have hsmall := haLeSmall
      have hsumSmall : a * (3 * Cz + 6 * K) ≤ 6 / 100 := by
        have hx : 0 < K + Cz + 1 := by positivity
        have hprod : a * (K + Cz + 1) ≤ 1 / 100 := by
          calc
            a * (K + Cz + 1) ≤ (1 / (100 * (K + Cz + 1))) * (K + Cz + 1) :=
              mul_le_mul_of_nonneg_right hsmall (by positivity)
            _ = 1 / 100 := by field_simp [ne_of_gt hx]
        have hfactor : 3 * Cz + 6 * K ≤ 6 * (K + Cz + 1) := by
          nlinarith [hKnonneg, hCz.le]
        calc
          a * (3 * Cz + 6 * K) ≤ a * (6 * (K + Cz + 1)) :=
            mul_le_mul_of_nonneg_left hfactor haPos.le
          _ = 6 * (a * (K + Cz + 1)) := by ring
          _ ≤ 6 / 100 := by nlinarith [hprod]
      have hA : a * (3 / a + 3 * Cz + 6 * K) < 40 / 11 := by
        have ha_ne : a ≠ 0 := ne_of_gt haPos
        calc
          a * (3 / a + 3 * Cz + 6 * K) = 3 + a * (3 * Cz + 6 * K) := by
            field_simp [ha_ne]; ring
          _ ≤ 3 + 6 / 100 := by simpa [add_comm] using add_le_add_left hsumSmall 3
          _ < 40 / 11 := by norm_num
      have hac : a + c = 11 * a / 10 := by dsimp [c]; ring
      have hdenomEq : a * (4 / (a + c)) = 40 / 11 := by
        rw [hac]
        field_simp
        norm_num
      have hcoeff' : 3 / a + 3 * Cz + 6 * K < 4 / (a + c) := by
        have ha_ne : a ≠ 0 := ne_of_gt haPos
        have hscaled' : a * (3 / a + 3 * Cz + 6 * K) < a * (4 / (a + c)) := by
          calc
            _ < 40 / 11 := hA
            _ = _ := hdenomEq.symm
        field_simp [ha_ne, ne_of_gt (add_pos haPos hcPos)] at hscaled' ⊢
        nlinarith [hscaled']
      exact hcoeff'
    have hlower : (4 / (a + c)) * ell < 4 / (σ - z.re) := by
      have hscaled := mul_lt_mul_of_pos_left hrecip (by norm_num : (0 : ℝ) < 4)
      have hleft : (4 / (a + c)) * ell = 4 * (1 / ((a + c) / ell)) := by
        have hsum : a + c ≠ 0 := ne_of_gt (add_pos haPos hcPos)
        field_simp [ne_of_gt hLpos, hsum]
      have hright : 4 * (1 / (σ - z.re)) = 4 / (σ - z.re) := by ring
      calc
        (4 / (a + c)) * ell = 4 * (1 / ((a + c) / ell)) := hleft
        _ < 4 * (1 / (σ - z.re)) := hscaled
        _ = 4 / (σ - z.re) := hright
    have hcoeffL := mul_lt_mul_of_pos_right hcoeff hLpos
    linarith
  exact hcontradiction

#print axioms dirichlet_LFunction_zero_free_nonreal_character

private theorem zeta_add_character_vonMangoldt_term_nonneg
    {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    0 ≤ (LSeries.term ↗ArithmeticFunction.vonMangoldt (σ : ℂ) n +
      LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hfactor :
      LSeries.term ↗ArithmeticFunction.vonMangoldt (σ : ℂ) n +
        LSeries.term (↗χ * ↗ArithmeticFunction.vonMangoldt) (σ : ℂ) n =
      ((ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ : ℝ) : ℂ) *
        (1 + χ n) := by
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    simp only [Pi.mul_apply, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    ring
  have ha : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  have hχre : -(1 : ℝ) ≤ (χ n).re := by
    have h := (neg_le_abs (χ n).re).trans
      ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one (n : ZMod q)))
    linarith
  rw [hfactor]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.one_re, zero_mul, sub_zero]
  exact mul_nonneg ha (by linarith)

/-- The actual zeta-character logarithmic derivative has nonnegative real
part on the real half-line to the right of one. This bounds the possible
near-one zero contribution even without a real-character hypothesis. -/
theorem zeta_add_character_logDeriv_nonneg
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ : ℝ) (hσ : 1 < σ) :
    0 ≤ (-logDeriv riemannZeta (σ : ℂ) -
      logDeriv (DirichletCharacter.LFunction χ) (σ : ℂ)).re := by
  have hσ0 : 1 < (σ : ℂ).re := hσ
  have h0 := (ArithmeticFunction.LSeriesSummable_vonMangoldt hσ0).hasSum
  have h1 := (χ.LSeriesSummable_twist_vonMangoldt hσ0).hasSum
  have hre := Complex.hasSum_re (h0.add h1)
  have hnonneg : 0 ≤ (LSeries ↗ArithmeticFunction.vonMangoldt (σ : ℂ) +
      LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) (σ : ℂ)).re := by
    dsimp only [LSeries]
    rw [← hre.tsum_eq]
    exact tsum_nonneg (zeta_add_character_vonMangoldt_term_nonneg χ σ)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ0,
    χ.LSeries_twist_vonMangoldt_eq hσ0] at hnonneg
  simpa only [logDeriv_apply, neg_div, sub_eq_add_neg,
    χ.deriv_LFunction_eq_deriv_LSeries hσ0, χ.LFunction_eq_LSeries hσ0] using hnonneg

/-- One pole budget bounds the actual zero divisor on the real axis, with
positive constants chosen before the modulus and character. Combined with
the positive integer zero multiplicities, it proves near-one real-zero
uniqueness and simplicity. -/
theorem exists_dirichlet_LFunction_real_axis_divisor_sum_bound :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ σ : ℝ,
        1 < σ → σ ≤ 1 + η →
          (∑ᶠ u : ℂ,
            ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
              (ball (2 : ℂ) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
                ((σ : ℂ) - u)).re ≤
            1 / (σ - 1) + C * (Real.log (56 * (q : ℝ)) + 1) := by
  obtain ⟨δz, Cz, hδz, hCz, hzeta⟩ :=
    exists_neg_logDeriv_riemannZeta_real_upper_bound
  let K : ℝ := 8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))
  have hK : 0 < K := by
    dsimp [K]
    have h5 := Real.log_pos (by norm_num : (1 : ℝ) < 5)
    have h65 := Real.log_pos (by norm_num : (1 : ℝ) < 6 / 5)
    positivity
  refine ⟨min δz (1 / 10), Cz + K,
    lt_min hδz (by norm_num), add_pos hCz hK, ?_⟩
  intro q hq χ hχ σ hσ hσδ
  letI : NeZero q := hq
  have hσupper : σ ≤ 11 / 10 := by
    have h := min_le_right δz (1 / 10 : ℝ)
    linarith
  have hσz : σ ≤ 1 + δz := by
    linarith [min_le_left δz (1 / 10 : ℝ)]
  have hdisc : (σ : ℂ) ∈ closedBall (2 : ℂ) (6 / 5 : ℝ) := by
    rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : σ - 2 ≤ 0)]
    linarith
  have hsne : DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
    rw [χ.LFunction_eq_LSeries hσ]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hσ
  have hbound := norm_dirichlet_LFunction_local_logDeriv_sub_divisor_sum_le
    χ hχ 0 (by simpa using hdisc) hsne
  have hcenter : (2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = 2 := by simp
  rw [hcenter] at hbound
  simp only [abs_zero, zero_add] at hbound
  let S : ℂ := ∑ᶠ u : ℂ,
    ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 : ℂ) (5 / 4 : ℝ)) u : ℤ) : ℂ) / ((σ : ℂ) - u)
  have herror := Complex.re_le_norm (S - logDeriv (DirichletCharacter.LFunction χ) σ)
  rw [Complex.sub_re, norm_sub_rev] at herror
  have hbound' : ‖logDeriv (DirichletCharacter.LFunction χ) σ - S‖ ≤
      K * (Real.log (56 * (q : ℝ)) + 1) := by
    have hscalar : 28 * (q : ℝ) * 2 = 56 * (q : ℝ) := by ring
    simpa only [hscalar] using hbound
  have hpositive := zeta_add_character_logDeriv_nonneg χ σ hσ
  simp only [Complex.sub_re, Complex.neg_re] at hpositive
  have hz := hzeta σ hσ hσz
  have hL : 1 ≤ Real.log (56 * (q : ℝ)) + 1 := by
    have hqpos : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (NeZero.pos q))
    have hlog : 0 ≤ Real.log (56 * (q : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  change S.re ≤ _
  have hC : Cz ≤ Cz * (Real.log (56 * (q : ℝ)) + 1) := by
    simpa using mul_le_mul_of_nonneg_left hL hCz.le
  nlinarith

/-- Two distinct actual local zeros contribute their two reciprocal terms;
all remaining divisor terms have nonnegative real part for `σ > 1`. -/
theorem dirichlet_LFunction_local_divisor_sum_ge_two_reciprocals
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (τ σ : ℝ) (hσ : 1 < σ) (z₁ z₂ : ℂ) (hzz : z₁ ≠ z₂)
    (hz₁U : z₁ ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
    (hz₁ : DirichletCharacter.LFunction χ z₁ = 0)
    (hz₂U : z₂ ∈ ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
    (hz₂ : DirichletCharacter.LFunction χ z₂ = 0) :
    (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - z₁)).re +
      (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - z₂)).re ≤
      (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) u : ℤ) : ℂ) /
            ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re := by
  classical
  let U : Set ℂ := ball (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)
  let D : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.LFunction χ) U
  let T : ℂ → ℝ := fun u =>
    (((D u : ℤ) : ℂ) / ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re
  obtain ⟨hfinite, hnonneg, _, _, _, _⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ τ
  have hfU : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U := by
    intro u hu
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt u
  have horder : ∀ u : U,
      meromorphicOrderAt (DirichletCharacter.LFunction χ) u ≠ ⊤ := by
    intro u
    rw [(hfU u.1 u.2).meromorphicOrderAt_eq]
    exact fun h => dirichlet_LFunction_analyticOrderAt_ne_top χ hχ u.1
      (ENat.map_eq_top_iff.mp h)
  have hzeroSet := hfU.meromorphicNFOn.zero_set_eq_divisor_support horder
  have hterm (u : ℂ) (hu : D u ≠ 0) : 0 ≤ T u := by
    have huSupport : u ∈ Function.support D := Function.mem_support.mpr hu
    have huZero : u ∈ U ∧ DirichletCharacter.LFunction χ u = 0 := by
      change u ∈ Function.support (MeromorphicOn.divisor
        (DirichletCharacter.LFunction χ) U) at huSupport
      rw [← hzeroSet] at huSupport
      exact huSupport
    have hreu : u.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ huZero.2
    have hgap : 0 < (((σ : ℂ) + (τ : ℂ) * Complex.I) - u).re := by
      simp
      linarith
    have hden : 0 < Complex.normSq ((σ : ℂ) + (τ : ℂ) * Complex.I - u) := by
      apply Complex.normSq_pos.mpr
      intro hzero
      have hzeroRe := congrArg Complex.re hzero
      rw [show (((σ : ℂ) + (τ : ℂ) * Complex.I - u).re) = σ - u.re by simp] at hzeroRe
      simp at hzeroRe
      linarith
    have hD : 0 ≤ (D u : ℝ) := by exact_mod_cast hnonneg u
    dsimp [T]
    rw [Complex.div_re]
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, zero_div]
    simpa using div_nonneg (mul_nonneg hD hgap.le) hden.le
  have hchosen (z : ℂ) (hzU : z ∈ U)
      (hz : DirichletCharacter.LFunction χ z = 0) :
      z ∈ hfinite.toFinset ∧
        (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - z)).re ≤ T z := by
    have hzSupport : z ∈ Function.support D := by
      change z ∈ Function.support (MeromorphicOn.divisor
        (DirichletCharacter.LFunction χ) U)
      rw [← hzeroSet]
      exact ⟨hzU, hz⟩
    have hzD : D z ≠ 0 := Function.mem_support.mp hzSupport
    have hDpos : (1 : ℝ) ≤ (D z : ℝ) := by
      have hDnonneg : 0 ≤ D z := by exact_mod_cast hnonneg z
      have hDint : (0 : ℤ) < D z := lt_of_le_of_ne hDnonneg (Ne.symm hzD)
      exact_mod_cast hDint
    let w : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I - z
    have hwre : 0 < w.re := by
      dsimp [w]
      simp
      linarith [dirichlet_LFunction_zero_re_le_one χ hz]
    have hwnorm : 0 < Complex.normSq w := by
      apply Complex.normSq_pos.mpr
      intro hw
      have hwre0 : w.re = 0 := by simp [hw]
      exact (ne_of_gt hwre) hwre0
    have hrecip : 0 < (1 / w).re := by
      rw [one_div, Complex.inv_re]
      exact div_pos hwre hwnorm
    have htermEq : T z = (D z : ℝ) * (1 / w).re := by
      dsimp [T, w]
      rw [Complex.div_re, one_div, Complex.inv_re]
      simp only [Complex.intCast_re, Complex.intCast_im, zero_mul]
      ring
    refine ⟨(Set.Finite.mem_toFinset hfinite).mpr hzD, ?_⟩
    rw [htermEq]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hDpos hrecip.le
  obtain ⟨hz₁Fin, hz₁bound⟩ := hchosen z₁ hz₁U hz₁
  obtain ⟨hz₂Fin, hz₂bound⟩ := hchosen z₂ hz₂U hz₂
  have hpair : ({z₁, z₂} : Finset ℂ) ⊆ hfinite.toFinset := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hz₁Fin
    · exact hz₂Fin
  have hsum : (∑ᶠ u : ℂ, ((D u : ℤ) : ℂ) /
      ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re =
      ∑ u ∈ hfinite.toFinset, T u := by
    have hsumC : (∑ᶠ u : ℂ, ((D u : ℤ) : ℂ) /
        ((σ : ℂ) + (τ : ℂ) * Complex.I - u)) =
        ∑ u ∈ hfinite.toFinset, ((D u : ℤ) : ℂ) /
          ((σ : ℂ) + (τ : ℂ) * Complex.I - u) := by
      apply finsum_eq_sum_of_support_subset
      intro u hu
      have hDu : D u ≠ 0 := by
        intro hzero
        apply hu
        simp [hzero]
      exact (Set.Finite.mem_toFinset hfinite).mpr hDu
    rw [hsumC]
    simp only [Complex.re_sum, T]
  change _ ≤ (∑ᶠ u : ℂ, ((D u : ℤ) : ℂ) /
    ((σ : ℂ) + (τ : ℂ) * Complex.I - u)).re
  rw [hsum]
  calc
    _ ≤ T z₁ + T z₂ := add_le_add hz₁bound hz₂bound
    _ = ∑ u ∈ ({z₁, z₂} : Finset ℂ), T u := by simp [hzz]
    _ ≤ ∑ u ∈ hfinite.toFinset, T u :=
      Finset.sum_le_sum_of_subset_of_nonneg hpair fun u hu _ =>
        hterm u ((Set.Finite.mem_toFinset hfinite).mp hu)

#print axioms dirichlet_LFunction_local_divisor_sum_ge_two_reciprocals

private theorem two_close_real_zeros_exceed_pole_budget
    (η C ell β₁ β₂ : ℝ) (hη : 0 < η) (hC : 0 < C) (hell : 1 ≤ ell)
    (hβ₁le : β₁ ≤ 1) (hβ₂le : β₂ ≤ 1)
    (hβ₁ : 1 - (min η (min (1 / 100) (1 / (100 * (C + 1)))) / 10) / ell < β₁)
    (hβ₂ : 1 - (min η (min (1 / 100) (1 / (100 * (C + 1)))) / 10) / ell < β₂) :
    let a : ℝ := min η (min (1 / 100) (1 / (100 * (C + 1))))
    let σ : ℝ := 1 + a / ell
    ¬ (1 / (σ - β₁) + 1 / (σ - β₂) ≤ 1 / (σ - 1) + C * ell) := by
  let a : ℝ := min η (min (1 / 100) (1 / (100 * (C + 1))))
  let σ : ℝ := 1 + a / ell
  change ¬ (1 / (σ - β₁) + 1 / (σ - β₂) ≤ 1 / (σ - 1) + C * ell)
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hapos : 0 < a := by dsimp [a]; positivity
  have haBound : a ≤ 1 / (100 * (C + 1)) :=
    (min_le_right η _).trans (min_le_right _ _)
  have hac : a * C ≤ 1 / 100 := by
    have h := (le_div_iff₀ (by positivity : 0 < 100 * (C + 1))).mp haBound
    nlinarith
  have hσ1 : 1 < σ := by dsimp [σ]; exact lt_add_of_pos_right 1 (div_pos hapos hellpos)
  have hgap₁ : 0 < σ - β₁ := by linarith
  have hgap₂ : 0 < σ - β₂ := by linarith
  have hgap₁upper : σ - β₁ ≤ (3 / 2) * a / ell := by
    change 1 - (a / 10) / ell < β₁ at hβ₁
    dsimp [σ]
    have hpay : a / ell = 10 * ((a / 10) / ell) := by ring
    have hpay' : (3 / 2) * a / ell = 15 * ((a / 10) / ell) := by ring
    have hpos : 0 < (a / 10) / ell := by positivity
    linarith
  have hgap₂upper : σ - β₂ ≤ (3 / 2) * a / ell := by
    change 1 - (a / 10) / ell < β₂ at hβ₂
    dsimp [σ]
    have hpay : a / ell = 10 * ((a / 10) / ell) := by ring
    have hpay' : (3 / 2) * a / ell = 15 * ((a / 10) / ell) := by ring
    have hpos : 0 < (a / 10) / ell := by positivity
    linarith
  have hrecip₁ : (2 / 3) * ell / a ≤ 1 / (σ - β₁) := by
    have h := one_div_le_one_div_of_le hgap₁ hgap₁upper
    have heq : 1 / ((3 / 2) * a / ell) = (2 / 3) * ell / a := by
      field_simp [hapos.ne', hellpos.ne']
    rwa [heq] at h
  have hrecip₂ : (2 / 3) * ell / a ≤ 1 / (σ - β₂) := by
    have h := one_div_le_one_div_of_le hgap₂ hgap₂upper
    have heq : 1 / ((3 / 2) * a / ell) = (2 / 3) * ell / a := by
      field_simp [hapos.ne', hellpos.ne']
    rwa [heq] at h
  have hpole : 1 / (σ - 1) = ell / a := by
    simp [σ]
  intro hbound
  rw [hpole] at hbound
  have htotal : (4 / 3) * ell / a ≤ ell / a + C * ell := by
    have hsum := add_le_add hrecip₁ hrecip₂
    have heq : (2 / 3) * ell / a + (2 / 3) * ell / a = (4 / 3) * ell / a := by ring
    rw [heq] at hsum
    exact hsum.trans hbound
  have hpaid := (div_le_iff₀ hapos).mp htotal
  have heq : (ell / a + C * ell) * a = ell + a * C * ell := by
    field_simp [hapos.ne']
  rw [heq] at hpaid
  have hcost : a * C * ell ≤ (1 / 100) * ell :=
    mul_le_mul_of_nonneg_right hac hellpos.le
  linarith


/-- For each nonprincipal character, at most one real zero lies in this
uniform logarithmic neighbourhood of `1`. No primitivity is required. -/
theorem exists_dirichlet_LFunction_real_zero_unique_near_one :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ β₁ β₂ : ℝ,
        1 - c / (Real.log (56 * (q : ℝ)) + 1) < β₁ →
        1 - c / (Real.log (56 * (q : ℝ)) + 1) < β₂ →
        DirichletCharacter.LFunction χ (β₁ : ℂ) = 0 →
        DirichletCharacter.LFunction χ (β₂ : ℂ) = 0 → β₁ = β₂ := by
  obtain ⟨η, C, hη, hC, hbudget⟩ :=
    exists_dirichlet_LFunction_real_axis_divisor_sum_bound
  let a : ℝ := min η (min (1 / 100) (1 / (100 * (C + 1))))
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a / 10, by positivity, ?_⟩
  intro q hq χ hχ β₁ β₂ hβ₁lower hβ₂lower hβ₁zero hβ₂zero
  letI : NeZero q := hq
  let ell : ℝ := Real.log (56 * (q : ℝ)) + 1
  have hell : 1 ≤ ell := by
    have hqpos : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (NeZero.pos q))
    have hlog : 0 ≤ Real.log (56 * (q : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [ell]
    linarith
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hβ₁le : β₁ ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hβ₁zero
  have hβ₂le : β₂ ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hβ₂zero
  let σ : ℝ := 1 + a / ell
  have hσ : 1 < σ := by dsimp [σ]; exact lt_add_of_pos_right 1 (div_pos ha hellpos)
  have hση : σ ≤ 1 + η := by
    have haη : a ≤ η := min_le_left _ _
    have hratio : a / ell ≤ a := div_le_self ha.le hell
    dsimp [σ]
    linarith
  have haSmall : a ≤ 1 / 100 :=
    (min_le_right η _).trans (min_le_left _ _)
  have hsmall : (a / 10) / ell ≤ 1 / 1000 := by
    have hratio : (a / 10) / ell ≤ a / 10 := div_le_self (by positivity) hell
    linarith
  have hlocal (β : ℝ) (hβle : β ≤ 1)
      (hβlower : 1 - (a / 10) / ell < β) :
      (β : ℂ) ∈ ball (2 : ℂ) (5 / 4 : ℝ) := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : β - 2 ≤ 0)]
    linarith
  by_contra hne
  have hcomplexNe : (β₁ : ℂ) ≠ (β₂ : ℂ) := by
    exact fun h => hne (Complex.ofReal_injective h)
  have htwobound := dirichlet_LFunction_local_divisor_sum_ge_two_reciprocals
    χ hχ 0 σ hσ (β₁ : ℂ) (β₂ : ℂ) hcomplexNe
    (by simpa using hlocal β₁ hβ₁le hβ₁lower) hβ₁zero
    (by simpa using hlocal β₂ hβ₂le hβ₂lower) hβ₂zero
  have hrecip (β : ℝ) : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Complex.ofReal_re]
  have htwo : 1 / (σ - β₁) + 1 / (σ - β₂) ≤
      (∑ᶠ u : ℂ,
        ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
          (ball (2 : ℂ) (5 / 4 : ℝ)) u : ℤ) : ℂ) / ((σ : ℂ) - u)).re := by
    have hcenter : (2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = 2 := by norm_num
    have hpoint : (σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = σ := by norm_num
    rw [hcenter, hpoint, hrecip β₁, hrecip β₂] at htwobound
    exact htwobound
  have hupper := hbudget q hq χ hχ σ hσ hση
  exact two_close_real_zeros_exceed_pole_budget η C ell β₁ β₂ hη hC hell
    hβ₁le hβ₂le hβ₁lower hβ₂lower (htwo.trans hupper)

#print axioms exists_dirichlet_LFunction_real_zero_unique_near_one

private theorem low_height_reciprocal_lower
    (a ell β γ : ℝ) (ha : 0 < a) (hell : 0 < ell) (hβle : β ≤ 1)
    (hβ : 1 - (a / 10) / ell < β) (hγ : |γ| < (a / 10) / ell) :
    (3 / 4) * ell / a ≤
      ((1 + a / ell) - β) / (((1 + a / ell) - β) ^ 2 + γ ^ 2) := by
  let t : ℝ := a / ell
  let x : ℝ := (1 + a / ell) - β
  have ht : 0 < t := div_pos ha hell
  have hx : t ≤ x := by dsimp [t, x]; linarith
  have hxpos : 0 < x := lt_of_lt_of_le ht hx
  have hxupper : x ≤ (11 / 10) * t := by
    have heq : (a / 10) / ell = t / 10 := by dsimp [t]; ring
    rw [heq] at hβ
    dsimp [x]
    change _ ≤ (11 / 10) * (a / ell)
    dsimp [t] at hβ
    linarith
  have hγupper : |γ| ≤ (1 / 10) * t := by
    have heq : (a / 10) / ell = (1 / 10) * t := by dsimp [t]; ring
    rw [heq] at hγ
    exact hγ.le
  have hx2 : x ^ 2 ≤ ((11 / 10) * t) ^ 2 := pow_le_pow_left₀ hxpos.le hxupper 2
  have hγ2 : γ ^ 2 ≤ ((1 / 10) * t) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg γ) hγupper 2
  have hden : 0 < x ^ 2 + γ ^ 2 := by nlinarith [sq_nonneg γ]
  have hcore : (3 / 4) / t ≤ x / (x ^ 2 + γ ^ 2) := by
    apply (div_le_div_iff₀ ht hden).mpr
    have hpaid : t ^ 2 ≤ x * t := by nlinarith
    nlinarith
  have heq : (3 / 4) / t = (3 / 4) * ell / a := by
    dsimp [t]
    field_simp
  rwa [heq] at hcore


/-- Real characters have no nonreal zeros in a uniform small near-one box.
The conjugate pair would exceed the actual real-axis pole budget. -/
theorem exists_dirichlet_LFunction_real_character_low_height_zero_real :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        (∀ r : ZMod q, (χ r).im = 0) → ∀ z : ℂ,
        DirichletCharacter.LFunction χ z = 0 →
        1 - c / (Real.log (56 * (q : ℝ)) + 1) < z.re →
        |z.im| < c / (Real.log (56 * (q : ℝ)) + 1) → z.im = 0 := by
  obtain ⟨η, C, hη, hC, hbudget⟩ :=
    exists_dirichlet_LFunction_real_axis_divisor_sum_bound
  let a : ℝ := min η (min (1 / 100) (1 / (100 * (C + 1))))
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a / 10, by positivity, ?_⟩
  intro q hq χ hχ hχreal z hz hβ hγ
  letI : NeZero q := hq
  let ell : ℝ := Real.log (56 * (q : ℝ)) + 1
  have hell : 1 ≤ ell := by
    have hqpos : 1 ≤ (q : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (NeZero.pos q))
    have hlog : 0 ≤ Real.log (56 * (q : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [ell]
    linarith
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hβle : z.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hz
  let σ : ℝ := 1 + a / ell
  have hσ : 1 < σ := by dsimp [σ]; exact lt_add_of_pos_right 1 (div_pos ha hellpos)
  have hση : σ ≤ 1 + η := by
    have haη : a ≤ η := min_le_left _ _
    have hratio : a / ell ≤ a := div_le_self ha.le hell
    dsimp [σ]
    linarith
  have haSmall : a ≤ 1 / 100 :=
    (min_le_right η _).trans (min_le_left _ _)
  have hsmall : (a / 10) / ell ≤ 1 / 1000 := by
    have hratio : (a / 10) / ell ≤ a / 10 := div_le_self (by positivity) hell
    linarith
  have hzre : 0 < z.re := by
    change 1 - (a / 10) / ell < z.re at hβ
    linarith
  have hzstar : DirichletCharacter.LFunction χ (star z) = 0 := by
    rw [siegel_realCharacter_LFunction_conj χ hχreal hχ hzre, hz, star_zero]
  have hlocal (w : ℂ) (hwre : w.re = z.re) (hwim : |w.im| = |z.im|) :
      w ∈ ball (2 : ℂ) (5 / 4 : ℝ) := by
    rw [mem_ball, dist_eq_norm]
    have hn := Complex.norm_le_abs_re_add_abs_im (w - 2)
    norm_num at hn
    rw [hwre, hwim] at hn
    rw [abs_of_nonpos (by linarith : z.re - 2 ≤ 0)] at hn
    change |z.im| < (a / 10) / ell at hγ
    linarith
  by_contra him
  have hpairNe : z ≠ star z := by
    intro heq
    have h := congrArg Complex.im heq
    simp only [Complex.star_def, Complex.conj_im] at h
    exact him (by linarith)
  have hpair := dirichlet_LFunction_local_divisor_sum_ge_two_reciprocals χ hχ 0 σ hσ z (star z) hpairNe
    (by simpa using hlocal z rfl rfl) hz
    (by simpa using hlocal (star z) (by simp) (by simp)) hzstar
  have hcenter : (2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = 2 := by norm_num
  have hpoint : (σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = σ := by norm_num
  rw [hcenter, hpoint] at hpair
  have hrecip (w : ℂ) :
      (1 / ((σ : ℂ) - w)).re = (σ - w.re) / ((σ - w.re) ^ 2 + w.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring
  rw [hrecip z, hrecip (star z)] at hpair
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, neg_sq] at hpair
  have hrecipLower := low_height_reciprocal_lower a ell z.re z.im ha hellpos hβle hβ hγ
  have htotal : (3 / 2) * ell / a ≤ 1 / (σ - 1) + C * ell := by
    have hsum : (3 / 2) * ell / a ≤
        (∑ᶠ u : ℂ,
          ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
            (ball (2 : ℂ) (5 / 4 : ℝ)) u : ℤ) : ℂ) / ((σ : ℂ) - u)).re := by
      change (3 / 4) * ell / a ≤
        (σ - z.re) / ((σ - z.re) ^ 2 + z.im ^ 2) at hrecipLower
      have heq : (3 / 4) * ell / a + (3 / 4) * ell / a = (3 / 2) * ell / a := by ring
      have hlower := add_le_add hrecipLower hrecipLower
      rw [heq] at hlower
      exact hlower.trans hpair
    exact hsum.trans (hbudget q hq χ hχ σ hσ hση)
  have hpole : 1 / (σ - 1) = ell / a := by simp [σ]
  rw [hpole] at htotal
  have haBound : a ≤ 1 / (100 * (C + 1)) :=
    (min_le_right η _).trans (min_le_right _ _)
  have hac : a * C ≤ 1 / 100 := by
    have h := (le_div_iff₀ (by positivity : 0 < 100 * (C + 1))).mp haBound
    nlinarith
  have hpaid := (div_le_iff₀ ha).mp htotal
  have heq : (ell / a + C * ell) * a = ell + a * C * ell := by
    field_simp [ha.ne']
  rw [heq] at hpaid
  have hcost : a * C * ell ≤ (1 / 100) * ell :=
    mul_le_mul_of_nonneg_right hac hellpos.le
  linarith

#print axioms exists_dirichlet_LFunction_real_character_low_height_zero_real

private theorem divisor_ge_two_of_derivative_zero
    {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (β : ℝ)
    (hβ : (β : ℂ) ∈ ball (2 : ℂ) (5 / 4 : ℝ))
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hder : deriv (DirichletCharacter.LFunction χ) (β : ℂ) = 0) :
    2 ≤ MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 : ℂ) (5 / 4 : ℝ)) (β : ℂ) := by
  let f : ℂ → ℂ := DirichletCharacter.LFunction χ
  let U : Set ℂ := ball (2 : ℂ) (5 / 4 : ℝ)
  have hfU : AnalyticOnNhd ℂ f U := by
    intro z hz
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hfβ : AnalyticAt ℂ f (β : ℂ) := hfU _ hβ
  have horder : (2 : ℕ∞) ≤ analyticOrderAt f (β : ℂ) := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) hfβ).2
    intro i hi
    interval_cases i
    · simp [f, hzero]
    · simpa [f] using hder
  have hfinite : analyticOrderAt f (β : ℂ) ≠ ⊤ :=
    dirichlet_LFunction_analyticOrderAt_ne_top χ hχ (β : ℂ)
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfU hβ]
  cases hA : analyticOrderAt f (β : ℂ) with
  | top => exact (hfinite hA).elim
  | coe n =>
    have hn : 2 ≤ n := by simpa [hA] using horder
    simp
    exact_mod_cast hn

/-- Every actual near-one real zero is simple, uniformly over the modulus
and nonprincipal character, by the actual zero-divisor pole budget. -/
theorem exists_dirichlet_LFunction_real_zero_simple_near_one :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∀ (_hq : NeZero q),
      letI : NeZero q := _hq
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ β : ℝ,
        1 - c / (Real.log (56 * (q : ℝ)) + 1) < β →
        DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
  obtain ⟨η, C, hη, hC, hbudget⟩ :=
    exists_dirichlet_LFunction_real_axis_divisor_sum_bound
  let a : ℝ := min η (min (1 / 100) (1 / (100 * (C + 1))))
  let c : ℝ := a / 10
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have haη : a ≤ η := min_le_left _ _
  have haa : a ≤ 1 / 100 := (min_le_right _ _).trans (min_le_left _ _)
  have haC : a ≤ 1 / (100 * (C + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, hc, ?_⟩
  intro q hq χ hχ β hβ hzero
  by_contra hder0
  letI : NeZero q := hq
  let ell : ℝ := Real.log (56 * (q : ℝ)) + 1
  have hqpos : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (NeZero.pos q))
  have hell : 1 ≤ ell := by
    dsimp [ell]
    have hlog : 0 ≤ Real.log (56 * (q : ℝ)) := Real.log_nonneg (by linarith)
    linarith
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hβle : β ≤ 1 := by
    exact dirichlet_LFunction_zero_re_le_one χ hzero
  let σ : ℝ := 1 + a / ell
  have hσ : 1 < σ := by dsimp [σ]; exact lt_add_of_pos_right 1 (div_pos ha hellpos)
  have haOver : a / ell ≤ a := by
    apply (div_le_iff₀ hellpos).2
    nlinarith [mul_le_mul_of_nonneg_left hell ha.le]
  have hσupper : σ ≤ 1 + η := by dsimp [σ]; linarith
  have hcOver : c / ell ≤ c := by
    apply (div_le_iff₀ hellpos).2
    nlinarith [mul_le_mul_of_nonneg_left hell hc.le]
  have hβball : (β : ℂ) ∈ ball (2 : ℂ) (5 / 4 : ℝ) := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith : β - 2 ≤ 0)]
    have hβgap : 2 - β < 1 + c / ell := by linarith
    have hcSmall : c / ell ≤ 1 / 1000 := by
      have hcLim : c ≤ 1 / 1000 := by dsimp [c]; linarith
      linarith
    linarith
  let D : ℂ → ℤ := MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
    (ball (2 : ℂ) (5 / 4 : ℝ))
  have hDtwo : (2 : ℝ) ≤ (D (β : ℂ) : ℝ) := by
    have hDint := divisor_ge_two_of_derivative_zero χ hχ β hβball hzero hder0
    exact_mod_cast hDint
  have hgap : 0 < σ - β := by linarith
  let S : ℝ := ∑ᶠ u : ℂ,
    ((((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 : ℂ) (5 / 4 : ℝ)) u : ℤ) : ℂ) / ((σ : ℂ) - u)).re)
  have hcenter : (2 : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = 2 := by simp
  have hselectedRaw := dirichlet_LFunction_local_divisor_sum_ge_zero_term
    χ hχ 0 σ hσ β (by simpa using hβball) hzero
  rw [hcenter] at hselectedRaw
  have hselected :
      ((((D (β : ℂ) : ℤ) : ℂ) / ((σ : ℂ) - (β : ℂ))).re) ≤ S := by
    simpa [S, D] using hselectedRaw
  have hselectedTerm :
      ((((D (β : ℂ) : ℤ) : ℂ) / ((σ : ℂ) - (β : ℂ))).re) =
        (D (β : ℂ) : ℝ) / (σ - β) := by
    have hcast : ((D (β : ℂ) : ℝ) : ℂ) = ((D (β : ℂ) : ℤ) : ℂ) := by norm_cast
    have hden : (σ : ℂ) - (β : ℂ) = ((σ - β : ℝ) : ℂ) := by simp
    rw [← hcast, hden, ← Complex.ofReal_div, Complex.ofReal_re]
  have hselectedReal : (D (β : ℂ) : ℝ) / (σ - β) ≤ S := by
    rw [← hselectedTerm]
    exact hselected
  obtain ⟨hfinite, _, _, _, _, _⟩ :=
    exists_dirichlet_LFunction_local_factorization χ hχ 0
  have hfiniteD : (MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 : ℂ) (5 / 4 : ℝ))).support.Finite := by
    rw [hcenter] at hfinite
    exact hfinite
  let T : ℂ → ℂ := fun u =>
    ((MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
      (ball (2 : ℂ) (5 / 4 : ℝ)) u : ℤ) : ℂ) / ((σ : ℂ) - u)
  have hsumT : (∑ᶠ u : ℂ, T u) = ∑ u ∈ hfiniteD.toFinset, T u := by
    apply finsum_eq_sum_of_support_subset
    intro u hu
    change T u ≠ 0 at hu
    have huD : MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 : ℂ) (5 / 4 : ℝ)) u ≠ 0 := by
      intro hz
      apply hu
      simp [T, hz]
    exact (Set.Finite.mem_toFinset hfiniteD).mpr huD
  have hsumS : S = ∑ u ∈ hfiniteD.toFinset, (T u).re := by
    dsimp [S]
    apply finsum_eq_sum_of_support_subset
    intro u hu
    change (T u).re ≠ 0 at hu
    have huD : MeromorphicOn.divisor (DirichletCharacter.LFunction χ)
        (ball (2 : ℂ) (5 / 4 : ℝ)) u ≠ 0 := by
      intro hz
      apply hu
      simp [T, hz]
    exact (Set.Finite.mem_toFinset hfiniteD).mpr huD
  have hsumRe : (∑ u ∈ hfiniteD.toFinset, T u).re =
      ∑ u ∈ hfiniteD.toFinset, (T u).re := by simp only [Complex.re_sum]
  have hsumUpper : S ≤ 1 / (σ - 1) + C * ell := by
    rw [hsumS, ← hsumRe, ← hsumT]
    simpa [T, ell] using hbudget q hq χ hχ σ hσ hσupper
  have hlow : 2 / (σ - β) ≤ (D (β : ℂ) : ℝ) / (σ - β) :=
    div_le_div_of_nonneg_right hDtwo hgap.le
  have hacC : a * C ≤ 1 / 100 := by
    have h := (le_div_iff₀ (by positivity : 0 < 100 * (C + 1))).mp haC
    nlinarith
  have hgapUpper' : σ - β ≤ (3 / 2) * a / ell := by
    have hβ' : 1 - (a / 10) / ell < β := by simpa [c] using hβ
    dsimp [σ]
    have hpay : a / ell = 10 * ((a / 10) / ell) := by ring
    have hpay' : (3 / 2) * a / ell = 15 * ((a / 10) / ell) := by ring
    have hpos : 0 < (a / 10) / ell := by positivity
    linarith
  have hrecip : (2 / 3) * ell / a ≤ 1 / (σ - β) := by
    have h := one_div_le_one_div_of_le hgap hgapUpper'
    have heq : 1 / ((3 / 2) * a / ell) = (2 / 3) * ell / a := by
      field_simp [ha.ne', hellpos.ne']
    rwa [heq] at h
  have hpole : 1 / (σ - 1) + C * ell = ell / a + C * ell := by
    dsimp [σ]
    field_simp [ha.ne']
    ring
  have hbudgetPair : 1 / (σ - β) + 1 / (σ - β) ≤
      1 / (σ - 1) + C * ell := by
    calc
      _ = 2 / (σ - β) := by ring
      _ ≤ (D (β : ℂ) : ℝ) / (σ - β) := hlow
      _ ≤ S := hselectedReal
      _ ≤ 1 / (σ - 1) + C * ell := hsumUpper
  have hβlower : 1 - (a / 10) / ell < β := by simpa [c] using hβ
  exact two_close_real_zeros_exceed_pole_budget η C ell β β hη hC hell
    hβle hβle (by simpa [a] using hβlower) (by simpa [a] using hβlower) hbudgetPair

#print axioms exists_dirichlet_LFunction_real_zero_simple_near_one
#print axioms divisor_ge_two_of_derivative_zero

private theorem exists_principal_LFunction_logDeriv_high_height_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} [NeZero q], 1 ≤ (q : ℝ) →
      ∀ σ τ : ℝ, 1 < σ → σ < 2 → |τ| ≥ 4 →
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
          ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re +
            K * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
  obtain ⟨C, hCpos, hShiftTwo⟩ := ShiftTwoBound
  let c₀ : ℝ := ((2 : ℝ) ^ (-1 / 2 : ℝ)) /
    (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))
  refine ⟨C + c₀, add_pos hCpos ?_, ?_⟩
  · dsimp [c₀]
    have hpow : 0 < (2 : ℝ) ^ (-1 / 2 : ℝ) := by positivity
    have hpowlt : (2 : ℝ) ^ (-1 / 2 : ℝ) < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    positivity
  · intro q hq hqge σ τ hσ hσupper hτ
    let del : ℝ := σ - 1
    let t : ℝ := τ / 2
    have hδ : del ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> dsimp [del] <;> linarith
    have ht : |t| ≥ 2 := by
      dsimp [t]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
      linarith
    have ht2 : |2 * t| ≥ 2 := by
      dsimp [t]
      rw [show (2 : ℝ) * (τ / 2) = τ by ring]
      exact le_trans (by norm_num : (2 : ℝ) ≤ 4) hτ
    have hfinite : (ZeroWindow (2 * t)).Finite := by
      simpa using ZeroWindowFinite ht2
    have hzeta := hShiftTwo del hδ t ht hfinite
    have harg : (1 + (del : ℂ) + 2 * Complex.I * (t : ℂ)) =
        (σ : ℂ) + (τ : ℂ) * Complex.I := by
      dsimp [del, t]
      push_cast
      ring
    rw [harg] at hzeta
    have hsRe : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
    have hs : 0 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by rw [hsRe]; linarith
    have hsHalf : 1 / 2 ≤ ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by rw [hsRe]; linarith
    have hs1 : (σ : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsRe] at hre
      norm_num at hre
      linarith
    have hζ : riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by rw [hsRe]; exact hσ)
    have hqNat : 1 ≤ q := by exact_mod_cast hqge
    have hcorr := norm_sub_logDeriv_LFunctionTrivChar_le hqNat hs hsHalf hs1 hζ
    have hcorr' :
        ‖logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I) -
          logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ c₀ * Real.log q := by
      simpa [c₀, logDeriv_apply] using hcorr
    have hrealDiff :
        (logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re -
          (logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
            c₀ * Real.log q := by
      have h := (Complex.re_le_norm _).trans (by
        simpa only [norm_sub_rev] using hcorr')
      simpa only [Complex.sub_re] using h
    have hprin :
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re +
            c₀ * Real.log q := by
      rw [Complex.neg_re, Complex.neg_re]
      linarith
    have hBge : 1 ≤ 28 * (q : ℝ) * (|τ| + 2) := by
      have hτ' : 2 ≤ |τ| + 2 := by have := abs_nonneg τ; linarith
      nlinarith
    have hqlog : Real.log q ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 := by
      have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqge
      have hBpos : 0 < 28 * (q : ℝ) * (|τ| + 2) := lt_of_lt_of_le zero_lt_one hBge
      calc
        Real.log q ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) := by
          apply Real.log_le_log hqpos
          have hτ' : 1 ≤ |τ| + 2 := by have := abs_nonneg τ; linarith
          nlinarith [hqge]
        _ ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 := by linarith
    have htlog : Real.log |t| ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 := by
      have htpos : 0 < |t| := lt_of_lt_of_le zero_lt_one (by linarith [ht])
      have hBpos : 0 < 28 * (q : ℝ) * (|τ| + 2) := lt_of_lt_of_le zero_lt_one hBge
      have htle : |t| ≤ 28 * (q : ℝ) * (|τ| + 2) := by
        dsimp [t]
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hqge, abs_nonneg τ]
      have hlogle := Real.log_le_log htpos htle
      linarith
    have hζupper :
        (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          C * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
      have hζ' :
          -(deriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I) /
            riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ C * Real.log |t| := by
        simpa only [harg, logDeriv_apply] using hzeta
      have hlognonneg : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith [ht])
      have hCmul := mul_le_mul_of_nonneg_left htlog hCpos.le
      change -(deriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ _
      exact hζ'.trans (by linarith)
    have hpole : 0 ≤ (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re := by
      rw [Complex.div_re]
      simp [Complex.normSq, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.I_re, Complex.I_im]
      have hδpos : 0 < σ - 1 := by linarith
      apply div_nonneg
      · exact le_of_lt hδpos
      · exact le_of_lt (lt_of_lt_of_le (mul_pos hδpos hδpos)
          (le_add_of_nonneg_right (mul_self_nonneg τ)))
    have hlogs : 0 ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 := by
      have := Real.log_nonneg hBge
      linarith
    have hc₀ : 0 ≤ c₀ := by
      dsimp [c₀]
      have hpow : 0 < (2 : ℝ) ^ (-1 / 2 : ℝ) := by positivity
      have hpowlt : (2 : ℝ) ^ (-1 / 2 : ℝ) < 1 := by
        exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      positivity
    have hqterm := mul_le_mul_of_nonneg_left hqlog hc₀
    have hτterm := mul_le_mul_of_nonneg_left htlog hCpos.le
    have hsum : c₀ * Real.log q + C * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) ≤
        (C + c₀) * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
      nlinarith [hqterm, hτterm]
    have h :
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
          ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          (C + c₀) * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
      calc
        _ ≤ (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re +
            c₀ * Real.log q := hprin
        _ ≤ c₀ * Real.log q + C *
            (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
              linarith [hζupper]
        _ ≤ (C + c₀) * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := hsum
    have hKnonneg : 0 ≤ (C + c₀) * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
      apply mul_nonneg
      · linarith [hCpos.le, hc₀]
      · exact hlogs
    have hsumPole :
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
          ((σ : ℂ) + (τ : ℝ) * Complex.I)).re ≤
          (1 / ((σ : ℂ) + (τ : ℝ) * Complex.I - 1)).re +
            (C + c₀) * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
      exact h.trans (by linarith [hpole])
    change (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
        ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ _
    exact hsumPole

#print axioms exists_principal_LFunction_logDeriv_high_height_bound

/-- The actual principal-character logarithmic derivative is bounded by its
simple-pole contribution and a uniform logarithmic error at every height. -/
theorem exists_principal_LFunction_pole_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ {q : ℕ} [NeZero q], 1 ≤ (q : ℝ) →
      ∀ σ τ : ℝ, 1 < σ → σ ≤ 11 / 10 →
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
          ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re +
            K * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := by
  obtain ⟨K₁, hK₁pos, hhigh⟩ := exists_principal_LFunction_logDeriv_high_height_bound
  obtain ⟨C, hCpos, hlow⟩ :=
    exists_zeta_pole_corrected_logDeriv_bounded_height_bound
  let c₀ : ℝ := ((2 : ℝ) ^ (-1 / 2 : ℝ)) /
    (1 - (2 : ℝ) ^ (-1 / 2 : ℝ))
  let K : ℝ := max K₁ (C + c₀)
  have hKpos : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hKpos, ?_⟩
  intro q hq hqge σ τ hσ hσupper
  let B : ℝ := Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1
  have hBge : 1 ≤ 28 * (q : ℝ) * (|τ| + 2) := by
    have hτ' : 2 ≤ |τ| + 2 := by have := abs_nonneg τ; linarith
    nlinarith [hqge]
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Real.log_nonneg hBge]
  by_cases hτ : |τ| ≥ 4
  · have hhigh' := hhigh (q := q) hqge σ τ hσ (by linarith [hσupper]) hτ
    have hKle : K₁ ≤ K := le_max_left _ _
    have hBnonneg : 0 ≤ B := le_trans (by norm_num) hB
    dsimp [B] at hhigh' ⊢
    have hKscaled := mul_le_mul_of_nonneg_right hKle hBnonneg
    calc
      _ ≤ (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re +
          K₁ * (Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1) := hhigh'
      _ ≤ _ := by
        simpa only [add_comm ((1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re)] using
          (add_le_add_left hKscaled ((1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re))
  · have hτ' : |τ| ≤ 4 := le_of_not_ge hτ
    have hlow' := hlow σ τ hσ hσupper hτ'
    have hs : 0 < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simp; linarith
    have hsHalf : (1 / 2 : ℝ) ≤ ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by
      simp
      linarith
    have hs1 : (σ : ℂ) + (τ : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    have hzeta : riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I) ≠ 0 :=
      riemannZeta_ne_zero_of_one_lt_re (by simp; exact hσ)
    have hcorr := norm_sub_logDeriv_LFunctionTrivChar_le
      (by exact_mod_cast hqge) hs hsHalf hs1 hzeta
    have hcorr' :
        ‖logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I) -
          logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
            c₀ * Real.log q := by
      simpa [c₀, logDeriv_apply] using hcorr
    have hrealDiff :
        (logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re -
          (logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤ c₀ * Real.log q := by
      have h := (Complex.re_le_norm _).trans (by
        simpa only [norm_sub_rev] using hcorr')
      simpa only [Complex.sub_re] using h
    have hprin :
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re +
            c₀ * Real.log q := by
      rw [Complex.neg_re, Complex.neg_re]
      linarith
    have hqlog : Real.log q ≤ B := by
      have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le zero_lt_one hqge
      have hBargpos : 0 < 28 * (q : ℝ) * (|τ| + 2) := by linarith [hBge]
      have hargle : (q : ℝ) ≤ 28 * (q : ℝ) * (|τ| + 2) := by
        have hτnonneg : 0 ≤ |τ| := abs_nonneg τ
        nlinarith [hqge]
      dsimp [B]
      calc
        Real.log q ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) :=
          Real.log_le_log hqpos hargle
        _ ≤ Real.log (28 * (q : ℝ) * (|τ| + 2)) + 1 := by linarith
    have hc₀ : 0 ≤ c₀ := by
      dsimp [c₀]
      have hp : 0 < (2 : ℝ) ^ (-1 / 2 : ℝ) := by positivity
      have hplt : (2 : ℝ) ^ (-1 / 2 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      positivity
    have hCterm : C ≤ C * B := by nlinarith [hCpos, hB]
    have hc₀term := mul_le_mul_of_nonneg_left hqlog hc₀
    have hbudget : C + c₀ * Real.log q ≤ (C + c₀) * B := by nlinarith [hCterm, hc₀term]
    have hKle : C + c₀ ≤ K := le_max_right _ _
    have hKterm : (C + c₀) * B ≤ K * B := mul_le_mul_of_nonneg_right hKle (by linarith [hB])
    have hfinal :
        (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
            ((σ : ℂ) + (τ : ℂ) * Complex.I)).re ≤
          (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re + K * B := by
      calc
        _ ≤ (-logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * Complex.I)).re +
            c₀ * Real.log q := hprin
        _ ≤ (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re + C +
            c₀ * Real.log q := by
              have h := add_le_add_right hlow' (c₀ * Real.log q)
              simpa [Complex.neg_re, add_assoc, add_left_comm, add_comm] using h
        _ ≤ (1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re +
            (C + c₀) * B := by linarith [hbudget]
        _ ≤ _ := by
          simpa only [add_comm ((1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re)] using
            (add_le_add_left hKterm
              ((1 / ((σ : ℂ) + (τ : ℂ) * Complex.I - 1)).re))
    simpa [B] using hfinal

#print axioms exists_principal_LFunction_pole_log_bound

private theorem real_character_principal_pole_small
    (a ell c₀ t : ℝ) (ha : 0 < a) (hell : 0 < ell)
    (haSmall : a ≤ c₀ / 10) (ht : c₀ / ell ≤ |t|) :
    (a / ell) / ((a / ell) ^ 2 + (2 * t) ^ 2) ≤ (1 / 400) * ell / a := by
  let x : ℝ := a / ell
  have hx : 0 < x := div_pos ha hell
  have htim : 10 * x ≤ |t| := by
    calc
      10 * x = (10 * a) / ell := by dsimp [x]; ring
      _ ≤ c₀ / ell := div_le_div_of_nonneg_right (by linarith) hell.le
      _ ≤ |t| := ht
  have ht2 : (10 * x) ^ 2 ≤ t ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (by positivity : 0 ≤ 10 * x) htim 2
  have hden : 0 < x ^ 2 + (2 * t) ^ 2 := by positivity
  have hcore : x / (x ^ 2 + (2 * t) ^ 2) ≤ 1 / (400 * x) := by
    apply (div_le_div_iff₀ hden (by positivity : 0 < 400 * x)).mpr
    nlinarith
  have heq : 1 / (400 * x) = (1 / 400) * ell / a := by
    dsimp [x]
    field_simp
  rwa [heq] at hcore

#print axioms real_character_principal_pole_small

set_option maxHeartbeats 0 in
/-- A real nonprincipal character has no nonreal zero in a uniform
logarithmic region, with constants chosen before its modulus and height. -/
theorem dirichlet_LFunction_zero_free_real_character_nonreal_zero :
    ∃ c : ℝ, 0 < c ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ ≠ 1 → (∀ r : ZMod q, (χ r).im = 0) → ∀ z : ℂ,
        DirichletCharacter.LFunction χ z = 0 → z.im ≠ 0 →
          z.re ≤ 1 - c / (Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1) := by
  obtain ⟨Kp, hKp, hP⟩ := exists_principal_LFunction_pole_log_bound
  let ηp : ℝ := 1 / 10
  have hηp : 0 < ηp := by norm_num [ηp]
  obtain ⟨ηz, Cz, hηz, hCz, hζ⟩ := exists_neg_logDeriv_riemannZeta_real_upper_bound
  obtain ⟨c₀, hc₀, hlow⟩ := exists_dirichlet_LFunction_real_character_low_height_zero_real
  let K : ℝ := 8760 * (1 + Real.log 5 / Real.log (6 / 5 : ℝ))
  have hK : 0 < K := by
    dsimp [K]
    have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
    positivity
  let a : ℝ := min ηz (min ηp (min (c₀ / 10)
    (min (1 / 100) (1 / (100 * (K + Kp + Cz + 1))))))
  have ha : 0 < a := by dsimp [a]; positivity
  have haz : a ≤ ηz := min_le_left _ _
  have hap : a ≤ ηp := (min_le_right _ _).trans (min_le_left _ _)
  have hac₀ : a ≤ c₀ / 10 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have haSmall : a ≤ 1 / 100 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have haCost : a ≤ 1 / (100 * (K + Kp + Cz + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨a / 10, by positivity, ?_⟩
  intro q hq χ hχ hreal z hz him
  let ell₀ : ℝ := Real.log (56 * (q : ℝ)) + 1
  let ell : ℝ := Real.log (28 * (q : ℝ) * (|z.im| + 2)) + 1
  let σ : ℝ := 1 + a / ell
  have hqge : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast NeZero.pos q
  have hbase : 1 ≤ 56 * (q : ℝ) := by linarith
  have hell₀ : 1 ≤ ell₀ := by
    dsimp [ell₀]
    linarith [Real.log_nonneg hbase]
  have hell₀pos : 0 < ell₀ := lt_of_lt_of_le zero_lt_one hell₀
  have hellCompare : ell₀ ≤ ell := by
    dsimp [ell₀, ell]
    have hlog : Real.log (56 * (q : ℝ)) ≤ Real.log (28 * (q : ℝ) * (|z.im| + 2)) := by
      apply Real.log_le_log (by positivity)
      nlinarith [abs_nonneg z.im]
    exact add_le_add hlog le_rfl
  have hell : 1 ≤ ell := hell₀.trans hellCompare
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  by_contra hbad
  have hβ : 1 - (a / 10) / ell < z.re := lt_of_not_ge hbad
  have hβle : z.re ≤ 1 := dirichlet_LFunction_zero_re_le_one χ hz
  have hlowPay : (a / 10) / ell ≤ c₀ / ell₀ := by
    have hc : a / 10 ≤ c₀ := by linarith
    exact (div_le_div_of_nonneg_right hc hellpos.le).trans
      (div_le_div_of_nonneg_left hc₀.le hell₀pos hellCompare)
  have hheight : c₀ / ell₀ ≤ |z.im| := by
    by_contra h
    have hsmall : |z.im| < c₀ / ell₀ := lt_of_not_ge h
    exact him (hlow q hq χ hχ hreal z hz (by linarith) hsmall)
  have hheight' : c₀ / ell ≤ |z.im| :=
    (div_le_div_of_nonneg_left hc₀.le hell₀pos hellCompare).trans hheight
  have hσ : 1 < σ := by dsimp [σ]; exact lt_add_of_pos_right 1 (div_pos ha hellpos)
  have hratio : a / ell ≤ a := div_le_self ha.le hell
  have hσupper : σ ≤ 11 / 10 := by dsimp [σ]; linarith
  have hσz : σ ≤ 1 + ηz := by dsimp [σ]; linarith
  have hlog2 : Real.log (28 * (q : ℝ) * (|2 * z.im| + 2)) + 1 ≤ 2 * ell := by
    have hBpos : 0 < 28 * (q : ℝ) * (|z.im| + 2) := by positivity
    have hB2pos : 0 < 28 * (q : ℝ) * (|2 * z.im| + 2) := by positivity
    have hB2le : 28 * (q : ℝ) * (|2 * z.im| + 2) ≤
        2 * (28 * (q : ℝ) * (|z.im| + 2)) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [abs_nonneg z.im]
    have hlogs := Real.log_le_log hB2pos hB2le
    rw [Real.log_mul (by norm_num) hBpos.ne'] at hlogs
    have hlogTwo : Real.log 2 ≤ 1 := by
      calc
        Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    dsimp [ell] at hell ⊢
    linarith
  have hpole :
      (1 / ((σ : ℂ) + ((2 * z.im : ℝ) : ℂ) * Complex.I - 1)).re ≤
        (1 / 400) * ell / a := by
    have hformula :
        (1 / ((σ : ℂ) + ((2 * z.im : ℝ) : ℂ) * Complex.I - 1)).re =
        (a / ell) / ((a / ell) ^ 2 + (2 * z.im) ^ 2) := by
      rw [one_div, Complex.inv_re, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
        mul_zero, mul_one, zero_add, add_zero, sub_zero]
      dsimp [σ]
      ring
    rw [hformula]
    exact real_character_principal_pole_small a ell c₀ z.im ha hellpos hac₀ hheight'
  have harg : (σ : ℂ) + ((2 * z.im : ℝ) : ℂ) * Complex.I =
      (σ : ℂ) + 2 * (z.im : ℂ) * Complex.I := by push_cast; ring
  have hPbound :
      (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + 2 * (z.im : ℂ) * Complex.I)).re ≤
        (1 / 400) * ell / a + 2 * Kp * ell := by
    have hraw := hP (q := q) hqge σ (2 * z.im) hσ hσupper
    have hlogPaid := mul_le_mul_of_nonneg_left hlog2 hKp.le
    have hcore : (-logDeriv (DirichletCharacter.LFunctionTrivChar q)
        ((σ : ℂ) + ((2 * z.im : ℝ) : ℂ) * Complex.I)).re ≤
        (1 / 400) * ell / a + 2 * Kp * ell := by linarith
    rw [harg] at hcore
    rw [siegel_realCharacter_sq_eq_one χ hreal]
    exact hcore
  have hdiff : z - (2 + (z.im : ℂ) * Complex.I) = ((z.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hzU : z ∈ ball (2 + (z.im : ℂ) * Complex.I) (5 / 4 : ℝ) := by
    rw [mem_ball, dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith : z.re - 2 ≤ 0)]
    have hsmall : (a / 10) / ell ≤ 1 / 1000 := by
      have h := div_le_self (show 0 ≤ a / 10 by positivity) hell
      linarith
    linarith
  have hχbound := neg_re_dirichlet_LFunction_logDeriv_le_sub_zero
    χ hχ z.im σ hσ hσupper z hzU hz
  have hdenom : (σ : ℂ) + (z.im : ℂ) * Complex.I - z = ((σ - z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hrecip : (1 / ((σ : ℂ) + (z.im : ℂ) * Complex.I - z)).re =
      1 / (σ - z.re) := by
    rw [hdenom, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hrecip] at hχbound
  have hχbound' :
      (-logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (z.im : ℂ) * Complex.I)).re ≤ K * ell - 1 / (σ - z.re) := hχbound
  have hζbound : -(logDeriv riemannZeta (σ : ℂ)).re ≤ ell / a + Cz := by
    have h := hζ σ hσ hσz
    have hpoleReal : 1 / (σ - 1) = ell / a := by simp [σ]
    rwa [hpoleReal] at h
  have hpos := deLaValleePoussin_logDeriv_nonneg χ σ z.im hσ
  have hpos' : 0 ≤ 3 * (-(logDeriv riemannZeta (σ : ℂ)).re) +
      4 * (-logDeriv (DirichletCharacter.LFunction χ)
        ((σ : ℂ) + (z.im : ℂ) * Complex.I)).re +
      (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
        ((σ : ℂ) + 2 * (z.im : ℂ) * Complex.I)).re := by
    simpa [Complex.add_re, Complex.mul_re] using hpos
  have hcore : 4 / (σ - z.re) ≤
      (3 + 1 / 400) * ell / a + (3 * Cz + 4 * K + 2 * Kp) * ell := by
    have hCL : Cz ≤ Cz * ell := by nlinarith
    have hsumUpper := add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left hζbound (by norm_num : (0 : ℝ) ≤ 3))
        (mul_le_mul_of_nonneg_left hχbound' (by norm_num : (0 : ℝ) ≤ 4))) hPbound
    have hupper := hpos'.trans hsumUpper
    have hformula : 3 * (ell / a + Cz) + 4 * (K * ell - 1 / (σ - z.re)) +
        ((1 / 400) * ell / a + 2 * Kp * ell) =
        (3 + 1 / 400) * ell / a + 3 * Cz + (4 * K + 2 * Kp) * ell -
          4 / (σ - z.re) := by ring
    rw [hformula] at hupper
    nlinarith
  have hgap : 0 < σ - z.re := by linarith
  have hgapSmall : σ - z.re < (11 / 10) * a / ell := by
    dsimp [σ]
    have heq : (a / 10) / ell = (1 / 10) * (a / ell) := by ring
    rw [heq] at hβ
    have hupperEq : (11 / 10) * a / ell = (11 / 10) * (a / ell) := by ring
    rw [hupperEq]
    linarith
  have hrecipStrict := one_div_lt_one_div_of_lt hgap hgapSmall
  have hrecipScaled : (40 / 11) * ell / a < 4 / (σ - z.re) := by
    have h := mul_lt_mul_of_pos_left hrecipStrict (by norm_num : (0 : ℝ) < 4)
    have heq : 4 * (1 / ((11 / 10) * a / ell)) = (40 / 11) * ell / a := by
      field_simp
      norm_num
    rw [heq] at h
    simpa only [mul_one_div] using h
  have hpaid := (div_lt_iff₀ ha).mp (hrecipScaled.trans_le hcore)
  have hformula : ((3 + 1 / 400) * ell / a + (3 * Cz + 4 * K + 2 * Kp) * ell) * a =
      (3 + 1 / 400) * ell + a * (3 * Cz + 4 * K + 2 * Kp) * ell := by
    field_simp [ha.ne']
  rw [hformula] at hpaid
  have haCostPaid : a * (K + Kp + Cz + 1) ≤ 1 / 100 := by
    have h := (le_div_iff₀ (by positivity : 0 < 100 * (K + Kp + Cz + 1))).mp haCost
    nlinarith
  have htotalCost : a * (3 * Cz + 4 * K + 2 * Kp) ≤ 6 / 100 := by
    have hfactor : 3 * Cz + 4 * K + 2 * Kp ≤ 6 * (K + Kp + Cz + 1) := by
      linarith
    have hpaid := mul_le_mul_of_nonneg_left hfactor ha.le
    nlinarith
  have hcost := mul_le_mul_of_nonneg_right htotalCost hellpos.le
  linarith

#print axioms dirichlet_LFunction_zero_free_real_character_nonreal_zero

#print axioms zeta_add_character_logDeriv_nonneg
#print axioms exists_dirichlet_LFunction_real_axis_divisor_sum_bound
#print axioms neg_re_dirichlet_LFunction_logDeriv_le
#print axioms neg_re_dirichlet_LFunction_logDeriv_le_sub_zero

#print axioms deLaValleePoussin_vonMangoldt_term_nonneg
#print axioms deLaValleePoussin_vonMangoldt_LSeries_nonneg
#print axioms deLaValleePoussin_logDeriv_nonneg
#print axioms dirichlet_LFunction_zero_re_le_one
#print axioms dirichlet_LFunction_local_divisor_sum_nonneg
#print axioms dirichlet_LFunction_local_divisor_sum_ge_zero_term
#print axioms dirichlet_LFunction_local_divisor_sum_ge_reciprocal

end SystolicGrowth.CookMagyarMajorArc
