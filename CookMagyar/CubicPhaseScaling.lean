module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicMajorArcPoweredModel
public import CookMagyar.SingularIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

open MeasureTheory

namespace SystolicGrowth.CookMagyarMajorArc

open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier CookMagyarReal

/-! # Removing the lower-order term after cubic rescaling

At frequency `tau/N³`, the smooth discrete phase is `x³ - x/N²` after
the substitution `t = Nx`. This file quantifies its convergence to the
homogeneous cubic phase used by the singular integral.
-/

private theorem norm_exp_I_mul_sub_exp_I_mul_le (u v : ℝ) :
    ‖Complex.exp (Complex.I * (u : ℂ)) -
        Complex.exp (Complex.I * (v : ℂ))‖ ≤ |u - v| := by
  have heq :
      Complex.exp (Complex.I * (u : ℂ)) -
          Complex.exp (Complex.I * (v : ℂ)) =
        Complex.exp (Complex.I * (v : ℂ)) *
          (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [heq, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v))

/-- The scaled `t³-t` phase differs from the cubic singular-integral
phase by `O(|tau|/N²)` on the unit interval. -/
theorem norm_cubicAbelWeight_scaled_sub_realAddChar_le
    (N : ℕ) (hN : 0 < N) (tau : ℝ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x) -
        realAddChar tau (x ^ 3)‖ ≤
      2 * Real.pi * |tau| / (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hphase :
      cubicAbelRealPhase (tau / (N : ℝ) ^ 3) ((N : ℝ) * x) =
        2 * Real.pi * tau * (x ^ 3 - x / (N : ℝ) ^ 2) := by
    unfold cubicAbelRealPhase
    field_simp
  have hab :
      cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x) =
        Complex.exp (Complex.I *
          ((2 * Real.pi * tau * (x ^ 3 - x / (N : ℝ) ^ 2) : ℝ) : ℂ)) := by
    unfold cubicAbelWeight
    rw [hphase]
    congr 1
    ring
  have hreal : realAddChar tau (x ^ 3) =
      Complex.exp (Complex.I * ((2 * Real.pi * tau * x ^ 3 : ℝ) : ℂ)) := by
    unfold realAddChar
    congr 1
    push_cast
    ring
  rw [hab, hreal]
  have hdiff := norm_exp_I_mul_sub_exp_I_mul_le
    (2 * Real.pi * tau * (x ^ 3 - x / (N : ℝ) ^ 2))
    (2 * Real.pi * tau * x ^ 3)
  have hbound :
      |2 * Real.pi * tau * (x ^ 3 - x / (N : ℝ) ^ 2) -
          2 * Real.pi * tau * x ^ 3| ≤
        2 * Real.pi * |tau| / (N : ℝ) ^ 2 := by
    have hxabs : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    have hden : 0 ≤ (N : ℝ) ^ 2 := by positivity
    have heq :
        |2 * Real.pi * tau * (x ^ 3 - x / (N : ℝ) ^ 2) -
          2 * Real.pi * tau * x ^ 3| =
        2 * Real.pi * |tau| * |x| / (N : ℝ) ^ 2 := by
      have halg :
          2 * Real.pi * tau * (x ^ 3 - x / (N : ℝ) ^ 2) -
            2 * Real.pi * tau * x ^ 3 =
          -(2 * Real.pi * tau * x / (N : ℝ) ^ 2) := by ring
      rw [halg, abs_neg, abs_div, abs_mul, abs_mul, abs_mul]
      simp [abs_of_nonneg hpi, abs_of_nonneg hden, mul_assoc]
    rw [heq]
    exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hxabs
          (show 0 ≤ 2 * Real.pi * |tau| by positivity))) hden
  exact hdiff.trans hbound

/-- After rescaling to `[0,1]`, the continuous cubic Abel factor converges
to the one-dimensional singular-integral factor with an explicit error. -/
theorem norm_integral_scaled_cubicAbelWeight_sub_oneDimensional_le
    (N : ℕ) (hN : 0 < N) (tau : ℝ) :
    ‖(∫ x in Set.Icc (0 : ℝ) 1,
        cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x)) -
        oneDimensionalCubicIntegral tau‖ ≤
      2 * Real.pi * |tau| / (N : ℝ) ^ 2 := by
  have hscaled : IntegrableOn
      (fun x : ℝ =>
        cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x))
      (Set.Icc (0 : ℝ) 1) := by
    apply Continuous.integrableOn_Icc
    unfold cubicAbelWeight cubicAbelRealPhase
    fun_prop
  have hbase : IntegrableOn (fun x : ℝ => realAddChar tau (x ^ 3))
      (Set.Icc (0 : ℝ) 1) :=
    oneDimensionalCubicIntegrand_integrable tau
  unfold oneDimensionalCubicIntegral
  rw [← integral_sub hscaled hbase]
  calc
    ‖∫ x in Set.Icc (0 : ℝ) 1,
        cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x) -
          realAddChar tau (x ^ 3)‖ ≤
      (2 * Real.pi * |tau| / (N : ℝ) ^ 2) *
        volume.real (Set.Icc (0 : ℝ) 1) := by
        apply norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
        intro x hx
        exact norm_cubicAbelWeight_scaled_sub_realAddChar_le N hN tau hx
    _ = 2 * Real.pi * |tau| / (N : ℝ) ^ 2 := by simp

/-- Exact change of variables for the continuous Abel weight. -/
theorem integral_cubicAbelWeight_eq_scaled_integral
    (N : ℕ) (tau : ℝ) :
    (∫ t in Set.Icc (0 : ℝ) N,
        cubicAbelWeight (tau / (N : ℝ) ^ 3) t) =
      (N : ℝ) •
        ∫ x in Set.Icc (0 : ℝ) 1,
          cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x) := by
  let f : ℝ → ℂ := cubicAbelWeight (tau / (N : ℝ) ^ 3)
  have hleft :
      (∫ t in Set.Icc (0 : ℝ) N, f t) =
        ∫ t in (0 : ℝ)..(N : ℝ), f t := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N),
      ← integral_Icc_eq_integral_Ioc]
  have hright :
      (∫ x in Set.Icc (0 : ℝ) 1, f ((N : ℝ) * x)) =
        ∫ x in (0 : ℝ)..(1 : ℝ), f ((N : ℝ) * x) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
  change (∫ t in Set.Icc (0 : ℝ) N, f t) =
    (N : ℝ) • ∫ x in Set.Icc (0 : ℝ) 1, f ((N : ℝ) * x)
  rw [hleft, hright]
  simpa only [mul_zero, mul_one] using (intervalIntegral.smul_integral_comp_mul_left
    (f := f) (a := (0 : ℝ)) (b := (1 : ℝ)) (N : ℝ)).symm

/-- At cubic frequency `tau/N³`, the unscaled Abel integral is within
`2π|tau|/N` of `N` times the homogeneous singular-integral factor. -/
theorem norm_integral_cubicAbelWeight_sub_scaledCubicIntegral_le
    (N : ℕ) (hN : 0 < N) (tau : ℝ) :
    ‖(∫ t in Set.Icc (0 : ℝ) N,
        cubicAbelWeight (tau / (N : ℝ) ^ 3) t) -
        (N : ℝ) • oneDimensionalCubicIntegral tau‖ ≤
      2 * Real.pi * |tau| / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [integral_cubicAbelWeight_eq_scaled_integral, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos hNr]
  calc
    (N : ℝ) *
        ‖(∫ x in Set.Icc (0 : ℝ) 1,
          cubicAbelWeight (tau / (N : ℝ) ^ 3) ((N : ℝ) * x)) -
          oneDimensionalCubicIntegral tau‖ ≤
      (N : ℝ) * (2 * Real.pi * |tau| / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_scaled_cubicAbelWeight_sub_oneDimensional_le
            N hN tau) hNr.le
    _ = 2 * Real.pi * |tau| / (N : ℝ) := by
      field_simp

/-- The normalized first-power prime sum is compared directly with the
homogeneous cubic factor used by the singular integral. The only unproved
input here is the stated quantitative AP discrepancy. -/
theorem norm_cubicVonMangoldtExpSum_sub_homogeneousModel_le_of_AP
    (q : ℕ) [NeZero q] (a N Q : ℕ) {tau Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta) (htau : |tau| ≤ Q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicVonMangoldtExpSum
        (rationalCenter a q + tau / (N : ℝ) ^ 3) N -
        (unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) *
          ((N : ℝ) • oneDimensionalCubicIntegral tau)‖ ≤
      ((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) +
      2 * Real.pi * |tau| / (N : ℝ) := by
  let U : ℂ := unitCubicExponentialSum (a : ZMod q) *
    (Nat.totient q : ℂ)⁻¹
  let J : ℂ := ∫ t in Set.Icc (0 : ℝ) N,
    cubicAbelWeight (tau / (N : ℝ) ^ 3) t
  let I : ℂ := (N : ℝ) • oneDimensionalCubicIntegral tau
  let S : ℂ := cubicVonMangoldtExpSum
    (rationalCenter a q + tau / (N : ℝ) ^ 3) N
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hbeta : |tau / (N : ℝ) ^ 3| ≤ cubicArcRadius N Q := by
    unfold cubicArcRadius
    rw [abs_div, abs_pow, abs_of_pos hNr]
    exact div_le_div_of_nonneg_right htau (by positivity)
  have hfirst : ‖S - U * J‖ ≤
      ((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) := by
    simpa only [S, U, J, mul_assoc] using
      norm_cubicVonMangoldtExpSum_sub_normalizedIntegralModel_le_on_arc
        q a N Q hN hDelta hbeta hAP
  have hsecond : ‖J - I‖ ≤ 2 * Real.pi * |tau| / (N : ℝ) :=
    norm_integral_cubicAbelWeight_sub_scaledCubicIntegral_le N hN tau
  have hU : ‖U‖ ≤ 1 :=
    norm_unitCubicExponentialSum_mul_inv_totient_le_one q (a : ZMod q)
  calc
    ‖S - U * I‖ ≤ ‖S - U * J‖ + ‖U * J - U * I‖ :=
      norm_sub_le_norm_sub_add_norm_sub S (U * J) (U * I)
    _ = ‖S - U * J‖ + ‖U‖ * ‖J - I‖ := by
      rw [← mul_sub, norm_mul]
    _ ≤ ((q : ℝ) * Delta + 1) *
          (1 + 8 * Real.pi * (Q : ℝ)) +
        2 * Real.pi * |tau| / (N : ℝ) := by
      have hlast : ‖U‖ * ‖J - I‖ ≤
          2 * Real.pi * |tau| / (N : ℝ) := by
        calc
          ‖U‖ * ‖J - I‖ ≤ 1 * ‖J - I‖ :=
            mul_le_mul_of_nonneg_right hU (norm_nonneg _)
          _ ≤ 2 * Real.pi * |tau| / (N : ℝ) := by
            simpa only [one_mul] using hsecond
      exact add_le_add hfirst hlast

/-- The same arithmetic and phase errors propagate to the powered
Fourier integrand at the homogeneous cubic model. -/
theorem norm_cubicIntegrand_sub_homogeneousModel_le_of_AP
    (q : ℕ) [NeZero q] (a N Q n T : ℕ) {tau Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta) (htau : |tau| ≤ Q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicIntegrand n N T
        (rationalCenter a q + tau / (N : ℝ) ^ 3) -
        ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) *
          ((N : ℝ) • oneDimensionalCubicIntegral tau)) ^ n *
          negAddChar (rationalCenter a q + tau / (N : ℝ) ^ 3) T‖ ≤
      (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((q : ℝ) * Delta + 1) *
          (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * |tau| / (N : ℝ)) := by
  let x : ℂ := cubicVonMangoldtExpSum
    (rationalCenter a q + tau / (N : ℝ) ^ 3) N
  let y : ℂ := (unitCubicExponentialSum (a : ZMod q) *
    (Nat.totient q : ℂ)⁻¹) *
      ((N : ℝ) • oneDimensionalCubicIntegral tau)
  let B : ℝ := (Real.log 4 + 4) * (N : ℝ)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hx : ‖x‖ ≤ B :=
    (norm_cubicVonMangoldtExpSum_le_mass _ _).trans
      (cubicVonMangoldtMass_le_const_mul N)
  have hy : ‖y‖ ≤ B := by
    have hU := norm_unitCubicExponentialSum_mul_inv_totient_le_one
      q (a : ZMod q)
    have hI := norm_oneDimensionalCubicIntegral_le_one tau
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    have hscaled :
        ‖(N : ℝ) • oneDimensionalCubicIntegral tau‖ ≤ (N : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hNnonneg]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hI hNnonneg)
    have hmodel : ‖y‖ ≤ (N : ℝ) := by
      change ‖(unitCubicExponentialSum (a : ZMod q) *
        (Nat.totient q : ℂ)⁻¹) *
          ((N : ℝ) • oneDimensionalCubicIntegral tau)‖ ≤ (N : ℝ)
      rw [norm_mul]
      calc
        ‖unitCubicExponentialSum (a : ZMod q) *
            (Nat.totient q : ℂ)⁻¹‖ *
            ‖(N : ℝ) • oneDimensionalCubicIntegral tau‖ ≤
          1 * (N : ℝ) := by gcongr
        _ = (N : ℝ) := one_mul _
    exact hmodel.trans (by dsimp [B]; nlinarith)
  have hfirst : ‖x - y‖ ≤
      ((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) +
      2 * Real.pi * |tau| / (N : ℝ) :=
    norm_cubicVonMangoldtExpSum_sub_homogeneousModel_le_of_AP
      q a N Q hN hDelta htau hAP
  have hpower := norm_pow_sub_pow_le x y n hB hx hy
  change ‖x ^ n *
      negAddChar (rationalCenter a q + tau / (N : ℝ) ^ 3) T -
      y ^ n *
        negAddChar (rationalCenter a q + tau / (N : ℝ) ^ 3) T‖ ≤
    (n : ℝ) * B ^ (n - 1) *
      (((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) +
        2 * Real.pi * |tau| / (N : ℝ))
  rw [← sub_mul, norm_mul, norm_negAddChar, mul_one]
  exact hpower.trans (mul_le_mul_of_nonneg_left hfirst
    (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hB _)))

end SystolicGrowth.CookMagyarMajorArc
