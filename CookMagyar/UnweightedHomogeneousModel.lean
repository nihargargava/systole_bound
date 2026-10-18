module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.UnweightedCompleteModel
public import CookMagyar.CubicPhaseScaling
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open MeasureTheory Finset

namespace SystolicGrowth
namespace CookMagyarMajorArc

open CookMagyarCircle CookMagyarArcs CookMagyarReal

/-! # Homogeneous all-residue cubic model

This completes the elementary model conversion on auxiliary major arcs.
Unlike the prime major arcs, the complete sum includes every residue.
-/

/-- The rescaled inhomogeneous real cubic integral differs from its
homogeneous limit by the lower-order linear phase. -/
theorem norm_integral_cubicAbelWeight_sub_homogeneous_le
    (N : ℕ) (hN : 0 < N) (beta : ℝ) :
    ‖(∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t) -
        (N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖ ≤
      2 * Real.pi * |beta| * (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hβ : beta * (N : ℝ) ^ 3 / (N : ℝ) ^ 3 = beta := by
    field_simp
  have h := norm_integral_cubicAbelWeight_sub_scaledCubicIntegral_le
    N hN (beta * (N : ℝ) ^ 3)
  rw [hβ] at h
  calc
    ‖(∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t) -
        (N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)‖ ≤
      2 * Real.pi * |beta * (N : ℝ) ^ 3| / (N : ℝ) := h
    _ = 2 * Real.pi * |beta| * (N : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)]
      field_simp

/-- Complete all-residue sum times the scaled homogeneous cubic factor. -/
noncomputable def cubicAllResidueHomogeneousModel
    (q : ℕ) [NeZero q] (a : ZMod q) (beta : ℝ) (N : ℕ) : ℂ :=
  allResidueCubicExponentialSum q a * ((1 / (q : ℝ) : ℝ) : ℂ) *
    ((N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3))

/-- Explicit ordinary-cubic major-arc approximation, uniform in the
residue center and displacement, before restricting to a power cutoff. -/
theorem norm_cubicUnweightedExpSum_sub_homogeneousModel_le
    (q a N : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N) (beta : ℝ) :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
      ((q : ℝ) + 1) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) +
        2 * Real.pi * |beta| * (N : ℝ) ^ 2 := by
  let C : ℂ := allResidueCubicExponentialSum q (a : ZMod q)
  let A : ℂ := C * ((1 / (q : ℝ) : ℝ) : ℂ)
  let J : ℂ := ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t
  let V : ℂ := (N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoef : ‖A‖ ≤ 1 := by
    dsimp [A, C]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (q : ℝ))]
    calc
      ‖allResidueCubicExponentialSum q (a : ZMod q)‖ * (1 / (q : ℝ)) ≤
          (q : ℝ) * (1 / (q : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (norm_allResidueCubicExponentialSum_le q (a : ZMod q))
          (by positivity)
      _ = 1 := by field_simp
  have hJV : ‖J - V‖ ≤ 2 * Real.pi * |beta| * (N : ℝ) ^ 2 := by
    simpa only [J, V] using
      norm_integral_cubicAbelWeight_sub_homogeneous_le N hN beta
  have hmodel :
      ‖cubicAllResidueIntegralModel q (a : ZMod q) beta N -
          cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
        2 * Real.pi * |beta| * (N : ℝ) ^ 2 := by
    have heq :
        cubicAllResidueIntegralModel q (a : ZMod q) beta N -
            cubicAllResidueHomogeneousModel q (a : ZMod q) beta N =
          A * (J - V) := by
      dsimp [cubicAllResidueIntegralModel,
        cubicAllResidueHomogeneousModel, A, C, J, V]
      ring
    rw [heq, norm_mul]
    simpa only [one_mul] using
      (mul_le_mul hcoef hJV (norm_nonneg _) (by norm_num))
  calc
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
      ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
          cubicAllResidueIntegralModel q (a : ZMod q) beta N‖ +
        ‖cubicAllResidueIntegralModel q (a : ZMod q) beta N -
          cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ((q : ℝ) + 1) *
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) +
          2 * Real.pi * |beta| * (N : ℝ) ^ 2 := by
      exact add_le_add
        (norm_cubicUnweightedExpSum_sub_allResidueIntegralModel_le
          q a N hq hN beta) hmodel

/-- On the auxiliary power-cutoff arcs, the elementary model error is
quadratic in the cutoff. The hypotheses use the exact rational-center
displacement rather than periodic distance. -/
theorem norm_cubicUnweightedExpSum_sub_homogeneousModel_le_auxCutoff
    (q a N P : ℕ) [NeZero q] (hq : 0 < q) (hN : 0 < N)
    (hqP : q ≤ P) (beta : ℝ)
    (hbeta : |beta| * (N : ℝ) ^ 3 ≤ (P : ℝ)) :
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
      64 * ((P : ℝ) + 1) ^ 2 := by
  let X : ℝ := N
  let Y : ℝ := P
  let b : ℝ := |beta|
  have hX : 1 ≤ X := by dsimp [X]; exact_mod_cast hN
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hb : 0 ≤ b := abs_nonneg beta
  have hbX : b * X ^ 3 ≤ Y := by simpa only [b, X, Y] using hbeta
  have hqY : (q : ℝ) ≤ Y := by dsimp [Y]; exact_mod_cast hqP
  have hXsq : 1 ≤ X ^ 2 := by nlinarith
  have hpoly : 3 * X ^ 2 + 1 ≤ 4 * X ^ 2 := by nlinarith
  have hvar : X * b * (3 * X ^ 2 + 1) ≤ 4 * Y := by
    calc
      X * b * (3 * X ^ 2 + 1) ≤ X * b * (4 * X ^ 2) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 4 * (b * X ^ 3) := by ring
      _ ≤ 4 * Y := by linarith
  have hXpow : X ^ 2 ≤ X ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg X) (sub_nonneg.mpr hX)]
  have hlinear : b * X ^ 2 ≤ Y := by
    calc
      b * X ^ 2 ≤ b * X ^ 3 := mul_le_mul_of_nonneg_left hXpow hb
      _ ≤ Y := hbX
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hE :
      1 + X * (2 * Real.pi * b * (3 * X ^ 2 + 1)) ≤
        1 + 32 * Y := by
    have hmul := mul_le_mul_of_nonneg_left hvar
      (show 0 ≤ 2 * Real.pi by positivity)
    have hpiY : 8 * Real.pi * Y ≤ 32 * Y := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hY]
    nlinarith
  have hlast : 2 * Real.pi * b * X ^ 2 ≤ 8 * Y := by
    have hmul := mul_le_mul_of_nonneg_left hlinear
      (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hY]
  have hE0 : 0 ≤ 1 + X * (2 * Real.pi * b * (3 * X ^ 2 + 1)) := by
    positivity
  have hfirst :
      ((q : ℝ) + 1) *
          (1 + X * (2 * Real.pi * b * (3 * X ^ 2 + 1))) ≤
        (Y + 1) * (1 + 32 * Y) := by
    exact mul_le_mul (by linarith) hE (by positivity) (by linarith)
  have hpolyfinal : (Y + 1) * (1 + 32 * Y) + 8 * Y ≤
      64 * (Y + 1) ^ 2 := by
    nlinarith [sq_nonneg Y]
  calc
    ‖cubicUnweightedExpSum (rationalCenter a q + beta) N -
        cubicAllResidueHomogeneousModel q (a : ZMod q) beta N‖ ≤
      ((q : ℝ) + 1) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) +
        2 * Real.pi * |beta| * (N : ℝ) ^ 2 :=
      norm_cubicUnweightedExpSum_sub_homogeneousModel_le q a N hq hN beta
    _ ≤ (Y + 1) * (1 + 32 * Y) + 8 * Y := by
      simpa only [X, Y, b] using add_le_add hfirst hlast
    _ ≤ 64 * (Y + 1) ^ 2 := hpolyfinal
    _ = 64 * ((P : ℝ) + 1) ^ 2 := rfl

end CookMagyarMajorArc
end SystolicGrowth
