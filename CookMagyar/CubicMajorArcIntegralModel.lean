module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicResidueAbel

@[expose] public section

open Finset MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.CookMagyarMajorArc

open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier

/-! # From progression sums to a continuous cubic major-arc model

This separates the arithmetic-progression error from the deterministic
sum-to-integral error. The former still requires a quantitative prime number
theorem in progressions; the latter is proved in `CubicResidueAbel`.
-/

/-- The complete cubic unit sum is bounded trivially by the number of
invertible residue classes. -/
theorem norm_unitCubicExponentialSum_le_totient
    (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖unitCubicExponentialSum a‖ ≤ (Nat.totient q : ℝ) := by
  unfold unitCubicExponentialSum
  calc
    ‖∑ u : (ZMod q)ˣ,
        standardAdditiveCharacter (a * cubicResidue (u : ZMod q))‖ ≤
        ∑ u : (ZMod q)ˣ,
          ‖standardAdditiveCharacter (a * cubicResidue (u : ZMod q))‖ :=
      norm_sum_le _ _
    _ = (Nat.totient q : ℝ) := by
      simp [AddChar.norm_apply, ZMod.card_units_eq_totient]

/-- The normalized complete cubic sum has norm at most one. -/
theorem norm_unitCubicExponentialSum_mul_inv_totient_le_one
    (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖unitCubicExponentialSum a * (Nat.totient q : ℂ)⁻¹‖ ≤ 1 := by
  have hpos : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  simp only [norm_mul, norm_inv, norm_natCast]
  exact (mul_inv_le_iff₀ hpos).2
    (by simpa using norm_unitCubicExponentialSum_le_totient q a)

/-- On a cubic major arc, the Abel variation is at most a fixed multiple
of the denominator cutoff, independently of the scale `N`. -/
theorem cubicAbelVariation_le_of_arc_radius
    (N Q : ℕ) (hN : 0 < N) {beta : ℝ}
    (hbeta : |beta| ≤ cubicArcRadius N Q) :
    1 + (N : ℝ) *
      (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) ≤
        1 + 8 * Real.pi * (Q : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpoly : 3 * (N : ℝ) ^ 2 + 1 ≤ 4 * (N : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hbeta' : |beta| ≤ (Q : ℝ) / (N : ℝ) ^ 3 := by
    simpa only [cubicArcRadius] using hbeta
  calc
    1 + (N : ℝ) *
        (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) ≤
      1 + (N : ℝ) *
        (2 * Real.pi * ((Q : ℝ) / (N : ℝ) ^ 3) *
          (4 * (N : ℝ) ^ 2)) := by
      gcongr
    _ = 1 + 8 * Real.pi * (Q : ℝ) := by
      field_simp
      ring

/-- The continuous cubic weight has integral mass at most the interval
length. -/
theorem norm_integral_cubicAbelWeight_le (beta : ℝ) (N : ℕ) :
    ‖∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t‖ ≤ (N : ℝ) := by
  have hfin : volume (Set.Icc (0 : ℝ) N) < ∞ := by simp
  have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) N,
      ‖cubicAbelWeight beta t‖ ≤ (1 : ℝ) := by
    intro t _ht
    simp [cubicAbelWeight_norm]
  have h := norm_setIntegral_le_of_norm_le_const hfin hpoint
  simpa [Measure.real] using h

/-- The normalized continuous major-arc model is bounded by its length. -/
theorem norm_normalizedCubicIntegralModel_le
    (q : ℕ) [NeZero q] (a : ZMod q) (beta : ℝ) (N : ℕ) :
    ‖unitCubicExponentialSum a *
        ((Nat.totient q : ℂ)⁻¹ *
          ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)‖ ≤
      (N : ℝ) := by
  rw [← mul_assoc, norm_mul]
  calc
    ‖unitCubicExponentialSum a * (Nat.totient q : ℂ)⁻¹‖ *
        ‖∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t‖ ≤
      1 * (N : ℝ) := by
        gcongr
        · exact norm_unitCubicExponentialSum_mul_inv_totient_le_one q a
        · exact norm_integral_cubicAbelWeight_le beta N
    _ = (N : ℝ) := one_mul _

/-- An arithmetic-progression partial-sum estimate gives a continuous
first-power model, with the discretization loss stated separately. -/
theorem norm_cubicVonMangoldtExpSum_sub_integralModel_le_of_AP
    (q : ℕ) [NeZero q] (a : ℕ) (A : ℂ)
    (beta : ℝ) (N : ℕ) {Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) * (if IsUnit r then A else 0)‖ ≤ Delta) :
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) *
          (A * ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)‖ ≤
      (q : ℝ) *
        (Delta * (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)))) +
      ‖unitCubicExponentialSum (a : ZMod q) * A‖ *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  let S : ℂ := cubicVonMangoldtExpSum (rationalCenter a q + beta) N
  let U : ℂ := unitCubicExponentialSum (a : ZMod q)
  let W : ℂ := ∑ k ∈ Icc 0 N, addChar beta (primeCubic k)
  let J : ℂ := ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t
  have hstep :
      ‖S - U * (A * W)‖ ≤
        (q : ℝ) * (Delta * (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)))) := by
    exact norm_cubicVonMangoldtExpSum_sub_stepModel_le_of_AP
      q a A beta N hN hDelta hAP
  have hdisc :
      ‖W - J‖ ≤
        1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)) := by
    simpa only [W, J, ← cubicAbelWeight_nat] using
      norm_sum_cubicAbelWeight_sub_integral_le beta N
  calc
    ‖S - U * (A * J)‖ ≤
        ‖S - U * (A * W)‖ + ‖U * (A * W) - U * (A * J)‖ :=
      norm_sub_le_norm_sub_add_norm_sub S (U * (A * W)) (U * (A * J))
    _ = ‖S - U * (A * W)‖ + ‖U * A‖ * ‖W - J‖ := by
      congr 1
      rw [← mul_assoc, ← mul_assoc, ← mul_sub, norm_mul]
    _ ≤ (q : ℝ) * (Delta * (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1)))) +
        ‖U * A‖ * (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
      exact add_le_add hstep (mul_le_mul_of_nonneg_left hdisc (norm_nonneg _))

/-- With the singular-series normalization, the discretization error loses
no factor depending on the modulus. -/
theorem norm_cubicVonMangoldtExpSum_sub_normalizedIntegralModel_le_of_AP
    (q : ℕ) [NeZero q] (a : ℕ)
    (beta : ℝ) (N : ℕ) {Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) *
          ((Nat.totient q : ℂ)⁻¹ *
            ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)‖ ≤
      ((q : ℝ) * Delta + 1) *
        (1 + (N : ℝ) *
          (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) := by
  let V : ℝ := 1 + (N : ℝ) *
    (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have h := norm_cubicVonMangoldtExpSum_sub_integralModel_le_of_AP
    q a (Nat.totient q : ℂ)⁻¹ beta N hN hDelta hAP
  have hnorm := norm_unitCubicExponentialSum_mul_inv_totient_le_one
    q (a : ZMod q)
  calc
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) *
          ((Nat.totient q : ℂ)⁻¹ *
            ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)‖ ≤
        (q : ℝ) * (Delta * V) +
          ‖unitCubicExponentialSum (a : ZMod q) *
            (Nat.totient q : ℂ)⁻¹‖ * V := h
    _ ≤ ((q : ℝ) * Delta + 1) * V := by
      nlinarith [mul_le_mul_of_nonneg_right hnorm hV]

/-- The first-power major-arc approximation is uniform in the real
displacement once it lies inside the cubic arc radius. -/
theorem norm_cubicVonMangoldtExpSum_sub_normalizedIntegralModel_le_on_arc
    (q : ℕ) [NeZero q] (a : ℕ)
    (N Q : ℕ) {beta Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hbeta : |beta| ≤ cubicArcRadius N Q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) *
          ((Nat.totient q : ℂ)⁻¹ *
            ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)‖ ≤
      ((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) := by
  calc
    ‖cubicVonMangoldtExpSum (rationalCenter a q + beta) N -
        unitCubicExponentialSum (a : ZMod q) *
          ((Nat.totient q : ℂ)⁻¹ *
            ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)‖ ≤
        ((q : ℝ) * Delta + 1) *
          (1 + (N : ℝ) *
            (2 * Real.pi * |beta| * (3 * (N : ℝ) ^ 2 + 1))) :=
      norm_cubicVonMangoldtExpSum_sub_normalizedIntegralModel_le_of_AP
        q a beta N hN hDelta hAP
    _ ≤ ((q : ℝ) * Delta + 1) *
          (1 + 8 * Real.pi * (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (cubicAbelVariation_le_of_arc_radius N Q hN hbeta)
        (by positivity)

end SystolicGrowth.CookMagyarMajorArc
