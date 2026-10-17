module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicMajorArcIntegralModel
public import CookMagyar.PrimePowerMass
public import CookMagyar.ArcPhasePeriodicity

@[expose] public section

namespace SystolicGrowth.CookMagyarMajorArc

open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier

/-! # Powered continuous model on a cubic major arc

The elementary Chebyshev mass bound controls both the prime sum and its
normalized continuous model at scale `N`. The remaining pointwise error is
exactly the arithmetic-progression discrepancy from the first-power bridge.
-/

/-- An AP partial-sum estimate controls the powered major-arc integrand,
uniformly in the target `T` and in displacements inside the cubic arc. -/
theorem norm_cubicIntegrand_sub_normalizedIntegralModel_le_on_arc
    (q : ℕ) [NeZero q] (a : ℕ)
    (N Q n T : ℕ) {beta Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (hbeta : |beta| ≤ cubicArcRadius N Q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicIntegrand n N T (rationalCenter a q + beta) -
        (unitCubicExponentialSum (a : ZMod q) *
          ((Nat.totient q : ℂ)⁻¹ *
            ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)) ^ n *
          negAddChar (rationalCenter a q + beta) T‖ ≤
      (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((q : ℝ) * Delta + 1) *
          (1 + 8 * Real.pi * (Q : ℝ))) := by
  let x : ℂ := cubicVonMangoldtExpSum (rationalCenter a q + beta) N
  let y : ℂ := unitCubicExponentialSum (a : ZMod q) *
    ((Nat.totient q : ℂ)⁻¹ *
      ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)
  let B : ℝ := (Real.log 4 + 4) * (N : ℝ)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hx : ‖x‖ ≤ B :=
    (norm_cubicVonMangoldtExpSum_le_mass _ _).trans
      (cubicVonMangoldtMass_le_const_mul N)
  have hy : ‖y‖ ≤ B := by
    have hmodel := norm_normalizedCubicIntegralModel_le
      q (a : ZMod q) beta N
    have hNnonneg : (0 : ℝ) ≤ N := by positivity
    exact hmodel.trans (by dsimp [B]; nlinarith)
  have hfirst : ‖x - y‖ ≤
      ((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) :=
    norm_cubicVonMangoldtExpSum_sub_normalizedIntegralModel_le_on_arc
      q a N Q hN hDelta hbeta hAP
  have hpower := norm_pow_sub_pow_le x y n hB hx hy
  change ‖x ^ n * negAddChar (rationalCenter a q + beta) T -
      y ^ n * negAddChar (rationalCenter a q + beta) T‖ ≤
    (n : ℝ) * B ^ (n - 1) *
      (((q : ℝ) * Delta + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)))
  rw [← sub_mul, norm_mul, norm_negAddChar, mul_one]
  exact hpower.trans (mul_le_mul_of_nonneg_left hfirst
    (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hB _)))

/-- The same powered estimate applies to a clipped arc even when it wraps
across the endpoints of the unit interval. -/
theorem exists_normalizedIntegralModel_error_of_mem_majorArcAt
    (q a N Q n T : ℕ) [NeZero q] {alpha Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (halpha : alpha ∈ majorArcAt N Q a q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ∃ beta : ℝ, |beta| < cubicArcRadius N Q ∧
      ‖cubicIntegrand n N T alpha -
          (unitCubicExponentialSum (a : ZMod q) *
            ((Nat.totient q : ℂ)⁻¹ *
              ∫ t in Set.Icc (0 : ℝ) N, cubicAbelWeight beta t)) ^ n *
            negAddChar (rationalCenter a q + beta) T‖ ≤
        (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((q : ℝ) * Delta + 1) *
            (1 + 8 * Real.pi * (Q : ℝ))) := by
  obtain ⟨beta, hbeta, heq⟩ :=
    cubicIntegrand_eq_center_add_small_displacement n T halpha
  refine ⟨beta, hbeta, ?_⟩
  rw [heq]
  exact norm_cubicIntegrand_sub_normalizedIntegralModel_le_on_arc
    q a N Q n T hN hDelta (le_of_lt hbeta) hAP

end SystolicGrowth.CookMagyarMajorArc
