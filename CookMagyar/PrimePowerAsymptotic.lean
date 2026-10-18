module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaMoment
public import CookMagyar.PrimePowerBridge
public import CookMagyar.PrimePowerMass

@[expose] public section

open Filter Asymptotics

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Asymptotic removal of prime powers

The exact Fourier and union-bound argument in `PrimePowerBridge` reduces
prime-power removal to an eighth moment.  This file completes all remaining
asymptotic bookkeeping.  The sole analytic input is the familiar weak form
of Hua's estimate

`∫ |S_N(α)|⁸ dα = o(N⁵ √N)`.

Cook--Magyar (and the classical cubic Hua lemma) gives the stronger bound
`O(N^(5+ε))` for every positive `ε`.  Thus the statement below deliberately
uses less than the available saving, while avoiding any target parameter:
the discarded error is automatically uniform in `T`.
-/

/-- The weak Hua estimate sufficient for deleting proper prime powers and
the prime `2` in every arity `n ≥ 9`. -/
def CubicHuaEstimate : Prop :=
  (fun N : ℕ ↦ cubicVonMangoldtEighthMoment N) =o[atTop]
    (fun N : ℕ ↦ (N : ℝ) ^ 5 * Real.sqrt N)

/-- The target-independent upper envelope furnished by the exact
prime-power-removal argument. -/
noncomputable def cubicDiscardedEnvelope (n N : ℕ) : ℝ :=
  (n : ℝ) *
    (cubicBadPrimePowerMass N *
      cubicVonMangoldtMass N ^ (n - 9) *
        cubicVonMangoldtEighthMoment N)

theorem cubicDiscardedRepresentation_le_envelope
    {n N T : ℕ} (hn : 9 ≤ n) :
    cubicDiscardedRepresentation n N T ≤ cubicDiscardedEnvelope n N := by
  exact cubicDiscardedRepresentation_le_eighthMoment_error hn

theorem cubicDiscardedEnvelope_nonneg (n N : ℕ) :
    0 ≤ cubicDiscardedEnvelope n N := by
  have hmoment : 0 ≤ cubicVonMangoldtEighthMoment N := by
    unfold cubicVonMangoldtEighthMoment
    exact MeasureTheory.integral_nonneg fun _ ↦ by positivity
  unfold cubicDiscardedEnvelope
  exact mul_nonneg (by positivity)
    (mul_nonneg
      (mul_nonneg (cubicBadPrimePowerMass_nonneg N)
        (pow_nonneg (cubicVonMangoldtMass_nonneg N) _))
      hmoment)

private theorem comparison_scale_identity {n : ℕ} (hn : 9 ≤ n) (N : ℕ) :
    (Real.sqrt N * (N : ℝ) ^ (n - 9)) *
        ((N : ℝ) ^ 5 * Real.sqrt N) =
      (N : ℝ) ^ (n - 3) := by
  have hsqrt : Real.sqrt (N : ℝ) * Real.sqrt N = (N : ℝ) := by
    calc
      Real.sqrt (N : ℝ) * Real.sqrt N = Real.sqrt (N : ℝ) ^ 2 := by ring
      _ = (N : ℝ) := Real.sq_sqrt (by positivity)
  rw [show
      (Real.sqrt N * (N : ℝ) ^ (n - 9)) *
          ((N : ℝ) ^ 5 * Real.sqrt N) =
        ((N : ℝ) ^ (n - 9) * (N : ℝ) ^ 5) *
          (Real.sqrt N * Real.sqrt N) by ring]
  rw [hsqrt, ← pow_add, ← pow_succ]
  congr 1
  omega

/-- Once the cubic Hua estimate is supplied, the complete discarded
prime-power envelope is little-oh of the natural circle-method scale. -/
theorem cubicDiscardedEnvelope_isLittleO
    (hua : CubicHuaEstimate) {n : ℕ} (hn : 9 ≤ n) :
    (fun N : ℕ ↦ cubicDiscardedEnvelope n N) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ (n - 3)) := by
  have hbad := isBigO_cubicBadPrimePowerMass_sqrt
  have hmass := isBigO_cubicVonMangoldtMass_id
  have hmassPow := hmass.pow (n - 9)
  have hpre := hbad.mul hmassPow
  have hprod := hpre.mul_isLittleO hua
  have hright :
      (fun N : ℕ ↦
        (Real.sqrt N * (N : ℝ) ^ (n - 9)) *
          ((N : ℝ) ^ 5 * Real.sqrt N)) =
        (fun N : ℕ ↦ (N : ℝ) ^ (n - 3)) := by
    funext N
    exact comparison_scale_identity hn N
  rw [hright] at hprod
  have hprod' :
      (fun N : ℕ ↦
        (cubicBadPrimePowerMass N *
          cubicVonMangoldtMass N ^ (n - 9)) *
            cubicVonMangoldtEighthMoment N) =o[atTop]
        (fun N : ℕ ↦ (N : ℝ) ^ (n - 3)) := by
    exact hprod
  simpa only [cubicDiscardedEnvelope, mul_assoc] using
    hprod'.const_mul_left (n : ℝ)

/-- Quantitative, target-uniform prime-power removal.  Any prescribed
positive fraction of `N^(n-3)` eventually dominates the discarded weighted
count, simultaneously for every target `T`. -/
theorem eventually_discarded_le_mul_cubicMainScale
    (hua : CubicHuaEstimate) {n : ℕ} (hn : 9 ≤ n)
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ T : ℕ,
      cubicDiscardedRepresentation n N T ≤
        c * (N : ℝ) ^ (n - 3) := by
  have hlo := cubicDiscardedEnvelope_isLittleO hua hn
  filter_upwards [hlo.bound hc] with N hN
  intro T
  calc
    cubicDiscardedRepresentation n N T ≤ cubicDiscardedEnvelope n N :=
      cubicDiscardedRepresentation_le_envelope hn
    _ = ‖cubicDiscardedEnvelope n N‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (cubicDiscardedEnvelope_nonneg n N)]
    _ ≤ c * ‖(N : ℝ) ^ (n - 3)‖ := hN
    _ = c * (N : ℝ) ^ (n - 3) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end CookMagyarCircle
end SystolicGrowth
