module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

/-
## Vendoring provenance

Extracted from
`RiemannDynamics/Hyperbolic/DiskModel/MobiusDisk.lean`, lines 36–90 and 96–166,
at immutable upstream commit `b3fa37cc0f18a23ea66b654ea3f73eb472129010` of
https://github.com/will1491/RiemannDynamics. The upstream file is Apache-2.0 licensed.
The original header and proofs are retained; imports and namespace are adapted.
Only the disk automorphism lemmas needed by `DiscAutomorphisms` are retained.
The unrelated zero-value and distance-translation lemmas are not copied.
-/
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-! # Elementary Möbius disc automorphisms for the imported classification -/

namespace SystolicGrowth.Vendored.RiemannDynamics

open Complex Metric

/-- The Möbius transformation `M_w(z) = (z − w) / (1 − conj(w) · z)`. -/
noncomputable def mobiusDisk (w z : ℂ) : ℂ :=
  (z - w) / (1 - (starRingEnd ℂ) w * z)

/-- **Möbius automorphism norm identity**:
`‖1 − conj(w) · z‖² − ‖z − w‖² = (1 − ‖z‖²) · (1 − ‖w‖²)`. -/
theorem mobiusDisk_normSq_identity (z w : ℂ) :
    ‖1 - (starRingEnd ℂ) w * z‖ ^ 2 - ‖z - w‖ ^ 2
      = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := by
  have h1 : ‖1 - (starRingEnd ℂ) w * z‖ ^ 2
      = Complex.normSq (1 - (starRingEnd ℂ) w * z) :=
    (Complex.normSq_eq_norm_sq _).symm
  have h2 : ‖z - w‖ ^ 2 = Complex.normSq (z - w) :=
    (Complex.normSq_eq_norm_sq _).symm
  have h3 : ‖z‖ ^ 2 = Complex.normSq z := (Complex.normSq_eq_norm_sq z).symm
  have h4 : ‖w‖ ^ 2 = Complex.normSq w := (Complex.normSq_eq_norm_sq w).symm
  rw [h1, h2, h3, h4]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
             Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
             Complex.one_re, Complex.one_im]
  ring

/-- For `z, w ∈ 𝔻 = ball 0 1`, the denominator `1 − conj(w) · z` is nonzero. -/
theorem mobiusDisk_denom_ne_zero {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    (1 : ℂ) - (starRingEnd ℂ) w * z ≠ 0 := by
  have hz1 : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have hw1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have h_prod : ‖(starRingEnd ℂ) w * z‖ < 1 := by
    rw [norm_mul, RCLike.norm_conj]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg w) hw1 hz1.le
  intro heq
  have h1 : (starRingEnd ℂ) w * z = 1 := by linear_combination -heq
  have : ‖((starRingEnd ℂ) w * z : ℂ)‖ = 1 := by rw [h1]; simp
  linarith

/-- The "conjugate self" expression `conj w * w` equals the real scalar `‖w‖²`. -/
theorem conj_mul_self_eq_normSq (w : ℂ) :
    (starRingEnd ℂ) w * w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj']; push_cast; ring

/-- For `w ∈ 𝔻`, `1 − conj(w) · w ≠ 0`. -/
theorem one_sub_conj_self_ne_zero {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    (1 : ℂ) - (starRingEnd ℂ) w * w ≠ 0 := by
  have hw1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have h_real_ne : (1 - ‖w‖ ^ 2 : ℝ) ≠ 0 := by
    have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
    linarith
  rw [conj_mul_self_eq_normSq]
  rw [show (1 : ℂ) - ((‖w‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) from by push_cast; ring]
  exact_mod_cast h_real_ne

/-- `M_w(w) = 0`. -/
theorem mobiusDisk_self (w : ℂ) : mobiusDisk w w = 0 := by
  unfold mobiusDisk; simp

/-- `M_{-w}(0) = w`. -/
theorem mobiusDisk_neg_apply_zero (w : ℂ) : mobiusDisk (-w) 0 = w := by
  unfold mobiusDisk; simp

/-- `‖mobiusDisk w z‖ = ‖z − w‖ / ‖1 − conj(w) · z‖`. -/
theorem mobiusDisk_norm (z w : ℂ) :
    ‖mobiusDisk w z‖ = ‖z - w‖ / ‖1 - (starRingEnd ℂ) w * z‖ := by
  unfold mobiusDisk; rw [norm_div]

/-- On the disk, `mobiusDisk w` maps `𝔻 → 𝔻`. -/
theorem mobiusDisk_mapsTo {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    mobiusDisk w z ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right]
  have hz1 : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right] at hz
  have hw1 : ‖w‖ < 1 := by rwa [mem_ball, dist_zero_right] at hw
  have hz2 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hw2 : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h_denom_ne : (1 : ℂ) - (starRingEnd ℂ) w * z ≠ 0 :=
    mobiusDisk_denom_ne_zero hz hw
  have h_denom_norm_pos : 0 < ‖1 - (starRingEnd ℂ) w * z‖ :=
    norm_pos_iff.mpr h_denom_ne
  have h_id : ‖1 - (starRingEnd ℂ) w * z‖ ^ 2 - ‖z - w‖ ^ 2
      = (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) :=
    mobiusDisk_normSq_identity z w
  have h_pos : 0 < (1 - ‖z‖ ^ 2) * (1 - ‖w‖ ^ 2) := mul_pos hz2 hw2
  have h_lt : ‖z - w‖ ^ 2 < ‖1 - (starRingEnd ℂ) w * z‖ ^ 2 := by linarith
  rw [mobiusDisk_norm, div_lt_one h_denom_norm_pos]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h_lt

/-- The inverse identity: `mobiusDisk (-w) ∘ mobiusDisk w = id` on `𝔻`. -/
theorem mobiusDisk_neg_mobiusDisk {z w : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ ball (0 : ℂ) 1) :
    mobiusDisk (-w) (mobiusDisk w z) = z := by
  have hD : (1 : ℂ) - (starRingEnd ℂ) w * z ≠ 0 :=
    mobiusDisk_denom_ne_zero hz hw
  have hone_minus_ne : (1 : ℂ) - (starRingEnd ℂ) w * w ≠ 0 :=
    one_sub_conj_self_ne_zero hw
  -- The outer Möbius denominator, after substituting the inner Möbius and
  -- normalising signs, equals `(1 − conj w · w) / (1 − conj w · z)`.
  have hOuter_eq :
      (1 : ℂ) + (starRingEnd ℂ) w * ((z - w) / (1 - (starRingEnd ℂ) w * z))
        = (1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) := by
    field_simp
    ring
  have hOuter_ne :
      (1 : ℂ) + (starRingEnd ℂ) w * ((z - w) / (1 - (starRingEnd ℂ) w * z)) ≠ 0 := by
    rw [hOuter_eq]; exact div_ne_zero hone_minus_ne hD
  -- Same for the outer numerator.
  have hOuterNum_eq :
      (z - w) / (1 - (starRingEnd ℂ) w * z) + w
        = z * (1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) := by
    rw [div_add' _ _ _ hD, mul_div_assoc]
    ring
  have hRatio_ne :
      (1 - (starRingEnd ℂ) w * w) / (1 - (starRingEnd ℂ) w * z) ≠ 0 :=
    div_ne_zero hone_minus_ne hD
  unfold mobiusDisk
  simp only [map_neg, neg_mul, sub_neg_eq_add]
  rw [hOuterNum_eq, hOuter_eq, mul_div_assoc, mul_div_cancel_right₀ _ hRatio_ne]

/-- `mobiusDisk w` is differentiable on `𝔻`. -/
theorem mobiusDisk_differentiableOn {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    DifferentiableOn ℂ (mobiusDisk w) (ball (0 : ℂ) 1) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold mobiusDisk
  refine DifferentiableAt.div ?_ ?_ (mobiusDisk_denom_ne_zero hz hw)
  · exact (differentiable_id.differentiableAt).sub_const w
  · exact (differentiableAt_const _).sub
      ((differentiableAt_const _).mul differentiable_id.differentiableAt)

#print axioms mobiusDisk_mapsTo
#print axioms mobiusDisk_neg_mobiusDisk
#print axioms mobiusDisk_differentiableOn

end SystolicGrowth.Vendored.RiemannDynamics

