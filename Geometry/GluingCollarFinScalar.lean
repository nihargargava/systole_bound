module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Scalar fin-boundary estimate for the collar

This is the bounded scalar smooth-boundary estimate from the strip/fin
construction. It is an analytic input only, not a metric curvature theorem.
-/

open Set

namespace SystolicGrowth

private theorem x_cosh_sub_sinh_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x * Real.cosh x - Real.sinh x := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh |>.continuousOn
    · intro t ht
      have hd : HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
          (t * Real.sinh t) t := by
        convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
          (Real.hasDerivAt_sinh t) using 1 <;> first | rfl | simp
      exact hd.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici, mem_Ioi] at ht
      have hd : HasDerivAt (fun u : ℝ => u * Real.cosh u - Real.sinh u)
          (t * Real.sinh t) t := by
        convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).sub
          (Real.hasDerivAt_sinh t) using 1 <;> first | rfl | simp
      change 0 ≤ deriv (fun u : ℝ => u * Real.cosh u - Real.sinh u) t
      rw [hd.deriv]
      exact mul_nonneg (le_of_lt ht) (Real.sinh_nonneg_iff.mpr (le_of_lt ht))
  have hzero : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr le_rfl
  have := hmono hzero (Set.mem_Ici.mpr hx) hx
  simpa [Real.cosh_zero, Real.sinh_zero] using this

private theorem tanh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.tanh x ≤ x := by
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_le_iff₀ hcosh).2
  nlinarith [x_cosh_sub_sinh_nonneg hx]

private theorem sinh_div_bound {x : ℝ} (hx : 0 < x) :
    Real.cosh x * Real.sinh x / x ≤ Real.cosh x ^ 2 := by
  have h := x_cosh_sub_sinh_nonneg hx.le
  have hmul := mul_le_mul_of_nonneg_right h (Real.cosh_pos x).le
  have hx' : 0 < x := hx
  apply (div_le_iff₀ hx').2
  nlinarith [hmul]

private theorem cosh_sq_le_one_add_sq_cosh_bound {x M : ℝ}
    (hx : 0 ≤ x) (hM : 0 ≤ M) (hxm : x ≤ M) :
    Real.cosh x ^ 2 ≤ 1 + x ^ 2 * Real.cosh M ^ 2 := by
  have hsinh : Real.sinh x ≤ x * Real.cosh x := by
    nlinarith [x_cosh_sub_sinh_nonneg hx]
  have hsinh_nonneg : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  have hcosh_x : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh_bound : Real.cosh x ≤ Real.cosh M := by
    exact Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hx, abs_of_nonneg hM]; exact hxm)
  have hsinhM : Real.sinh x ≤ x * Real.cosh M := by
    calc
      Real.sinh x ≤ x * Real.cosh x := hsinh
      _ ≤ x * Real.cosh M := mul_le_mul_of_nonneg_left hcosh_bound hx
  have hsinhMsq : Real.sinh x ^ 2 ≤ (x * Real.cosh M) ^ 2 :=
    (sq_le_sq₀ hsinh_nonneg (mul_nonneg hx (Real.cosh_pos M).le)).2 hsinhM
  nlinarith [Real.cosh_sq_sub_sinh_sq x, hsinhMsq]

/-- The bounded CBA boundary estimate used by the AB04 fin approximation.
All smallness assumptions are explicit; in particular, no target-like
inequality is included among the hypotheses. -/
theorem gluingCollarFinScalar_boundary_estimate
    {ε F M p D : ℝ}
    (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hF : 0 < F) (hFM : F ≤ M) (hM : 0 < M)
    (hp : |p| ≤ D) (hD : 0 ≤ D)
    (hsmall : ε * (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2) ≤ 1) :
    (1 - ε) *
        (Real.cosh (Real.sqrt (1 - ε) * ε * F) *
            Real.sinh (Real.sqrt (1 - ε) * ε * F) /
              (Real.sqrt (1 - ε) * ε * F) +
          2 * ε ^ 2 * p ^ 2 *
            Real.tanh (Real.sqrt (1 - ε) * ε * F) /
              (Real.sqrt (1 - ε) * ε * F)) ≤ 1 := by
  let x := Real.sqrt (1 - ε) * ε * F
  have hεlt : ε < 1 := by linarith
  have hsqrt : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.2 (by linarith)
  have hsqrt_le : Real.sqrt (1 - ε) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxnonneg : 0 ≤ x := hxpos.le
  have hxM : x ≤ ε * M := by
    have hse : Real.sqrt (1 - ε) * ε ≤ ε := by
      nlinarith [mul_le_mul_of_nonneg_right hsqrt_le hε.le]
    dsimp [x]
    calc
      Real.sqrt (1 - ε) * ε * F ≤ ε * F :=
        mul_le_mul_of_nonneg_right hse hF.le
      _ ≤ ε * M := mul_le_mul_of_nonneg_left hFM hε.le
  have hxe : x ≤ M := by nlinarith [hxM, hε', hM]
  have hcosh : 0 < Real.cosh x := Real.cosh_pos x
  have hsinhbound := sinh_div_bound hxpos
  have hcoshsq := cosh_sq_le_one_add_sq_cosh_bound hxnonneg hM.le hxe
  have htanh := tanh_le_self_of_nonneg hxnonneg
  have hp2 : p ^ 2 ≤ D ^ 2 := by
    have hp' : |p| ^ 2 ≤ D ^ 2 := (sq_le_sq₀ (abs_nonneg p) hD).2 hp
    simpa [sq_abs] using hp'
  have hA : 0 ≤ M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2 := by positivity
  have hx2 : x ^ 2 ≤ ε ^ 2 * M ^ 2 := by nlinarith [hxM]
  have hterm1 : Real.cosh x * Real.sinh x / x ≤
      1 + ε ^ 2 * M ^ 2 * Real.cosh M ^ 2 := by
    calc
      Real.cosh x * Real.sinh x / x ≤ Real.cosh x ^ 2 := hsinhbound
      _ ≤ 1 + x ^ 2 * Real.cosh M ^ 2 := hcoshsq
      _ ≤ 1 + ε ^ 2 * M ^ 2 * Real.cosh M ^ 2 := by
        gcongr
  have hterm2 : Real.tanh x / x ≤ 1 := by
    exact (div_le_iff₀ hxpos).2 (by nlinarith [htanh])
  have hinside :
      Real.cosh x * Real.sinh x / x + 2 * ε ^ 2 * p ^ 2 * Real.tanh x / x ≤
        1 + ε ^ 2 * (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2) := by
    have hcoeff : 0 ≤ 2 * ε ^ 2 * p ^ 2 := by positivity
    calc
      _ ≤ 1 + ε ^ 2 * M ^ 2 * Real.cosh M ^ 2 + 2 * ε ^ 2 * p ^ 2 := by
        calc
          _ = (Real.cosh x * Real.sinh x / x) +
              (2 * ε ^ 2 * p ^ 2) * (Real.tanh x / x) := by ring
          _ ≤ _ := by
            simpa only [mul_one] using
              add_le_add hterm1 (mul_le_mul_of_nonneg_left hterm2 hcoeff)
      _ ≤ _ := by nlinarith [hp2]
  have hfinal : ε ^ 2 * (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2) ≤ ε := by
    nlinarith [mul_le_mul_of_nonneg_left hsmall hε.le]
  have hparent : (1 - ε) *
      (1 + ε ^ 2 * (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2)) ≤ 1 := by
    have hone : 0 ≤ 1 - ε := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hfinal hone]
  dsimp [x] at *
  calc
    _ ≤ (1 - ε) * (1 + ε ^ 2 * (M ^ 2 * Real.cosh M ^ 2 + 2 * D ^ 2)) := by
      gcongr
    _ ≤ 1 := hparent

#print axioms gluingCollarFinScalar_boundary_estimate

end SystolicGrowth
