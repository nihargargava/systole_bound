module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SiegelCharacterBounds
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-!
# From a real zero to the value at one

Cauchy's estimate on a logarithmic-radius circle gives an actual uniform
derivative bound for the nonprincipal Dirichlet `L`-function near one.
The mean-value estimate retains a real zero as the lower endpoint. A
coarse estimate handles zeros outside that neighborhood, and a scalar
logarithm bound absorbs the resulting logarithmic square into any positive
power of the modulus.
-/

open scoped Topology

namespace SystolicGrowth.CookMagyarCircle

open Metric Set

variable {q : ℕ} [NeZero q]

/-- The actual complex derivative has a logarithmic-square bound in the
real logarithmic neighborhood of one. -/
theorem siegel_LFunction_deriv_norm_le_near_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {x : ℝ}
    (hxlo : 1 - 1 / (4 * (1 + Real.log q)) ≤ x) (hxhi : x ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
      16 * Real.exp 1 * (1 + Real.log q) ^ 2 := by
  let A : ℝ := 1 + Real.log q
  let r : ℝ := 1 / (4 * A)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqpos : (0 : ℝ) < q := by positivity
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_natCast_nonneg q
  have hA : 1 ≤ A := by dsimp only [A]; linarith
  have hApos : 0 < A := by linarith
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrle : r ≤ 1 / 4 := by
    dsimp only [r]
    apply (div_le_iff₀ (by positivity : 0 < 4 * A)).mpr
    linarith
  have hAr : r * A = 1 / 4 := by dsimp only [r]; field_simp
  have hxlo' : 1 - r ≤ x := hxlo
  have hxpos : 0 ≤ x := by linarith
  have hpow : (q : ℝ) ^ (2 * r) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hqpos]
    apply Real.exp_le_exp.mpr
    have hlogA : Real.log (q : ℝ) ≤ A := by dsimp only [A]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hlogA (show 0 ≤ 2 * r by positivity)]
  have hsphere (s : ℂ) (hs : s ∈ sphere (x : ℂ) r) :
      ‖DirichletCharacter.LFunction χ s‖ ≤ 4 * Real.exp 1 * A := by
    have hdist : ‖s - (x : ℂ)‖ = r := mem_sphere_iff_norm.mp hs
    have hreLower : x - s.re ≤ r := by
      calc
        x - s.re = ((x : ℂ) - s).re := by simp
        _ ≤ ‖(x : ℂ) - s‖ := Complex.re_le_norm _
        _ = r := by rw [norm_sub_rev, hdist]
    have hstrip : 1 - 2 * r ≤ s.re := by linarith
    have hre : 1 / 2 ≤ s.re := by linarith
    have hspos : 0 < s.re := by linarith
    have hnorm : ‖s‖ ≤ 5 / 4 := by
      calc
        ‖s‖ = ‖s - (x : ℂ) + (x : ℂ)‖ := by rw [sub_add_cancel]
        _ ≤ ‖s - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
        _ = r + x := by rw [hdist, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos]
        _ ≤ 5 / 4 := by linarith
    have hquot : ‖s‖ / s.re ≤ 3 := by
      apply (div_le_iff₀ hspos).mpr
      linarith
    have hfactor : A + ‖s‖ / s.re ≤ 4 * A := by linarith
    have hbound := siegel_LFunction_norm_le_near_one χ hχ
      (show 0 ≤ 2 * r by positivity) hspos hstrip
    change ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) ^ (2 * r) *
      (A + ‖s‖ / s.re) at hbound
    calc
      _ ≤ (q : ℝ) ^ (2 * r) * (A + ‖s‖ / s.re) := hbound
      _ ≤ Real.exp 1 * (4 * A) :=
        mul_le_mul hpow hfactor (by positivity) (by positivity)
      _ = _ := by ring
  change ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤ 16 * Real.exp 1 * A ^ 2
  calc
    _ ≤ (4 * Real.exp 1 * A) / r :=
      Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
        (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl hsphere
    _ = _ := by dsimp only [r]; field_simp; ring

/-- A real zero in the logarithmic neighborhood controls the actual value
at one, with no derivative estimate supplied as a premise. -/
theorem siegel_LFunction_one_norm_le_of_real_zero_near_one
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {β : ℝ}
    (hβlo : 1 - 1 / (4 * (1 + Real.log q)) ≤ β) (hβhi : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (1 - β) * (16 * Real.exp 1 * (1 + Real.log q) ^ 2) := by
  have hderiv (x : ℝ) (hx : x ∈ Icc β 1) :
      HasDerivWithinAt (fun x : ℝ => DirichletCharacter.LFunction χ (x : ℂ))
        (deriv (DirichletCharacter.LFunction χ) (x : ℂ)) (Icc β 1) x :=
    (χ.differentiableAt_LFunction (x : ℂ) (Or.inr hχ)).hasDerivAt.comp_ofReal.hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Ico β 1) :
      ‖deriv (DirichletCharacter.LFunction χ) (x : ℂ)‖ ≤
        16 * Real.exp 1 * (1 + Real.log q) ^ 2 :=
    siegel_LFunction_deriv_norm_le_near_one χ hχ (hβlo.trans hx.1) hx.2.le
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    1 (right_mem_Icc.mpr hβhi)
  simpa only [Complex.ofReal_one, hzero, sub_zero, mul_comm] using hmean

/-- Any real zero below one controls `L(χ,1)`. Zeros outside the small
Cauchy neighborhood are covered by the actual coarse value-at-one bound. -/
theorem siegel_LFunction_one_norm_le_of_real_zero
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {β : ℝ} (hβhi : β < 1)
    (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (1 - β) * (16 * Real.exp 1 * (1 + Real.log q) ^ 2) := by
  by_cases hnear : 1 - 1 / (4 * (1 + Real.log q)) ≤ β
  · exact siegel_LFunction_one_norm_le_of_real_zero_near_one χ hχ hnear hβhi.le hzero
  · let A : ℝ := 1 + Real.log q
    have hA : 1 ≤ A := by dsimp only [A]; linarith [Real.log_natCast_nonneg q]
    have hApos : 0 < A := by linarith
    have hδ : 1 / (4 * A) ≤ 1 - β := by change ¬1 - 1 / (4 * A) ≤ β at hnear; linarith
    have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    calc
      _ ≤ 2 + Real.log q := siegel_LFunction_one_norm_le χ hχ
      _ ≤ 2 * A := by dsimp only [A]; linarith [Real.log_natCast_nonneg q]
      _ ≤ (1 / (4 * A)) * (16 * Real.exp 1 * A ^ 2) := by
        have heq : (1 / (4 * A)) * (16 * Real.exp 1 * A ^ 2) = 4 * Real.exp 1 * A := by
          field_simp
          ring
        rw [heq]
        nlinarith [mul_le_mul_of_nonneg_right hexp hApos.le]
      _ ≤ (1 - β) * (16 * Real.exp 1 * A ^ 2) :=
        mul_le_mul_of_nonneg_right hδ (by positivity)
      _ = _ := rfl

/-- The logarithmic square is absorbed into any positive modulus power,
uniformly for every positive natural modulus rather than only eventually. -/
theorem siegel_logSquare_le_modulus_rpow {ε : ℝ} (hε : 0 < ε) :
    (1 + Real.log q) ^ 2 ≤ (1 + 2 / ε) ^ 2 * (q : ℝ) ^ ε := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hhalf : 0 < ε / 2 := by positivity
  have hpow : 1 ≤ (q : ℝ) ^ (ε / 2) := Real.one_le_rpow hq1 hhalf.le
  have hlog := Real.log_le_rpow_div hqnonneg hhalf
  have hquot : (q : ℝ) ^ (ε / 2) / (ε / 2) =
      (2 / ε) * (q : ℝ) ^ (ε / 2) := by field_simp
  rw [hquot] at hlog
  have hsum : 1 + Real.log q ≤ (1 + 2 / ε) * (q : ℝ) ^ (ε / 2) := by nlinarith
  have hpoweq : ((q : ℝ) ^ (ε / 2)) ^ 2 = (q : ℝ) ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hqnonneg]
    congr 1
    norm_num
  calc
    _ ≤ ((1 + 2 / ε) * (q : ℝ) ^ (ε / 2)) ^ 2 :=
      pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg q]) hsum 2
    _ = _ := by rw [mul_pow, hpoweq]

/-- The actual zero-to-value bound with any positive power loss. This
consumes the constructed derivative bound and supplies the final scalar
adapter for a uniform lower bound on `L(χ,1)`. -/
theorem siegel_LFunction_one_norm_le_of_real_zero_rpow
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε)
    {β : ℝ} (hβhi : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤
      (1 - β) * (16 * Real.exp 1 * (1 + 2 / ε) ^ 2) * (q : ℝ) ^ ε := by
  calc
    _ ≤ (1 - β) * (16 * Real.exp 1 * (1 + Real.log q) ^ 2) :=
      siegel_LFunction_one_norm_le_of_real_zero χ hχ hβhi hzero
    _ ≤ (1 - β) * (16 * Real.exp 1 * ((1 + 2 / ε) ^ 2 * (q : ℝ) ^ ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (siegel_logSquare_le_modulus_rpow hε) (by positivity))
        (by linarith)
    _ = _ := by ring

/-- The final pointwise rate transfer: the actual uniform value lower
bound with loss `ε` gives the real-zero distance with loss `2ε`.
All derivative and logarithmic losses are already discharged above. -/
theorem siegel_real_zero_lower_of_one_norm_lower
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ε c β : ℝ} (hε : 0 < ε)
    (hLower : c * (q : ℝ) ^ (-ε) ≤ ‖DirichletCharacter.LFunction χ 1‖)
    (hβhi : β < 1) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    (c / (16 * Real.exp 1 * (1 + 2 / ε) ^ 2)) * (q : ℝ) ^ (-2 * ε) ≤
      1 - β := by
  let D : ℝ := 16 * Real.exp 1 * (1 + 2 / ε) ^ 2
  have hD : 0 < D := by dsimp only [D]; positivity
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hUpper := siegel_LFunction_one_norm_le_of_real_zero_rpow χ hχ hε hβhi hzero
  change ‖DirichletCharacter.LFunction χ 1‖ ≤ (1 - β) * D * (q : ℝ) ^ ε at hUpper
  have hpower : (q : ℝ) ^ ε * (q : ℝ) ^ (-ε) = 1 := by
    rw [← Real.rpow_add hq, add_neg_cancel, Real.rpow_zero]
  have hrate : c * (q : ℝ) ^ (-2 * ε) ≤ (1 - β) * D := by
    calc
      _ = (c * (q : ℝ) ^ (-ε)) * (q : ℝ) ^ (-ε) := by
        rw [mul_assoc, ← Real.rpow_add hq]
        congr 2
        ring
      _ ≤ ((1 - β) * D * (q : ℝ) ^ ε) * (q : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (hLower.trans hUpper) (Real.rpow_nonneg hq.le _)
      _ = (1 - β) * D := by rw [mul_assoc, hpower, mul_one]
  change (c / D) * (q : ℝ) ^ (-2 * ε) ≤ 1 - β
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ hD).mpr hrate

end SystolicGrowth.CookMagyarCircle
