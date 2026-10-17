module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PerronOscillatoryKernel
public import CookMagyar.PerronCoefficientSeries
public import CookMagyar.PerronHalfIntegerHarmonic

@[expose] public section

/-!
# Far-range coefficient summation for truncated Perron

Outside the middle window, logarithmic separation is at least one half.
The scalar truncation error is therefore dominated by the absolutely
convergent von Mangoldt coefficient series, with a universal constant.
The contour limit need not be evaluated to establish this remainder bound.
-/

open Finset

namespace SystolicGrowth.CookMagyarCircle

/- TASK-SLOT PERRON-AMPLITUDE: P07 is implemented below with a universal
constant. The endpoint specialization belongs to the later MA01 assembly. -/

/-- The near-one Perron abscissa increases the amplitude by at most `exp 1`
when the positive base lies below the logarithmic endpoint. -/
theorem perron_rpow_one_add_inv_log_le
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) (hy : 1 < y) :
    x ^ (1 + (Real.log y)⁻¹) ≤ Real.exp 1 * x := by
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogs : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  have hscaled : Real.log x * (Real.log y)⁻¹ ≤ 1 := by
    simpa only [mul_inv_cancel₀ hlogy.ne'] using
      mul_le_mul_of_nonneg_right hlogs (inv_nonneg.mpr hlogy.le)
  rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_def_of_pos hx]
  calc
    _ ≤ x * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscaled) hx.le
    _ = _ := mul_comm _ _

/-- Either far window gives a uniform nonzero logarithmic frequency. -/
theorem perronLogRatio_far_ge_half (x : ℝ) (k : ℕ)
    (hx : 0 < x) (hk : 0 < k)
    (hfar : (k : ℝ) ≤ x / 2 ∨ 2 * x ≤ (k : ℝ)) :
    (1 / 2 : ℝ) ≤ |Real.log (x / (k : ℝ))| := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hgap : (1 / 2 : ℝ) ≤ |x - (k : ℝ)| / max x (k : ℝ) := by
    rcases hfar with hlo | hhi
    · have hkx : (k : ℝ) ≤ x := by linarith
      rw [max_eq_left hkx, abs_of_nonneg (sub_nonneg.mpr hkx)]
      exact (le_div_iff₀ hx).mpr (by linarith)
    · have hxk : x ≤ (k : ℝ) := by linarith
      rw [max_eq_right hxk, abs_of_nonpos (sub_nonpos.mpr hxk)]
      exact (le_div_iff₀ hkR).mpr (by linarith)
  exact hgap.trans (perronLogRatio_gap x (k : ℝ) hx hkR)

/-- A far-index truncation error is bounded by a fixed multiple of its
von Mangoldt Dirichlet coefficient. -/
theorem vonMangoldt_far_perronScalarKernel_error_le
    (x σ H : ℝ) (k : ℕ) (hx : 0 < x) (hk : 0 < k)
    (hσ : 0 < σ) (hH : 0 < H)
    (hfar : (k : ℝ) ≤ x / 2 ∨ 2 * x ≤ (k : ℝ)) :
    ArithmeticFunction.vonMangoldt k *
      ‖(((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (x / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel x k σ t‖ ≤
      (36 * x ^ σ / H) *
        (ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) := by
  have hfreq := perronLogRatio_far_ge_half x k hx hk hfar
  have hlog : Real.log (x / (k : ℝ)) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hfreq
    norm_num at hfreq
  have herr := norm_perronScalarKernel_limit_sub_integral_le x σ H k hx hk hσ hH hlog
  have hden : H * (1 / 2 : ℝ) ≤ H * |Real.log (x / (k : ℝ))| :=
    mul_le_mul_of_nonneg_left hfreq hH.le
  have hscalar :
      ‖(((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (x / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel x k σ t‖ ≤
      36 * (x / (k : ℝ)) ^ σ / H := by
    calc
      _ ≤ 18 * (x / (k : ℝ)) ^ σ / (H * |Real.log (x / (k : ℝ))|) := herr
      _ ≤ 18 * (x / (k : ℝ)) ^ σ / (H * (1 / 2 : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by ring
  calc
    _ ≤ ArithmeticFunction.vonMangoldt k * (36 * (x / (k : ℝ)) ^ σ / H) :=
      mul_le_mul_of_nonneg_left hscalar ArithmeticFunction.vonMangoldt_nonneg
    _ = _ := by rw [Real.div_rpow hx.le (Nat.cast_nonneg k)]; ring

/-- The entire finite far-range remainder fits a conductor-independent
Perron error budget. -/
theorem sum_far_perronScalarKernel_truncation_error_le
    (x σ H : ℝ) (s : Finset ℕ) (hx : 0 < x)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hH : 0 < H)
    (hkpos : ∀ k ∈ s, 0 < k)
    (hfar : ∀ k ∈ s, (k : ℝ) ≤ x / 2 ∨ 2 * x ≤ (k : ℝ)) :
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k *
      ‖(((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (x / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel x k σ t‖) ≤
      216 * x ^ σ / (H * (σ - 1) ^ 2) := by
  obtain ⟨hcoeffsum, hcoeffbound⟩ :=
    vonMangoldt_rpow_series_summable_and_tsum_le σ hσ hσ₂
  have hpartial :
      (∑ k ∈ s, ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) ≤
        ∑' k : ℕ, ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ :=
    hcoeffsum.sum_le_tsum s (fun k _ =>
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) σ))
  calc
    _ ≤ ∑ k ∈ s, (36 * x ^ σ / H) *
        (ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ) :=
      sum_le_sum (fun k hk => vonMangoldt_far_perronScalarKernel_error_le
        x σ H k hx (hkpos k hk) (by linarith) hH (hfar k hk))
    _ = (36 * x ^ σ / H) *
        ∑ k ∈ s, ArithmeticFunction.vonMangoldt k / (k : ℝ) ^ σ := (mul_sum _ _ _).symm
    _ ≤ (36 * x ^ σ / H) * (6 / (σ - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (hpartial.trans hcoeffbound) (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/- TASK-SLOT PERRON-RANGE-SPLIT: P11 is implemented below using a disjoint
filter/complement partition of an arbitrary finite set of positive indices. -/

/-- Every finite positive-index remainder is bounded by the sum of the
middle-window and far-window budgets, without double-counting endpoints. -/
theorem sum_perronScalarKernel_truncation_error_le
    (m : ℕ) (s : Finset ℕ) (σ H : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hH : 0 < H)
    (hkpos : ∀ k ∈ s, 0 < k) :
    (∑ k ∈ s, ArithmeticFunction.vonMangoldt k *
      ‖(((((m : ℝ) + 1 / 2) / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (((m : ℝ) + 1 / 2) / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel ((m : ℝ) + 1 / 2) k σ t‖) ≤
      3456 * ((m : ℝ) + 1 / 2) * Real.log ((m : ℝ) + 2) ^ 2 / H +
        216 * ((m : ℝ) + 1 / 2) ^ σ / (H * (σ - 1) ^ 2) := by
  classical
  let x : ℝ := (m : ℝ) + 1 / 2
  let p : ℕ → Prop := fun k => x / 2 ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * x
  let sMid := s.filter p
  let sFar := s.filter fun k => ¬ p k
  have hMidSubset : sMid ⊆ range (2 * (m + 1)) := by
    intro k hk
    have hhi : (k : ℝ) ≤ 2 * ((m : ℝ) + 1 / 2) :=
      (mem_filter.mp hk).2.2
    have hlt : (k : ℝ) < ((2 * (m + 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact mem_range.mpr (by exact_mod_cast hlt)
  have hMidPos : ∀ k ∈ sMid, 0 < k := fun k hk =>
    hkpos k (mem_filter.mp hk).1
  have hMidLo : ∀ k ∈ sMid, ((m : ℝ) + 1 / 2) / 2 ≤ (k : ℝ) :=
    fun k hk => (mem_filter.mp hk).2.1
  have hMid := sum_middle_perronScalarKernel_truncation_error_le
    m sMid σ H (by linarith) hσ₂ hH hMidSubset hMidPos hMidLo
  have hFarPos : ∀ k ∈ sFar, 0 < k := fun k hk =>
    hkpos k (mem_filter.mp hk).1
  have hFar : ∀ k ∈ sFar, (k : ℝ) ≤ x / 2 ∨ 2 * x ≤ (k : ℝ) := by
    intro k hk
    have hp : ¬ p k := (mem_filter.mp hk).2
    by_cases hlo : x / 2 ≤ (k : ℝ)
    · right
      have hhi : ¬ (k : ℝ) ≤ 2 * x := fun h => hp ⟨hlo, h⟩
      exact (lt_of_not_ge hhi).le
    · exact Or.inl (lt_of_not_ge hlo).le
  have hFarBound := sum_far_perronScalarKernel_truncation_error_le
    x σ H sFar (by dsimp [x]; positivity) hσ hσ₂ hH hFarPos hFar
  have hsplit := sum_filter_add_sum_filter_not s p (fun k =>
    ArithmeticFunction.vonMangoldt k *
      ‖(((x / (k : ℝ)) ^ σ : ℝ) : ℂ) *
          perronPhaseContourLimit σ (Real.log (x / (k : ℝ))) -
        ∫ t in -H..H, perronScalarKernel x k σ t‖)
  simpa only [sMid, sFar, x, hsplit] using add_le_add hMid hFarBound

end SystolicGrowth.CookMagyarCircle

#print axioms SystolicGrowth.CookMagyarCircle.perronLogRatio_far_ge_half
#print axioms SystolicGrowth.CookMagyarCircle.perron_rpow_one_add_inv_log_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_far_perronScalarKernel_truncation_error_le
#print axioms SystolicGrowth.CookMagyarCircle.sum_perronScalarKernel_truncation_error_le
