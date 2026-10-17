module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.MajorArcArithmetic
public import CookMagyar.ArcGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.Floor

@[expose] public section

namespace SystolicGrowth.CookMagyarArcs

open CookMagyarCircle

/-! # Periodic cubic phases on wrapped major arcs

The Fourier characters have period one. A point in a circle-metric major arc
may lie across an endpoint of `[0,1]`; subtracting the nearest integer gives
a genuinely small real displacement from its rational center.
-/

/-- The additive character is trivial at integer frequencies. -/
theorem addChar_int (z : ℤ) (k : ℕ) :
    addChar (z : ℝ) k = 1 := by
  unfold addChar
  have h : 2 * Real.pi * Complex.I * (k : ℂ) * ((z : ℝ) : ℂ) =
      (((z * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- Real-frequency characters are unchanged by an integer shift. -/
theorem addChar_add_int (alpha : ℝ) (z : ℤ) (k : ℕ) :
    addChar (alpha + z) k = addChar alpha k := by
  rw [CookMagyarMajorArc.addChar_add_real]
  simp [addChar_int]

/-- Negative characters are positive characters at the opposite frequency. -/
theorem negAddChar_eq_addChar_neg (alpha : ℝ) (k : ℕ) :
    negAddChar alpha k = addChar (-alpha) k := by
  unfold negAddChar addChar
  congr 1
  push_cast
  ring

/-- The target character has the same period one. -/
theorem negAddChar_add_int (alpha : ℝ) (z : ℤ) (k : ℕ) :
    negAddChar (alpha + z) k = negAddChar alpha k := by
  rw [negAddChar_eq_addChar_neg, negAddChar_eq_addChar_neg]
  have hneg : -(alpha + (z : ℝ)) = -alpha + ((-z : ℤ) : ℝ) := by push_cast; ring
  rw [hneg, addChar_add_int]

/-- The cubic von--Mangoldt sum is period one. -/
theorem cubicVonMangoldtExpSum_add_int (alpha : ℝ) (z : ℤ) (N : ℕ) :
    cubicVonMangoldtExpSum (alpha + z) N =
      cubicVonMangoldtExpSum alpha N := by
  unfold cubicVonMangoldtExpSum
  simp_rw [addChar_add_int]

/-- The powered target integrand is also period one. -/
theorem cubicIntegrand_add_int (alpha : ℝ) (z : ℤ) (n N T : ℕ) :
    cubicIntegrand n N T (alpha + z) = cubicIntegrand n N T alpha := by
  unfold cubicIntegrand
  rw [cubicVonMangoldtExpSum_add_int, negAddChar_add_int]

/-- Circle distance is the absolute displacement after nearest-integer reduction. -/
theorem periodicDistance_eq_abs_sub_round (alpha beta : ℝ) :
    periodicDistance alpha beta =
      |alpha - beta - (round (alpha - beta) : ℤ)| := by
  unfold periodicDistance
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact UnitAddCircle.norm_eq

/-- The canonical nearest-integer displacement from a fixed center is
measurable, including across the wrap point of the unit circle. -/
theorem measurable_wrappedDisplacement (center : ℝ) :
    Measurable (fun alpha : ℝ =>
      alpha - center - (round (alpha - center) : ℝ)) := by
  have hshift : Measurable (fun alpha : ℝ => alpha - center + (1 / 2 : ℝ)) :=
    measurable_id.sub_const center |>.add_const _
  have hfloor : Measurable (fun alpha : ℝ =>
      (⌊alpha - center + (1 / 2 : ℝ)⌋ : ℤ)) :=
    Int.measurable_floor.comp hshift
  have hcast : Measurable (fun alpha : ℝ =>
      (⌊alpha - center + (1 / 2 : ℝ)⌋ : ℝ)) :=
    Int.cast_continuous.measurable.comp hfloor
  have hround : (fun alpha : ℝ => (round (alpha - center) : ℝ)) =
      (fun alpha : ℝ =>
        (⌊alpha - center + (1 / 2 : ℝ)⌋ : ℝ)) := by
    funext alpha
    rw [round_eq]
  convert (measurable_id.sub_const center).sub hcast using 1
  funext alpha
  rw [round_eq]
  rfl

/-- A point on a possibly wrapped arc has a small real displacement after
an integer shift. -/
theorem exists_small_displacement_of_mem_majorArcAt
    {N Q a q : ℕ} {alpha : ℝ}
    (halpha : alpha ∈ majorArcAt N Q a q) :
    ∃ z : ℤ, ∃ beta : ℝ,
      |beta| < cubicArcRadius N Q ∧
      alpha = rationalCenter a q + beta + z := by
  let z : ℤ := round (alpha - rationalCenter a q)
  let beta : ℝ := alpha - rationalCenter a q - z
  refine ⟨z, beta, ?_, ?_⟩
  · simpa [z, beta, periodicDistance_eq_abs_sub_round] using halpha.2
  · dsimp [beta]
    ring

/-- Evaluate the cubic integrand at a small displacement from the center,
even when the original arc wraps across an endpoint. -/
theorem cubicIntegrand_eq_center_add_small_displacement
    {N Q a q : ℕ} {alpha : ℝ} (n T : ℕ)
    (halpha : alpha ∈ majorArcAt N Q a q) :
    ∃ beta : ℝ, |beta| < cubicArcRadius N Q ∧
      cubicIntegrand n N T alpha =
        cubicIntegrand n N T (rationalCenter a q + beta) := by
  obtain ⟨z, beta, hbeta, halpha'⟩ :=
    exists_small_displacement_of_mem_majorArcAt halpha
  refine ⟨beta, hbeta, ?_⟩
  rw [halpha', cubicIntegrand_add_int]

/-- The same small-displacement reduction for the underlying prime sum. -/
theorem cubicVonMangoldtExpSum_eq_center_add_small_displacement
    {N Q a q : ℕ} {alpha : ℝ}
    (halpha : alpha ∈ majorArcAt N Q a q) :
    ∃ beta : ℝ, |beta| < cubicArcRadius N Q ∧
      cubicVonMangoldtExpSum alpha N =
        cubicVonMangoldtExpSum (rationalCenter a q + beta) N := by
  obtain ⟨z, beta, hbeta, halpha'⟩ :=
    exists_small_displacement_of_mem_majorArcAt halpha
  refine ⟨beta, hbeta, ?_⟩
  rw [halpha', cubicVonMangoldtExpSum_add_int]

end SystolicGrowth.CookMagyarArcs
