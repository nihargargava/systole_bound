module

public import CookMagyar.RealFourier
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory Filter
open scoped Interval Topology

namespace SystolicGrowth.CookMagyarReal

noncomputable def linearPhaseCoefficient (tau : ℝ) : ℂ :=
  2 * Real.pi * Complex.I * (tau : ℂ)

noncomputable def linearPhasePrimitive (tau y : ℝ) : ℂ :=
  Complex.exp (linearPhaseCoefficient tau * (y : ℂ)) /
    linearPhaseCoefficient tau

theorem linearPhaseCoefficient_ne_zero {tau : ℝ} (htau : tau ≠ 0) :
    linearPhaseCoefficient tau ≠ 0 := by
  unfold linearPhaseCoefficient
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast htau)

theorem hasDerivAt_linearPhasePrimitive {tau : ℝ} (htau : tau ≠ 0)
    (y : ℝ) :
    HasDerivAt (linearPhasePrimitive tau) (realAddChar tau y) y := by
  let c := linearPhaseCoefficient tau
  have hc : c ≠ 0 := linearPhaseCoefficient_ne_zero htau
  have hd : HasDerivAt (fun t : ℝ ↦ Complex.exp (c * (t : ℂ)) / c)
      (Complex.exp (c * (y : ℂ))) y := by
    conv => congr
    rw [← mul_div_cancel_right₀ (Complex.exp (c * (y : ℂ))) hc]
    apply ((Complex.hasDerivAt_exp _).comp y _).div_const c
    simpa only [mul_one] using!
      ((hasDerivAt_id (y : ℂ)).const_mul c).comp_ofReal
  convert hd using 1
  · rfl
  · unfold realAddChar
    dsimp [c, linearPhaseCoefficient]

noncomputable def cubicPushforwardDensityDeriv (y : ℝ) : ℂ :=
  ((-(2 : ℝ) / 9) * y ^ (-(5 : ℝ) / 3) : ℝ)

theorem hasDerivAt_cubicPushforwardDensity_complex {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ ↦ (cubicPushforwardDensity t : ℂ))
      (cubicPushforwardDensityDeriv y) y := by
  have hr := (Real.hasDerivAt_rpow_const
    (x := y) (p := (-(2 : ℝ) / 3)) (Or.inl hy.ne')).const_mul (1 / 3 : ℝ)
  have hrreal : HasDerivAt cubicPushforwardDensity
      ((1 / 3 : ℝ) * ((-(2 : ℝ) / 3) *
        y ^ (-(2 : ℝ) / 3 - 1))) y := by
    change HasDerivAt (fun z : ℝ ↦ (1 / 3 : ℝ) * z ^ (-(2 : ℝ) / 3))
      ((1 / 3 : ℝ) * ((-(2 : ℝ) / 3) *
        y ^ (-(2 : ℝ) / 3 - 1))) y
    exact hr
  have hrc := hrreal.ofReal_comp
  have heq :
      ((((1 / 3 : ℝ) * ((-(2 : ℝ) / 3) *
        y ^ (-(2 : ℝ) / 3 - 1))) : ℝ) : ℂ) =
          cubicPushforwardDensityDeriv y := by
    unfold cubicPushforwardDensityDeriv
    have hexp : (-(2 : ℝ) / 3 - 1) = -(5 : ℝ) / 3 := by ring
    rw [hexp]
    push_cast
    ring
  rw [← heq]
  exact hrc

theorem cubicPushforwardDensityDeriv_intervalIntegrable
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable cubicPushforwardDensityDeriv volume a 1 := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  rw [Set.uIcc_of_le ha1] at hy
  have hy0 : y ≠ 0 := ne_of_gt (ha.trans_le hy.1)
  unfold cubicPushforwardDensityDeriv
  have hp : ContinuousAt (fun z : ℝ ↦ z ^ (-(5 : ℝ) / 3)) y :=
    Real.continuousAt_rpow_const y _ (Or.inl hy0)
  have hreal : ContinuousAt (fun z : ℝ ↦ (-(2 : ℝ) / 9) *
      z ^ (-(5 : ℝ) / 3)) y := continuousAt_const.mul hp
  exact (Complex.continuous_ofReal.continuousAt.comp hreal).continuousWithinAt

theorem linearPhasePrimitive_intervalIntegrable (tau a : ℝ) :
    IntervalIntegrable (linearPhasePrimitive tau) volume a 1 := by
  apply Continuous.intervalIntegrable
  unfold linearPhasePrimitive linearPhaseCoefficient
  fun_prop

theorem realAddChar_intervalIntegrable (tau a : ℝ) :
    IntervalIntegrable (realAddChar tau) volume a 1 := by
  apply Continuous.intervalIntegrable
  unfold realAddChar
  fun_prop

theorem cubicDensity_integrationByParts {tau a : ℝ} (htau : tau ≠ 0)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    (∫ y in a..1, cubicDensityFourierIntegrand tau y) =
      (cubicPushforwardDensity 1 : ℂ) * linearPhasePrimitive tau 1 -
        (cubicPushforwardDensity a : ℂ) * linearPhasePrimitive tau a -
          ∫ y in a..1,
            cubicPushforwardDensityDeriv y * linearPhasePrimitive tau y := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := 1)
    (u := fun y : ℝ ↦ (cubicPushforwardDensity y : ℂ))
    (u' := cubicPushforwardDensityDeriv)
    (v := linearPhasePrimitive tau)
    (v' := realAddChar tau)
    (fun y hy ↦ by
      rw [Set.uIcc_of_le ha1] at hy
      exact hasDerivAt_cubicPushforwardDensity_complex (ha.trans_le hy.1))
    (fun y _hy ↦ hasDerivAt_linearPhasePrimitive htau y)
    (cubicPushforwardDensityDeriv_intervalIntegrable ha ha1)
    (realAddChar_intervalIntegrable tau a)
  simpa only [cubicDensityFourierIntegrand, Complex.real_smul] using h

theorem norm_linearPhaseCoefficient (tau : ℝ) :
    ‖linearPhaseCoefficient tau‖ = 2 * Real.pi * |tau| := by
  simp [linearPhaseCoefficient, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]

theorem norm_linearPhasePrimitive {tau : ℝ} (_htau : tau ≠ 0) (y : ℝ) :
    ‖linearPhasePrimitive tau y‖ = (2 * Real.pi * |tau|)⁻¹ := by
  have hphase : Complex.exp (linearPhaseCoefficient tau * (y : ℂ)) =
      realAddChar tau y := by
    unfold linearPhaseCoefficient realAddChar
    congr 1
  unfold linearPhasePrimitive
  rw [norm_div, hphase, norm_realAddChar, norm_linearPhaseCoefficient,
    one_div]

theorem cubicPushforwardDensity_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ cubicPushforwardDensity y := by
  unfold cubicPushforwardDensity
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg hy _)

theorem norm_cubicPushforwardDensity_complex {y : ℝ} (hy : 0 ≤ y) :
    ‖(cubicPushforwardDensity y : ℂ)‖ = cubicPushforwardDensity y := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (cubicPushforwardDensity_nonneg hy)]

theorem norm_cubicPushforwardDensityDeriv {y : ℝ} (hy : 0 < y) :
    ‖cubicPushforwardDensityDeriv y‖ =
      (2 / 9 : ℝ) * y ^ (-(5 : ℝ) / 3) := by
  unfold cubicPushforwardDensityDeriv
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonpos (by norm_num : (-(2 : ℝ) / 9) ≤ 0)]
  norm_num
  exact Real.rpow_nonneg hy.le _

theorem norm_cubicDensityFourierIntegrand {tau y : ℝ} (hy : 0 ≤ y) :
    ‖cubicDensityFourierIntegrand tau y‖ = cubicPushforwardDensity y := by
  unfold cubicDensityFourierIntegrand
  rw [norm_smul, norm_realAddChar, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (cubicPushforwardDensity_nonneg hy)]

theorem norm_cubicDensityIntegral_zero_le {tau a : ℝ} (ha : 0 ≤ a) :
    ‖∫ y in (0 : ℝ)..a, cubicDensityFourierIntegrand tau y‖ ≤
      a ^ ((3 : ℝ)⁻¹) := by
  calc
    ‖∫ y in (0 : ℝ)..a, cubicDensityFourierIntegrand tau y‖ ≤
        ∫ y in (0 : ℝ)..a, ‖cubicDensityFourierIntegrand tau y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ha
    _ = ∫ y in (0 : ℝ)..a, cubicPushforwardDensity y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le ha] at hy
      exact norm_cubicDensityFourierIntegrand hy.1
    _ = a ^ ((3 : ℝ)⁻¹) := by
      unfold cubicPushforwardDensity
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num))]
      rw [Real.zero_rpow (by norm_num : (-(2 : ℝ) / 3 + 1) ≠ 0)]
      norm_num
      ring

theorem norm_densityDeriv_mul_primitive_integral_le
    {tau a : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖∫ y in a..1,
        cubicPushforwardDensityDeriv y * linearPhasePrimitive tau y‖ ≤
      (2 * Real.pi * |tau|)⁻¹ / 3 *
        (a ^ (-(2 : ℝ) / 3) - 1) := by
  let K : ℝ := (2 * Real.pi * |tau|)⁻¹
  have hzero : (0 : ℝ) ∉ Set.uIcc a 1 := by
    rw [Set.uIcc_of_le ha1]
    exact fun h ↦ (not_le_of_gt ha) h.1
  calc
    ‖∫ y in a..1,
        cubicPushforwardDensityDeriv y * linearPhasePrimitive tau y‖ ≤
        ∫ y in a..1,
          ‖cubicPushforwardDensityDeriv y * linearPhasePrimitive tau y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ha1
    _ = ∫ y in a..1,
        ((2 / 9 : ℝ) * K) * y ^ (-(5 : ℝ) / 3) := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le ha1] at hy
      have hy0 : 0 < y := ha.trans_le hy.1
      change ‖cubicPushforwardDensityDeriv y * linearPhasePrimitive tau y‖ =
        ((2 / 9 : ℝ) * K) * y ^ (-(5 : ℝ) / 3)
      rw [norm_mul, norm_cubicPushforwardDensityDeriv hy0,
        norm_linearPhasePrimitive htau]
      dsimp only [K]
      ring
    _ = ((2 / 9 : ℝ) * K) *
        ∫ y in a..1, y ^ (-(5 : ℝ) / 3) := by
      rw [intervalIntegral.integral_const_mul]
    _ = K / 3 * (a ^ (-(2 : ℝ) / 3) - 1) := by
      rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩), Real.one_rpow]
      norm_num
      ring

theorem norm_cubicDensityIntegral_tail_le
    {tau a : ℝ} (htau : tau ≠ 0) (ha : 0 < a) (ha1 : a ≤ 1) :
    ‖∫ y in a..1, cubicDensityFourierIntegrand tau y‖ ≤
      (2 / 3 : ℝ) * (2 * Real.pi * |tau|)⁻¹ *
        a ^ (-(2 : ℝ) / 3) := by
  let K : ℝ := (2 * Real.pi * |tau|)⁻¹
  let A : ℂ := (cubicPushforwardDensity 1 : ℂ) *
    linearPhasePrimitive tau 1
  let B : ℂ := (cubicPushforwardDensity a : ℂ) *
    linearPhasePrimitive tau a
  let J : ℂ := ∫ y in a..1,
    cubicPushforwardDensityDeriv y * linearPhasePrimitive tau y
  rw [cubicDensity_integrationByParts htau ha ha1]
  change ‖A - B - J‖ ≤ _
  have hA : ‖A‖ = (1 / 3 : ℝ) * K := by
    dsimp only [A]
    rw [norm_mul, norm_cubicPushforwardDensity_complex (by norm_num),
      norm_linearPhasePrimitive htau]
    unfold cubicPushforwardDensity
    rw [Real.one_rpow]
    dsimp only [K]
    ring
  have hB : ‖B‖ = (1 / 3 : ℝ) * a ^ (-(2 : ℝ) / 3) * K := by
    dsimp only [B]
    rw [norm_mul, norm_cubicPushforwardDensity_complex ha.le,
      norm_linearPhasePrimitive htau]
    unfold cubicPushforwardDensity
    dsimp only [K]
  have hJ : ‖J‖ ≤ K / 3 * (a ^ (-(2 : ℝ) / 3) - 1) := by
    dsimp only [J, K]
    exact norm_densityDeriv_mul_primitive_integral_le htau ha ha1
  calc
    ‖A - B - J‖ ≤ ‖A - B‖ + ‖J‖ := norm_sub_le _ _
    _ ≤ (‖A‖ + ‖B‖) + ‖J‖ :=
      add_le_add_left (norm_sub_le A B) _
    _ = ((1 / 3 : ℝ) * K +
        (1 / 3 : ℝ) * a ^ (-(2 : ℝ) / 3) * K) + ‖J‖ := by
      rw [hA, hB]
    _ ≤ ((1 / 3 : ℝ) * K +
        (1 / 3 : ℝ) * a ^ (-(2 : ℝ) / 3) * K) +
          K / 3 * (a ^ (-(2 : ℝ) / 3) - 1) :=
      add_le_add_right hJ _
    _ = (2 / 3 : ℝ) * K * a ^ (-(2 : ℝ) / 3) := by ring

theorem cubicDensityFourierIntegrand_intervalIntegrable (tau : ℝ) :
    IntervalIntegrable (cubicDensityFourierIntegrand tau) volume 0 1 := by
  have hchar : Continuous (realAddChar tau) := by
    unfold realAddChar
    fun_prop
  change IntervalIntegrable
    (fun x ↦ cubicPushforwardDensity x • realAddChar tau x) volume 0 1
  exact
    cubicPushforwardDensity_intervalIntegrable.smul_continuousOn
      hchar.continuousOn

theorem norm_oneDimensionalCubicIntegral_le_split
    {tau : ℝ} (htau : 1 ≤ |tau|) :
    ‖oneDimensionalCubicIntegral tau‖ ≤
      (|tau|⁻¹) ^ ((3 : ℝ)⁻¹) +
        (2 / 3 : ℝ) * (2 * Real.pi * |tau|)⁻¹ *
          (|tau|⁻¹) ^ (-(2 : ℝ) / 3) := by
  have htau0 : tau ≠ 0 := by
    intro h
    simp only [h, abs_zero] at htau
    norm_num at htau
  have habs : 0 < |tau| := abs_pos.mpr htau0
  let a : ℝ := |tau|⁻¹
  have ha : 0 < a := inv_pos.mpr habs
  have ha1 : a ≤ 1 := (inv_le_one₀ habs).mpr htau
  have hwhole := cubicDensityFourierIntegrand_intervalIntegrable tau
  have hsmall : IntervalIntegrable (cubicDensityFourierIntegrand tau)
      volume 0 a := hwhole.mono_set (by
    rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc_right ha1)
  have htail : IntervalIntegrable (cubicDensityFourierIntegrand tau)
      volume a 1 := hwhole.mono_set (by
    rw [Set.uIcc_of_le ha1, Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc_left ha.le)
  have hsplit :
      (∫ y in (0 : ℝ)..1, cubicDensityFourierIntegrand tau y) =
        (∫ y in (0 : ℝ)..a, cubicDensityFourierIntegrand tau y) +
          ∫ y in a..1, cubicDensityFourierIntegrand tau y :=
    (intervalIntegral.integral_add_adjacent_intervals hsmall htail).symm
  rw [oneDimensionalCubicIntegral_eq_densityIntegral,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1), hsplit]
  calc
    ‖(∫ y in (0 : ℝ)..a, cubicDensityFourierIntegrand tau y) +
        ∫ y in a..1, cubicDensityFourierIntegrand tau y‖ ≤
        ‖∫ y in (0 : ℝ)..a, cubicDensityFourierIntegrand tau y‖ +
          ‖∫ y in a..1, cubicDensityFourierIntegrand tau y‖ := norm_add_le _ _
    _ ≤ a ^ ((3 : ℝ)⁻¹) +
        (2 / 3 : ℝ) * (2 * Real.pi * |tau|)⁻¹ *
          a ^ (-(2 : ℝ) / 3) := add_le_add
      (norm_cubicDensityIntegral_zero_le ha.le)
      (norm_cubicDensityIntegral_tail_le htau0 ha ha1)
    _ = (|tau|⁻¹) ^ ((3 : ℝ)⁻¹) +
        (2 / 3 : ℝ) * (2 * Real.pi * |tau|)⁻¹ *
          (|tau|⁻¹) ^ (-(2 : ℝ) / 3) := by rfl

theorem cubicDecay_tail_identity {t : ℝ} (ht : 0 < t) :
    (2 / 3 : ℝ) * (2 * Real.pi * t)⁻¹ *
        (t⁻¹) ^ (-(2 : ℝ) / 3) =
      (1 / (3 * Real.pi)) * t ^ (-(1 : ℝ) / 3) := by
  have hneg_two : (-(2 : ℝ) / 3) = -((2 : ℝ) / 3) := by ring
  rw [hneg_two, Real.inv_rpow ht.le, Real.rpow_neg ht.le,
    inv_inv]
  have hmul : t ^ (-1 : ℝ) * t ^ ((2 : ℝ) / 3) =
      t ^ (-(1 : ℝ) / 3) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [show (2 * Real.pi * t)⁻¹ = (2 * Real.pi)⁻¹ * t⁻¹ by
    field_simp, ← Real.rpow_neg_one t]
  calc
    (2 / 3 : ℝ) * ((2 * Real.pi)⁻¹ * t ^ (-1 : ℝ)) *
        t ^ ((2 : ℝ) / 3) =
        (2 / 3 : ℝ) * (2 * Real.pi)⁻¹ *
          (t ^ (-1 : ℝ) * t ^ ((2 : ℝ) / 3)) := by ring
    _ = (2 / 3 : ℝ) * (2 * Real.pi)⁻¹ *
          t ^ (-(1 : ℝ) / 3) := by rw [hmul]
    _ = (1 / (3 * Real.pi)) * t ^ (-(1 : ℝ) / 3) := by
      field_simp

theorem inv_rpow_one_third {t : ℝ} :
    (t⁻¹) ^ ((3 : ℝ)⁻¹) = t ^ (-(1 : ℝ) / 3) := by
  have hexp : -(1 : ℝ) / 3 = -((3 : ℝ)⁻¹) := by norm_num
  rw [hexp, Real.rpow_neg_eq_inv_rpow]

/-- The elementary van der Corput bound obtained by splitting the pushed
forward density at `|tau|⁻¹` and integrating by parts once. -/
theorem norm_oneDimensionalCubicIntegral_le_two_mul_rpow
    {tau : ℝ} (htau : 1 ≤ |tau|) :
    ‖oneDimensionalCubicIntegral tau‖ ≤
      2 * |tau| ^ (-(1 : ℝ) / 3) := by
  have htau0 : tau ≠ 0 := by
    intro h
    simp only [h, abs_zero] at htau
    norm_num at htau
  have habs : 0 < |tau| := abs_pos.mpr htau0
  have hcoeff : (1 / (3 * Real.pi) : ℝ) ≤ 1 := by
    rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
    nlinarith [Real.pi_gt_three]
  have hrpow : 0 ≤ |tau| ^ (-(1 : ℝ) / 3) :=
    Real.rpow_nonneg habs.le _
  calc
    ‖oneDimensionalCubicIntegral tau‖ ≤
        (|tau|⁻¹) ^ ((3 : ℝ)⁻¹) +
          (2 / 3 : ℝ) * (2 * Real.pi * |tau|)⁻¹ *
            (|tau|⁻¹) ^ (-(2 : ℝ) / 3) :=
      norm_oneDimensionalCubicIntegral_le_split htau
    _ = |tau| ^ (-(1 : ℝ) / 3) +
        (1 / (3 * Real.pi)) * |tau| ^ (-(1 : ℝ) / 3) := by
      rw [inv_rpow_one_third, cubicDecay_tail_identity habs]
    _ ≤ |tau| ^ (-(1 : ℝ) / 3) +
        1 * |tau| ^ (-(1 : ℝ) / 3) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hrpow) _
    _ = 2 * |tau| ^ (-(1 : ℝ) / 3) := by ring

theorem norm_singularIntegrand_tail_bound {n : ℕ} (mu tau : ℝ)
    (htau : 1 ≤ |tau|) :
    ‖singularIntegrand n mu tau‖ ≤
      (2 : ℝ) ^ n * |tau| ^ (-((n : ℝ)) / 3) := by
  have hone := norm_oneDimensionalCubicIntegral_le_two_mul_rpow htau
  unfold singularIntegrand
  rw [norm_mul, norm_realAddChar, mul_one, norm_pow]
  calc
    ‖oneDimensionalCubicIntegral tau‖ ^ n ≤
        (2 * |tau| ^ (-(1 : ℝ) / 3)) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hone n
    _ = (2 : ℝ) ^ n *
        (|tau| ^ (-(1 : ℝ) / 3)) ^ n := by rw [mul_pow]
    _ = (2 : ℝ) ^ n * |tau| ^ (-((n : ℝ)) / 3) := by
      rw [← Real.rpow_mul_natCast (abs_nonneg tau)]
      congr 2
      ring

/-- Absolute convergence of the real singular integral.  Four variables
already suffice for convergence; Cook--Magyar uses far more. -/
theorem singularIntegrand_integrable {n : ℕ} (hn : 4 ≤ n) (mu : ℝ) :
    Integrable (singularIntegrand n mu) := by
  let r : ℝ := -((n : ℝ)) / 3
  let C : ℝ := (2 : ℝ) ^ n
  have hnR : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : r < -1 := by
    dsimp only [r]
    linarith
  have hdomIoi : IntegrableOn (fun x : ℝ ↦ C * x ^ r) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hr zero_lt_one).const_mul C
  have hdompos : IntegrableOn (fun x : ℝ ↦ C * x ^ r) (Set.Ici 1) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hdomIoi
  have hpos : IntegrableOn (singularIntegrand n mu) (Set.Ici 1) := by
    apply hdompos.mono'
    · exact (singularIntegrand_continuous n mu).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx1 : 1 ≤ x := Set.mem_Ici.mp hx
      have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx1)
      have hbound := norm_singularIntegrand_tail_bound (n := n) mu x
        (by simpa only [hxabs] using hx1)
      simpa only [C, r, hxabs] using hbound
  have hdomneg : IntegrableOn (fun x : ℝ ↦ C * (-x) ^ r) (Set.Iic (-1)) := by
    let f : ℝ → ℝ := fun x ↦ C * x ^ r
    have hf : IntegrableOn f (Set.Ici 1) := hdompos
    have hpre : IntegrableOn (f ∘ fun x : ℝ ↦ -x)
        ((fun x : ℝ ↦ -x) ⁻¹' Set.Ici 1) :=
      (Measure.measurePreserving_neg volume).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding |>.mpr hf
    have hset : (fun x : ℝ ↦ -x) ⁻¹' Set.Ici 1 = Set.Iic (-1) := by
      ext x
      constructor
      · intro hx
        change 1 ≤ -x at hx
        change x ≤ -1
        linarith
      · intro hx
        change x ≤ -1 at hx
        change 1 ≤ -x
        linarith
    rw [hset] at hpre
    change IntegrableOn (fun x : ℝ ↦ C * (-x) ^ r) (Set.Iic (-1)) at hpre
    exact hpre
  have hneg : IntegrableOn (singularIntegrand n mu) (Set.Iic (-1)) := by
    apply hdomneg.mono'
    · exact (singularIntegrand_continuous n mu).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      have hxle : x ≤ -1 := Set.mem_Iic.mp hx
      have hxneg : x ≤ 0 := hxle.trans (by norm_num)
      have hxabs : |x| = -x := abs_of_nonpos hxneg
      have hbound := norm_singularIntegrand_tail_bound (n := n) mu x
        (by rw [hxabs]; linarith)
      simpa only [C, r, hxabs] using hbound
  have hmid : IntegrableOn (singularIntegrand n mu) (Set.Icc (-1) 1) :=
    (singularIntegrand_continuous n mu).integrableOn_Icc
  have hall : IntegrableOn (singularIntegrand n mu)
      ((Set.Iic (-1) ∪ Set.Icc (-1) 1) ∪ Set.Ici 1) :=
    (hneg.union hmid).union hpos
  rw [← integrableOn_univ]
  convert hall using 1
  ext x
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ici,
    Set.mem_univ]
  constructor
  · intro _
    rcases le_total x (-1 : ℝ) with hleft | hright
    · exact Or.inl (Or.inl hleft)
    · rcases le_total x 1 with hmiddle | hright'
      · exact Or.inl (Or.inr ⟨hright, hmiddle⟩)
      · exact Or.inr hright'
  · intro _
    trivial

end SystolicGrowth.CookMagyarReal
