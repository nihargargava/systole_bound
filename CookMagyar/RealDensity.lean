module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularIntegral
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace SystolicGrowth
namespace CookMagyarReal

/-! # A positive geometric density at the real place

The Fourier singular integral is expected to be the density of the sum of
independent cubes of unit-interval variables.  This file constructs that
geometric density directly by solving for the last coordinate.  More
importantly, it gives an explicit lower bound which is uniform over the whole
normalized Cook--Magyar target window.

The remaining analytic bridge is Fourier inversion: identifying
`singularIntegral` with the finite real value of `geometricCubicDensity`.
-/

/-- After the first `m` coordinates have been chosen, this is the cube of the
last coordinate required to represent `mu`. -/
def cubicFiberResidual {m : ℕ} (mu : ℝ) (x : Fin m → ℝ) : ℝ :=
  mu - ∑ i, x i ^ 3

theorem cubicFiberResidual_continuous {m : ℕ} (mu : ℝ) :
    Continuous (cubicFiberResidual (m := m) mu) := by
  unfold cubicFiberResidual
  fun_prop

/-- The Jacobian density obtained from the change of variables `y = x^3` in
the last coordinate.  It is supported exactly when the last coordinate lies
in the open unit interval. -/
noncomputable def cubicFiberDensityIntegrand {m : ℕ} (mu : ℝ)
    (x : Fin m → ℝ) : ℝ≥0∞ :=
  let r := cubicFiberResidual mu x
  if 0 < r ∧ r < 1 then
    (ENNReal.ofReal r) ^ (-(2 : ℝ) / 3) / 3
  else 0

theorem cubicFiberDensityIntegrand_measurable {m : ℕ} (mu : ℝ) :
    Measurable (cubicFiberDensityIntegrand (m := m) mu) := by
  let r : (Fin m → ℝ) → ℝ := cubicFiberResidual mu
  have hr : Measurable r := (cubicFiberResidual_continuous mu).measurable
  have hs : MeasurableSet {x | 0 < r x ∧ r x < 1} :=
    (measurableSet_lt measurable_const hr).inter
      (measurableSet_lt hr measurable_const)
  unfold cubicFiberDensityIntegrand
  change Measurable (fun x ↦ if 0 < r x ∧ r x < 1 then
    ENNReal.ofReal (r x) ^ (-(2 : ℝ) / 3) / 3 else 0)
  apply Measurable.ite hs
  · exact (ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp hr)).div_const 3
  · exact measurable_const

/-- The geometric density of a sum of `n` cubes, expressed by integrating
over the first `n - 1` unit-interval coordinates and solving for the last.
The value is extended-real so its definition does not presuppose the
integrability theorem needed by Fourier inversion. -/
noncomputable def geometricCubicDensity (n : ℕ) (mu : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Fin (n - 1) → ℝ in Set.Icc 0 1,
    cubicFiberDensityIntegrand mu x

/-- The lower endpoint of a small box adjacent to `(1, ..., 1)`. -/
noncomputable def realDensityBoxLower (n : ℕ) : ℝ :=
  1 - 1 / (30 * (n : ℝ))

/-- The explicit positive lower bound supplied by the box argument. -/
noncomputable def geometricDensityLowerBound (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (30 * (n : ℝ))) ^ (n - 1) / 3

theorem realDensityBoxLower_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ realDensityBoxLower n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold realDensityBoxLower
  have hden : 0 < 30 * (n : ℝ) := by positivity
  have hdiv : 1 / (30 * (n : ℝ)) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  linarith

theorem cube_deficit_nonneg_of_mem_realDensityBox {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hlower : realDensityBoxLower n ≤ x) (hupper : x ≤ 1) :
    0 ≤ 1 - x ^ 3 := by
  have hx0 : 0 ≤ x := (realDensityBoxLower_nonneg hn).trans hlower
  nlinarith [sq_nonneg x]

theorem cube_deficit_le_of_mem_realDensityBox {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hlower : realDensityBoxLower n ≤ x) (hupper : x ≤ 1) :
    1 - x ^ 3 ≤ 1 / (10 * (n : ℝ)) := by
  have hx0 : 0 ≤ x := (realDensityBoxLower_nonneg hn).trans hlower
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hfactor_nonneg : 0 ≤ 1 - x := sub_nonneg.mpr hupper
  have hfactor_le : 1 + x + x ^ 2 ≤ 3 := by linarith
  have hwidth : 1 - x ≤ 1 / (30 * (n : ℝ)) := by
    unfold realDensityBoxLower at hlower
    linarith
  calc
    1 - x ^ 3 = (1 - x) * (1 + x + x ^ 2) := by ring
    _ ≤ (1 - x) * 3 :=
      mul_le_mul_of_nonneg_left hfactor_le hfactor_nonneg
    _ ≤ (1 / (30 * (n : ℝ))) * 3 :=
      mul_le_mul_of_nonneg_right hwidth (by norm_num)
    _ = 1 / (10 * (n : ℝ)) := by ring

theorem sum_cube_deficit_le_of_mem_realDensityBox {n : ℕ} (hn : 0 < n)
    {x : Fin (n - 1) → ℝ}
    (hx : x ∈ Set.Icc (fun _ ↦ realDensityBoxLower n)
      (1 : Fin (n - 1) → ℝ)) :
    ∑ i, (1 - x i ^ 3) ≤ (1 : ℝ) / 10 := by
  calc
    ∑ i, (1 - x i ^ 3) ≤ ∑ _i : Fin (n - 1), 1 / (10 * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact cube_deficit_le_of_mem_realDensityBox hn (hx.1 i) (hx.2 i)
    _ = ((n - 1 : ℕ) : ℝ) * (1 / (10 * (n : ℝ))) := by simp
    _ ≤ (n : ℝ) * (1 / (10 * (n : ℝ))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.sub_le n 1
      · positivity
    _ = (1 : ℝ) / 10 := by
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp

theorem cubicFiberResidual_mem_uniform_interval {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu)
    {x : Fin (n - 1) → ℝ}
    (hx : x ∈ Set.Icc (fun _ ↦ realDensityBoxLower n)
      (1 : Fin (n - 1) → ℝ)) :
    (2 : ℝ) / 3 ≤ cubicFiberResidual mu x ∧
      cubicFiberResidual mu x ≤ (9 : ℝ) / 10 := by
  have hdeficit_nonneg : ∀ i, 0 ≤ 1 - x i ^ 3 := fun i ↦
    cube_deficit_nonneg_of_mem_realDensityBox hn (hx.1 i) (hx.2 i)
  have hdeficit_sum_nonneg : 0 ≤ ∑ i, (1 - x i ^ 3) :=
    Finset.sum_nonneg fun i _hi ↦ hdeficit_nonneg i
  have hdeficit_sum_le : ∑ i, (1 - x i ^ 3) ≤ (1 : ℝ) / 10 :=
    sum_cube_deficit_le_of_mem_realDensityBox hn hx
  have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
    norm_num
  have hsum_identity :
      ∑ i, x i ^ 3 = (n : ℝ) - 1 - ∑ i, (1 - x i ^ 3) := by
    rw [← hcard]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rcases hmu with ⟨hmu_lower, hmu_upper⟩
  unfold cubicFiberResidual
  rw [hsum_identity]
  constructor <;> norm_num at hmu_lower hmu_upper ⊢ <;> linarith

theorem cubicFiberDensityIntegrand_ge_one_third_on_box {n : ℕ}
    (hn : 0 < n) {mu : ℝ} (hmu : NormalizedTargetWindow n mu)
    {x : Fin (n - 1) → ℝ}
    (hx : x ∈ Set.Icc (fun _ ↦ realDensityBoxLower n)
      (1 : Fin (n - 1) → ℝ)) :
    (1 : ℝ≥0∞) / 3 ≤ cubicFiberDensityIntegrand mu x := by
  have hr := cubicFiberResidual_mem_uniform_interval hn hmu hx
  have hr0 : 0 < cubicFiberResidual mu x := by linarith [hr.1]
  have hr1 : cubicFiberResidual mu x < 1 := by linarith [hr.2]
  unfold cubicFiberDensityIntegrand
  rw [if_pos ⟨hr0, hr1⟩]
  apply ENNReal.div_le_div_right
  simpa only [ENNReal.one_rpow, ENNReal.rpow_zero] using
    (ENNReal.rpow_le_rpow_of_exponent_ge
      (ENNReal.ofReal_le_one.mpr hr1.le)
      (show (-(2 : ℝ) / 3) ≤ 0 by norm_num))

theorem realDensityBox_subset_unitCube {n : ℕ} (hn : 0 < n) :
    Set.Icc (fun _ : Fin (n - 1) ↦ realDensityBoxLower n)
      (1 : Fin (n - 1) → ℝ) ⊆
      Set.Icc (0 : Fin (n - 1) → ℝ) 1 := by
  intro x hx
  exact ⟨fun i ↦ (realDensityBoxLower_nonneg hn).trans (hx.1 i), hx.2⟩

/-- In the high target window, the last-coordinate residual is uniformly
separated from the singular value zero on the *entire* unit cube. -/
theorem cubicFiberResidual_ge_two_thirds_on_unitCube {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu)
    {x : Fin (n - 1) → ℝ}
    (hx : x ∈ Set.Icc (0 : Fin (n - 1) → ℝ) 1) :
    (2 : ℝ) / 3 ≤ cubicFiberResidual mu x := by
  have hcoord : ∀ i, x i ^ 3 ≤ 1 := by
    intro i
    have hx0 : 0 ≤ x i := by simpa using hx.1 i
    have hx1 : x i ≤ 1 := by simpa using hx.2 i
    exact pow_le_one₀ hx0 hx1
  have hsum : ∑ i, x i ^ 3 ≤ ((n - 1 : ℕ) : ℝ) := by
    calc
      ∑ i, x i ^ 3 ≤ ∑ _i : Fin (n - 1), (1 : ℝ) := by
        exact Finset.sum_le_sum fun i _hi ↦ hcoord i
      _ = ((n - 1 : ℕ) : ℝ) := by simp
  have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
    norm_num
  unfold cubicFiberResidual
  rw [hcard] at hsum
  norm_num at hmu ⊢
  linarith [hmu.1]

/-- On the relevant unit cube, the exact Jacobian density is bounded by one.
This elementary estimate is enough to show that the geometric density is a
finite extended-real number. -/
theorem cubicFiberDensityIntegrand_le_one_on_unitCube {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu)
    {x : Fin (n - 1) → ℝ}
    (hx : x ∈ Set.Icc (0 : Fin (n - 1) → ℝ) 1) :
    cubicFiberDensityIntegrand mu x ≤ 1 := by
  have hr_lower := cubicFiberResidual_ge_two_thirds_on_unitCube hn hmu hx
  dsimp only [cubicFiberDensityIntegrand]
  split_ifs with hr
  · let a : ℝ≥0∞ := ENNReal.ofReal (cubicFiberResidual mu x)
    have ha_le_one : a ≤ 1 := ENNReal.ofReal_le_one.mpr hr.2.le
    have hpow_le_inv : a ^ (-(2 : ℝ) / 3) ≤ a⁻¹ := by
      rw [← ENNReal.rpow_neg_one]
      exact ENNReal.rpow_le_rpow_of_exponent_ge ha_le_one (by norm_num)
    have ha_inv_le_three : a⁻¹ ≤ 3 := by
      rw [ENNReal.inv_le_iff_inv_le]
      calc
        (3 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 3) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]
          norm_num
        _ ≤ ENNReal.ofReal (cubicFiberResidual mu x) :=
          ENNReal.ofReal_le_ofReal (by linarith)
    calc
      a ^ (-(2 : ℝ) / 3) / 3 ≤ (3 : ℝ≥0∞) / 3 :=
        ENNReal.div_le_div_right (hpow_le_inv.trans ha_inv_le_three) 3
      _ ≤ 1 := ENNReal.div_self_le_one
  · exact bot_le

/-- The geometric density is finite throughout the normalized target
window. -/
theorem geometricCubicDensity_lt_top {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    geometricCubicDensity n mu < ∞ := by
  unfold geometricCubicDensity
  apply setLIntegral_lt_top_of_le_nnreal
  · exact measure_Icc_lt_top.ne
  · refine ⟨1, ?_⟩
    intro x hx
    simpa using cubicFiberDensityIntegrand_le_one_on_unitCube hn hmu hx

/-- The ordinary real value of the geometric density.  Its finiteness on the
target window is proved above rather than built into the definition. -/
noncomputable def geometricCubicDensityReal (n : ℕ) (mu : ℝ) : ℝ :=
  (geometricCubicDensity n mu).toReal

theorem volume_realDensityBox {n : ℕ} (_hn : 0 < n) :
    volume (Set.Icc (fun _ : Fin (n - 1) ↦ realDensityBoxLower n)
      (1 : Fin (n - 1) → ℝ)) =
      ENNReal.ofReal (1 / (30 * (n : ℝ))) ^ (n - 1) := by
  rw [Real.volume_Icc_pi]
  simp only [Pi.one_apply, realDensityBoxLower, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 2
  ring

/-- Uniform Archimedean positivity, proved directly from an explicit box near
`(1, ..., 1)`.  No Fourier inversion or oscillatory estimate is used. -/
theorem geometricCubicDensity_uniform_lower_bound {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    geometricDensityLowerBound n ≤ geometricCubicDensity n mu := by
  let box : Set (Fin (n - 1) → ℝ) :=
    Set.Icc (fun _ ↦ realDensityBoxLower n) 1
  let cube : Set (Fin (n - 1) → ℝ) := Set.Icc 0 1
  have hpoint : ∀ x ∈ box,
      (1 : ℝ≥0∞) / 3 ≤ cubicFiberDensityIntegrand mu x := by
    intro x hx
    exact cubicFiberDensityIntegrand_ge_one_third_on_box hn hmu hx
  have hfirst :
      ∫⁻ _x : Fin (n - 1) → ℝ in box, (1 : ℝ≥0∞) / 3 ≤
        ∫⁻ x : Fin (n - 1) → ℝ in box, cubicFiberDensityIntegrand mu x := by
    exact setLIntegral_mono (cubicFiberDensityIntegrand_measurable mu) hpoint
  have hsecond :
      ∫⁻ x : Fin (n - 1) → ℝ in box, cubicFiberDensityIntegrand mu x ≤
        ∫⁻ x : Fin (n - 1) → ℝ in cube, cubicFiberDensityIntegrand mu x := by
    apply lintegral_mono'
    · exact Measure.restrict_mono (realDensityBox_subset_unitCube hn) le_rfl
    · exact le_rfl
  unfold geometricDensityLowerBound geometricCubicDensity
  change ENNReal.ofReal (1 / (30 * (n : ℝ))) ^ (n - 1) / 3 ≤ _
  calc
    ENNReal.ofReal (1 / (30 * (n : ℝ))) ^ (n - 1) / 3 =
        (1 / 3 : ℝ≥0∞) * volume box := by
      rw [volume_realDensityBox hn]
      simp only [div_eq_mul_inv, one_mul]
      exact mul_comm _ _
    _ = ∫⁻ _x : Fin (n - 1) → ℝ in box, (1 : ℝ≥0∞) / 3 := by
      rw [setLIntegral_const]
    _ ≤ ∫⁻ x : Fin (n - 1) → ℝ in box,
        cubicFiberDensityIntegrand mu x := hfirst
    _ ≤ ∫⁻ x : Fin (n - 1) → ℝ in cube,
        cubicFiberDensityIntegrand mu x := hsecond

theorem geometricDensityLowerBound_pos {n : ℕ} (hn : 0 < n) :
    0 < geometricDensityLowerBound n := by
  unfold geometricDensityLowerBound
  have hbase : 0 < ENNReal.ofReal (1 / (30 * (n : ℝ))) := by
    rw [ENNReal.ofReal_pos]
    exact one_div_pos.mpr (mul_pos (by norm_num) (by exact_mod_cast hn))
  apply ENNReal.div_pos
  · exact pow_ne_zero _ hbase.ne'
  · norm_num

theorem geometricCubicDensity_pos {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    0 < geometricCubicDensity n mu :=
  (geometricDensityLowerBound_pos hn).trans_le
    (geometricCubicDensity_uniform_lower_bound hn hmu)

theorem geometricCubicDensityReal_pos {n : ℕ} (hn : 0 < n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    0 < geometricCubicDensityReal n mu := by
  unfold geometricCubicDensityReal
  exact ENNReal.toReal_pos
    (ne_of_gt (geometricCubicDensity_pos hn hmu))
    (geometricCubicDensity_lt_top hn hmu).ne

/-- The precise analytic statement still needed to identify the geometric
density with the oscillatory singular integral.  Keeping integrability in the
statement records both absolute convergence and Fourier inversion. -/
def HasCubicRealFourierInversion (n : ℕ) : Prop :=
  ∀ mu, NormalizedTargetWindow n mu →
    Integrable (singularIntegrand n mu) ∧
      singularIntegral n mu = (geometricCubicDensityReal n mu : ℂ)

theorem singularIntegral_integrable_of_fourierInversion {n : ℕ}
    (hfourier : HasCubicRealFourierInversion n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    Integrable (singularIntegrand n mu) :=
  (hfourier mu hmu).1

theorem singularIntegral_re_eq_geometricDensityReal_of_fourierInversion
    {n : ℕ} (hfourier : HasCubicRealFourierInversion n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    (singularIntegral n mu).re = geometricCubicDensityReal n mu := by
  rw [(hfourier mu hmu).2]
  exact Complex.ofReal_re _

/-- Once Fourier inversion is supplied, the explicit box estimate becomes a
uniform lower bound for the real part of the singular integral itself. -/
theorem singularIntegral_re_uniform_lower_bound_of_fourierInversion
    {n : ℕ} (hn : 0 < n) (hfourier : HasCubicRealFourierInversion n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    (geometricDensityLowerBound n).toReal ≤ (singularIntegral n mu).re := by
  rw [singularIntegral_re_eq_geometricDensityReal_of_fourierInversion
    hfourier hmu]
  unfold geometricCubicDensityReal
  exact ENNReal.toReal_mono (geometricCubicDensity_lt_top hn hmu).ne
    (geometricCubicDensity_uniform_lower_bound hn hmu)

theorem singularIntegral_re_pos_of_fourierInversion
    {n : ℕ} (hn : 0 < n) (hfourier : HasCubicRealFourierInversion n)
    {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    0 < (singularIntegral n mu).re := by
  rw [singularIntegral_re_eq_geometricDensityReal_of_fourierInversion
    hfourier hmu]
  exact geometricCubicDensityReal_pos hn hmu

end CookMagyarReal
end SystolicGrowth
