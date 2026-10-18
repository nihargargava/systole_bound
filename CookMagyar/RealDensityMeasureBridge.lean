module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.RealDensityConvolution
public import Mathlib.Probability.Independence.CharacteristicFunction

@[expose] public section

/-!
# The cube-pushforward model for the real cubic law

This module identifies the convolution measures used by the Fourier argument
with the pushforward of unit-cube volume under the sum of cubes, then proves
that the explicit convolution and geometric fiber densities agree pointwise.
It proves continuity of that convolution density on the normalized target
window and closes real Fourier inversion at the Cook--Magyar arities.
-/

open MeasureTheory Filter Set ProbabilityTheory
open Topology
open scoped BigOperators ENNReal FourierTransform

namespace SystolicGrowth
namespace CookMagyarReal

noncomputable section

/-- The law of one cubed unit-interval variable, written directly as a
pushforward measure. -/
def cubicUnitIntervalImageMeasure : Measure ℝ :=
  Measure.map (fun x : ℝ ↦ x ^ 3) (volume.restrict (Set.Icc 0 1))

theorem charFun_cubicUnitIntervalImageMeasure_two_pi_mul (tau : ℝ) :
    charFun cubicUnitIntervalImageMeasure (2 * Real.pi * tau) =
      oneDimensionalCubicIntegral tau := by
  unfold cubicUnitIntervalImageMeasure
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  unfold oneDimensionalCubicIntegral realAddChar
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  push_cast
  ring

/-- The explicit one-dimensional density measure is exactly the cube-map
pushforward of unit-interval volume. -/
theorem unitCubicMeasure_eq_cubicUnitIntervalImageMeasure :
    unitCubicMeasure = cubicUnitIntervalImageMeasure := by
  let : IsFiniteMeasure cubicUnitIntervalImageMeasure := by
    unfold cubicUnitIntervalImageMeasure
    infer_instance
  apply Measure.ext_of_charFun
  funext t
  let tau : ℝ := t / (2 * Real.pi)
  have hscale : 2 * Real.pi * tau = t := by
    dsimp [tau]
    field_simp [Real.pi_ne_zero]
  calc
    charFun unitCubicMeasure t = charFun unitCubicMeasure (2 * Real.pi * tau) := by
      rw [hscale]
    _ = oneDimensionalCubicIntegral tau :=
      charFun_unitCubicMeasure_two_pi_mul tau
    _ = charFun cubicUnitIntervalImageMeasure (2 * Real.pi * tau) :=
      (charFun_cubicUnitIntervalImageMeasure_two_pi_mul tau).symm
    _ = charFun cubicUnitIntervalImageMeasure t := by
      rw [hscale]

theorem unitCubicMeasure_isProbabilityMeasure :
    IsProbabilityMeasure unitCubicMeasure := by
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [unitCubicMeasure_eq_cubicUnitIntervalImageMeasure]
  unfold cubicUnitIntervalImageMeasure
  exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance

/-- Finite-dimensional cube volume is the product of the one-dimensional
unit-interval measures. -/
theorem unitCubeVolume_eq_pi (n : ℕ) :
    volume.restrict (Set.Icc (0 : Fin n → ℝ) 1) =
      Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [volume_pi, ← Set.pi_univ_Icc, Measure.restrict_pi_pi]
  simp

/-- The pushforward of unit-cube volume by the diagonal sum of cubes. -/
def cubicCubeSumMeasure (n : ℕ) : Measure ℝ :=
  Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 3)
    (volume.restrict (Set.Icc (0 : Fin n → ℝ) 1))

theorem cubicCoordinateMap_pi_eq_unitPi (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))).map
      (fun x i ↦ x i ^ 3) =
      Measure.pi (fun _ : Fin n ↦ unitCubicMeasure) := by
  change Measure.map (fun x i ↦ (fun y : ℝ ↦ y ^ 3) (x i))
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))) = _
  rw [Measure.pi_map_pi (μ := fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1))
    (f := fun _ (x : ℝ) ↦ x ^ 3) (fun _ ↦ (by fun_prop))]
  have hcoord :
      (fun _ : Fin n ↦ Measure.map (fun x : ℝ ↦ x ^ 3)
        (volume.restrict (Set.Icc (0 : ℝ) 1))) =
        (fun _ : Fin n ↦ unitCubicMeasure) := by
    funext i
    exact unitCubicMeasure_eq_cubicUnitIntervalImageMeasure.symm
  rw [hcoord]

/-- The iterated convolution law is the pushforward of the product law of
the one-dimensional cubic variables under their sum. -/
theorem cubicSumMeasure_eq_sum_unitPi (n : ℕ) :
    cubicSumMeasure n =
      ((Measure.pi (fun _ : Fin n ↦ unitCubicMeasure)).map (fun x ↦ ∑ i, x i)) := by
  let : IsProbabilityMeasure unitCubicMeasure := unitCubicMeasure_isProbabilityMeasure
  let : ∀ i : Fin n, IsProbabilityMeasure unitCubicMeasure := fun _ ↦
    unitCubicMeasure_isProbabilityMeasure
  apply Measure.ext_of_charFun
  funext t
  let tau : ℝ := t / (2 * Real.pi)
  have hscale : 2 * Real.pi * tau = t := by
    dsimp [tau]
    field_simp [Real.pi_ne_zero]
  calc
    charFun (cubicSumMeasure n) t =
        charFun (cubicSumMeasure n) (2 * Real.pi * tau) := by rw [hscale]
    _ = oneDimensionalCubicIntegral tau ^ n :=
      charFun_cubicSumMeasure_two_pi_mul n tau
    _ = ∏ _ : Fin n, oneDimensionalCubicIntegral tau := by simp
    _ = ∏ i : Fin n, charFun unitCubicMeasure (2 * Real.pi * tau) := by
      simp_rw [charFun_unitCubicMeasure_two_pi_mul]
    _ = charFun ((Measure.pi (fun _ : Fin n ↦ unitCubicMeasure)).map
        (fun x ↦ ∑ i, x i)) (2 * Real.pi * tau) := by
      rw [ProbabilityTheory.charFun_map_sum_pi_eq_prod, Finset.prod_apply]
    _ = charFun ((Measure.pi (fun _ : Fin n ↦ unitCubicMeasure)).map
        (fun x ↦ ∑ i, x i)) t := by rw [hscale]

/-- The convolution measure for `n` cubes agrees exactly with the direct
unit-cube pushforward under `x ↦ ∑ i, x i³`. -/
theorem cubicCubeSumMeasure_eq_cubicSumMeasure (n : ℕ) :
    cubicCubeSumMeasure n = cubicSumMeasure n := by
  calc
    cubicCubeSumMeasure n =
        Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i)
          (Measure.map (fun x i ↦ x i ^ 3)
            (Measure.pi (fun _ : Fin n ↦ volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
      unfold cubicCubeSumMeasure
      rw [unitCubeVolume_eq_pi, Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
    _ = Measure.map (fun x : Fin n → ℝ ↦ ∑ i, x i)
          (Measure.pi (fun _ : Fin n ↦ unitCubicMeasure)) := by
      rw [cubicCoordinateMap_pi_eq_unitPi]
    _ = cubicSumMeasure n := (cubicSumMeasure_eq_sum_unitPi n).symm

/-- A convenient orientation of the cube-pushforward description. -/
theorem cubicSumMeasure_eq_cubicCubeSumMeasure (n : ℕ) :
    cubicSumMeasure n = cubicCubeSumMeasure n :=
  (cubicCubeSumMeasure_eq_cubicSumMeasure n).symm

/-- The cube-pushforward model is supported in the interval `[0,n]`.
This is the compact support input needed to localize the singular kernel in
`cubicSumDensity` near targets close to the top endpoint. -/
theorem cubicSumMeasure_ae_mem_Icc (n : ℕ) :
    ∀ᵐ y ∂cubicSumMeasure n, y ∈ Set.Icc (0 : ℝ) n := by
  rw [cubicSumMeasure_eq_cubicCubeSumMeasure]
  unfold cubicCubeSumMeasure
  have hf : Measurable (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 3) := by fun_prop
  apply (ae_map_iff (f := fun x : Fin n → ℝ ↦ ∑ i, x i ^ 3)
    (μ := volume.restrict (Set.Icc (0 : Fin n → ℝ) 1))
    hf.aemeasurable (by measurability)).2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hx' : x ∈ Set.Icc (0 : Fin n → ℝ) 1 := hx
  have hx' := Set.mem_Icc.mp hx'
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (hx'.1 i) 3
  · calc
      (∑ i, x i ^ 3) ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (pow_le_one₀ (hx'.1 i) (hx'.2 i))
      _ = (n : ℝ) := by simp

/-- Positive-arity cubic sum laws have no atoms. In particular, the moving
endpoint where the one-variable density jumps contributes on a null set. -/
theorem cubicSumMeasure_singleton_eq_zero (n : ℕ) (hn : 0 < n) (a : ℝ) :
    cubicSumMeasure n {a} = 0 := by
  have hindex : n = (n - 1) + 1 := by omega
  rw [hindex, cubicSumMeasure_succ_eq_withDensity,
    withDensity_apply _ (measurableSet_singleton a)]
  exact setLIntegral_measure_zero _ _ (measure_singleton a)

/-- The one-variable density is continuous at every positive point except
its jump at the right endpoint of its support. -/
theorem unitCubicDensityReal_continuousAt {y : ℝ} (hy : 0 < y) (hyone : y ≠ 1) :
    ContinuousAt unitCubicDensityReal y := by
  by_cases hylt : y < 1
  · have hmem : ∀ᶠ z in 𝓝 y, z ∈ Set.Ioc (0 : ℝ) 1 := by
      filter_upwards [Ioo_mem_nhds hy hylt] with z hz
      exact ⟨hz.1, hz.2.le⟩
    have hbase : ContinuousAt cubicPushforwardDensity y := by
      unfold cubicPushforwardDensity
      exact continuousAt_const.mul
        (Real.continuousAt_rpow_const y (-(2 : ℝ) / 3) (Or.inl hy.ne'))
    apply hbase.congr_of_eventuallyEq
    filter_upwards [hmem] with z hz
    simp [unitCubicDensityReal, Set.indicator_of_mem hz]
  · have hygt : 1 < y := lt_of_le_of_ne (le_of_not_gt hylt) hyone.symm
    have hmem : ∀ᶠ z in 𝓝 y, z ∉ Set.Ioc (0 : ℝ) 1 := by
      filter_upwards [Ioi_mem_nhds hygt] with z hz
      simp only [Set.mem_Ioc, not_and_or, not_le]
      exact Or.inr hz
    have hEq : unitCubicDensityReal =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [hmem] with z hz
      simp [unitCubicDensityReal, hz]
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) y)
      |>.congr_of_eventuallyEq hEq

/-- Above one half, the cubic kernel is bounded by two. This coarse bound is
uniform in the target and is enough for the local dominated-convergence
argument. -/
theorem unitCubicDensityReal_le_two_of_half_le {y : ℝ} (hy : 1 / 2 ≤ y) :
    unitCubicDensityReal y ≤ 2 := by
  by_cases hmem : y ∈ Set.Ioc (0 : ℝ) 1
  · rw [unitCubicDensityReal, Set.indicator_of_mem hmem]
    unfold cubicPushforwardDensity
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy
    have hpow : y ^ (-(2 : ℝ) / 3) ≤ y ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hypos hmem.2 (by norm_num)
    have hinv : y ^ (-1 : ℝ) ≤ 2 := by
      rw [Real.rpow_neg_one]
      rw [← one_div]
      apply (div_le_iff₀ hypos).2
      nlinarith [hmem.1, hy]
    nlinarith
  · simp [unitCubicDensityReal, hmem]

/-- When the residual variable stays above one half almost everywhere, the
ENNReal convolution density is the real integral of the bounded kernel. -/
theorem cubicSumDensity_toReal_eq_integral_of_residual_half
    (k : ℕ) (z : ℝ)
    (hhalf : ∀ᵐ x ∂cubicSumMeasure k, 1 / 2 ≤ z - x) :
    (cubicSumDensity k z).toReal =
      ∫ x, unitCubicDensityReal (z - x) ∂cubicSumMeasure k := by
  let F : ℝ → ℝ := fun x ↦ unitCubicDensityReal (z - x)
  have hmeas : Measurable F := by
    dsimp [F]
    exact unitCubicDensityReal_measurable.comp (measurable_const.sub measurable_id)
  have hnonneg : 0 ≤ᵐ[cubicSumMeasure k] F := by
    filter_upwards [] with x
    exact unitCubicDensityReal_nonneg _
  have hnorm : ∀ᵐ x ∂cubicSumMeasure k, ‖F x‖ ≤ (2 : ℝ) := by
    filter_upwards [hhalf] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (unitCubicDensityReal_nonneg _)]
    exact unitCubicDensityReal_le_two_of_half_le hx
  have hInt : Integrable F (cubicSumMeasure k) :=
    (integrable_const (2 : ℝ)).mono' hmeas.aestronglyMeasurable hnorm
  have hrepr : cubicSumDensity k z = ENNReal.ofReal (∫ x, F x ∂cubicSumMeasure k) := by
    change (∫⁻ x, ENNReal.ofReal (F x) ∂cubicSumMeasure k) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hInt hnonneg]
  rw [hrepr, ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]

/-- The explicit convolution density is continuous at every target in the
normalized window for arity at least four. The preceding sum is supported
below `n - 1`, so nearby residuals stay away from the singularity at zero;
the only discontinuity at residual one occurs on a null singleton. -/
theorem cubicSumDensity_continuousAt_of_normalizedTargetWindow
    (n : ℕ) (hn : 4 ≤ n) {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    ContinuousAt (fun z : ℝ ↦ ((cubicSumDensity (n - 1) z).toReal : ℂ)) mu := by
  let k := n - 1
  let F : ℝ → ℝ → ℝ := fun z x ↦ unitCubicDensityReal (z - x)
  have hk : (k : ℝ) = (n : ℝ) - 1 := by
    dsimp [k]
    norm_num [Nat.cast_sub (by omega : 1 ≤ n)]
  have hwindow : Set.Ioo (mu - 1 / 12) (mu + 1 / 12) ∈ 𝓝 mu :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hlower : (n : ℝ) - 1 / 3 ≤ mu := hmu.1
  have hsupport := cubicSumMeasure_ae_mem_Icc k
  have hcontInt : ContinuousAt (fun z : ℝ ↦ ∫ x, F z x ∂cubicSumMeasure k) mu := by
    change Tendsto (fun z : ℝ ↦ ∫ x, F z x ∂cubicSumMeasure k)
      (𝓝 mu) (𝓝 (∫ x, F mu x ∂cubicSumMeasure k))
    refine tendsto_integral_filter_of_dominated_convergence
      (F := F) (f := F mu) (bound := fun _ ↦ (2 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [] with z
      have hm : Measurable (F z) := by
        dsimp [F]
        exact unitCubicDensityReal_measurable.comp (measurable_const.sub measurable_id)
      exact hm.aestronglyMeasurable
    · filter_upwards [hwindow] with z hz
      filter_upwards [hsupport] with x hx
      have hres : 1 / 2 ≤ z - x := by
        have hxupper : x ≤ (n : ℝ) - 1 := by rw [← hk]; exact hx.2
        have hzlower := hz.1
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (unitCubicDensityReal_nonneg _)]
      exact unitCubicDensityReal_le_two_of_half_le hres
    · exact integrable_const (2 : ℝ)
    · have hnoatom : cubicSumMeasure k {mu - 1} = 0 := by
        apply cubicSumMeasure_singleton_eq_zero
        dsimp [k]
        omega
      have hnot : ∀ᵐ x ∂cubicSumMeasure k, x ≠ mu - 1 := by
        exact compl_mem_ae_iff.mpr hnoatom
      filter_upwards [hsupport, hnot] with x hx hxneq
      have hxpos : 0 < mu - x := by
        have hxupper : x ≤ (n : ℝ) - 1 := by rw [← hk]; exact hx.2
        linarith
      have hxne : mu - x ≠ 1 := by
        intro heq
        apply hxneq
        linarith
      have hsub : ContinuousAt (fun z : ℝ ↦ z - x) mu :=
        continuousAt_id.sub (continuousAt_const : ContinuousAt (fun _ : ℝ ↦ x) mu)
      simpa [F] using
        (ContinuousAt.comp' (x := mu)
          (unitCubicDensityReal_continuousAt hxpos hxne) hsub).tendsto
  have heq : ∀ᶠ z in 𝓝 mu,
      ((cubicSumDensity k z).toReal : ℂ) =
        ((∫ x, F z x ∂cubicSumMeasure k : ℝ) : ℂ) := by
    filter_upwards [hwindow] with z hz
    have hhalf : ∀ᵐ x ∂cubicSumMeasure k, 1 / 2 ≤ z - x := by
      filter_upwards [hsupport] with x hx
      have hxupper : x ≤ (n : ℝ) - 1 := by rw [← hk]; exact hx.2
      have hzlower := hz.1
      linarith
    have hrepr := cubicSumDensity_toReal_eq_integral_of_residual_half k z hhalf
    exact congrArg (fun y : ℝ ↦ (y : ℂ)) hrepr
  have hcast : ContinuousAt (fun z : ℝ ↦ ((∫ x, F z x ∂cubicSumMeasure k : ℝ) : ℂ)) mu :=
    Complex.continuous_ofReal.continuousAt.comp hcontInt
  exact hcast.congr_of_eventuallyEq heq

/-- Away from the endpoint `1`, the one-dimensional convolution density is
exactly the fiber Jacobian density used by `geometricCubicDensity`. -/
theorem unitCubicDensityENNReal_eq_cubicFiberDensityIntegrand_of_ne_one
    {m : ℕ} (mu : ℝ) (x : Fin m → ℝ)
    (hneq : cubicFiberResidual mu x ≠ 1) :
    unitCubicDensityENNReal (cubicFiberResidual mu x) =
      cubicFiberDensityIntegrand mu x := by
  let r := cubicFiberResidual mu x
  by_cases hr0 : 0 < r
  · by_cases hr1 : r < 1
    · have hrmem : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨hr0, hr1.le⟩
      change ENNReal.ofReal (Set.indicator (Set.Ioc (0 : ℝ) 1)
        cubicPushforwardDensity r) = _
      rw [Set.indicator_of_mem hrmem]
      unfold cubicFiberDensityIntegrand
      dsimp
      rw [ite_eq_left ⟨hr0, hr1⟩]
      change ENNReal.ofReal (cubicPushforwardDensity r) =
        ENNReal.ofReal r ^ (-(2 : ℝ) / 3) / 3
      unfold cubicPushforwardDensity
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 3 : ℝ)),
        ENNReal.ofReal_rpow_of_pos hr0]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      simp [div_eq_mul_inv, mul_comm]
    · have hrgt : 1 < r := lt_of_le_of_ne (le_of_not_gt hr1) hneq.symm
      have hrnotmem : r ∉ Set.Ioc (0 : ℝ) 1 := by
        simp only [Set.mem_Ioc, not_and_or, not_le]
        exact Or.inr hrgt
      change ENNReal.ofReal (Set.indicator (Set.Ioc (0 : ℝ) 1)
        cubicPushforwardDensity r) = _
      rw [Set.indicator_of_notMem hrnotmem]
      unfold cubicFiberDensityIntegrand
      dsimp
      rw [ite_eq_right (by
        intro h
        exact hr1 (by simpa [r] using h.2))]
      simp
  · have hrnotmem : r ∉ Set.Ioc (0 : ℝ) 1 := by
      simp only [Set.mem_Ioc, not_and_or]
      exact Or.inl hr0
    change ENNReal.ofReal (Set.indicator (Set.Ioc (0 : ℝ) 1)
      cubicPushforwardDensity r) = _
    rw [Set.indicator_of_notMem hrnotmem]
    unfold cubicFiberDensityIntegrand
    dsimp
    rw [ite_eq_right (by
      intro h
      exact hr0 (by simpa [r] using h.1))]
    simp

/-- For at least two variables, the potential endpoint discrepancy in the
fiber density lies on a null level set of the preceding cube sum. -/
theorem cubicFiberResidual_eq_one_measure_zero (n : ℕ) (hn : 2 ≤ n) (mu : ℝ) :
    (volume.restrict (Set.Icc (0 : Fin (n - 1) → ℝ) 1))
      {x | cubicFiberResidual mu x = 1} = 0 := by
  have hnoatom : cubicSumMeasure (n - 1) {mu - 1} = 0 :=
    cubicSumMeasure_singleton_eq_zero (n - 1) (by omega) (mu - 1)
  have hmap : cubicCubeSumMeasure (n - 1) {mu - 1} = 0 := by
    rw [cubicCubeSumMeasure_eq_cubicSumMeasure]
    exact hnoatom
  unfold cubicCubeSumMeasure at hmap
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (mu - 1))] at hmap
  have hsets :
      {x : Fin (n - 1) → ℝ | cubicFiberResidual mu x = 1} =
        (fun x : Fin (n - 1) → ℝ ↦ ∑ i, x i ^ 3) ⁻¹' {mu - 1} := by
    ext x
    change cubicFiberResidual mu x = 1 ↔ ∑ i, x i ^ 3 = mu - 1
    unfold cubicFiberResidual
    constructor <;> intro h <;> linarith
  rw [hsets]
  exact hmap

/-- The explicit convolution density and the geometric fiber density agree
pointwise for every sum of at least two cubic unit-interval variables. -/
theorem cubicSumDensity_eq_geometricCubicDensity (n : ℕ) (hn : 2 ≤ n) (mu : ℝ) :
    cubicSumDensity (n - 1) mu = geometricCubicDensity n mu := by
  unfold cubicSumDensity
  rw [cubicSumMeasure_eq_cubicCubeSumMeasure]
  unfold cubicCubeSumMeasure
  have hf : Measurable (fun y : ℝ ↦ unitCubicDensityENNReal (mu - y)) :=
    unitCubicDensityENNReal_measurable.comp (measurable_const.sub measurable_id)
  rw [MeasureTheory.lintegral_map hf (by fun_prop)]
  unfold geometricCubicDensity
  apply lintegral_congr_ae
  filter_upwards [compl_mem_ae_iff.mpr
    (cubicFiberResidual_eq_one_measure_zero n hn mu)] with x hx
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx
  simpa only [cubicFiberResidual] using
    unitCubicDensityENNReal_eq_cubicFiberDensityIntegrand_of_ne_one mu x hx

/-- At the Cook--Magyar arities, continuity of the explicit convolution
density on the normalized target window is sufficient for the full
real Fourier-inversion statement.  The density identification itself is
unconditional by `cubicSumDensity_eq_geometricCubicDensity`. -/
theorem hasCubicRealFourierInversion_of_cubicSumDensity_continuousOn
    (n : ℕ) (hn : 4 ≤ n)
    (hcont : ∀ mu, NormalizedTargetWindow n mu →
      ContinuousAt (fun x : ℝ ↦ ((cubicSumDensity (n - 1) x).toReal : ℂ)) mu) :
    HasCubicRealFourierInversion n := by
  intro mu hmu
  refine ⟨singularIntegrand_integrable (by omega) mu, ?_⟩
  have hinv := cubicSumDensity_eq_singularIntegral_of_continuous (n - 1) mu
    (by omega) (hcont mu hmu)
  rw [cubicSumDensity_eq_geometricCubicDensity n (by omega) mu] at hinv
  have hindex : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [geometricCubicDensityReal, hindex] using hinv.symm

/-- The normalized-target continuity argument closes the real-place
Fourier-inversion gate for every Cook--Magyar arity `n ≥ 4`. -/
theorem hasCubicRealFourierInversion_of_normalizedTargetWindow
    (n : ℕ) (hn : 4 ≤ n) : HasCubicRealFourierInversion n := by
  apply hasCubicRealFourierInversion_of_cubicSumDensity_continuousOn n hn
  intro mu hmu
  exact cubicSumDensity_continuousAt_of_normalizedTargetWindow n hn hmu

/-- The positive geometric box estimate is now an unconditional uniform
lower bound for the real singular integral on the normalized target window. -/
theorem singularIntegral_re_uniform_lower_bound_of_normalizedTargetWindow
    {n : ℕ} (hn : 4 ≤ n) {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    (geometricDensityLowerBound n).toReal ≤ (singularIntegral n mu).re :=
  singularIntegral_re_uniform_lower_bound_of_fourierInversion
    (by omega) (hasCubicRealFourierInversion_of_normalizedTargetWindow n hn) hmu

/-- In particular the real singular integral has positive real part at every
admissible normalized target. -/
theorem singularIntegral_re_pos_of_normalizedTargetWindow
    {n : ℕ} (hn : 4 ≤ n) {mu : ℝ} (hmu : NormalizedTargetWindow n mu) :
    0 < (singularIntegral n mu).re :=
  singularIntegral_re_pos_of_fourierInversion
    (by omega) (hasCubicRealFourierInversion_of_normalizedTargetWindow n hn) hmu

end

end CookMagyarReal
end SystolicGrowth
