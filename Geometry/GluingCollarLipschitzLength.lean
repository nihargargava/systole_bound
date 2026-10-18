module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarModelUpperBounds
public import Geometry.GluingCollarWarpRegularity
public import Geometry.GluingCollarFrozenSpeed
public import Geometry.LipschitzCoordinateCalculus
public import Geometry.GluingCollarCurveIntegrability

@[expose] public section

/-!
# Weighted length control for Lipschitz collar-coordinate curves

Finite affine replacements and the actual native triangle inequality compare
the C¹ path-infimum distance with weighted lengths of Lipschitz coordinate
curves. Coordinates and derivatives use the ordinary complex norm; native
distance statements explicitly select the constructed collar metric.
-/

open Set MeasureTheory
open scoped NNReal ENNReal

namespace SystolicGrowth

private theorem collar_lipschitz_radial_bound {K : ℝ≥0} {α : ℝ → ℂ}
    (hα : LipschitzOnWith K α (Icc 0 1)) {t : ℝ} (ht : t ∈ Icc 0 1) :
    |(α t).re| ≤ |(α 0).re| + K := by
  have hd := hα.dist_le_mul t ht 0 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  have hn : ‖α t - α 0‖ ≤ (K : ℝ) * t := by
    simpa only [Complex.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using hd
  have hreNorm : |(α t).re - (α 0).re| ≤ ‖α t - α 0‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (α t - α 0)
  have hre := hreNorm.trans hn
  have htK : (K : ℝ) * t ≤ K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg
  calc
    |(α t).re| = |((α t).re - (α 0).re) + (α 0).re| := by congr 1; ring
    _ ≤ |(α t).re - (α 0).re| + |(α 0).re| := abs_add_le _ _
    _ ≤ |(α 0).re| + K := by linarith

private theorem collar_lipschitz_warp_sub_le (r : ℝ) {K : ℝ≥0} {α : ℝ → ℂ}
    (hα : LipschitzOnWith K α (Icc 0 1)) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    |gluingCollarWarp r (α s).re - gluingCollarWarp r (α t).re| ≤
      (Real.cosh (|r| + (|(α 0).re| + K)) * K) * |s - t| := by
  let R : ℝ := |(α 0).re| + K
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) K.coe_nonneg
  have hrad : ∀ u ∈ Icc (0 : ℝ) 1, (α u).re ∈ Icc (-R) R :=
    fun u hu => abs_le.mp (collar_lipschitz_radial_bound hα hu)
  have hw := gluingCollarWarp_abs_sub_le r hR (hrad s hs) (hrad t ht)
  have hn : ‖α s - α t‖ ≤ (K : ℝ) * |s - t| := by
    simpa only [Complex.dist_eq, Real.dist_eq] using hα.dist_le_mul s hs t ht
  have hreNorm : |(α s).re - (α t).re| ≤ ‖α s - α t‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (α s - α t)
  have hre := hreNorm.trans hn
  calc
    _ ≤ Real.cosh (|r| + R) * ((K : ℝ) * |s - t|) :=
      hw.trans (mul_le_mul_of_nonneg_left hre (Real.cosh_pos _).le)
    _ = _ := by ring

private theorem collar_lipschitz_affine_warp_sub_le (r : ℝ) {K : ℝ≥0} {α : ℝ → ℂ}
    (hα : LipschitzOnWith K α (Icc 0 1)) {a b t : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    |gluingCollarWarp r (gluingCollarLinearSegment (α a) (α b) t).re -
        gluingCollarWarp r (α a).re| ≤
      (Real.cosh (|r| + (|(α 0).re| + K)) * K) * |b - a| := by
  let R : ℝ := |(α 0).re| + K
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) K.coe_nonneg
  have hstart := collar_lipschitz_radial_bound hα ha
  have hend := collar_lipschitz_radial_bound hα hb
  have hseg := gluingCollarLinearSegment_radial_bound (α a) (α b) hstart hend ht
  have hw := gluingCollarWarp_abs_sub_le r hR (abs_le.mp hseg) (abs_le.mp hstart)
  have hlin : (gluingCollarLinearSegment (α a) (α b) t).re - (α a).re =
      t * ((α b).re - (α a).re) := by
    simp only [gluingCollarLinearSegment, Complex.add_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hdiff : |(gluingCollarLinearSegment (α a) (α b) t).re - (α a).re| ≤
      (K : ℝ) * |b - a| := by
    have hn : ‖α b - α a‖ ≤ (K : ℝ) * |b - a| := by
      simpa only [Complex.dist_eq, Real.dist_eq] using hα.dist_le_mul b hb a ha
    have hreNorm : |(α b).re - (α a).re| ≤ ‖α b - α a‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (α b - α a)
    have hre := hreNorm.trans hn
    rw [hlin, abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans hre
  calc
    _ ≤ Real.cosh (|r| + R) * ((K : ℝ) * |b - a|) :=
      hw.trans (mul_le_mul_of_nonneg_left hdiff (Real.cosh_pos _).le)
    _ = _ := by ring

private theorem collar_lipschitz_cell_dist_le {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0} {α : ℝ → ℂ} (hα : LipschitzOnWith K α (Icc 0 1))
    {a b : ℝ} (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hab : a ≤ b) :
    @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α a) (α b) ≤
      (∫ t in a..b, Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t))) +
        2 * (Real.cosh (|r| + (|(α 0).re| + K)) * K) * (b - a) *
          (∫ t in a..b, |(deriv α t).im|) := by
  let H : ℝ := Real.cosh (|r| + (|(α 0).re| + K)) * K
  let η : ℝ := H * (b - a)
  have hH : 0 ≤ H := mul_nonneg (Real.cosh_pos _).le K.coe_nonneg
  have hη : 0 ≤ η := mul_nonneg hH (sub_nonneg.mpr hab)
  have hcell : Icc a b ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc ha.1 hb.2
  have hαcell := hα.mono hcell
  have hwarp (t : ℝ) (ht : t ∈ Icc 0 1) :
      |gluingCollarWarp r (gluingCollarLinearSegment (α a) (α b) t).re -
        gluingCollarWarp r (α a).re| ≤ η := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using
      collar_lipschitz_affine_warp_sub_le r hα ha hb ht
  have hd := gluingCollarModelMetric_dist_le_frozen hr hη (α a) (α b) hwarp
  let L : ℂ →L[ℝ] ℂ := gluingCollarFrozenVelocity r (α a)
  have hderiv := lipschitzCoordinate_intervalIntegrable_deriv hab hαcell
  have hFTC := lipschitzCoordinate_integral_deriv_eq_sub hab hαcell
  have hmap : IntervalIntegrable (fun t => L (deriv α t)) volume a b :=
    ⟨L.integrable_comp hderiv.1, L.integrable_comp hderiv.2⟩
  have hfrozen : IntervalIntegrable (fun t => ‖L (deriv α t)‖) volume a b :=
    ⟨hmap.1.norm, hmap.2.norm⟩
  have hspeed := gluingCollarCurve_speed_intervalIntegrable hr hab hαcell
  have hang := gluingCollarCurve_abs_im_deriv_intervalIntegrable hab hαcell
  have herr : IntervalIntegrable (fun t => η * |(deriv α t).im|) volume a b :=
    ⟨hang.1.const_mul η, hang.2.const_mul η⟩
  have hfrozen_le : (∫ t in a..b, ‖L (deriv α t)‖) ≤
      (∫ t in a..b, Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t))) + η * (∫ t in a..b, |(deriv α t).im|) := by
    have h := intervalIntegral.integral_mono_on hab hfrozen (hspeed.add herr)
      (fun t ht => ?_)
    · rw [intervalIntegral.integral_add hspeed herr, intervalIntegral.integral_const_mul] at h
      exact h
    · have htime : |a - t| ≤ b - a := by
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.1)]
        linarith [ht.2]
      have hw : |gluingCollarWarp r (α a).re - gluingCollarWarp r (α t).re| ≤ η :=
        (collar_lipschitz_warp_sub_le r hα ha (hcell ht)).trans
          (mul_le_mul_of_nonneg_left htime hH)
      have hs := gluingCollarModel_speed_sub_le r (α a) (α t) (deriv α t)
      have hp := mul_le_mul_of_nonneg_right hw (abs_nonneg (deriv α t).im)
      change ‖gluingCollarFrozenVelocity r (α a) (deriv α t)‖ ≤ _
      rw [gluingCollarFrozenVelocity_norm]
      linarith [le_abs_self (Real.sqrt (gluingComplexCollarTangentForm r
        (α a) (deriv α t) (deriv α t)) -
          Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t)))]
  calc
    _ ≤ ‖L (α b - α a)‖ + η * |(α b).im - (α a).im| := by
      simpa only [L, gluingCollarFrozenVelocity_norm] using hd
    _ = ‖∫ t in a..b, L (deriv α t)‖ + η * |(α b).im - (α a).im| := by
      rw [L.intervalIntegral_comp_comm hderiv, hFTC]
    _ ≤ (∫ t in a..b, ‖L (deriv α t)‖) + η * (∫ t in a..b, |(deriv α t).im|) :=
      add_le_add (intervalIntegral.norm_integral_le_integral_norm hab)
        (mul_le_mul_of_nonneg_left
          (lipschitzCoordinate_im_sub_le_integral_abs_deriv hab hαcell) hη)
    _ ≤ (∫ t in a..b, Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t))) +
          2 * H * (b - a) * (∫ t in a..b, |(deriv α t).im|) := by
      dsimp [η] at hfrozen_le ⊢
      linarith

/-- The actual native collar distance is at most the weighted length of
every ordinary-coordinate Lipschitz curve. Affine replacements are used
only cellwise; no differentiability of the curve at the endpoints or
smoothness of a concatenated polygonal path is assumed. -/
theorem gluingCollarModelMetric_dist_le_lipschitz_length {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0} {α : ℝ → ℂ} (hα : LipschitzOnWith K α (Icc 0 1)) :
    @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α 0) (α 1) ≤
      ∫ t in (0 : ℝ)..1, Real.sqrt (gluingComplexCollarTangentForm r
        (α t) (deriv α t) (deriv α t)) := by
  let S : ℝ → ℝ := fun t => Real.sqrt (gluingComplexCollarTangentForm r
    (α t) (deriv α t) (deriv α t))
  let A : ℝ → ℝ := fun t => |(deriv α t).im|
  let H : ℝ := Real.cosh (|r| + (|(α 0).re| + K)) * K
  have hS : IntervalIntegrable S volume 0 1 :=
    gluingCollarCurve_speed_intervalIntegrable hr zero_le_one hα
  have hA : IntervalIntegrable A volume 0 1 :=
    gluingCollarCurve_abs_im_deriv_intervalIntegrable zero_le_one hα
  have hmesh (n : ℕ) (hn : 0 < n) :
      @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α 0) (α 1) ≤
        (∫ t in (0 : ℝ)..1, S t) + (2 * H / n) * (∫ t in (0 : ℝ)..1, A t) := by
    let u : ℕ → ℝ := fun i => (i : ℝ) / n
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hu0 : u 0 = 0 := by simp [u]
    have hun : u n = 1 := by simp [u, hn0]
    have hule {i j : ℕ} (hij : i ≤ j) : u i ≤ u j := by
      apply div_le_div_of_nonneg_right _ hnR.le
      exact_mod_cast hij
    have humem {i : ℕ} (hi : i ≤ n) : u i ∈ Icc (0 : ℝ) 1 := by
      constructor
      · simpa [hu0] using hule (Nat.zero_le i)
      · simpa [hun] using hule hi
    have husub {i : ℕ} (hi : i < n) : uIcc (u i) (u (i + 1)) ⊆ uIcc (0 : ℝ) 1 := by
      rw [uIcc_of_le (hule (Nat.le_succ i)), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (humem hi.le).1 (humem (Nat.succ_le_of_lt hi)).2
    have hstep (i : ℕ) : u (i + 1) - u i = 1 / (n : ℝ) := by
      dsimp [u]
      push_cast
      ring
    have hcell (i : ℕ) (hi : i < n) :
        @dist ℂ (gluingCollarModelMetricSpace hr).toDist (α (u i)) (α (u (i + 1))) ≤
          (∫ t in u i..u (i + 1), S t) +
            (2 * H / n) * (∫ t in u i..u (i + 1), A t) := by
      have hd := collar_lipschitz_cell_dist_le hr hα (humem hi.le)
        (humem (Nat.succ_le_of_lt hi)) (hule (Nat.le_succ i))
      rw [hstep] at hd
      convert hd using 1
      dsimp [S, A, H]
      ring
    have hs := intervalIntegral.sum_integral_adjacent_intervals (a := u)
      (fun i hi => hS.mono_set (husub hi))
    have ha := intervalIntegral.sum_integral_adjacent_intervals (a := u)
      (fun i hi => hA.mono_set (husub hi))
    rw [hu0, hun] at hs ha
    have hd := @dist_le_range_sum_of_dist_le ℂ
      (gluingCollarModelMetricSpace hr).toPseudoMetricSpace (fun i => α (u i)) n
      (fun i => (∫ t in u i..u (i + 1), S t) +
        (2 * H / n) * (∫ t in u i..u (i + 1), A t)) (fun {i} hi => hcell i hi)
    rw [hu0, hun, Finset.sum_add_distrib, ← Finset.mul_sum, hs, ha] at hd
    exact hd
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hnBig⟩ := exists_nat_gt (max 0 (2 * H * (∫ t in (0 : ℝ)..1, A t) / ε))
  have hnR : (0 : ℝ) < n := (le_max_left _ _).trans_lt hnBig
  have hn : 0 < n := by exact_mod_cast hnR
  have hprod : 2 * H * (∫ t in (0 : ℝ)..1, A t) < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hnBig)
  have hsmall : (2 * H / n) * (∫ t in (0 : ℝ)..1, A t) < ε := by
    rw [show (2 * H / n) * (∫ t in (0 : ℝ)..1, A t) =
      (2 * H * (∫ t in (0 : ℝ)..1, A t)) / n by ring]
    apply (div_lt_iff₀ hnR).mpr
    nlinarith
  exact (hmesh n hn).trans (add_le_add (le_refl _) hsmall.le)

/-- Extended-distance version of the genuine Lipschitz length bound,
using the same closed-interval weighted integral as the admissible infimum. -/
theorem gluingCollarModelEDist_le_lipschitz_warp_length {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0} {α : ℝ → ℂ} (hα : LipschitzOnWith K α (Icc 0 1)) :
    gluingCollarModelEDist hr (α 0) (α 1) ≤
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  have hspeed := gluingCollarCurve_speed_intervalIntegrable hr zero_le_one hα
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hspeed
  have heq : ENNReal.ofReal (∫ t in (0 : ℝ)..1,
      Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) =
      ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg _))
  calc
    _ = ENNReal.ofReal (@dist ℂ (gluingCollarModelMetricSpace hr).toDist (α 0) (α 1)) :=
      @edist_dist ℂ (gluingCollarModelMetricSpace hr).toPseudoMetricSpace (α 0) (α 1)
    _ ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..1,
        Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) :=
      ENNReal.ofReal_le_ofReal (gluingCollarModelMetric_dist_le_lipschitz_length hr hα)
    _ = _ := heq

#print axioms gluingCollarModelMetric_dist_le_lipschitz_length
#print axioms gluingCollarModelEDist_le_lipschitz_warp_length

end SystolicGrowth
