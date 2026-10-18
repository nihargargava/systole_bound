module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CubicPhaseScaling
public import CookMagyar.ArcPhasePeriodicity
public import CookMagyar.CubicMajorArcMeasurableModel
public import CookMagyar.MajorArcSumError
public import CookMagyar.SingularSeries

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SystolicGrowth.CookMagyarMajorArc

open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier CookMagyarReal

/-! # A wrapped homogeneous-cubic model

The continuous Abel model can be replaced by the homogeneous cubic singular
integral using the explicit phase-scaling estimate. The canonical displacement
keeps this replacement measurable across the circle seam.
-/

/-- Splitting the rational-center phase from the normalized target phase
after cubic rescaling. -/
theorem negAddChar_add_div_eq_mul_realAddChar
    (center tau D mu : ℝ) (T : ℕ)
    (hD : D ≠ 0) (hmu : mu = (T : ℝ) / D) :
    negAddChar (center + tau / D) T =
      negAddChar center T * realAddChar (-tau) mu := by
  unfold negAddChar realAddChar
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  rw [hmu]
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  field_simp [hDc]
  push_cast
  field_simp [hDc]
  ring_nf

/-- At the scaled displacement `tau/N³`, the homogeneous major-arc
integrand factors into its arithmetic coefficient and the truncated
Archimedean singular-integral integrand. -/
theorem homogeneousMajorArcLocalModel_eq_singularIntegrand_factor
    (q a N n T : ℕ) [NeZero q] (tau : ℝ) (hN : 0 < N) :
    ((unitCubicExponentialSum (a : ZMod q) *
        (Nat.totient q : ℂ)⁻¹) *
        ((N : ℝ) • oneDimensionalCubicIntegral tau)) ^ n *
        negAddChar (rationalCenter a q + tau / (N : ℝ) ^ 3) T =
      ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) *
        negAddChar (rationalCenter a q) T) *
        singularIntegrand n ((T : ℝ) / (N : ℝ) ^ 3) tau := by
  have hN3 : (N : ℝ) ^ 3 ≠ 0 := by positivity
  have hphase := negAddChar_add_div_eq_mul_realAddChar
    (rationalCenter a q) tau ((N : ℝ) ^ 3)
    ((T : ℝ) / (N : ℝ) ^ 3) T hN3 rfl
  unfold singularIntegrand
  rw [hphase]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The local homogeneous model written in the original displacement
coordinate rather than the rescaled variable. -/
noncomputable def homogeneousMajorArcLocalIntegrand
    (q a N n T : ℕ) [NeZero q] (beta : ℝ) : ℂ :=
  ((unitCubicExponentialSum (a : ZMod q) *
      (Nat.totient q : ℂ)⁻¹) *
      ((N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3))) ^ n *
    negAddChar (rationalCenter a q + beta) T

/-- In displacement coordinates the homogeneous local model is an explicit
arithmetic coefficient times the Archimedean Fourier integrand. -/
theorem homogeneousMajorArcLocalIntegrand_eq_factor_mul_singularIntegrand
    (q a N n T : ℕ) [NeZero q] (beta : ℝ) (hN : 0 < N) :
    homogeneousMajorArcLocalIntegrand q a N n T beta =
      ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) *
        negAddChar (rationalCenter a q) T) *
        singularIntegrand n ((T : ℝ) / (N : ℝ) ^ 3)
          (beta * (N : ℝ) ^ 3) := by
  have hN3 : (N : ℝ) ^ 3 ≠ 0 := by positivity
  have hscale : (beta * (N : ℝ) ^ 3) / (N : ℝ) ^ 3 = beta := by
    field_simp
  have h := homogeneousMajorArcLocalModel_eq_singularIntegrand_factor
    q a N n T (beta * (N : ℝ) ^ 3) hN
  rw [hscale] at h
  simpa [homogeneousMajorArcLocalIntegrand] using h

/-- Integrate the pointwise factorization over any measurable set. -/
theorem setIntegral_homogeneousMajorArcLocalIntegrand_eq_factor
    (q a N n T : ℕ) [NeZero q] (hN : 0 < N) (s : Set ℝ) :
    (∫ beta in s, homogeneousMajorArcLocalIntegrand q a N n T beta) =
      ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) *
        negAddChar (rationalCenter a q) T) *
        (∫ beta in s,
          singularIntegrand n ((T : ℝ) / (N : ℝ) ^ 3)
            (beta * (N : ℝ) ^ 3)) := by
  let C : ℂ :=
    (unitCubicExponentialSum (a : ZMod q) *
        (Nat.totient q : ℂ)⁻¹) ^ n *
      ((N : ℝ) ^ n : ℂ) * negAddChar (rationalCenter a q) T
  calc
    (∫ beta in s, homogeneousMajorArcLocalIntegrand q a N n T beta) =
        ∫ beta in s, C * singularIntegrand n ((T : ℝ) / (N : ℝ) ^ 3)
          (beta * (N : ℝ) ^ 3) := by
        apply integral_congr_ae
        filter_upwards with beta
        simpa [C] using
          homogeneousMajorArcLocalIntegrand_eq_factor_mul_singularIntegrand
            q a N n T beta hN
    _ = C * (∫ beta in s,
          singularIntegrand n ((T : ℝ) / (N : ℝ) ^ 3)
            (beta * (N : ℝ) ^ 3)) := by
        rw [integral_const_mul]

/-- Change variables from displacement `beta` to homogeneous frequency
`tau = beta*N³` on the symmetric major-arc window. -/
theorem integral_singularIntegrand_scaled_on_window
    (n N T Q : ℕ) (hN : 0 < N) :
    (∫ beta in Set.Icc
        (-((Q : ℝ) / (N : ℝ) ^ 3)) ((Q : ℝ) / (N : ℝ) ^ 3),
        singularIntegrand n ((T : ℝ) / (N : ℝ) ^ 3)
          (beta * (N : ℝ) ^ 3)) =
      ((N : ℝ) ^ 3)⁻¹ •
        truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q := by
  let c : ℝ := (N : ℝ) ^ 3
  let r : ℝ := (Q : ℝ) / c
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hcn : c ≠ 0 := ne_of_gt hcpos
  have hrpos : 0 ≤ r := by dsimp [r]; positivity
  have hlow : -r * c = -(Q : ℝ) := by
    dsimp [r]
    field_simp [hcn]
  have hupp : r * c = (Q : ℝ) := by
    dsimp [r]
    field_simp [hcn]
  let f : ℝ → ℂ := singularIntegrand n ((T : ℝ) / c)
  have hleft :
      (∫ beta in Set.Icc (-r) r, f (beta * c)) =
        ∫ beta in (-r)..r, f (beta * c) := by
    rw [intervalIntegral.integral_of_le (by linarith [hrpos]),
      ← integral_Icc_eq_integral_Ioc]
  have hright :
      (∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau) =
        ∫ tau in (-(Q : ℝ))..(Q : ℝ), f tau := by
    have hQr : (0 : ℝ) ≤ Q := by exact_mod_cast Nat.zero_le Q
    have hQ : (-(Q : ℝ)) ≤ (Q : ℝ) := by linarith
    rw [intervalIntegral.integral_of_le hQ,
      ← integral_Icc_eq_integral_Ioc]
  calc
    (∫ beta in Set.Icc (-r) r, f (beta * c)) =
        ∫ beta in (-r)..r, f (beta * c) := hleft
    _ = c⁻¹ • ∫ tau in (-(Q : ℝ))..(Q : ℝ), f tau := by
      rw [intervalIntegral.integral_comp_mul_right f hcn, hlow, hupp]
    _ = c⁻¹ • ∫ tau in Set.Icc (-(Q : ℝ)) (Q : ℝ), f tau := by
      rw [hright]
    _ = ((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q := by
      simp [f, c, truncatedSingularIntegral]

/-- Exact evaluation of the unwrapped homogeneous local model: its arc
integral is the arithmetic coefficient times a truncated Archimedean
singular integral, with the cubic Jacobian factor. -/
theorem integral_homogeneousMajorArcLocalIntegrand_window_eq_truncatedSingularIntegral
    (q a N n T Q : ℕ) [NeZero q] (hN : 0 < N) :
    (∫ beta in Set.Icc
        (-((Q : ℝ) / (N : ℝ) ^ 3)) ((Q : ℝ) / (N : ℝ) ^ 3),
        homogeneousMajorArcLocalIntegrand q a N n T beta) =
      ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) *
        negAddChar (rationalCenter a q) T) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q) := by
  rw [setIntegral_homogeneousMajorArcLocalIntegrand_eq_factor
    q a N n T hN]
  rw [integral_singularIntegrand_scaled_on_window n N T Q hN]

/-- Away from the seam of the unit-circle fundamental interval, a sufficiently
small circle displacement is the ordinary real displacement. -/
theorem wrappedMajorArcDisplacement_eq_sub_of_interior
    {alpha center radius : ℝ}
    (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hright : radius < center) (hleft : radius < 1 - center)
    (hdist : CookMagyarArcs.periodicDistance alpha center < radius) :
    alpha - center - (round (alpha - center) : ℤ) = alpha - center := by
  have hbeta : |alpha - center - (round (alpha - center) : ℤ)| < radius := by
    simpa [CookMagyarArcs.periodicDistance_eq_abs_sub_round] using hdist
  rcases abs_lt.mp hbeta with ⟨hbeta_lo, hbeta_hi⟩
  have hdecomp : alpha = center +
      (alpha - center - (round (alpha - center) : ℤ)) +
      (round (alpha - center) : ℤ) := by ring
  by_cases hz : round (alpha - center) = 0
  · simp [hz]
  · have hpos : 1 ≤ round (alpha - center) ∨
        (round (alpha - center) : ℤ) ≤ -1 := by omega
    rcases hpos with hpos | hneg
    · have hposR : (1 : ℝ) ≤ (round (alpha - center) : ℝ) := by
        exact_mod_cast hpos
      have : (1 : ℝ) < alpha := by linarith [hdecomp, hbeta_lo, hright]
      linarith [halpha.2]
    · have hnegR : (round (alpha - center) : ℝ) ≤ -1 := by
        exact_mod_cast hneg
      have : alpha < 0 := by linarith [hdecomp, hbeta_hi, hleft]
      linarith [halpha.1]

/-- If the circle ball around a center stays away from both endpoints, its
clipped preimage is precisely the corresponding open real interval. -/
theorem majorArcAt_eq_Ioo_of_interior_radius
    (N Q a q : ℕ)
    (hright : cubicArcRadius N Q < rationalCenter a q)
    (hleft : cubicArcRadius N Q < 1 - rationalCenter a q) :
    majorArcAt N Q a q =
      Set.Ioo (rationalCenter a q - cubicArcRadius N Q)
        (rationalCenter a q + cubicArcRadius N Q) := by
  ext alpha
  constructor
  · intro h
    have hbeta : |alpha - rationalCenter a q| < cubicArcRadius N Q := by
      have hdist := h.2
      have hdisp := wrappedMajorArcDisplacement_eq_sub_of_interior
        h.1 hright hleft hdist
      simpa [CookMagyarArcs.periodicDistance_eq_abs_sub_round, hdisp]
        using hdist
    rcases abs_lt.mp hbeta with ⟨hlo, hhi⟩
    constructor <;> linarith
  · intro h
    rcases h with ⟨hlo, hhi⟩
    have hrad : 0 ≤ cubicArcRadius N Q := by
      unfold cubicArcRadius
      positivity
    have hcpos : 0 < rationalCenter a q := lt_of_le_of_lt hrad hright
    have hcone : rationalCenter a q < 1 := by linarith [hrad, hleft]
    have halpha : alpha ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith
    have hbeta : |alpha - rationalCenter a q| < cubicArcRadius N Q := by
      apply abs_lt.mpr
      constructor <;> linarith
    have hhalf : cubicArcRadius N Q < (1 / 2 : ℝ) := by
      by_cases hc : rationalCenter a q ≤ 1 / 2
      · linarith [hright]
      · linarith [hleft]
    have hround : round (alpha - rationalCenter a q) = 0 := by
      apply (round_eq_zero_iff).2
      exact ⟨by have := (abs_lt.mp hbeta).1; linarith,
        by have := (abs_lt.mp hbeta).2; linarith⟩
    refine ⟨halpha, ?_⟩
    rw [CookMagyarArcs.periodicDistance_eq_abs_sub_round, hround]
    simpa [hround] using hbeta

/-- Under the standard major-arc scale separation, every non-endpoint
reduced center with denominator at least two has clearance exceeding the
arc radius on both sides. -/
theorem cubicArcRadius_lt_rationalCenter_and_one_sub
    {N Q a q : ℕ} (hq0 : q ≠ 0) (hqQ : q ≤ Q)
    (ha0 : 0 < a) (haq : a < q) (hq2 : 2 ≤ q)
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    cubicArcRadius N Q < rationalCenter a q ∧
      cubicArcRadius N Q < 1 - rationalCenter a q := by
  have hsep := two_cubicArcRadius_le_fraction_separation
    hq0 hq0 hqQ hqQ hscale
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hqgt1 : (1 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hq2)
  have hinv : 1 / ((q : ℝ) * q) < 1 / (q : ℝ) := by
    apply (div_lt_div_iff₀ (mul_pos hqpos hqpos) hqpos).2
    nlinarith
  have hrnonneg : 0 ≤ cubicArcRadius N Q := by
    unfold cubicArcRadius
    positivity
  have hrle : cubicArcRadius N Q ≤ 2 * cubicArcRadius N Q := by linarith
  have hsmall : cubicArcRadius N Q < 1 / (q : ℝ) :=
    lt_of_le_of_lt (hrle.trans hsep) hinv
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hleft : 1 / (q : ℝ) ≤ rationalCenter a q := by
    unfold rationalCenter
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha1) hqpos.le
  have hqa : 1 ≤ q - a := by omega
  have hratio : 1 / (q : ℝ) ≤ ((q - a : ℕ) : ℝ) / q :=
    div_le_div_of_nonneg_right (by exact_mod_cast hqa) hqpos.le
  have hratio_eq : ((q - a : ℕ) : ℝ) / q =
      1 - rationalCenter a q := by
    unfold rationalCenter
    rw [Nat.cast_sub (Nat.le_of_lt haq)]
    field_simp
  exact ⟨hsmall.trans_le hleft,
    hsmall.trans_le (hratio_eq ▸ hratio)⟩

/-- The denominator-one arc centered at zero splits into its two pieces at
the fundamental-interval seam. The midpoint is excluded at radius `1/2`
because the circle ball is open. -/
theorem majorArcAt_zero_one_eq_seam_intervals
    (N Q : ℕ) (hradius : cubicArcRadius N Q ≤ (1 / 2 : ℝ)) :
    majorArcAt N Q 0 1 =
      Set.Ico (0 : ℝ) (cubicArcRadius N Q) ∪
        Set.Ioc (1 - cubicArcRadius N Q) 1 := by
  let r : ℝ := cubicArcRadius N Q
  have hrnonneg : 0 ≤ r := by dsimp [r, cubicArcRadius]; positivity
  ext alpha
  constructor
  · intro h
    have hIcc : alpha ∈ Set.Icc (0 : ℝ) 1 := h.1
    have hdist := h.2
    by_cases hhalf : alpha < 1 / 2
    · have hround : round alpha = 0 := by
        apply round_eq_zero_iff.mpr
        constructor <;> linarith [hIcc.1, hhalf]
      have hrad : |alpha| < r := by
        simpa [r, periodicDistance_eq_abs_sub_round, rationalCenter, hround]
          using hdist
      left
      refine ⟨hIcc.1, ?_⟩
      simpa [abs_of_nonneg hIcc.1] using hrad
    · have hround : round alpha = 1 := by
        apply round_eq_iff.mpr
        constructor <;> norm_num at * <;> linarith [hIcc.2, hhalf]
      have hrad : |alpha - 1| < r := by
        simpa [r, periodicDistance_eq_abs_sub_round, rationalCenter, hround]
          using hdist
      right
      refine ⟨?_, hIcc.2⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hIcc.2)] at hrad
      linarith
  · intro h
    rcases h with hlow | hhigh
    · have hround : round alpha = 0 := by
        apply round_eq_zero_iff.mpr
        constructor <;> norm_num at * <;> linarith [hlow.1, hlow.2, hradius]
      have hIcc : alpha ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact hlow.1
        · have : alpha < 1 / 2 := by linarith [hlow.2, hradius]
          linarith
      refine ⟨hIcc, ?_⟩
      rw [periodicDistance_eq_abs_sub_round]
      simpa [r, rationalCenter, hround, abs_of_nonneg hlow.1] using hlow.2
    · have hround : round alpha = 1 := by
        apply round_eq_iff.mpr
        constructor <;> norm_num at * <;> linarith [hhigh.1, hhigh.2, hradius]
      have hIcc : alpha ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · have : 1 / 2 ≤ alpha := by linarith [hhigh.1, hradius]
          linarith
        · exact hhigh.2
      refine ⟨hIcc, ?_⟩
      rw [periodicDistance_eq_abs_sub_round]
      have hle : alpha - 1 ≤ 0 := by linarith [hhigh.2]
      have hrad : |alpha - 1| < r := by
        rw [abs_of_nonpos hle]
        linarith [hhigh.1]
      simpa [r, rationalCenter, hround] using hrad

/-- Homogeneous cubic approximation at the canonical displacement from a
rational major-arc center. -/
noncomputable def wrappedHomogeneousMajorArcModel
    (q a N n T : ℕ) [NeZero q] (alpha : ℝ) : ℂ := by
  let beta := wrappedMajorArcDisplacement a q alpha
  let tau := beta * (N : ℝ) ^ 3
  exact ((unitCubicExponentialSum (a : ZMod q) *
      (Nat.totient q : ℂ)⁻¹) *
      ((N : ℝ) • oneDimensionalCubicIntegral tau)) ^ n *
      negAddChar (rationalCenter a q + beta) T

/-- The homogeneous wrapped model is unchanged by integer translations, as
required to unfold a seam-crossing circle arc. -/
theorem wrappedHomogeneousMajorArcModel_add_int
    (q a N n T : ℕ) [NeZero q] (alpha : ℝ) (z : ℤ) :
    wrappedHomogeneousMajorArcModel q a N n T (alpha + z) =
      wrappedHomogeneousMajorArcModel q a N n T alpha := by
  simp [wrappedHomogeneousMajorArcModel,
    wrappedMajorArcDisplacement_add_int]

/-- On an interior clipped arc, the wrapped homogeneous model is exactly the
local homogeneous model in the ordinary displacement coordinate. -/
theorem wrappedHomogeneousMajorArcModel_eq_localIntegrand_of_interior
    (q a N n T : ℕ) [NeZero q] {alpha radius : ℝ}
    (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (hright : radius < rationalCenter a q)
    (hleft : radius < 1 - rationalCenter a q)
    (hdist : CookMagyarArcs.periodicDistance alpha
      (rationalCenter a q) < radius) :
    wrappedHomogeneousMajorArcModel q a N n T alpha =
      homogeneousMajorArcLocalIntegrand q a N n T
        (alpha - rationalCenter a q) := by
  have hdisp := wrappedMajorArcDisplacement_eq_sub_of_interior
    halpha hright hleft hdist
  simp [wrappedHomogeneousMajorArcModel,
    homogeneousMajorArcLocalIntegrand, wrappedMajorArcDisplacement, hdisp]

/-- Exact evaluation of the homogeneous model on a clipped major arc whose
circle neighborhood does not cross the endpoints of `[0,1]`. -/
theorem integral_wrappedHomogeneousMajorArcModel_eq_truncatedSingularIntegral_of_interior
    (q a N n T Q : ℕ) [NeZero q] (hN : 0 < N)
    (hright : cubicArcRadius N Q < rationalCenter a q)
    (hleft : cubicArcRadius N Q < 1 - rationalCenter a q) :
    (∫ alpha in majorArcAt N Q a q,
        wrappedHomogeneousMajorArcModel q a N n T alpha) =
      ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) *
        negAddChar (rationalCenter a q) T) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q) := by
  let c : ℝ := rationalCenter a q
  let r : ℝ := cubicArcRadius N Q
  have hrnonneg : 0 ≤ r := by
    dsimp [r, cubicArcRadius]
    positivity
  have hset : majorArcAt N Q a q = Set.Ioo (c - r) (c + r) := by
    simpa [c, r] using majorArcAt_eq_Ioo_of_interior_radius N Q a q hright hleft
  calc
    (∫ alpha in majorArcAt N Q a q,
        wrappedHomogeneousMajorArcModel q a N n T alpha) =
      ∫ alpha in Set.Ioo (c - r) (c + r),
        wrappedHomogeneousMajorArcModel q a N n T alpha := by rw [hset]
    _ = ∫ alpha in Set.Ioo (c - r) (c + r),
        homogeneousMajorArcLocalIntegrand q a N n T (alpha - c) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro alpha halpha
      have harc : alpha ∈ majorArcAt N Q a q := by rw [hset]; exact halpha
      exact wrappedHomogeneousMajorArcModel_eq_localIntegrand_of_interior
        q a N n T harc.1 hright hleft harc.2
    _ = ∫ alpha in Set.Icc (c - r) (c + r),
        homogeneousMajorArcLocalIntegrand q a N n T (alpha - c) := by
      rw [← integral_Icc_eq_integral_Ioo]
    _ = ∫ alpha in (c - r)..(c + r),
        homogeneousMajorArcLocalIntegrand q a N n T (alpha - c) := by
      rw [intervalIntegral.integral_of_le (by linarith [hrnonneg]),
        ← integral_Icc_eq_integral_Ioc]
    _ = ∫ beta in (-r)..r,
        homogeneousMajorArcLocalIntegrand q a N n T beta := by
      calc
        (∫ alpha in (c - r)..(c + r),
            homogeneousMajorArcLocalIntegrand q a N n T (alpha - c)) =
          ∫ alpha in (c - r)..(c + r),
            homogeneousMajorArcLocalIntegrand q a N n T (alpha + -c) := by
              congr 1
        _ = ∫ beta in (c - r + -c)..(c + r + -c),
            homogeneousMajorArcLocalIntegrand q a N n T beta :=
          intervalIntegral.integral_comp_add_right
            (f := homogeneousMajorArcLocalIntegrand q a N n T) (-c)
        _ = ∫ beta in (-r)..r,
            homogeneousMajorArcLocalIntegrand q a N n T beta := by
          congr 1 <;> ring
    _ = ∫ beta in Set.Icc (-r) r,
        homogeneousMajorArcLocalIntegrand q a N n T beta := by
      rw [intervalIntegral.integral_of_le (by linarith [hrnonneg]),
        ← integral_Icc_eq_integral_Ioc]
    _ = _ := by
      simpa [r, cubicArcRadius] using
        integral_homogeneousMajorArcLocalIntegrand_window_eq_truncatedSingularIntegral
          q a N n T Q hN

/-- Exact evaluation of the endpoint-centered denominator-one arc, obtained
by unfolding its two pieces across the period-one seam. -/
private theorem integral_wrappedHomogeneousMajorArcModel_zero_one_eq_truncatedSingularIntegral_of_integrable
    (N n T Q : ℕ) (hN : 0 < N)
    (hradius : cubicArcRadius N Q ≤ (1 / 2 : ℝ))
    (hFint : IntegrableOn (wrappedHomogeneousMajorArcModel 1 0 N n T)
      (majorArcAt N Q 0 1)) :
    (∫ alpha in majorArcAt N Q 0 1,
        wrappedHomogeneousMajorArcModel 1 0 N n T alpha) =
      ((unitCubicExponentialSum (0 : ZMod 1) *
          (Nat.totient 1 : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) * negAddChar 0 T) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q) := by
  let r : ℝ := cubicArcRadius N Q
  let F : ℝ → ℂ := wrappedHomogeneousMajorArcModel 1 0 N n T
  let G : ℝ → ℂ := homogeneousMajorArcLocalIntegrand 1 0 N n T
  have hrnonneg : 0 ≤ r := by dsimp [r, cubicArcRadius]; positivity
  have hrhalf : r ≤ 1 / 2 := by simpa [r] using hradius
  have hdecomp : majorArcAt N Q 0 1 =
      Set.Ico (0 : ℝ) r ∪ Set.Ioc (1 - r) 1 := by
    simpa [r] using majorArcAt_zero_one_eq_seam_intervals N Q hradius
  have hdisj : Disjoint (Set.Ico (0 : ℝ) r) (Set.Ioc (1 - r) 1) := by
    rw [Set.disjoint_left]
    intro alpha hlow hhigh
    have hlow' := hlow.2
    have hhigh' := hhigh.1
    linarith
  have hFint' : IntegrableOn F (majorArcAt N Q 0 1) := by
    simpa [F] using hFint
  have hFintLow : IntegrableOn F (Set.Ico (0 : ℝ) r) :=
    hFint'.mono_set (by rw [hdecomp]; exact Set.subset_union_left)
  have hFintHigh : IntegrableOn F (Set.Ioc (1 - r) 1) :=
    hFint'.mono_set (by rw [hdecomp]; exact Set.subset_union_right)
  have hLowPoint : ∀ alpha ∈ Set.Ico (0 : ℝ) r,
      F alpha = G alpha := by
    intro alpha halpha
    have hround : round alpha = 0 := by
      apply round_eq_zero_iff.mpr
      constructor <;> linarith [halpha.1, halpha.2, hrhalf]
    simp [F, G, wrappedHomogeneousMajorArcModel,
      homogeneousMajorArcLocalIntegrand, wrappedMajorArcDisplacement,
      rationalCenter, hround]
  have hHighPoint : ∀ alpha ∈ Set.Ioc (1 - r) 1,
      F alpha = G (alpha - 1) := by
    intro alpha halpha
    have hround : round alpha = 1 := by
      apply round_eq_iff.mpr
      constructor <;> linarith [halpha.1, halpha.2, hrhalf]
    simp [F, G, wrappedHomogeneousMajorArcModel,
      homogeneousMajorArcLocalIntegrand, wrappedMajorArcDisplacement,
      rationalCenter, hround]
  have hlow :
      (∫ alpha in Set.Ico (0 : ℝ) r, F alpha) =
        ∫ beta in (0 : ℝ)..r, G beta := by
    calc
      (∫ alpha in Set.Ico (0 : ℝ) r, F alpha) =
          ∫ alpha in Set.Ico (0 : ℝ) r, G alpha :=
        setIntegral_congr_fun measurableSet_Ico hLowPoint
      _ = ∫ beta in Set.Ioc (0 : ℝ) r, G beta := by
        rw [integral_Ico_eq_integral_Ioc]
      _ = ∫ beta in (0 : ℝ)..r, G beta := by
        rw [← intervalIntegral.integral_of_le hrnonneg]
  have hhigh :
      (∫ alpha in Set.Ioc (1 - r) 1, F alpha) =
        ∫ beta in (-r)..(0 : ℝ), G beta := by
    calc
      (∫ alpha in Set.Ioc (1 - r) 1, F alpha) =
          ∫ alpha in Set.Ioc (1 - r) 1, G (alpha - 1) :=
        setIntegral_congr_fun measurableSet_Ioc hHighPoint
      _ = ∫ alpha in (1 - r)..1, G (alpha - 1) := by
        rw [← intervalIntegral.integral_of_le (by linarith [hrhalf])]
      _ = ∫ beta in (1 - r + -1)..(1 + -1), G beta := by
        calc
          (∫ alpha in (1 - r)..1, G (alpha - 1)) =
              ∫ alpha in (1 - r)..1, G (alpha + -1) := by
                congr 1
          _ = ∫ beta in (1 - r + -1)..(1 + -1), G beta :=
            intervalIntegral.integral_comp_add_right (f := G) (-1)
      _ = ∫ beta in (-r)..(0 : ℝ), G beta := by
        congr 1 <;> ring
  have hGcont : Continuous G := by
    let U : ℂ := unitCubicExponentialSum (0 : ZMod 1) *
      (Nat.totient 1 : ℂ)⁻¹
    let J : ℝ → ℂ := fun beta =>
      (N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)
    have hJ : Continuous J := by
      dsimp [J]
      exact (oneDimensionalCubicIntegral_continuous.comp
        (continuous_id.mul continuous_const)).const_smul (N : ℝ)
    have hbase : Continuous (fun beta : ℝ => U * J beta) :=
      continuous_const.mul hJ
    have hpow : Continuous (fun beta : ℝ => (U * J beta) ^ n) := hbase.pow n
    have hphase : Continuous (fun beta : ℝ =>
        negAddChar (rationalCenter 0 1 + beta) T) := by
      fun_prop [negAddChar]
    change Continuous (fun beta : ℝ =>
      (U * J beta) ^ n * negAddChar (rationalCenter 0 1 + beta) T)
    exact hpow.mul hphase
  have hsplit :
      (∫ beta in (0 : ℝ)..r, G beta) +
        ∫ beta in (-r)..(0 : ℝ), G beta =
          ∫ beta in (-r)..r, G beta := by
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (hGcont.intervalIntegrable (-r) 0)
      (hGcont.intervalIntegrable 0 r)
  calc
    (∫ alpha in majorArcAt N Q 0 1, F alpha) =
        (∫ alpha in Set.Ico (0 : ℝ) r, F alpha) +
          ∫ alpha in Set.Ioc (1 - r) 1, F alpha := by
      rw [hdecomp]
      exact setIntegral_union hdisj measurableSet_Ioc hFintLow hFintHigh
    _ = ∫ beta in (-r)..r, G beta := by rw [hlow, hhigh, hsplit]
    _ = ∫ beta in Set.Icc (-r) r, G beta := by
      rw [intervalIntegral.integral_of_le (by linarith [hrnonneg]),
        ← integral_Icc_eq_integral_Ioc]
    _ = _ := by
      simpa [r, G, cubicArcRadius, rationalCenter] using
        integral_homogeneousMajorArcLocalIntegrand_window_eq_truncatedSingularIntegral
          1 0 N n T Q hN

theorem measurable_wrappedHomogeneousMajorArcModel
    (q a N n T : ℕ) [NeZero q] :
    Measurable (wrappedHomogeneousMajorArcModel q a N n T) := by
  let U : ℂ := unitCubicExponentialSum (a : ZMod q) *
    (Nat.totient q : ℂ)⁻¹
  let J : ℝ → ℂ := fun beta =>
    (N : ℝ) • oneDimensionalCubicIntegral (beta * (N : ℝ) ^ 3)
  have hJ : Continuous J := by
    dsimp [J]
    exact (oneDimensionalCubicIntegral_continuous.comp
      (continuous_id.mul continuous_const)).const_smul (N : ℝ)
  have hbase : Continuous (fun beta : ℝ => U * J beta) :=
    continuous_const.mul hJ
  have hpow : Continuous (fun beta : ℝ => (U * J beta) ^ n) := hbase.pow n
  have hphase : Continuous (fun beta : ℝ =>
      negAddChar (rationalCenter a q + beta) T) := by
    fun_prop [negAddChar]
  have hmodel : Continuous (fun beta : ℝ =>
      (U * J beta) ^ n * negAddChar (rationalCenter a q + beta) T) :=
    hpow.mul hphase
  have hdisp := measurable_wrappedMajorArcDisplacement a q
  change Measurable (fun alpha : ℝ =>
    (U * J (wrappedMajorArcDisplacement a q alpha)) ^ n *
      negAddChar (rationalCenter a q +
        wrappedMajorArcDisplacement a q alpha) T)
  exact hmodel.measurable.comp hdisp

theorem wrappedHomogeneousMajorArcModel_integrableOn
    (q a N Q n T : ℕ) [NeZero q] :
    IntegrableOn (wrappedHomogeneousMajorArcModel q a N n T)
      (majorArcAt N Q a q) := by
  have hfin : volume (majorArcAt N Q a q) ≠ ∞ := by
    apply ne_of_lt
    calc
      volume (majorArcAt N Q a q) ≤ volume (Set.Icc (0 : ℝ) 1) :=
        measure_mono (majorArcAt_subset_Icc N Q a q)
      _ < ∞ := by simp
  have hbound : ∀ alpha : ℝ,
      ‖wrappedHomogeneousMajorArcModel q a N n T alpha‖ ≤ (N : ℝ) ^ n := by
    intro alpha
    rw [wrappedHomogeneousMajorArcModel, norm_mul, norm_pow,
      norm_negAddChar, mul_one]
    have hU := norm_unitCubicExponentialSum_mul_inv_totient_le_one
      q (a : ZMod q)
    have hI := norm_oneDimensionalCubicIntegral_le_one
      (wrappedMajorArcDisplacement a q alpha * (N : ℝ) ^ 3)
    have hsmul :
        ‖(N : ℝ) • oneDimensionalCubicIntegral
          (wrappedMajorArcDisplacement a q alpha * (N : ℝ) ^ 3)‖ ≤
          (N : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hI (show 0 ≤ (N : ℝ) by positivity)
    have hprod :
        ‖(unitCubicExponentialSum (a : ZMod q) *
            (Nat.totient q : ℂ)⁻¹) *
          ((N : ℝ) • oneDimensionalCubicIntegral
            (wrappedMajorArcDisplacement a q alpha * (N : ℝ) ^ 3))‖ ≤
          (N : ℝ) := by
      rw [norm_mul]
      calc
        ‖unitCubicExponentialSum (a : ZMod q) *
            (Nat.totient q : ℂ)⁻¹‖ *
          ‖(N : ℝ) • oneDimensionalCubicIntegral
            (wrappedMajorArcDisplacement a q alpha * (N : ℝ) ^ 3)‖ ≤
          1 * (N : ℝ) := mul_le_mul hU hsmul
            (norm_nonneg _) (by norm_num)
        _ = (N : ℝ) := one_mul _
    exact pow_le_pow_left₀ (norm_nonneg _) hprod n
  exact volume.integrableOn_of_bounded hfin
    (measurable_wrappedHomogeneousMajorArcModel q a N n T).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- The endpoint-centered denominator-one arc has the same exact evaluation
as the other arcs after unfolding its two pieces across the seam. -/
theorem integral_wrappedHomogeneousMajorArcModel_zero_one_eq_truncatedSingularIntegral
    (N n T Q : ℕ) (hN : 0 < N)
    (hradius : cubicArcRadius N Q ≤ (1 / 2 : ℝ)) :
    (∫ alpha in majorArcAt N Q 0 1,
        wrappedHomogeneousMajorArcModel 1 0 N n T alpha) =
      ((unitCubicExponentialSum (0 : ZMod 1) *
          (Nat.totient 1 : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) * negAddChar 0 T) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q) := by
  exact integral_wrappedHomogeneousMajorArcModel_zero_one_eq_truncatedSingularIntegral_of_integrable
    N n T Q hN hradius
    (wrappedHomogeneousMajorArcModel_integrableOn 1 0 N Q n T)

/-- Under the standard scale separation, every reduced rational major arc,
including the seam-centered denominator-one arc, has the same exact local
singular-integral evaluation. -/
theorem integral_wrappedHomogeneousMajorArcModel_eq_truncatedSingularIntegral_of_majorArcCenter
    {q a N n T Q : ℕ} [NeZero q]
    (hcenter : (a, q) ∈ majorArcCenters Q) (hN : 0 < N)
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    (∫ alpha in majorArcAt N Q a q,
        wrappedHomogeneousMajorArcModel q a N n T alpha) =
      ((unitCubicExponentialSum (a : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
        ((N : ℝ) ^ n : ℂ) *
        negAddChar (rationalCenter a q) T) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q) := by
  rcases mem_majorArcCenters_iff.mp hcenter with
    ⟨hqQ, hq0, haq, hcop⟩
  by_cases hq1 : q = 1
  · have ha0 : a = 0 := by omega
    subst q
    subst a
    have hrad : cubicArcRadius N Q ≤ (1 / 2 : ℝ) := by
      have hsep := two_cubicArcRadius_le_fraction_separation
        (by norm_num : (1 : ℕ) ≠ 0) (by norm_num : (1 : ℕ) ≠ 0)
        hqQ hqQ hscale
      linarith
    simpa [rationalCenter] using
      integral_wrappedHomogeneousMajorArcModel_zero_one_eq_truncatedSingularIntegral
        N n T Q hN hrad
  · have hq2 : 2 ≤ q := by omega
    have ha_pos : 0 < a := by
      by_contra ha
      have haeq : a = 0 := by omega
      subst a
      have hqeq : q = 1 := by simpa [Nat.Coprime] using hcop
      exact hq1 hqeq
    have hmargin := cubicArcRadius_lt_rationalCenter_and_one_sub
      hq0 hqQ ha_pos haq hq2 hscale
    exact integral_wrappedHomogeneousMajorArcModel_eq_truncatedSingularIntegral_of_interior
      q a N n T Q hN hmargin.1 hmargin.2

/-- Summing the exact rational-center coefficients over one denominator
recovers the corresponding complete-sum coefficient in the singular series.
This is the arithmetic reindexing step needed after integrating the model on
each individual major arc. -/
theorem majorArcCenterCoefficient_sum_eq_singularSeriesCoefficient
    (q n T : ℕ) [NeZero q] :
    (letI : Fintype {a : ℕ // a < q ∧ Nat.Coprime a q} :=
        Fintype.ofEquiv (ZMod q)ˣ
          (CookMagyarMajorArc.reducedResiduesEquivUnits q).symm
     ∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q},
      (unitCubicExponentialSum (a.1 : ZMod q) *
        (Nat.totient q : ℂ)⁻¹) ^ n *
        negAddChar (rationalCenter a.1 q) T) =
      singularSeriesCoefficient q n T (NeZero.ne q) := by
  classical
  let e := CookMagyarMajorArc.reducedResiduesEquivUnits q
  letI : Fintype {a : ℕ // a < q ∧ Nat.Coprime a q} :=
    Fintype.ofEquiv (ZMod q)ˣ e.symm
  let f : (ZMod q)ˣ → ℂ := fun u =>
    (unitCubicExponentialSum (u : ZMod q) *
      (Nat.totient q : ℂ)⁻¹) ^ n *
      standardAdditiveCharacter (-((u : ZMod q) * (T : ZMod q)))
  calc
    (∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q},
        (unitCubicExponentialSum (a.1 : ZMod q) *
          (Nat.totient q : ℂ)⁻¹) ^ n *
          negAddChar (rationalCenter a.1 q) T) =
        ∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q}, f (e a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          change (unitCubicExponentialSum (a.1 : ZMod q) *
              (Nat.totient q : ℂ)⁻¹) ^ n *
              negAddChar (rationalCenter a.1 q) T =
            (unitCubicExponentialSum (e a : ZMod q) *
              (Nat.totient q : ℂ)⁻¹) ^ n *
              standardAdditiveCharacter
                (-((e a : ZMod q) * (T : ZMod q)))
          rw [CookMagyarMajorArc.negAddChar_rationalCenter]
          have hcoe : (e a : ZMod q) = (a.1 : ZMod q) := by
            simp only [e, CookMagyarMajorArc.reducedResiduesEquivUnits]
            exact (ZMod.isUnit_iff_coprime a.1 q).mpr a.2.2 |>.unit_spec
          rw [hcoe]
    _ = ∑ u : (ZMod q)ˣ, f u := e.sum_comp f
    _ = singularSeriesCoefficient q n T (NeZero.ne q) := by
      unfold f singularSeriesCoefficient
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _hu
      ring

/-- After summing over the reduced numerators of one denominator, the
homogeneous model contributes exactly the expected singular-series
coefficient times the common real-place factor. -/
theorem sum_wrappedHomogeneousMajorArcModel_integrals_eq_singularSeriesCoefficient
    {q N n T Q : ℕ} [NeZero q] (hqQ : q ≤ Q) (hN : 0 < N)
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    (letI : Fintype {a : ℕ // a < q ∧ Nat.Coprime a q} :=
        Fintype.ofEquiv (ZMod q)ˣ
          (CookMagyarMajorArc.reducedResiduesEquivUnits q).symm
     ∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q},
       ∫ alpha in majorArcAt N Q a.1 q,
         wrappedHomogeneousMajorArcModel q a.1 N n T alpha) =
      (((N : ℝ) ^ n : ℂ) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)) *
        singularSeriesCoefficient q n T (NeZero.ne q) := by
  classical
  let e := CookMagyarMajorArc.reducedResiduesEquivUnits q
  letI : Fintype {a : ℕ // a < q ∧ Nat.Coprime a q} :=
    Fintype.ofEquiv (ZMod q)ˣ e.symm
  let K : ℂ := ((N : ℝ) ^ n : ℂ) *
    (((N : ℝ) ^ 3)⁻¹ •
      truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)
  calc
    (∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q},
        ∫ alpha in majorArcAt N Q a.1 q,
          wrappedHomogeneousMajorArcModel q a.1 N n T alpha) =
        ∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q},
          K * ((unitCubicExponentialSum (a.1 : ZMod q) *
            (Nat.totient q : ℂ)⁻¹) ^ n *
            negAddChar (rationalCenter a.1 q) T) := by
      apply Finset.sum_congr rfl
      intro a _ha
      have hcenter : (a.1, q) ∈ majorArcCenters Q :=
        mem_majorArcCenters_iff.mpr
          ⟨hqQ, NeZero.ne q, a.2.1, a.2.2⟩
      rw [integral_wrappedHomogeneousMajorArcModel_eq_truncatedSingularIntegral_of_majorArcCenter
        hcenter hN hscale]
      simp only [K]
      ring
    _ = K *
        ∑ a : {a : ℕ // a < q ∧ Nat.Coprime a q},
          (unitCubicExponentialSum (a.1 : ZMod q) *
            (Nat.totient q : ℂ)⁻¹) ^ n *
            negAddChar (rationalCenter a.1 q) T := by
      rw [Finset.mul_sum]
    _ = K * singularSeriesCoefficient q n T (NeZero.ne q) := by
      rw [majorArcCenterCoefficient_sum_eq_singularSeriesCoefficient]

/-- Summing the fixed-denominator model identity over `1 ≤ q ≤ Q` gives the
truncated singular series exactly. -/
theorem sum_wrappedHomogeneousMajorArcModel_integrals_by_denominator_eq_truncatedSingularSeries
    (N n T Q : ℕ) (hN : 0 < N)
    (hscale : 2 * Q ^ 3 ≤ N ^ 3) :
    (∑ q : {q : ℕ // q ∈ Finset.Icc 1 Q},
      (letI : NeZero q.1 := ⟨by
        have hq := (Finset.mem_Icc.mp q.2).1
        omega⟩
       letI : Fintype {a : ℕ // a < q.1 ∧ Nat.Coprime a q.1} :=
         Fintype.ofEquiv (ZMod q.1)ˣ
           (CookMagyarMajorArc.reducedResiduesEquivUnits q.1).symm
       ∑ a : {a : ℕ // a < q.1 ∧ Nat.Coprime a q.1},
         ∫ alpha in majorArcAt N Q a.1 q.1,
           wrappedHomogeneousMajorArcModel q.1 a.1 N n T alpha)) =
      (((N : ℝ) ^ n : ℂ) *
        (((N : ℝ) ^ 3)⁻¹ •
          truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)) *
        truncatedSingularSeries n T Q := by
  classical
  let K : ℂ := ((N : ℝ) ^ n : ℂ) *
    (((N : ℝ) ^ 3)⁻¹ •
      truncatedSingularIntegral n ((T : ℝ) / (N : ℝ) ^ 3) Q)
  calc
    (∑ q : {q : ℕ // q ∈ Finset.Icc 1 Q},
        (letI : NeZero q.1 := ⟨by
          have hq := (Finset.mem_Icc.mp q.2).1
          omega⟩
         letI : Fintype {a : ℕ // a < q.1 ∧ Nat.Coprime a q.1} :=
           Fintype.ofEquiv (ZMod q.1)ˣ
             (CookMagyarMajorArc.reducedResiduesEquivUnits q.1).symm
         ∑ a : {a : ℕ // a < q.1 ∧ Nat.Coprime a q.1},
           ∫ alpha in majorArcAt N Q a.1 q.1,
             wrappedHomogeneousMajorArcModel q.1 a.1 N n T alpha)) =
        ∑ q : {q : ℕ // q ∈ Finset.Icc 1 Q},
          K * singularSeriesCoefficient q.1 n T (by
            have hq := (Finset.mem_Icc.mp q.2).1
            omega) := by
      apply Finset.sum_congr rfl
      intro q _
      have hqpos : 0 < q.1 := (Finset.mem_Icc.mp q.2).1
      letI : NeZero q.1 := ⟨hqpos.ne'⟩
      have hqQ : q.1 ≤ Q := (Finset.mem_Icc.mp q.2).2
      exact sum_wrappedHomogeneousMajorArcModel_integrals_eq_singularSeriesCoefficient
        hqQ hN hscale
    _ = K * ∑ q : {q : ℕ // q ∈ Finset.Icc 1 Q},
          singularSeriesCoefficient q.1 n T (by
            have hq := (Finset.mem_Icc.mp q.2).1
            omega) := by
      rw [Finset.mul_sum]
    _ = K * truncatedSingularSeries n T Q := by
      congr 1
      unfold truncatedSingularSeries
      calc
        (∑ q : {q : ℕ // q ∈ Finset.Icc 1 Q},
            singularSeriesCoefficient q.1 n T (by
              have hq := (Finset.mem_Icc.mp q.2).1
              omega)) =
          ∑ q : {q : ℕ // q ∈ Finset.Icc 1 Q},
            singularSeriesTerm n T q.1 := by
              apply Finset.sum_congr rfl
              intro q _
              exact (singularSeriesTerm_of_pos n T
                (Finset.mem_Icc.mp q.2).1).symm
        _ = ∑ q ∈ Finset.Icc 1 Q, singularSeriesTerm n T q := by
          rw [Finset.univ_eq_attach, Finset.sum_attach]

/-- Extend the model by zero to invalid denominator pairs, making it a
nondependent function on the finite set of rational centers. -/
noncomputable def wrappedHomogeneousMajorArcModelForCenter
    (N n T : ℕ) (aq : ℕ × ℕ) (alpha : ℝ) : ℂ := by
  classical
  by_cases hq : aq.2 = 0
  · exact 0
  · letI : NeZero aq.2 := ⟨hq⟩
    exact wrappedHomogeneousMajorArcModel aq.2 aq.1 N n T alpha

/-- On a rational major arc, the powered integrand is close to the wrapped
homogeneous model by the AP discrepancy plus the phase-scaling error. -/
theorem norm_cubicIntegrand_sub_wrappedHomogeneousMajorArcModel_le
    (q a N Q n T : ℕ) [NeZero q] {alpha Delta : ℝ}
    (hN : 0 < N) (hDelta : 0 ≤ Delta)
    (halpha : alpha ∈ majorArcAt N Q a q)
    (hAP : ∀ r : ZMod q, ∀ m ≤ N,
      ‖cubicResiduePartialSum q r m -
        (m + 1 : ℕ) *
          (if IsUnit r then (Nat.totient q : ℂ)⁻¹ else 0)‖ ≤ Delta) :
    ‖cubicIntegrand n N T alpha -
      wrappedHomogeneousMajorArcModel q a N n T alpha‖ ≤
      (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((q : ℝ) * Delta + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * Q / (N : ℝ)) := by
  let beta := wrappedMajorArcDisplacement a q alpha
  let tau := beta * (N : ℝ) ^ 3
  have hbeta : |beta| < cubicArcRadius N Q := by
    simpa [beta, wrappedMajorArcDisplacement,
      periodicDistance_eq_abs_sub_round] using halpha.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htau : |tau| ≤ Q := by
    have hrad : |beta| ≤ (Q : ℝ) / (N : ℝ) ^ 3 := by
      simpa only [cubicArcRadius] using le_of_lt hbeta
    dsimp [tau]
    rw [abs_mul, abs_of_nonneg (show 0 ≤ (N : ℝ) ^ 3 by positivity)]
    have hmul := mul_le_mul_of_nonneg_right hrad
      (show 0 ≤ (N : ℝ) ^ 3 by positivity)
    have hden : (N : ℝ) ^ 3 ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hden] at hmul
    exact hmul
  have hscale : tau / (N : ℝ) ^ 3 = beta := by
    dsimp [tau]
    field_simp
  have hperiod : cubicIntegrand n N T alpha =
      cubicIntegrand n N T (rationalCenter a q + beta) := by
    have hdecomp : alpha = rationalCenter a q + beta +
        (round (alpha - rationalCenter a q) : ℤ) := by
      dsimp [beta, wrappedMajorArcDisplacement]
      ring
    rw [hdecomp, cubicIntegrand_add_int]
  have hhom := norm_cubicIntegrand_sub_homogeneousModel_le_of_AP
    q a N Q n T hN hDelta htau hAP
  rw [hscale] at hhom
  rw [hperiod]
  change ‖cubicIntegrand n N T (rationalCenter a q + beta) -
      ((unitCubicExponentialSum (a : ZMod q) *
        (Nat.totient q : ℂ)⁻¹) *
        ((N : ℝ) • oneDimensionalCubicIntegral tau)) ^ n *
        negAddChar (rationalCenter a q + beta) T‖ ≤ _
  calc
    _ ≤ (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((q : ℝ) * Delta + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * |tau| / (N : ℝ)) := by
      simpa [tau, wrappedHomogeneousMajorArcModel, beta] using hhom
    _ ≤ (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
        (((q : ℝ) * Delta + 1) * (1 + 8 * Real.pi * (Q : ℝ)) +
          2 * Real.pi * Q / (N : ℝ)) := by
      have hcoef : 0 ≤ (n : ℝ) *
          ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) := by positivity
      have htail : 2 * Real.pi * |tau| / (N : ℝ) ≤
          2 * Real.pi * Q / (N : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left htau (by positivity)) hNr.le
      exact mul_le_mul_of_nonneg_left (by linarith [htail]) hcoef

/-- Integrate the homogeneous singular-integral approximation over all
disjoint major arcs, conditional on the uniform AP discrepancies. -/
theorem norm_cubicMajorArcIntegral_sub_sum_wrappedHomogeneousModels_le
    (n N T Q : ℕ) (hsep : 2 * Q ^ 3 ≤ N ^ 3)
    (Delta : ℕ → ℝ) (hN : 0 < N)
    (hDelta : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      0 ≤ Delta aq.2)
    (hAP : ∀ aq ∈ (majorArcCenters_finite Q).toFinset,
      ∀ (hqn : aq.2 ≠ 0), letI : NeZero aq.2 := ⟨hqn⟩
      ∀ r : ZMod aq.2, ∀ m ≤ N,
        ‖cubicResiduePartialSum aq.2 r m -
          (m + 1 : ℕ) *
            (if IsUnit r then (Nat.totient aq.2 : ℂ)⁻¹ else 0)‖ ≤
          Delta aq.2) :
    ‖cubicMajorArcIntegral n N T Q -
        ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
          ∫ alpha in majorArcAt N Q aq.1 aq.2,
            wrappedHomogeneousMajorArcModelForCenter N n T aq alpha‖ ≤
      ∑ aq ∈ (majorArcCenters_finite Q).toFinset,
        ((n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
          (((aq.2 : ℝ) * Delta aq.2 + 1) *
            (1 + 8 * Real.pi * (Q : ℝ)) +
            2 * Real.pi * Q / (N : ℝ))) *
          volume.real (majorArcAt N Q aq.1 aq.2) := by
  let F := (majorArcCenters_finite Q).toFinset
  let model : ℕ × ℕ → ℝ → ℂ := fun aq alpha =>
    wrappedHomogeneousMajorArcModelForCenter N n T aq alpha
  let E : ℕ × ℕ → ℝ := fun aq =>
    (n : ℝ) * ((Real.log 4 + 4) * (N : ℝ)) ^ (n - 1) *
      (((aq.2 : ℝ) * Delta aq.2 + 1) *
        (1 + 8 * Real.pi * (Q : ℝ)) +
        2 * Real.pi * Q / (N : ℝ))
  have hmodel : ∀ aq ∈ F,
      IntegrableOn (model aq) (majorArcAt N Q aq.1 aq.2) := by
    intro aq haq
    change aq ∈ (majorArcCenters_finite Q).toFinset at haq
    have hcenter : aq ∈ majorArcCenters Q := by
      simpa only [Set.Finite.mem_toFinset] using haq
    rcases hcenter with ⟨_, hqn, _, _⟩
    letI : NeZero aq.2 := ⟨hqn⟩
    have hmodel_eq : model aq =
        wrappedHomogeneousMajorArcModel aq.2 aq.1 N n T := by
      funext alpha
      simp [model, wrappedHomogeneousMajorArcModelForCenter, hqn]
    rw [hmodel_eq]
    exact wrappedHomogeneousMajorArcModel_integrableOn aq.2 aq.1 N Q n T
  have hpoint : ∀ aq ∈ F, ∀ alpha ∈ majorArcAt N Q aq.1 aq.2,
      ‖cubicIntegrand n N T alpha - model aq alpha‖ ≤ E aq := by
    intro aq haq alpha halpha
    change aq ∈ (majorArcCenters_finite Q).toFinset at haq
    have hcenter : aq ∈ majorArcCenters Q := by
      simpa only [Set.Finite.mem_toFinset] using haq
    have hqn : aq.2 ≠ 0 := hcenter.2.1
    letI : NeZero aq.2 := ⟨hqn⟩
    have hmodel_eq : model aq =
        wrappedHomogeneousMajorArcModel aq.2 aq.1 N n T := by
      funext x
      simp [model, wrappedHomogeneousMajorArcModelForCenter, hqn]
    rw [hmodel_eq]
    exact norm_cubicIntegrand_sub_wrappedHomogeneousMajorArcModel_le
      aq.2 aq.1 N Q n T hN (hDelta aq haq) halpha (hAP aq haq hqn)
  simpa only [F, model, E] using
    norm_cubicMajorArcIntegral_sub_sum_models_le n N T Q hsep
      model E hmodel hpoint

end SystolicGrowth.CookMagyarMajorArc
