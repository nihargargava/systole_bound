module

/-
Copyright (c) 2026.
-/
public import CookMagyar.Vaughan
public import CookMagyar.GeneralCubicWeyl

@[expose] public section

open Filter
open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarVaughan

open CookMagyarCircle CookMagyarArcs

/-! # The first Vaughan Type-I minor-arc block composition

This module composes the endpoint-uniform, logarithmically weighted
progression estimate with the exact quotient coordinates of Vaughan's first
Type-I sum. The remaining outer summation is displayed explicitly.
-/

set_option maxHeartbeats 800000 in
/-- On a minor arc, each divisor block in Vaughan's first Type-I sum is
controlled by the corresponding `Q=1`, `ell=d`, `r=1` progression estimate.
The hypotheses on `U` record the two cutoff facts needed for this source
specialization: its divisors lie in Hua's `ell` range and every such block has
positive progression length. -/
theorem eventually_cubicVaughanS1_minorArc_block_majorant
    (A sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
        ∀ U : ℕ,
          (U : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma3 →
          2 * U ≤ N →
          1 ≤ Real.log ((N : ℝ) + 2) →
          ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
            ∑ d ∈ Finset.Icc 1 N,
              if d ≤ U then
                2 * (1268822 *
                  (((N - d) / d + 2 : ℕ) : ℝ) /
                    (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                  (1 + 8 * Real.pi) *
                  Real.log ((((N - d) / d : ℕ) : ℝ) + 1)
              else 0 := by
  have hBlocks := eventually_logarithmicPrimeMinorArc_logWeighted_wrapped_progression_bound
    A sigma sigma0 sigma3 sigma4 saving hA hSA 1 (by norm_num)
    hbudget hsaving hcutoff
  filter_upwards [hBlocks] with N hN
  intro alpha hminor U hU hUshort hlog
  obtain ⟨a, q, beta, z, hqLower, hqUpper, ha, hac, halpha, hbeta,
      hscaled, hscaledOne, hprogressions⟩ := hN alpha hminor
  have hbase : ((1 : ℕ) : ℝ) ≤ (1 : ℝ) * Real.log ((N : ℝ) + 2) ^ sigma4 := by
    calc
      ((1 : ℕ) : ℝ) = (1 : ℝ) := by norm_num
      _ ≤ Real.log ((N : ℝ) + 2) ^ sigma4 := one_le_pow₀ hlog
      _ = (1 : ℝ) * Real.log ((N : ℝ) + 2) ^ sigma4 := by ring
  calc
    ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
        ∑ d ∈ Finset.Icc 1 N,
          if d ≤ U then
            ‖∑ m ∈ Finset.Icc 1 (N / d),
              (ArithmeticFunction.log m : ℂ) *
                addChar alpha (primeCubic (d * m))‖
          else 0 :=
      norm_cubic_vaughan_typeI_first_le_truncated_block_sum U N alpha
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hdu : d ≤ U
      · simp only [if_pos hdu]
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
        have htwo : 2 * d ≤ N := by omega
        have hM : 0 < (N - d) / d := by
          apply (Nat.le_div_iff_mul_le hdpos).2
          omega
        have hMsource :
            0 < (N - d * 1) / (d * (1 / Nat.gcd 1 d)) := by
          simpa [Nat.gcd_one_left] using hM
        have hblock := hprogressions d 1 1 (by norm_num) hdpos (by norm_num)
          (by simp) (by simpa using hdN)
          (le_trans (by exact_mod_cast hdu) hU) hbase hMsource
        have hshift := sum_log_primeCubic_divisor_quotient_eq_progression
          N d alpha hdpos hdN
        rw [hshift]
        simpa [Nat.gcd_one_left, halpha] using hblock
      · simp [hdu]

set_option maxHeartbeats 800000 in
/-- On a minor arc, the quotient block in Vaughan's second Type-I sum is a
wrapped unweighted progression with step `d*r`. Independent logarithmic
cutoffs on `d` and `r` imply the source step range when their exponents sum
to at most `sigmaStep`. -/
theorem eventually_cubicVaughanS2_minorArc_block_bound
    (A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hcutSteps : sigmaD + sigmaV ≤ sigmaStep)
    (hbudget : 8 * (sigma0 + sigmaStep) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigmaStep + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
        ∀ d r : ℕ,
          0 < d → 0 < r → d * r ≤ N →
          (d : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaD →
          (r : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaV →
          ‖∑ k ∈ Finset.Icc 0 ((N - d * r) / (d * r)),
            addChar alpha (primeCubic (d * r + d * r * k))‖ ≤
            (1268822 * (((N - d * r) / (d * r) + 2 : ℕ) : ℝ) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                (1 + 8 * Real.pi) := by
  have hSource := eventually_logarithmicPrimeMinorArc_wrapped_progression_character_bound
    A sigma sigma0 sigmaStep sigma4 saving hA hSA 1 (by norm_num)
    hbudget hsaving hcutoff
  have harg : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop := by
    convert tendsto_atTop_add_const_right _ (2 : ℝ)
      tendsto_natCast_atTop_atTop using 1
  have hlog : Tendsto
      (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  filter_upwards [hSource, hlog.eventually_ge_atTop (1 : ℝ)] with
    N hN hL
  intro alpha hminor d r hd hr hdr hD hR
  obtain ⟨a, q, beta, z, hqLower, hqUpper, ha, hac, halpha, hbeta,
      hscaled, hscaledOne, hprogressions⟩ := hN alpha hminor
  have hbase : (1 : ℝ) ≤ (1 : ℝ) * Real.log ((N : ℝ) + 2) ^ sigma4 := by
    calc
      1 = 1 * 1 := by ring
      _ ≤ 1 * Real.log ((N : ℝ) + 2) ^ sigma4 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hL) (by norm_num)
      _ = _ := by ring
  have hstepBound : (d * r : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaStep := by
    have hprod : (d : ℝ) * (r : ℝ) ≤
        Real.log ((N : ℝ) + 2) ^ sigmaD *
          Real.log ((N : ℝ) + 2) ^ sigmaV :=
      mul_le_mul hD hR (by positivity) (by positivity)
    calc
      (d * r : ℝ) = (d : ℝ) * (r : ℝ) := by norm_num
      _ ≤ Real.log ((N : ℝ) + 2) ^ sigmaD *
            Real.log ((N : ℝ) + 2) ^ sigmaV := hprod
      _ = Real.log ((N : ℝ) + 2) ^ (sigmaD + sigmaV) := by rw [← pow_add]
      _ ≤ Real.log ((N : ℝ) + 2) ^ sigmaStep :=
        pow_le_pow_right₀ hL hcutSteps
  have hstepBound' : (d * r : ℕ) ≤ (Real.log ((N : ℝ) + 2) ^ sigmaStep) := by
    exact_mod_cast hstepBound
  have hblock := hprogressions (d * r) 1 1 (by norm_num) (Nat.mul_pos hd hr)
    (by norm_num) (by simp) (by simpa using hdr)
    hstepBound' (by exact_mod_cast hbase)
    ((N - d * r) / (d * r)) (by simp [Nat.gcd_one_left])
  simpa [halpha, Nat.gcd_one_left] using hblock

set_option maxHeartbeats 800000 in
/-- The second Vaughan Type-I sum is bounded by its exact progression blocks,
with the truncated Möbius and low-Mangoldt supports made explicit. This is
the coefficient-aggregation interface: the remaining task is to sum this
majorant uniformly over `d ≤ U` and `r ≤ V`. -/
theorem eventually_cubicVaughanS2_minorArc_block_majorant
    (A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hcutSteps : sigmaD + sigmaV ≤ sigmaStep)
    (hbudget : 8 * (sigma0 + sigmaStep) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigmaStep + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
        ∀ U V : ℕ,
          U ≤ N → V ≤ N →
          (U : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaD →
          (V : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaV →
          1 ≤ Real.log ((N : ℝ) + 2) →
          ‖cubicArithmeticExpSum (vaughanS2 U V) alpha N‖ ≤
            ∑ d ∈ Finset.Icc 1 N,
              ∑ r ∈ Finset.Icc 1 (N / d),
                if d ≤ U then
                  if r ≤ V then
                    ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ *
                      ((1268822 *
                        (((N - d * r) / (d * r) + 2 : ℕ) : ℝ) /
                          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                        (1 + 8 * Real.pi))
                  else 0
                else 0 := by
  have hBlocks := eventually_cubicVaughanS2_minorArc_block_bound
    A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving hA hSA hcutSteps
    hbudget hsaving hcutoff
  filter_upwards [hBlocks] with N hN
  intro alpha hminor U V hUN hVN hU hV hlog
  calc
    ‖cubicArithmeticExpSum (vaughanS2 U V) alpha N‖ ≤
        ∑ d ∈ Finset.Icc 1 N,
          ∑ r ∈ Finset.Icc 1 (N / d),
            ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ *
              ‖∑ j ∈ Finset.Icc 1 ((N / d) / r),
                addChar alpha (primeCubic (d * (r * j)))‖ :=
      norm_cubic_vaughan_typeI_second_le_block_norm_sum U V N alpha
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro r hr
      by_cases hdu : d ≤ U
      · simp only [if_pos hdu]
        by_cases hrv : r ≤ V
        · simp only [if_pos hrv]
          have hdmem := Finset.mem_Icc.mp hd
          have hrmem := Finset.mem_Icc.mp hr
          have hdpos : 0 < d := hdmem.1
          have hrpos : 0 < r := hrmem.1
          have hdr : d * r ≤ N := by
            have hmul := (Nat.le_div_iff_mul_le hdpos).mp hrmem.2
            nlinarith [hmul]
          have hD : (d : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaD :=
            le_trans (by exact_mod_cast hdu) hU
          have hR : (r : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaV :=
            le_trans (by exact_mod_cast hrv) hV
          have hblock := hN alpha hminor d r hdpos hrpos hdr hD hR
          have hshift := sum_primeCubic_product_divisor_quotient_eq_progression
            N d r alpha (Nat.mul_pos hdpos hrpos) hdr
          rw [hshift]
          exact mul_le_mul_of_nonneg_left hblock (norm_nonneg _)
        · simp only [if_neg hrv]
          have hzero : vaughanLow V r = 0 :=
            vaughanLow_eq_zero_of_gt V r (lt_of_not_ge hrv)
          simp [hzero]
      · simp only [if_neg hdu]
        have hzero : muTruncated U d = 0 := by
          simp [muTruncated, not_le_of_gt (lt_of_not_ge hdu)]
        simp [hzero]

set_option maxHeartbeats 800000 in
/-- Coarsening the S₂ block majorant and counting its rectangular coefficient
support gives the expected `U*V` outer factor. The product-size condition
ensures every supported pair lies in the divisor triangle. -/
theorem eventually_cubicVaughanS2_minorArc_coarse_bound
    (A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hcutSteps : sigmaD + sigmaV ≤ sigmaStep)
    (hbudget : 8 * (sigma0 + sigmaStep) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigmaStep + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
        ∀ U V : ℕ,
          U ≤ N → V ≤ N → U * V ≤ N →
          (U : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaD →
          (V : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigmaV →
          1 ≤ Real.log ((N : ℝ) + 2) →
          ‖cubicArithmeticExpSum (vaughanS2 U V) alpha N‖ ≤
            (U : ℝ) * (V : ℝ) *
              ((1268822 * ((N : ℝ) + 2) /
                (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                (1 + 8 * Real.pi) * Real.log ((V + 1 : ℕ) : ℝ)) := by
  have hMajorant := eventually_cubicVaughanS2_minorArc_block_majorant
    A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving hA hSA hcutSteps
    hbudget hsaving hcutoff
  filter_upwards [hMajorant] with N hN
  intro alpha hminor U V hUN hVN hUV hU hV hlog
  have hfloor : 1 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) :=
    Nat.le_floor (by exact_mod_cast hlog)
  have hdenpos :
      0 < (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving := by
    exact pow_pos (by exact_mod_cast (show 0 < Nat.floor (Real.log ((N : ℝ) + 2)) from
      lt_of_lt_of_le Nat.zero_lt_one hfloor)) _
  have hbase : 0 ≤ Real.log ((V + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ V + 1 by omega))
  let K : ℝ :=
    (1268822 * ((N : ℝ) + 2) /
      (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
      (1 + 8 * Real.pi) * Real.log ((V + 1 : ℕ) : ℝ)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hKblock (d r : ℕ) (hd : d ∈ Finset.Icc 1 N)
      (hr : r ∈ Finset.Icc 1 (N / d)) (hdu : d ≤ U) (hrv : r ≤ V) :
      ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ *
          ((1268822 * (((N - d * r) / (d * r) + 2 : ℕ) : ℝ) /
            (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
            (1 + 8 * Real.pi)) ≤ K := by
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hdr : d * r ≤ N := by
      have hmul := (Nat.le_div_iff_mul_le hdpos).mp (Finset.mem_Icc.mp hr).2
      nlinarith [hmul]
    have hcoef :
        ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ ≤
          Real.log ((V + 1 : ℕ) : ℝ) := by
      apply le_trans (norm_muTruncated_mul_vaughanLow_le_log U V d r)
      apply Real.log_le_log (by exact_mod_cast (show 0 < r by omega))
      exact_mod_cast (Nat.le_succ_of_le hrv)
    have hquot : (N - d * r) / (d * r) ≤ N := by
      exact le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)
    have hquotCast :
        (((N - d * r) / (d * r) + 2 : ℕ) : ℝ) ≤ (N : ℝ) + 2 := by
      exact_mod_cast Nat.add_le_add_right hquot 2
    have hstep :
        (1268822 * (((N - d * r) / (d * r) + 2 : ℕ) : ℝ) /
          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
          (1 + 8 * Real.pi) ≤
        (1268822 * ((N : ℝ) + 2) /
          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
          (1 + 8 * Real.pi) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply div_le_div_of_nonneg_right _ (le_of_lt hdenpos)
      exact mul_le_mul_of_nonneg_left hquotCast (by norm_num)
    calc
      _ ≤ Real.log ((V + 1 : ℕ) : ℝ) *
            ((1268822 * ((N : ℝ) + 2) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
              (1 + 8 * Real.pi)) := by
          exact mul_le_mul hcoef hstep (by positivity) (by positivity)
      _ = K := by dsimp [K]; ring
  have hcount :
      (∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          if d ≤ U then if r ≤ V then K else 0 else 0) =
        (U : ℝ) * (V : ℝ) * K := by
    have houter :
        (Finset.Icc 1 N).filter (fun d ↦ d ≤ U) = Finset.Icc 1 U := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    have hinner (d : ℕ) (hd : d ∈ Finset.Icc 1 U) :
        (∑ r ∈ Finset.Icc 1 (N / d), if r ≤ V then K else 0) =
          (V : ℝ) * K := by
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdV : d * V ≤ N := by
        calc
          d * V ≤ U * V := Nat.mul_le_mul_right V (Finset.mem_Icc.mp hd).2
          _ ≤ N := hUV
      have hVlim : V ≤ N / d := (Nat.le_div_iff_mul_le hdpos).2 (by
        simpa [Nat.mul_comm] using hdV)
      rw [← Finset.sum_filter]
      have hfilter :
          (Finset.Icc 1 (N / d)).filter (fun r ↦ r ≤ V) = Finset.Icc 1 V := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilter]
      simp [Finset.sum_const, Nat.card_Icc]
    have houterSum :
        (∑ d ∈ Finset.Icc 1 N,
          if d ≤ U then (V : ℝ) * K else 0) = (U : ℝ) * (V : ℝ) * K := by
      rw [← Finset.sum_filter, houter]
      simp [Finset.sum_const, Nat.card_Icc]
      ring
    calc
      _ = ∑ d ∈ Finset.Icc 1 N,
            if d ≤ U then
              ∑ r ∈ Finset.Icc 1 (N / d), if r ≤ V then K else 0
            else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdu : d ≤ U
          · simp [hdu]
          · simp [hdu]
      _ = (U : ℝ) * (V : ℝ) * K := by
          calc
            _ = ∑ d ∈ Finset.Icc 1 N,
                  if d ≤ U then (V : ℝ) * K else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hdu : d ≤ U
              · simp [hdu, hinner d
                  (by simp [Finset.mem_Icc, hdu, (Finset.mem_Icc.mp hd).1])]
              · simp [hdu]
            _ = _ := houterSum
  have hRaw := hN alpha hminor U V hUN hVN hU hV hlog
  calc
    ‖cubicArithmeticExpSum (vaughanS2 U V) alpha N‖ ≤ _ := hRaw
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          ∑ r ∈ Finset.Icc 1 (N / d),
            if d ≤ U then if r ≤ V then K else 0 else 0 := by
          apply Finset.sum_le_sum
          intro d hd
          apply Finset.sum_le_sum
          intro r hr
          by_cases hdu : d ≤ U
          · simp only [if_pos hdu]
            by_cases hrv : r ≤ V
            · simp only [if_pos hrv]
              exact hKblock d r hd hr hdu hrv
            · simp [hrv]
          · simp [hdu]
    _ = (U : ℝ) * (V : ℝ) * K := hcount
    _ = _ := rfl

set_option maxHeartbeats 800000 in
/-- The two natural logarithmic cutoffs satisfy the rectangular support
condition and the source-size bounds, so the S₂ coarse estimate applies to
Vaughan's actual truncation parameters. -/
theorem eventually_cubicVaughanS2_minorArc_logarithmicCutoff_bound
    (A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hcutSteps : sigmaD + sigmaV ≤ sigmaStep)
    (hbudget : 8 * (sigma0 + sigmaStep) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigmaStep + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ‖cubicArithmeticExpSum
              (vaughanS2 (logarithmicDenominatorCutoff sigmaD N)
                (logarithmicDenominatorCutoff sigmaV N)) alpha N‖ ≤
            (logarithmicDenominatorCutoff sigmaD N : ℝ) *
              (logarithmicDenominatorCutoff sigmaV N : ℝ) *
                ((1268822 * ((N : ℝ) + 2) /
                  (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                  (1 + 8 * Real.pi) *
                  Real.log ((logarithmicDenominatorCutoff sigmaV N + 1 : ℕ) : ℝ)) := by
  have hCoarse := eventually_cubicVaughanS2_minorArc_coarse_bound
    A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 saving hA hSA hcutSteps
    hbudget hsaving hcutoff
  have hCutGrowth := tendsto_logarithmicDenominatorCutoff 1 (by omega)
  have hPowBound := eventually_logarithmicDenominatorCutoff_pow_le_add_two
    1 (sigmaD + sigmaV + 2)
  filter_upwards [hCoarse, hCutGrowth.eventually_ge_atTop 2,
    hPowBound, eventually_ge_atTop (2 : ℕ)] with N hN hB hPower hNlarge
  have hBfloor : 2 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) := by
    simpa [logarithmicDenominatorCutoff] using hB
  have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
  have hlogfloor :
      (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ≤
        Real.log ((N : ℝ) + 2) := Nat.floor_le hlognonneg
  have hlog : 1 ≤ Real.log ((N : ℝ) + 2) := by
    calc
      1 ≤ (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) := by
        exact_mod_cast (show 1 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) by omega)
      _ ≤ Real.log ((N : ℝ) + 2) := hlogfloor
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  have hBnat : 2 ≤ B := by simpa [B] using hBfloor
  have hBreal : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBnat
  have hBpow :
      4 * (B : ℝ) ^ (sigmaD + sigmaV) ≤ (B : ℝ) ^ (sigmaD + sigmaV + 2) := by
    have hBsquare : (4 : ℝ) ≤ (B : ℝ) ^ 2 := by nlinarith
    calc
      4 * (B : ℝ) ^ (sigmaD + sigmaV) =
          (B : ℝ) ^ (sigmaD + sigmaV) * 4 := by ring
      _ ≤ (B : ℝ) ^ (sigmaD + sigmaV) * (B : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBsquare (by positivity)
      _ = (B : ℝ) ^ (sigmaD + sigmaV + 2) := by rw [← pow_add]
  have hPowerReal :
      (B : ℝ) ^ (sigmaD + sigmaV + 2) ≤ (N : ℝ) + 2 := by
    simpa [B, logarithmicDenominatorCutoff] using hPower
  have hcutD :
      (logarithmicDenominatorCutoff sigmaD N : ℝ) ≤ (B : ℝ) ^ sigmaD := by
    simp [B, logarithmicDenominatorCutoff]
  have hcutV :
      (logarithmicDenominatorCutoff sigmaV N : ℝ) ≤ (B : ℝ) ^ sigmaV := by
    simp [B, logarithmicDenominatorCutoff]
  have hrect :
      4 * (logarithmicDenominatorCutoff sigmaD N : ℝ) *
          (logarithmicDenominatorCutoff sigmaV N : ℝ) ≤ (N : ℝ) + 2 := by
    calc
      _ = 4 * ((logarithmicDenominatorCutoff sigmaD N : ℝ) *
            (logarithmicDenominatorCutoff sigmaV N : ℝ)) := by ring
      _ ≤ 4 * ((B : ℝ) ^ sigmaD * (B : ℝ) ^ sigmaV) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul hcutD hcutV (by positivity) (by positivity)
      _ = 4 * (B : ℝ) ^ (sigmaD + sigmaV) := by rw [← pow_add]
      _ ≤ (B : ℝ) ^ (sigmaD + sigmaV + 2) := hBpow
      _ ≤ (N : ℝ) + 2 := hPowerReal
  have hcutDpos :
      1 ≤ logarithmicDenominatorCutoff sigmaD N := by
    simpa [logarithmicDenominatorCutoff] using
      Nat.one_le_pow sigmaD B (by omega)
  have hcutVpos :
      1 ≤ logarithmicDenominatorCutoff sigmaV N := by
    simpa [logarithmicDenominatorCutoff] using
      Nat.one_le_pow sigmaV B (by omega)
  have hcutDreal :
      1 ≤ (logarithmicDenominatorCutoff sigmaD N : ℝ) := by exact_mod_cast hcutDpos
  have hcutVreal :
      1 ≤ (logarithmicDenominatorCutoff sigmaV N : ℝ) := by exact_mod_cast hcutVpos
  have hrectpos :
      1 ≤ (logarithmicDenominatorCutoff sigmaD N : ℝ) *
        (logarithmicDenominatorCutoff sigmaV N : ℝ) := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ (logarithmicDenominatorCutoff sigmaD N : ℝ) *
            (logarithmicDenominatorCutoff sigmaV N : ℝ) :=
        mul_le_mul hcutDreal hcutVreal (by norm_num) (by positivity)
  have hUVreal :
      (logarithmicDenominatorCutoff sigmaD N : ℝ) *
        (logarithmicDenominatorCutoff sigmaV N : ℝ) ≤ (N : ℝ) := by
    nlinarith [hrect, hrectpos]
  have hUV :
      logarithmicDenominatorCutoff sigmaD N *
        logarithmicDenominatorCutoff sigmaV N ≤ N := by
    exact_mod_cast hUVreal
  have hUN : logarithmicDenominatorCutoff sigmaD N ≤ N := by
    calc
      logarithmicDenominatorCutoff sigmaD N ≤
          logarithmicDenominatorCutoff sigmaD N *
            logarithmicDenominatorCutoff sigmaV N :=
        Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ N := hUV
  have hVN : logarithmicDenominatorCutoff sigmaV N ≤ N := by
    calc
      logarithmicDenominatorCutoff sigmaV N ≤
          logarithmicDenominatorCutoff sigmaD N *
            logarithmicDenominatorCutoff sigmaV N :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ N := hUV
  have hD :
      (logarithmicDenominatorCutoff sigmaD N : ℝ) ≤
        Real.log ((N : ℝ) + 2) ^ sigmaD :=
    logarithmicDenominatorCutoff_le_log_pow sigmaD N
  have hV :
      (logarithmicDenominatorCutoff sigmaV N : ℝ) ≤
        Real.log ((N : ℝ) + 2) ^ sigmaV :=
    logarithmicDenominatorCutoff_le_log_pow sigmaV N
  intro alpha hminor
  exact hN alpha hminor _ _ hUN hVN hUV hD hV hlog

set_option maxHeartbeats 800000 in
/-- Spending one extra floor-log power for the two cutoffs and one for the
low-Mangoldt logarithm turns the S₂ cutoff bound into any prescribed
floor-log saving. -/
theorem eventually_cubicVaughanS2_minorArc_floorLog_saving_bound
    (A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 decay : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hcutSteps : sigmaD + sigmaV ≤ sigmaStep)
    (hbudget : 8 * (sigma0 + sigmaStep) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff :
      3 * (sigmaStep + sigma4 + 2) +
        20 * (decay + sigmaD + sigmaV + 1) ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ‖cubicArithmeticExpSum
              (vaughanS2 (logarithmicDenominatorCutoff sigmaD N)
                (logarithmicDenominatorCutoff sigmaV N)) alpha N‖ ≤
            (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ decay := by
  have hBase := eventually_cubicVaughanS2_minorArc_logarithmicCutoff_bound
    A sigma sigma0 sigmaD sigmaV sigmaStep sigma4
    (decay + sigmaD + sigmaV + 1) hA hSA hcutSteps hbudget
    (by omega) hcutoff
  have hFloorTendsto := tendsto_logarithmicDenominatorCutoff 1 (by omega)
  have hVpow := eventually_logarithmicDenominatorCutoff_pow_le_add_two
    1 (sigmaV + 2)
  filter_upwards [hBase, hFloorTendsto.eventually_ge_atTop 2,
    eventually_ge_atTop (2 : ℕ), hVpow] with N hN hB hNlarge hVpower
  intro alpha hminor
  have hBnat : 2 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) := by
    simpa [logarithmicDenominatorCutoff] using hB
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  have hBnat' : 2 ≤ B := by simpa [B] using hBnat
  have hBreal : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBnat'
  have hBpos : 0 < (B : ℝ) := by linarith
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNlarge
  have hNplus : (N : ℝ) + 2 ≤ 2 * (N : ℝ) := by linarith
  have hlogFloor :
      Real.log ((N : ℝ) + 2) < (B : ℝ) + 1 := by
    simpa [B] using (Nat.lt_floor_add_one (Real.log ((N : ℝ) + 2)))
  have hlogUpper : Real.log ((N : ℝ) + 1) ≤ 2 * (B : ℝ) := by
    have hlogMon : Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 2) := by
      apply Real.log_le_log (by positivity)
      linarith
    linarith
  have hBpow : 4 * (B : ℝ) ^ sigmaV ≤ (B : ℝ) ^ (sigmaV + 2) := by
    have hBsquare : (4 : ℝ) ≤ (B : ℝ) ^ 2 := by nlinarith
    calc
      4 * (B : ℝ) ^ sigmaV = (B : ℝ) ^ sigmaV * 4 := by ring
      _ ≤ (B : ℝ) ^ sigmaV * (B : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBsquare (by positivity)
      _ = (B : ℝ) ^ (sigmaV + 2) := by rw [← pow_add]
  have hVpowerReal : (B : ℝ) ^ (sigmaV + 2) ≤ (N : ℝ) + 2 := by
    simpa [B, logarithmicDenominatorCutoff] using hVpower
  have hVcutoffCast :
      (logarithmicDenominatorCutoff sigmaV N : ℝ) = (B : ℝ) ^ sigmaV := by
    simp [B, logarithmicDenominatorCutoff]
  have hVfour :
      4 * (logarithmicDenominatorCutoff sigmaV N : ℝ) ≤ (N : ℝ) + 2 := by
    rw [hVcutoffCast]
    exact hBpow.trans hVpowerReal
  have honeV : 1 ≤ (logarithmicDenominatorCutoff sigmaV N : ℝ) := by
    exact_mod_cast (Nat.one_le_pow sigmaV B (by omega))
  have hVtwice : 2 * logarithmicDenominatorCutoff sigmaV N ≤ N := by
    exact_mod_cast (show
      2 * (logarithmicDenominatorCutoff sigmaV N : ℝ) ≤ (N : ℝ) by
        nlinarith [hVfour, honeV])
  have hVshort : logarithmicDenominatorCutoff sigmaV N ≤ N := by omega
  have hlogV :
      Real.log ((logarithmicDenominatorCutoff sigmaV N + 1 : ℕ) : ℝ) ≤
        2 * (B : ℝ) := by
    have hVlog :
        Real.log ((logarithmicDenominatorCutoff sigmaV N + 1 : ℕ) : ℝ) ≤
          Real.log ((N : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.succ_le_succ hVshort
    exact hVlog.trans hlogUpper
  have hDenomPos : 0 < (B : ℝ) ^ (decay + sigmaD + sigmaV + 1) :=
    pow_pos hBpos _
  have hDenomEq :
      (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^
          (decay + sigmaD + sigmaV + 1) =
        (B : ℝ) ^ (decay + sigmaD + sigmaV + 1) := by rfl
  have hCutDcast :
      (logarithmicDenominatorCutoff sigmaD N : ℝ) = (B : ℝ) ^ sigmaD := by
    simp [B, logarithmicDenominatorCutoff]
  have hCutVcast :
      (logarithmicDenominatorCutoff sigmaV N : ℝ) = (B : ℝ) ^ sigmaV :=
    hVcutoffCast
  have hCutProduct :
      (logarithmicDenominatorCutoff sigmaD N : ℝ) *
        (logarithmicDenominatorCutoff sigmaV N : ℝ) =
          (B : ℝ) ^ (sigmaD + sigmaV) := by
    rw [hCutDcast, hCutVcast, ← pow_add]
  have hterm :
      (1268822 * ((N : ℝ) + 2) /
          (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) *
        (1 + 8 * Real.pi) *
        Real.log ((logarithmicDenominatorCutoff sigmaV N + 1 : ℕ) : ℝ) ≤
      (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) * (B : ℝ) /
        (B : ℝ) ^ (decay + sigmaD + sigmaV + 1) := by
    have hfactor :
        1268822 * ((N : ℝ) + 2) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1) ≤
          1268822 * (2 * (N : ℝ)) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hDenomPos)
      exact mul_le_mul_of_nonneg_left hNplus (by norm_num)
    calc
      _ = ((1268822 * ((N : ℝ) + 2) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) *
            (1 + 8 * Real.pi)) *
            Real.log ((logarithmicDenominatorCutoff sigmaV N + 1 : ℕ) : ℝ) := by ring
      _ ≤ ((1268822 * ((N : ℝ) + 2) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) *
            (1 + 8 * Real.pi)) * (2 * (B : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogV (by positivity)
      _ ≤ ((1268822 * (2 * (N : ℝ)) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) *
            (1 + 8 * Real.pi)) * (2 * (B : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring
  have hcancel :
      (B : ℝ) ^ (sigmaD + sigmaV) *
          ((4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) * (B : ℝ) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) =
        (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
          (B : ℝ) ^ decay := by
    calc
      _ = (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) *
            (((B : ℝ) ^ (sigmaD + sigmaV) * (B : ℝ)) /
              (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) := by ring
      _ = (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) *
            ((B : ℝ) ^ (sigmaD + sigmaV + 1) /
              (B : ℝ) ^ (decay + (sigmaD + sigmaV + 1))) := by
          have hnum : (B : ℝ) ^ (sigmaD + sigmaV) * (B : ℝ) =
              (B : ℝ) ^ (sigmaD + sigmaV + 1) := by rw [← pow_succ]
          rw [hnum, show decay + sigmaD + sigmaV + 1 =
            decay + (sigmaD + sigmaV + 1) by omega]
      _ = _ := by
          rw [pow_add]
          field_simp [ne_of_gt hBpos]
          ring
  calc
    ‖cubicArithmeticExpSum
        (vaughanS2 (logarithmicDenominatorCutoff sigmaD N)
          (logarithmicDenominatorCutoff sigmaV N)) alpha N‖ ≤
        (logarithmicDenominatorCutoff sigmaD N : ℝ) *
          (logarithmicDenominatorCutoff sigmaV N : ℝ) *
            ((1268822 * ((N : ℝ) + 2) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^
                (decay + sigmaD + sigmaV + 1)) *
              (1 + 8 * Real.pi) *
              Real.log ((logarithmicDenominatorCutoff sigmaV N + 1 : ℕ) : ℝ)) :=
      hN alpha hminor
    _ ≤ (B : ℝ) ^ (sigmaD + sigmaV) *
          ((4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) * (B : ℝ) /
            (B : ℝ) ^ (decay + sigmaD + sigmaV + 1)) := by
      rw [hCutProduct, hDenomEq]
      exact mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ decay := by
      rw [← hcancel]

set_option maxHeartbeats 800000 in
/-- Uniformly coarsening the divisor-dependent progression bounds gives the
first Vaughan Type-I estimate with the expected outer factor `U`. -/
theorem eventually_cubicVaughanS1_minorArc_coarse_bound
    (A sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
        ∀ U : ℕ,
          (U : ℝ) ≤ Real.log ((N : ℝ) + 2) ^ sigma3 →
          2 * U ≤ N →
          1 ≤ Real.log ((N : ℝ) + 2) →
          ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
            (U : ℝ) *
              (2 * (1268822 * ((N : ℝ) + 2) /
                (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1)) := by
  have hMajorant := eventually_cubicVaughanS1_minorArc_block_majorant
    A sigma sigma0 sigma3 sigma4 saving hA hSA hbudget hsaving hcutoff
  filter_upwards [hMajorant] with N hN
  intro alpha hminor U hU hUshort hlog
  have hUleN : U ≤ N := by omega
  have hfloor : 1 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) :=
    Nat.le_floor (by exact_mod_cast hlog)
  have hfloorpos :
      0 < (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hdenpos :
      0 < (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving :=
    pow_pos hfloorpos _
  let K : ℝ := 2 * (1268822 * ((N : ℝ) + 2) /
    (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
    (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1)
  have hKnonneg : 0 ≤ K := by
    have hlogN : 0 ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 1 by omega))
    dsimp [K]
    positivity
  have hKblock (d : ℕ) (hd : d ∈ Finset.Icc 1 N) (hdu : d ≤ U) :
      2 * (1268822 * (((N - d) / d + 2 : ℕ) : ℝ) /
          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
        (1 + 8 * Real.pi) * Real.log ((((N - d) / d : ℕ) : ℝ) + 1) ≤ K := by
    have hMle : (N - d) / d ≤ N :=
      (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
    have hMplus :
        (((N - d) / d + 2 : ℕ) : ℝ) ≤ (N : ℝ) + 2 := by
      exact_mod_cast (Nat.add_le_add_right hMle 2)
    have hnumerator :
        1268822 * (((N - d) / d + 2 : ℕ) : ℝ) ≤
          1268822 * ((N : ℝ) + 2) := by
      exact mul_le_mul_of_nonneg_left hMplus (by norm_num)
    have hquotient := (div_le_div_iff_of_pos_right hdenpos).2 hnumerator
    have hlogarg :
        (((N - d) / d : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      exact_mod_cast (Nat.add_le_add_right hMle 1)
    have hlogle := Real.log_le_log (by positivity) hlogarg
    have hlognonneg :
      0 ≤ Real.log ((((N - d) / d : ℕ) : ℝ) + 1) := by
      apply Real.log_nonneg
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le ((N - d) / d)))
    dsimp [K]
    calc
      2 * (1268822 * (((N - d) / d + 2 : ℕ) : ℝ) /
          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
        (1 + 8 * Real.pi) * Real.log ((((N - d) / d : ℕ) : ℝ) + 1) =
          (2 * (1 + 8 * Real.pi)) *
            (1268822 * (((N - d) / d + 2 : ℕ) : ℝ) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
            Real.log ((((N - d) / d : ℕ) : ℝ) + 1) := by ring
      _ ≤ (2 * (1 + 8 * Real.pi)) *
            (1268822 * ((N : ℝ) + 2) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
            Real.log ((((N - d) / d : ℕ) : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hquotient (by positivity)) hlognonneg
      _ ≤ (2 * (1 + 8 * Real.pi)) *
            (1268822 * ((N : ℝ) + 2) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
            Real.log ((N : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = 2 * (1268822 * ((N : ℝ) + 2) /
            (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
          (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1) := by ring
  have hcount :
      (∑ d ∈ Finset.Icc 1 N, if d ≤ U then K else 0) = (U : ℝ) * K := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.Icc 1 N).filter (fun d ↦ d ≤ U) = Finset.Icc 1 U := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilter]
    simp [Finset.sum_const, Nat.card_Icc]
  calc
    ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
        ∑ d ∈ Finset.Icc 1 N,
          if d ≤ U then
            2 * (1268822 * (((N - d) / d + 2 : ℕ) : ℝ) /
                (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
              (1 + 8 * Real.pi) *
              Real.log ((((N - d) / d : ℕ) : ℝ) + 1)
          else 0 := hN alpha hminor U hU hUshort hlog
    _ ≤ ∑ d ∈ Finset.Icc 1 N, if d ≤ U then K else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hdu : d ≤ U
      · simp only [if_pos hdu]
        exact hKblock d hd hdu
      · simp [hdu]
    _ = (U : ℝ) * K := hcount
    _ = _ := rfl

/-- Specializing the first Vaughan Type-I estimate to the natural
floor-logarithmic cutoff discharges the source-range and positive-length
conditions without auxiliary assumptions on `U`. -/
theorem eventually_cubicVaughanS1_minorArc_logarithmicCutoff_bound
    (A sigma sigma0 sigma3 sigma4 saving : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hsaving : 1 ≤ saving)
    (hcutoff : 3 * (sigma3 + sigma4 + 2) + 20 * saving ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ‖cubicArithmeticExpSum
              (vaughanS1 (logarithmicDenominatorCutoff sigma3 N)) alpha N‖ ≤
            (logarithmicDenominatorCutoff sigma3 N : ℝ) *
              (2 * (1268822 * ((N : ℝ) + 2) /
                (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ saving) *
                (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1)) := by
  have hCoarse := eventually_cubicVaughanS1_minorArc_coarse_bound
    A sigma sigma0 sigma3 sigma4 saving hA hSA hbudget hsaving hcutoff
  have hCutGrowth := tendsto_logarithmicDenominatorCutoff 1 (by omega)
  have hPowBound := eventually_logarithmicDenominatorCutoff_pow_le_add_two
    1 (sigma3 + 2)
  filter_upwards [hCoarse,
    hCutGrowth.eventually_ge_atTop 2,
    hPowBound] with N hN hB hPower
  have hBfloor : 2 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) := by
    simpa [logarithmicDenominatorCutoff] using hB
  have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
  have hlogfloor :
      (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ≤
        Real.log ((N : ℝ) + 2) := Nat.floor_le hlognonneg
  have hlog : 1 ≤ Real.log ((N : ℝ) + 2) := by
    calc
      1 ≤ (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) := by
        exact_mod_cast (show 1 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) by omega)
      _ ≤ Real.log ((N : ℝ) + 2) := hlogfloor
  have hU :
      (logarithmicDenominatorCutoff sigma3 N : ℝ) ≤
        Real.log ((N : ℝ) + 2) ^ sigma3 :=
    logarithmicDenominatorCutoff_le_log_pow sigma3 N
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  have hBpow :
      4 * (B : ℝ) ^ sigma3 ≤ (B : ℝ) ^ (sigma3 + 2) := by
    rw [pow_add]
    have hBsquare : (4 : ℝ) ≤ (B : ℝ) ^ 2 := by
      have hBnat : 2 ≤ B := by simpa [B] using hBfloor
      have hBreal : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBnat
      nlinarith
    calc
      4 * (B : ℝ) ^ sigma3 = (B : ℝ) ^ sigma3 * 4 := by ring
      _ ≤ (B : ℝ) ^ sigma3 * (B : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hBsquare
          (pow_nonneg (show 0 ≤ (B : ℝ) by exact_mod_cast (Nat.zero_le B)) sigma3)
  have hPowerReal :
      (B : ℝ) ^ (sigma3 + 2) ≤ (N : ℝ) + 2 := by
    simpa [B, logarithmicDenominatorCutoff] using hPower
  have hfour :
      4 * (logarithmicDenominatorCutoff sigma3 N : ℝ) ≤ (N : ℝ) + 2 := by
    have hcutoffCast :
        (logarithmicDenominatorCutoff sigma3 N : ℝ) = (B : ℝ) ^ sigma3 := by
      simp [B, logarithmicDenominatorCutoff]
    rw [hcutoffCast]
    exact hBpow.trans hPowerReal
  have honeU : 1 ≤ (logarithmicDenominatorCutoff sigma3 N : ℝ) := by
    have hBpowOne : 1 ≤ B ^ sigma3 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast hBpowOne
  have hUshort :
      2 * logarithmicDenominatorCutoff sigma3 N ≤ N := by
    exact_mod_cast (show
      2 * (logarithmicDenominatorCutoff sigma3 N : ℝ) ≤ (N : ℝ) by
        nlinarith [hfour, honeU])
  intro alpha hminor
  exact hN alpha hminor _ hU hUshort hlog

set_option maxHeartbeats 800000 in
/-- After choosing one extra Weyl-saving power for each outer logarithmic
factor, the first Vaughan Type-I term has a clean floor-logarithmic power
saving. -/
theorem eventually_cubicVaughanS1_minorArc_floorLog_saving_bound
    (A sigma sigma0 sigma3 sigma4 decay : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff :
      3 * (sigma3 + sigma4 + 2) + 20 * (decay + sigma3 + 1) ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ‖cubicArithmeticExpSum
              (vaughanS1 (logarithmicDenominatorCutoff sigma3 N)) alpha N‖ ≤
            (8 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
              (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ decay := by
  have hBase := eventually_cubicVaughanS1_minorArc_logarithmicCutoff_bound
    A sigma sigma0 sigma3 sigma4 (decay + sigma3 + 1) hA hSA hbudget
    (by omega) hcutoff
  have hFloorTendsto := tendsto_logarithmicDenominatorCutoff 1 (by omega)
  filter_upwards [hBase, hFloorTendsto.eventually_ge_atTop 2,
    eventually_ge_atTop (2 : ℕ)] with N hN hB hNlarge
  intro alpha hminor
  have hBnat : 2 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) := by
    simpa [logarithmicDenominatorCutoff] using hB
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  have hBnat' : 2 ≤ B := by simpa [B] using hBnat
  have hBreal : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBnat'
  have hBpos : 0 < (B : ℝ) := by linarith
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNlarge
  have hNplus : (N : ℝ) + 2 ≤ 2 * (N : ℝ) := by linarith
  have hlogMon :
      Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 2) := by
    apply Real.log_le_log (by positivity)
    linarith
  have hlogFloor :
      Real.log ((N : ℝ) + 2) < (B : ℝ) + 1 := by
    simpa [B] using (Nat.lt_floor_add_one (Real.log ((N : ℝ) + 2)))
  have hlogUpper : Real.log ((N : ℝ) + 1) ≤ 2 * (B : ℝ) := by
    linarith
  have hDpos :
      0 < (B : ℝ) ^ (decay + sigma3 + 1) := pow_pos hBpos _
  have hDenomEq :
      (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ (decay + sigma3 + 1) =
        (B : ℝ) ^ (decay + sigma3 + 1) := by rfl
  have hblockBound := hN alpha hminor
  have hterm :
      2 * (1268822 * ((N : ℝ) + 2) /
          (B : ℝ) ^ (decay + sigma3 + 1)) *
        (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1) ≤
      8 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ) * (B : ℝ) /
        (B : ℝ) ^ (decay + sigma3 + 1) := by
    calc
      2 * (1268822 * ((N : ℝ) + 2) /
          (B : ℝ) ^ (decay + sigma3 + 1)) *
        (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1) =
          (2 * (1268822 * ((N : ℝ) + 2) /
            (B : ℝ) ^ (decay + sigma3 + 1)) *
            (1 + 8 * Real.pi)) * Real.log ((N : ℝ) + 1) := by ring
      _ ≤ (2 * (1268822 * ((N : ℝ) + 2) /
            (B : ℝ) ^ (decay + sigma3 + 1)) *
            (1 + 8 * Real.pi)) * (2 * (B : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogUpper (by positivity)
      _ = 4 * (1268822 * ((N : ℝ) + 2) /
            (B : ℝ) ^ (decay + sigma3 + 1)) *
            (1 + 8 * Real.pi) * (B : ℝ) := by ring
      _ ≤ 4 * (1268822 * (2 * (N : ℝ)) /
            (B : ℝ) ^ (decay + sigma3 + 1)) *
            (1 + 8 * Real.pi) * (B : ℝ) := by
          gcongr
      _ = 8 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ) * (B : ℝ) /
            (B : ℝ) ^ (decay + sigma3 + 1) := by ring
  have hcutoffCast :
      (logarithmicDenominatorCutoff sigma3 N : ℝ) = (B : ℝ) ^ sigma3 := by
    simp [B, logarithmicDenominatorCutoff]
  have hcancel :
      (B : ℝ) ^ sigma3 *
          (8 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ) * (B : ℝ) /
            (B : ℝ) ^ (decay + sigma3 + 1)) =
        (8 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
          (B : ℝ) ^ decay := by
    rw [show decay + sigma3 + 1 = decay + (sigma3 + 1) by omega,
      pow_add, pow_succ]
    field_simp [ne_of_gt hBpos]
  calc
    ‖cubicArithmeticExpSum
        (vaughanS1 (logarithmicDenominatorCutoff sigma3 N)) alpha N‖ ≤
        (logarithmicDenominatorCutoff sigma3 N : ℝ) *
          (2 * (1268822 * ((N : ℝ) + 2) /
            (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^
              (decay + sigma3 + 1)) *
            (1 + 8 * Real.pi) * Real.log ((N : ℝ) + 1)) :=
      hblockBound
    _ ≤ (B : ℝ) ^ sigma3 *
          (8 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ) * (B : ℝ) /
            (B : ℝ) ^ (decay + sigma3 + 1)) := by
      rw [hcutoffCast, hDenomEq]
      exact mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (8 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
          (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ^ decay := by
      rw [← hcancel]

set_option maxHeartbeats 800000 in
/-- The floor-logarithmic Type-I saving implies the corresponding saving in
the real logarithm used by the circle-method error envelope. -/
theorem eventually_cubicVaughanS1_minorArc_log_power_saving_bound
    (A sigma sigma0 sigma3 sigma4 decay : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hbudget : 8 * (sigma0 + sigma3) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff :
      3 * (sigma3 + sigma4 + 2) + 20 * (decay + sigma3 + 1) ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ‖cubicArithmeticExpSum
              (vaughanS1 (logarithmicDenominatorCutoff sigma3 N)) alpha N‖ ≤
            (8 * 1268822 * (1 + 8 * Real.pi)) * (2 : ℝ) ^ decay *
              (N : ℝ) / Real.log ((N : ℝ) + 2) ^ decay := by
  have hFloorSaving := eventually_cubicVaughanS1_minorArc_floorLog_saving_bound
    A sigma sigma0 sigma3 sigma4 decay hA hSA hbudget hcutoff
  have hFloorTendsto := tendsto_logarithmicDenominatorCutoff 1 (by omega)
  filter_upwards [hFloorSaving, hFloorTendsto.eventually_ge_atTop 2] with N hN hB
  intro alpha hminor
  have hBnat : 2 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) := by
    simpa [logarithmicDenominatorCutoff] using hB
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  have hBnat' : 2 ≤ B := by simpa [B] using hBnat
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hlogLower : 0 < Real.log ((N : ℝ) + 2) := by
    have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
    have hlogFloor :
        (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ≤
          Real.log ((N : ℝ) + 2) := Nat.floor_le hlognonneg
    have htwo : (2 : ℝ) ≤
        (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) := by
      exact_mod_cast hBnat
    linarith
  have hlogUpper : Real.log ((N : ℝ) + 2) ≤ 2 * (B : ℝ) := by
    have hfloorLt :
        Real.log ((N : ℝ) + 2) < (B : ℝ) + 1 := by
      simpa [B] using (Nat.lt_floor_add_one (Real.log ((N : ℝ) + 2)))
    have hBone : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
    linarith
  have hpow :
      Real.log ((N : ℝ) + 2) ^ decay ≤
        (2 : ℝ) ^ decay * (B : ℝ) ^ decay := by
    calc
      Real.log ((N : ℝ) + 2) ^ decay ≤ (2 * (B : ℝ)) ^ decay :=
        pow_le_pow_left₀ (by positivity) hlogUpper decay
      _ = (2 : ℝ) ^ decay * (B : ℝ) ^ decay := by rw [mul_pow]
  have htarget := hN alpha hminor
  calc
    ‖cubicArithmeticExpSum
        (vaughanS1 (logarithmicDenominatorCutoff sigma3 N)) alpha N‖ ≤
        (8 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
          (B : ℝ) ^ decay := htarget
    _ ≤ (8 * 1268822 * (1 + 8 * Real.pi)) * (2 : ℝ) ^ decay *
          (N : ℝ) / Real.log ((N : ℝ) + 2) ^ decay := by
      apply (div_le_div_iff₀ (pow_pos hBpos decay)
        (pow_pos hlogLower decay)).2
      calc
        (8 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ)) *
            Real.log ((N : ℝ) + 2) ^ decay ≤
          (8 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ)) *
            ((2 : ℝ) ^ decay * (B : ℝ) ^ decay) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((8 * 1268822 * (1 + 8 * Real.pi)) * (2 : ℝ) ^ decay *
            (N : ℝ)) * (B : ℝ) ^ decay := by ring

set_option maxHeartbeats 800000 in
/-- The S₂ floor-logarithmic saving gives the corresponding saving in the
real logarithm used by the circle-method error envelope. -/
theorem eventually_cubicVaughanS2_minorArc_log_power_saving_bound
    (A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 decay : ℕ)
    (hA : 0 < A) (hSA : sigma + 2 < A)
    (hcutSteps : sigmaD + sigmaV ≤ sigmaStep)
    (hbudget : 8 * (sigma0 + sigmaStep) + 6 * sigma4 + 8 ≤ sigma)
    (hcutoff :
      3 * (sigmaStep + sigma4 + 2) +
        20 * (decay + sigmaD + sigmaV + 1) ≤ sigma0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ alpha : ℝ,
        alpha ∈ minorArcs N (logarithmicDenominatorCutoff A N) →
          ‖cubicArithmeticExpSum
              (vaughanS2 (logarithmicDenominatorCutoff sigmaD N)
                (logarithmicDenominatorCutoff sigmaV N)) alpha N‖ ≤
            (4 * 1268822 * (1 + 8 * Real.pi)) * (2 : ℝ) ^ decay *
              (N : ℝ) / Real.log ((N : ℝ) + 2) ^ decay := by
  have hFloorSaving := eventually_cubicVaughanS2_minorArc_floorLog_saving_bound
    A sigma sigma0 sigmaD sigmaV sigmaStep sigma4 decay hA hSA hcutSteps
    hbudget hcutoff
  have hFloorTendsto := tendsto_logarithmicDenominatorCutoff 1 (by omega)
  filter_upwards [hFloorSaving, hFloorTendsto.eventually_ge_atTop 2] with N hN hB
  intro alpha hminor
  have hBnat : 2 ≤ Nat.floor (Real.log ((N : ℝ) + 2)) := by
    simpa [logarithmicDenominatorCutoff] using hB
  let B : ℕ := Nat.floor (Real.log ((N : ℝ) + 2))
  have hBnat' : 2 ≤ B := by simpa [B] using hBnat
  have hBpos : 0 < (B : ℝ) := by exact_mod_cast (by omega : 0 < B)
  have hlogLower : 0 < Real.log ((N : ℝ) + 2) := by
    have hlognonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
    have hlogFloor :
        (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) ≤
          Real.log ((N : ℝ) + 2) := Nat.floor_le hlognonneg
    have htwo : (2 : ℝ) ≤
        (Nat.floor (Real.log ((N : ℝ) + 2)) : ℝ) := by
      exact_mod_cast hBnat
    linarith
  have hlogUpper : Real.log ((N : ℝ) + 2) ≤ 2 * (B : ℝ) := by
    have hfloorLt :
        Real.log ((N : ℝ) + 2) < (B : ℝ) + 1 := by
      simpa [B] using (Nat.lt_floor_add_one (Real.log ((N : ℝ) + 2)))
    have hBone : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (by omega : 1 ≤ B)
    linarith
  have hpow :
      Real.log ((N : ℝ) + 2) ^ decay ≤
        (2 : ℝ) ^ decay * (B : ℝ) ^ decay := by
    calc
      Real.log ((N : ℝ) + 2) ^ decay ≤ (2 * (B : ℝ)) ^ decay :=
        pow_le_pow_left₀ (by positivity) hlogUpper decay
      _ = (2 : ℝ) ^ decay * (B : ℝ) ^ decay := by rw [mul_pow]
  have htarget := hN alpha hminor
  calc
    ‖cubicArithmeticExpSum
        (vaughanS2 (logarithmicDenominatorCutoff sigmaD N)
          (logarithmicDenominatorCutoff sigmaV N)) alpha N‖ ≤
        (4 * 1268822 * (1 + 8 * Real.pi)) * (N : ℝ) /
          (B : ℝ) ^ decay := htarget
    _ ≤ (4 * 1268822 * (1 + 8 * Real.pi)) * (2 : ℝ) ^ decay *
          (N : ℝ) / Real.log ((N : ℝ) + 2) ^ decay := by
      apply (div_le_div_iff₀ (pow_pos hBpos decay)
        (pow_pos hlogLower decay)).2
      calc
        (4 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ)) *
            Real.log ((N : ℝ) + 2) ^ decay ≤
          (4 * 1268822 * (1 + 8 * Real.pi) * (N : ℝ)) *
            ((2 : ℝ) ^ decay * (B : ℝ) ^ decay) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = ((4 * 1268822 * (1 + 8 * Real.pi)) * (2 : ℝ) ^ decay *
            (N : ℝ)) * (B : ℝ) ^ decay := by ring

end CookMagyarVaughan
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS1_minorArc_block_majorant
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS1_minorArc_coarse_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS1_minorArc_logarithmicCutoff_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS1_minorArc_floorLog_saving_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS1_minorArc_log_power_saving_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS2_minorArc_block_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS2_minorArc_block_majorant
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS2_minorArc_coarse_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS2_minorArc_logarithmicCutoff_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS2_minorArc_floorLog_saving_bound
#print axioms SystolicGrowth.CookMagyarVaughan.eventually_cubicVaughanS2_minorArc_log_power_saving_bound
