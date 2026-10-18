module

public import Geometry.ComplexSobolevClassicalRepresentative

@[expose] public section

/-!
# Classical first derivatives from `H³(ℂ)`

The strict two-dimensional embedding `H³ ⊂ C¹` is proved using an actual
first Fourier moment and the Fourier integral derivative theorem. This is
used before the second weak chain rule to make the coefficient `Ψ'(u)`
classically `C¹` and the first derivatives of `u` bounded.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SystolicGrowth

noncomputable section

private theorem complex_hthree_moment_weight_memLp_two
    (k : ℕ) (hk : k ≤ 1) :
    MemLp (fun x : ℂ => ‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ)) 2
      (volume : Measure ℂ) := by
  have ha : MemLp (fun x : ℂ => (1 + ‖x‖ ^ 2)⁻¹) 2
      (volume : Measure ℂ) := by
    have he : (-2 / 2 : ℝ) = -1 := by norm_num [Rat.cast_divInt]
    simpa only [he, Real.rpow_neg_one] using complex_inverse_bessel_weight_memLp_two
  refine ha.of_le_mul (c := 1) (by fun_prop) ?_
  apply Filter.Eventually.of_forall
  intro x
  have hA : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hAle : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hcoeff : 0 ≤ ‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) := by positivity
  have hbound : ‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) ≤
      (1 + ‖x‖ ^ 2)⁻¹ := by
    interval_cases k
    · simpa only [pow_zero, one_mul, Real.rpow_neg_one] using
        (Real.rpow_le_rpow_of_exponent_le hAle (show (-3 / 2 : ℝ) ≤ -1 by norm_num))
    · have hsqrt : ‖x‖ ≤ (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        exact (Real.le_sqrt (norm_nonneg x) hA.le).2 (by nlinarith)
      calc
        ‖x‖ ^ 1 * (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) ≤
            (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) *
              (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ) := by
                simpa only [pow_one] using
                  mul_le_mul_of_nonneg_right hsqrt (Real.rpow_nonneg hA.le _)
        _ = (1 + ‖x‖ ^ 2)⁻¹ := by
          rw [← Real.rpow_add hA]
          norm_num [Rat.cast_divInt, Real.rpow_neg_one]
  change ‖‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-3 / 2 : ℝ)‖ ≤
    1 * ‖(1 + ‖x‖ ^ 2)⁻¹‖
  rw [Real.norm_eq_abs, abs_of_nonneg hcoeff, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), one_mul]
  exact hbound

/-- An actual `H³` distribution has integrable zeroth and first Fourier
moments. -/
theorem complex_memSobolev_three_fourier_moments
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 3 2 w) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ),
      𝓕 w = (v : 𝓢'(ℂ, ℂ)) ∧
      ∀ k : ℕ, k ≤ 1 →
        Integrable (fun ξ : ℂ => ‖ξ‖ ^ k * ‖v ξ‖) volume := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hw
  have ha : MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ)) 2 volume := by
    simpa using complex_hthree_moment_weight_memLp_two 0 (by norm_num)
  have hTempC : (fun ξ : ℂ =>
      (((1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  let a : Lp ℂ 2 (volume : Measure ℂ) :=
    ha.ofReal.toLp (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ) : ℝ) : ℂ))
  let v : Lp ℂ 1 (volume : Measure ℂ) := a • u
  have hv : 𝓕 w = (v : 𝓢'(ℂ, ℂ)) := by
    dsimp [v, a]
    rw [MeasureTheory.Lp.toTemperedDistribution_smul_eq]
    · rw [← hu, smulLeftCLM_smulLeftCLM_apply (by fun_prop) hTempC]
      convert! (smulLeftCLM_const 1 (𝓕 w)).symm using 1
      · simp
      · congr
        ext ξ
        rw [Pi.mul_apply]
        norm_cast
        have hbase : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
        rw [← Real.rpow_add hbase]
        norm_num [Rat.cast_divInt]
    · exact hTempC
  refine ⟨v, hv, ?_⟩
  intro k hk
  have hcoeff : MemLp (fun ξ : ℂ =>
      ((‖ξ‖ ^ k * (1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) 2 volume :=
    (complex_hthree_moment_weight_memLp_two k hk).ofReal
  have hprod : Integrable (fun ξ : ℂ =>
      ((‖ξ‖ ^ k * (1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * u ξ) volume :=
    hcoeff.integrable_mul (Lp.memLp u)
  have hvae : (v : ℂ → ℂ) =ᵐ[volume]
      (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * u ξ) := by
    have haae : (a : ℂ → ℂ) =ᵐ[volume]
        (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-3 / 2 : ℝ) : ℝ) : ℂ)) :=
      (ha.ofReal).coeFn_toLp
    filter_upwards [Lp.coeFn_lpSMul (r := 1) a u, haae] with ξ hvξ haξ
    simp only [Pi.smul_apply', smul_eq_mul] at hvξ
    rw [hvξ, haξ]
  have hmoment : Integrable (fun ξ : ℂ => (‖ξ‖ ^ k : ℂ) * v ξ) volume := by
    apply hprod.congr
    filter_upwards [hvae] with ξ hξ
    rw [hξ]
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  convert hmoment.norm using 1
  ext ξ
  simp

/-- `H³(ℂ)` has a bounded classical `C¹` representative. -/
theorem complex_memSobolev_three_contDiff_one_representation
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 3 2 w) :
    ∃ c : ℂ →ᵇ ℂ,
      ContDiff ℝ 1 (c : ℂ → ℂ) ∧
        ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ x, φ x * c x := by
  obtain ⟨v, hv, hmoment⟩ := complex_memSobolev_three_fourier_moments w hw
  let c : ℂ →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℂ => (Lp.fourierTransform v) (-x))
      ((Lp.fourierTransform v).continuous.comp continuous_neg)
      ‖Lp.fourierTransform v‖
      (fun x => (Lp.fourierTransform v).norm_coe_le_norm (-x))
  refine ⟨c, ?_, ?_⟩
  · have hf : ContDiff ℝ (1 : ℕ∞) (𝓕 (v : ℂ → ℂ)) :=
      Real.contDiff_fourier (fun k hk => hmoment k (by exact_mod_cast hk))
    have hc := hf.comp (contDiff_neg (𝕜 := ℝ) (F := ℂ))
    change ContDiff ℝ (1 : ℕ∞) (fun x : ℂ => (Lp.fourierTransform v) (-x))
    simpa only [Function.comp_def, Lp.fourierTransform_apply] using hc
  · intro φ
    have hwv : w = 𝓕⁻ (v : 𝓢'(ℂ, ℂ)) := by
      rw [← hv, FourierTransform.fourierInv_fourier_eq]
    rw [hwv, complex_fourierInv_L1_integral_representation]
    congr 1
    funext x
    simp [c, Lp.fourierTransform_apply, Real.fourierInv_eq_fourier_neg]

/-- The `C¹` function is a.e. the actual `L²` Sobolev representative. -/
theorem complex_memSobolev_three_ae_contDiff_one
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 3 2 w) :
    ∃ (f : Lp ℂ 2 (volume : Measure ℂ)) (c : ℂ →ᵇ ℂ),
      w = (f : 𝓢'(ℂ, ℂ)) ∧
        (f : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) ∧
          ContDiff ℝ 1 (c : ℂ → ℂ) := by
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp (hw.mono (by norm_num))
  obtain ⟨c, hcDiff, hc⟩ := complex_memSobolev_three_contDiff_one_representation w hw
  refine ⟨f, c, hf, ?_, hcDiff⟩
  have hfc : LocallyIntegrable (f : ℂ → ℂ) volume :=
    (Lp.memLp f).locallyIntegrable (by norm_num)
  have hcTop : MemLp (c : ℂ → ℂ) ⊤ volume :=
    memLp_top_of_bound c.continuous.aestronglyMeasurable ‖c‖
      (Filter.Eventually.of_forall c.norm_coe_le_norm)
  have hcc : LocallyIntegrable (c : ℂ → ℂ) volume :=
    hcTop.locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq hfc hcc
  intro g hg hgs
  let gC : ℂ → ℂ := fun x => (g x : ℂ)
  have hgC : ContDiff ℝ ∞ gC :=
    Complex.ofRealCLM.contDiff.comp hg
  have hgsC : HasCompactSupport gC :=
    hgs.comp_left Complex.ofRealCLM.map_zero
  let φ : 𝓢(ℂ, ℂ) := hgsC.toSchwartzMap hgC
  have hp := hc φ
  rw [hf, Lp.toTemperedDistribution_apply] at hp
  simpa [φ, gC, smul_eq_mul, mul_comm] using hp

#print axioms complex_memSobolev_three_fourier_moments
#print axioms complex_memSobolev_three_contDiff_one_representation
#print axioms complex_memSobolev_three_ae_contDiff_one

end

end SystolicGrowth
