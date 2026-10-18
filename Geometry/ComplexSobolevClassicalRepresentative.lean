module

public import Geometry.ComplexSobolevDerivativeRepresentative
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Classical representatives from complex-plane Sobolev regularity

The Fourier route first proves weighted Fourier integrability from the
actual Sobolev witness, then applies the Fourier integral's differentiability
theorem. This is needed to identify weak derivative representatives as
classical derivatives, not merely continuous functions a.e.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SystolicGrowth

noncomputable section

/-- The inverse quadratic weight is square-integrable on the complex plane.
Its squared decay exponent exceeds the real dimension two. -/
theorem complex_inverse_bessel_weight_memLp_two :
    MemLp (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-2 / 2 : ℝ)) 2
      (volume : Measure ℂ) := by
  have htemp : (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-2 / 2 : ℝ)).HasTemperateGrowth := by
    fun_prop
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num) (by norm_num) htemp.1.continuous.aestronglyMeasurable]
  suffices h : ∫⁻ a : ℂ, ENNReal.ofReal ‖(1 + ‖a‖ ^ 2) ^ (-2 : ℝ)‖ < ⊤ from by
    norm_cast
    simp_rw [ofReal_norm] at h
    simp_rw [← enorm_pow]
    convert h
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1
    norm_num [Rat.cast_divInt]
  apply ((integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
    (by rw [Complex.finrank_real_complex]; norm_num)).congr _).lintegral_lt_top
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
  congr 1
  ring

private theorem complex_fourierMomentWeight_memLp_two
    (n : ℕ) (hn : n ≤ 2) :
    MemLp (fun x : ℂ => ‖x‖ ^ n * ((1 + ‖x‖ ^ 2)⁻¹ : ℝ) ^ 2) 2
      (volume : Measure ℂ) := by
  let a : ℂ → ℝ := fun x => (1 + ‖x‖ ^ 2)⁻¹
  have ha : MemLp a 2 (volume : Measure ℂ) := by
    have he : (-2 / 2 : ℝ) = -1 := by norm_num [Rat.cast_divInt]
    simpa only [a, he, Real.rpow_neg_one] using
      complex_inverse_bessel_weight_memLp_two
  refine ha.of_le_mul (c := 2) (by fun_prop) ?_
  apply Filter.Eventually.of_forall
  intro x
  have hr : 0 ≤ ‖x‖ := norm_nonneg x
  have hbase : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hpow : ‖x‖ ^ n ≤ 2 * (1 + ‖x‖ ^ 2) := by
    interval_cases n <;> nlinarith [sq_nonneg (‖x‖ - 1)]
  have hainv : 0 ≤ a x := by positivity
  have hmul : ‖x‖ ^ n * a x ≤ 2 := by
    dsimp [a]
    rw [mul_inv_le_iff₀ hbase]
    exact hpow
  change ‖‖x‖ ^ n * (a x) ^ 2‖ ≤ 2 * ‖a x‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr n)
    (sq_nonneg _)), Real.norm_eq_abs, abs_of_nonneg hainv]
  nlinarith

/-- An `H⁴(ℂ)` distribution has an actual integrable Fourier representative
with integrable zeroth, first, and second radial moments. -/
theorem complex_memSobolev_four_fourier_moments
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 4 2 w) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ),
      𝓕 w = (v : 𝓢'(ℂ, ℂ)) ∧
      ∀ n : ℕ, n ≤ 2 →
        Integrable (fun ξ : ℂ => ‖ξ‖ ^ n * ‖v ξ‖) volume := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hw
  have ha : MemLp (fun ξ : ℂ =>
      ((1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 : ℝ)) 2 volume := by
    simpa using complex_fourierMomentWeight_memLp_two 0 (by norm_num)
  have hTempC : (fun ξ : ℂ =>
      (((1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    have h : (fun ξ : ℂ => (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ)).HasTemperateGrowth := by
      fun_prop
    convert h using 1
    funext ξ
    rw [Real.rpow_neg (by positivity)]
    simp [inv_pow]
  let a : Lp ℂ 2 (volume : Measure ℂ) :=
    ha.ofReal.toLp (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 : ℝ) : ℂ))
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
        simp only [show (4 / 2 : ℝ) = 2 by norm_num]
        field_simp
        exact Real.rpow_natCast _ 2
    · exact hTempC
  refine ⟨v, hv, ?_⟩
  intro n hn
  have hcoeff : MemLp (fun ξ : ℂ =>
      ((‖ξ‖ ^ n * ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ) ^ 2 : ℝ) : ℂ)) 2 volume :=
    (complex_fourierMomentWeight_memLp_two n hn).ofReal
  have hprod : Integrable (fun ξ : ℂ =>
      ((‖ξ‖ ^ n * ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ) ^ 2 : ℝ) : ℂ) * u ξ) volume :=
    hcoeff.integrable_mul (Lp.memLp u)
  have hvae : (v : ℂ → ℂ) =ᵐ[volume]
      (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 : ℝ) : ℂ) * u ξ) := by
    have haae : (a : ℂ → ℂ) =ᵐ[volume]
        (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ ^ 2 : ℝ) : ℂ)) :=
      (ha.ofReal).coeFn_toLp
    filter_upwards [Lp.coeFn_lpSMul (r := 1) a u, haae] with ξ hvξ haξ
    simp only [Pi.smul_apply', smul_eq_mul] at hvξ
    rw [hvξ, haξ]
  have hmoment : Integrable (fun ξ : ℂ => (‖ξ‖ ^ n : ℂ) * v ξ) volume := by
    apply hprod.congr
    filter_upwards [hvae] with ξ hξ
    rw [hξ]
    rw [Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  convert hmoment.norm using 1
  ext ξ
  simp

/-- An `H⁴(ℂ)` distribution has a bounded classical `C²` representative.
The equality is on every Schwartz test function, so this is the representative
of the original weak solution, not just an unrelated smooth function. -/
theorem complex_memSobolev_four_contDiff_two_representation
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 4 2 w) :
    ∃ c : ℂ →ᵇ ℂ,
      ContDiff ℝ 2 (c : ℂ → ℂ) ∧
        ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ x, φ x * c x := by
  obtain ⟨v, hv, hmoment⟩ := complex_memSobolev_four_fourier_moments w hw
  let c : ℂ →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℂ => (Lp.fourierTransform v) (-x))
      ((Lp.fourierTransform v).continuous.comp continuous_neg)
      ‖Lp.fourierTransform v‖
      (fun x => (Lp.fourierTransform v).norm_coe_le_norm (-x))
  refine ⟨c, ?_, ?_⟩
  · have hf : ContDiff ℝ (2 : ℕ∞) (𝓕 (v : ℂ → ℂ)) :=
      Real.contDiff_fourier (fun n hn => hmoment n (by exact_mod_cast hn))
    have hc := hf.comp (contDiff_neg (𝕜 := ℝ) (F := ℂ))
    change ContDiff ℝ (2 : ℕ∞) (fun x : ℂ => (Lp.fourierTransform v) (-x))
    simpa only [Function.comp_def, Lp.fourierTransform_apply] using hc
  · intro φ
    have hwv : w = 𝓕⁻ (v : 𝓢'(ℂ, ℂ)) := by
      rw [← hv, FourierTransform.fourierInv_fourier_eq]
    rw [hwv, complex_fourierInv_L1_integral_representation]
    congr 1
    funext x
    simp [c, Lp.fourierTransform_apply, Real.fourierInv_eq_fourier_neg]

/-- The classical `C²` representative is a.e. the genuine `L²` Sobolev
representative; in particular it realizes the distributional solution. -/
theorem complex_memSobolev_four_ae_contDiff_two
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 4 2 w) :
    ∃ (f : Lp ℂ 2 (volume : Measure ℂ)) (c : ℂ →ᵇ ℂ),
      w = (f : 𝓢'(ℂ, ℂ)) ∧
        (f : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) ∧
          ContDiff ℝ 2 (c : ℂ → ℂ) := by
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp (hw.mono (by norm_num))
  obtain ⟨c, hcDiff, hc⟩ := complex_memSobolev_four_contDiff_two_representation w hw
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

#print axioms complex_inverse_bessel_weight_memLp_two
#print axioms complex_memSobolev_four_fourier_moments
#print axioms complex_memSobolev_four_contDiff_two_representation
#print axioms complex_memSobolev_four_ae_contDiff_two

end

end SystolicGrowth
