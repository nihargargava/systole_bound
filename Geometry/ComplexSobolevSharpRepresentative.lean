module

public import Geometry.ComplexSobolevSmoothRepresentative

@[expose] public section

/-!
# Classical representatives with the two-dimensional Sobolev threshold

The bound `|ξ|ᵏ ≤ (1+|ξ|²)^(k/2)` gives `Hᵏ⁺² ⊂ Cᵏ` on the
complex plane. This exponent permits the nonlinear elliptic bootstrap
to gain one classical derivative at each step.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SystolicGrowth

noncomputable section

private theorem complex_sharp_inverse_weight_memLp_two :
    MemLp (fun x : ℂ => (1 + ‖x‖ ^ 2) ^ (-2 / 2 : ℝ)) 2
      (volume : Measure ℂ) :=
  complex_inverse_bessel_weight_memLp_two

/-- **Math.** The inverse Bessel weight for `Hⁿ⁺²`, multiplied by any
radial moment through order `n`, is genuinely square integrable in dimension two. -/
theorem complex_sharp_fourierMomentWeight_memLp_two
    (n k : ℕ) (hk : k ≤ n) :
    MemLp (fun x : ℂ => ‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2)) 2
      (volume : Measure ℂ) := by
  have ha : MemLp (fun x : ℂ => (1 + ‖x‖ ^ 2)⁻¹) 2 (volume : Measure ℂ) := by
    simpa only [show (-2 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one] using
      complex_sharp_inverse_weight_memLp_two
  refine ha.of_le_mul (c := 1) (by fun_prop) ?_
  apply Filter.Eventually.of_forall
  intro x
  have hA : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hA1 : 1 ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hsqrt : ‖x‖ ≤ (1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (norm_nonneg x) hA.le).2 (by nlinarith)
  have hpow : ‖x‖ ^ k ≤ (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) := by
    calc
      ‖x‖ ^ k ≤ ((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ)) ^ k :=
        pow_le_pow_left₀ (norm_nonneg x) hsqrt k
      _ = (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := by
        rw [← Real.rpow_mul_natCast hA.le]
        congr 1
        ring
      _ ≤ (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le hA1 (by
          have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
          linarith)
  change ‖‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2)‖ ≤
    1 * ‖(1 + ‖x‖ ^ 2)⁻¹‖
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (by positivity), one_mul]
  calc
    ‖x‖ ^ k * (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) ≤
        (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) *
          (1 + ‖x‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hA.le _)
    _ = (1 + ‖x‖ ^ 2)⁻¹ := by
      rw [← Real.rpow_add hA, show (n : ℝ) / 2 + (-((n : ℝ) + 2) / 2) = -1 by ring,
        Real.rpow_neg_one]

/-- **Math.** Genuine `Hⁿ⁺²` membership supplies every integrable Fourier
moment through order `n`, with the original distribution retained. -/
theorem complex_memSobolev_add_two_fourier_moments
    (n : ℕ) (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev ((n : ℝ) + 2) 2 w) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ), 𝓕 w = (v : 𝓢'(ℂ, ℂ)) ∧
      ∀ k : ℕ, k ≤ n → Integrable (fun ξ : ℂ => ‖ξ‖ ^ k * ‖v ξ‖) volume := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hw
  have ha : MemLp (fun ξ : ℂ => (1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2)) 2 volume := by
    simpa using complex_sharp_fourierMomentWeight_memLp_two n 0 (Nat.zero_le n)
  have hTempC : (fun ξ : ℂ =>
      (((1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) : ℝ) : ℂ)).HasTemperateGrowth := by
    fun_prop
  let a : Lp ℂ 2 (volume : Measure ℂ) :=
    ha.ofReal.toLp (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) : ℝ) : ℂ))
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
        have hweight : (1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) *
            (1 + ‖ξ‖ ^ 2) ^ (((n : ℝ) + 2) / 2) = 1 := by
          rw [← Real.rpow_add (by positivity : 0 < 1 + ‖ξ‖ ^ 2),
            show -((n : ℝ) + 2) / 2 + ((n : ℝ) + 2) / 2 = 0 by ring,
            Real.rpow_zero]
        simpa only [Complex.ofReal_mul, Complex.ofReal_one, mul_comm] using
          congrArg Complex.ofReal hweight
    · exact hTempC
  refine ⟨v, hv, ?_⟩
  intro k hk
  have hcoeff : MemLp (fun ξ : ℂ =>
      ((‖ξ‖ ^ k * (1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) : ℝ) : ℂ)) 2 volume :=
    (complex_sharp_fourierMomentWeight_memLp_two n k hk).ofReal
  have hprod : Integrable (fun ξ : ℂ =>
      ((‖ξ‖ ^ k * (1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) : ℝ) : ℂ) * u ξ) volume :=
    hcoeff.integrable_mul (Lp.memLp u)
  have hvae : (v : ℂ → ℂ) =ᵐ[volume]
      (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) : ℝ) : ℂ) * u ξ) := by
    have haae : (a : ℂ → ℂ) =ᵐ[volume]
        (fun ξ => (((1 + ‖ξ‖ ^ 2) ^ (-((n : ℝ) + 2) / 2) : ℝ) : ℂ)) :=
      (ha.ofReal).coeFn_toLp
    filter_upwards [Lp.coeFn_lpSMul (r := 1) a u, haae] with ξ hvξ haξ
    simp only [Pi.smul_apply', smul_eq_mul] at hvξ
    rw [hvξ, haξ]
  have hmoment : Integrable (fun ξ : ℂ => (‖ξ‖ ^ k : ℂ) * v ξ) volume := by
    apply hprod.congr
    filter_upwards [hvae] with ξ hξ
    rw [hξ, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  convert hmoment.norm using 1
  ext ξ
  simp

/-- **Math.** In dimension two, an actual `Hⁿ⁺²` distribution has a
bounded classical `Cⁿ` representative with exactly the same Schwartz action. -/
theorem complex_memSobolev_add_two_contDiff_representation
    (n : ℕ) (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev ((n : ℝ) + 2) 2 w) :
    ∃ c : ℂ →ᵇ ℂ, ContDiff ℝ n (c : ℂ → ℂ) ∧
      ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ x, φ x * c x := by
  obtain ⟨v, hv, hmoment⟩ := complex_memSobolev_add_two_fourier_moments n w hw
  let c : ℂ →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℂ => (Lp.fourierTransform v) (-x))
    ((Lp.fourierTransform v).continuous.comp continuous_neg) ‖Lp.fourierTransform v‖
    (fun x => (Lp.fourierTransform v).norm_coe_le_norm (-x))
  refine ⟨c, ?_, ?_⟩
  · have hf : ContDiff ℝ (n : ℕ∞) (𝓕 (v : ℂ → ℂ)) :=
      Real.contDiff_fourier (fun k hk => hmoment k (by exact_mod_cast hk))
    have hc := hf.comp (contDiff_neg (𝕜 := ℝ) (F := ℂ))
    change ContDiff ℝ (n : ℕ∞) (fun x : ℂ => (Lp.fourierTransform v) (-x))
    simpa only [Function.comp_def, Lp.fourierTransform_apply] using hc
  · intro φ
    have hwv : w = 𝓕⁻ (v : 𝓢'(ℂ, ℂ)) := by
      rw [← hv, FourierTransform.fourierInv_fourier_eq]
    rw [hwv, complex_fourierInv_L1_integral_representation]
    congr 1
    funext x
    simp [c, Lp.fourierTransform_apply, Real.fourierInv_eq_fourier_neg]

/-- **Math.** The sharp `Cⁿ` representative is almost everywhere the
actual `L²` field, not just an abstract function of the required regularity. -/
theorem complex_memSobolev_add_two_ae_contDiff
    (n : ℕ) (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev ((n : ℝ) + 2) 2 w) :
    ∃ (f : Lp ℂ 2 (volume : Measure ℂ)) (c : ℂ →ᵇ ℂ),
      w = (f : 𝓢'(ℂ, ℂ)) ∧ (f : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) ∧
        ContDiff ℝ n (c : ℂ → ℂ) := by
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp (hw.mono (by positivity))
  obtain ⟨c, hcDiff, hc⟩ := complex_memSobolev_add_two_contDiff_representation n w hw
  refine ⟨f, c, hf, ?_, hcDiff⟩
  have hfc : LocallyIntegrable (f : ℂ → ℂ) volume :=
    (Lp.memLp f).locallyIntegrable (by norm_num)
  have hcTop : MemLp (c : ℂ → ℂ) ⊤ volume :=
    memLp_top_of_bound c.continuous.aestronglyMeasurable ‖c‖
      (Filter.Eventually.of_forall c.norm_coe_le_norm)
  apply ae_eq_of_integral_contDiff_smul_eq hfc (hcTop.locallyIntegrable (by norm_num))
  intro g hg hgs
  let gC : ℂ → ℂ := fun x => (g x : ℂ)
  have hgC : ContDiff ℝ ∞ gC := Complex.ofRealCLM.contDiff.comp hg
  have hgsC : HasCompactSupport gC := hgs.comp_left Complex.ofRealCLM.map_zero
  let φ : 𝓢(ℂ, ℂ) := hgsC.toSchwartzMap hgC
  have hp := hc φ
  rw [hf, Lp.toTemperedDistribution_apply] at hp
  simpa [φ, gC, smul_eq_mul, mul_comm] using hp

#print axioms complex_sharp_fourierMomentWeight_memLp_two
#print axioms complex_memSobolev_add_two_fourier_moments
#print axioms complex_memSobolev_add_two_contDiff_representation
#print axioms complex_memSobolev_add_two_ae_contDiff

end

end SystolicGrowth
