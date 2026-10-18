module

public import Geometry.ComplexSobolevClassicalRepresentative

@[expose] public section

/-!
# Arbitrarily differentiable representatives from high Sobolev order

The local elliptic bootstrap can produce all integer Sobolev orders.  This
file identifies their common representative as a genuinely smooth function,
using only Fourier moments and Fourier-integral differentiability.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SystolicGrowth

noncomputable section

/-- The inverse quadratic weight is square-integrable; use the common
Bessel-weight estimate with its exponent simplified. -/
private theorem complex_inverse_quadratic_weight_memLp_two :
    MemLp (fun x : ℂ => (1 + ‖x‖ ^ 2)⁻¹) 2
      (volume : Measure ℂ) := by
  have he : (-2 / 2 : ℝ) = -1 := by norm_num [Rat.cast_divInt]
  simpa only [he, Real.rpow_neg_one] using complex_inverse_bessel_weight_memLp_two

private theorem complex_fourierMomentWeight_nat_memLp_two
    (n k : ℕ) (hk : k ≤ n) :
    MemLp (fun x : ℂ => ‖x‖ ^ k * ((1 + ‖x‖ ^ 2)⁻¹ : ℝ) ^ (n + 1)) 2
      (volume : Measure ℂ) := by
  let a : ℂ → ℝ := fun x => (1 + ‖x‖ ^ 2)⁻¹
  have ha : MemLp a 2 (volume : Measure ℂ) :=
    complex_inverse_quadratic_weight_memLp_two
  refine ha.of_le_mul (c := 1) (by fun_prop) ?_
  apply Filter.Eventually.of_forall
  intro x
  let A : ℝ := 1 + ‖x‖ ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hAle : 1 ≤ A := by dsimp [A]; nlinarith [sq_nonneg ‖x‖]
  have hnorm : 0 ≤ ‖x‖ := norm_nonneg x
  have hnormA : ‖x‖ ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hpow : ‖x‖ ^ k ≤ A ^ n :=
    (pow_le_pow_left₀ hnorm hnormA k).trans
      (pow_le_pow_right₀ hAle hk)
  have hinv : 0 ≤ a x := by dsimp [a]; positivity
  have hid : A ^ n * (A⁻¹) ^ (n + 1) = A⁻¹ := by
    rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hA.ne', one_pow, one_mul]
  change ‖‖x‖ ^ k * (a x) ^ (n + 1)‖ ≤ 1 * ‖a x‖
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hnorm k)
    (pow_nonneg hinv _)), Real.norm_eq_abs, abs_of_nonneg hinv, one_mul]
  calc
    ‖x‖ ^ k * (a x) ^ (n + 1) ≤ A ^ n * (a x) ^ (n + 1) := by gcongr
    _ = a x := by simpa only [a, A] using hid

/-- `H^{2n+2}` controls every Fourier moment through order `n` in
dimension two. The deliberately stronger Sobolev exponent makes the
comparison an elementary integer-power inequality. -/
theorem complex_memSobolev_even_fourier_moments
    (n : ℕ) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev (2 * (n : ℝ) + 2) 2 w) :
    ∃ v : Lp ℂ 1 (volume : Measure ℂ),
      𝓕 w = (v : 𝓢'(ℂ, ℂ)) ∧
      ∀ k : ℕ, k ≤ n →
        Integrable (fun ξ : ℂ => ‖ξ‖ ^ k * ‖v ξ‖) volume := by
  obtain ⟨u, hu⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hw
  have ha : MemLp (fun ξ : ℂ =>
      ((1 + ‖ξ‖ ^ 2)⁻¹ ^ (n + 1) : ℝ)) 2 volume := by
    simpa using complex_fourierMomentWeight_nat_memLp_two n 0 (Nat.zero_le n)
  have hTempC : (fun ξ : ℂ =>
      (((1 + ‖ξ‖ ^ 2)⁻¹ ^ (n + 1) : ℝ) : ℂ)).HasTemperateGrowth := by
    have h : (fun ξ : ℂ =>
        (((1 + ‖ξ‖ ^ 2) ^ (-(n + 1 : ℝ)) : ℝ) : ℂ)).HasTemperateGrowth := by
      fun_prop
    convert h using 1
    funext ξ
    norm_cast
    simp only [zpow_negSucc, inv_pow]
  let a : Lp ℂ 2 (volume : Measure ℂ) :=
    ha.ofReal.toLp (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ ^ (n + 1) : ℝ) : ℂ))
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
        rw [show ((2 * n + 2 : ℕ) : ℝ) / 2 = ((n + 1 : ℕ) : ℝ) by
          push_cast; ring, Real.rpow_natCast]
        rw [← mul_pow, mul_inv_cancel₀ hbase.ne', one_pow]
    · exact hTempC
  refine ⟨v, hv, ?_⟩
  intro k hk
  have hcoeff : MemLp (fun ξ : ℂ =>
      ((‖ξ‖ ^ k * ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ) ^ (n + 1) : ℝ) : ℂ)) 2 volume :=
    (complex_fourierMomentWeight_nat_memLp_two n k hk).ofReal
  have hprod : Integrable (fun ξ : ℂ =>
      ((‖ξ‖ ^ k * ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ) ^ (n + 1) : ℝ) : ℂ) * u ξ) volume :=
    hcoeff.integrable_mul (Lp.memLp u)
  have hvae : (v : ℂ → ℂ) =ᵐ[volume]
      (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ ^ (n + 1) : ℝ) : ℂ) * u ξ) := by
    have haae : (a : ℂ → ℂ) =ᵐ[volume]
        (fun ξ => (((1 + ‖ξ‖ ^ 2)⁻¹ ^ (n + 1) : ℝ) : ℂ)) :=
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

/-- The `H^{2n+2}` Fourier moment estimate yields a genuine bounded
classical `Cⁿ` representative of the original distribution. -/
theorem complex_memSobolev_even_contDiff_representation
    (n : ℕ) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev (2 * (n : ℝ) + 2) 2 w) :
    ∃ c : ℂ →ᵇ ℂ,
      ContDiff ℝ n (c : ℂ → ℂ) ∧
        ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ x, φ x * c x := by
  obtain ⟨v, hv, hmoment⟩ := complex_memSobolev_even_fourier_moments n w hw
  let c : ℂ →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℂ => (Lp.fourierTransform v) (-x))
      ((Lp.fourierTransform v).continuous.comp continuous_neg)
      ‖Lp.fourierTransform v‖
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

/-- The `Cⁿ` function is a.e. the original `L²` representative. -/
theorem complex_memSobolev_even_ae_contDiff
    (n : ℕ) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev (2 * (n : ℝ) + 2) 2 w) :
    ∃ (f : Lp ℂ 2 (volume : Measure ℂ)) (c : ℂ →ᵇ ℂ),
      w = (f : 𝓢'(ℂ, ℂ)) ∧
        (f : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) ∧
          ContDiff ℝ n (c : ℂ → ℂ) := by
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp (hw.mono (by positivity))
  obtain ⟨c, hcDiff, hc⟩ := complex_memSobolev_even_contDiff_representation n w hw
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

private theorem complex_boundedContinuous_eq_of_same_Schwartz_action
    (c d : ℂ →ᵇ ℂ)
    (h : ∀ φ : 𝓢(ℂ, ℂ),
      (∫ x, φ x * c x) = ∫ x, φ x * d x) : c = d := by
  have hcTop : MemLp (c : ℂ → ℂ) ⊤ volume :=
    memLp_top_of_bound c.continuous.aestronglyMeasurable ‖c‖
      (Filter.Eventually.of_forall c.norm_coe_le_norm)
  have hdTop : MemLp (d : ℂ → ℂ) ⊤ volume :=
    memLp_top_of_bound d.continuous.aestronglyMeasurable ‖d‖
      (Filter.Eventually.of_forall d.norm_coe_le_norm)
  have hae : (c : ℂ → ℂ) =ᵐ[volume] (d : ℂ → ℂ) := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (hcTop.locallyIntegrable (by norm_num))
      (hdTop.locallyIntegrable (by norm_num))
    intro g hg hgs
    let gC : ℂ → ℂ := fun x => (g x : ℂ)
    have hgC : ContDiff ℝ ∞ gC :=
      Complex.ofRealCLM.contDiff.comp hg
    have hgsC : HasCompactSupport gC :=
      hgs.comp_left Complex.ofRealCLM.map_zero
    let φ : 𝓢(ℂ, ℂ) := hgsC.toSchwartzMap hgC
    simpa [φ, gC, smul_eq_mul, mul_comm] using h φ
  exact DFunLike.ext _ _ (fun x => congrFun
    (MeasureTheory.Measure.eq_of_ae_eq hae c.continuous d.continuous) x)

/-- If a complex-plane distribution lies in every sufficiently high even
Sobolev space, the unique bounded continuous representative is genuinely
smooth. This is a direct Fourier consequence, independent of any assumed
elliptic regularity theorem. -/
theorem complex_memSobolev_all_even_smooth_representation
    (w : 𝓢'(ℂ, ℂ))
    (hw : ∀ n : ℕ, MemSobolev (2 * (n : ℝ) + 2) 2 w) :
    ∃ c : ℂ →ᵇ ℂ,
      ContDiff ℝ ∞ (c : ℂ → ℂ) ∧
        ∀ φ : 𝓢(ℂ, ℂ), w φ = ∫ x, φ x * c x := by
  obtain ⟨c, _, hc⟩ := complex_memSobolev_even_contDiff_representation 0 w (hw 0)
  refine ⟨c, ?_, hc⟩
  apply contDiff_iff_forall_nat_le.mpr
  intro n _
  obtain ⟨d, hdDiff, hd⟩ := complex_memSobolev_even_contDiff_representation n w (hw n)
  have hcd : c = d := complex_boundedContinuous_eq_of_same_Schwartz_action c d
    (fun φ => (hc φ).symm.trans (hd φ))
  rw [hcd]
  exact hdDiff

#print axioms complex_memSobolev_even_fourier_moments
#print axioms complex_memSobolev_even_contDiff_representation
#print axioms complex_memSobolev_even_ae_contDiff
#print axioms complex_memSobolev_all_even_smooth_representation

end

end SystolicGrowth
