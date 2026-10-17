module

public import Geometry.ComplexC1WeakTestExtension
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# Multiplication of an `L²` weak derivative by a compact `C¹` coefficient

The ordinary product rule is proved by applying the distributional weak
derivative to the compact `C¹` test obtained by multiplying a Schwartz test
by the coefficient. The preceding mollification theorem justifies this test.
-/

open MeasureTheory TemperedDistribution
open scoped LineDeriv SchwartzMap

namespace SystolicGrowth

noncomputable section

/-- A compact `C¹` multiplier obeys the distributional first-product rule
for actual global `L²` representatives. The three a.e. hypotheses only
identify the explicitly supplied `L²` product representatives. -/
theorem complex_L2_lineDeriv_mul_compact_C1
    (F G AF AG ADF : Lp ℂ 2 (volume : Measure ℂ))
    (a : ℂ → ℂ) (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (v : ℂ)
    (hderiv : ∂_{v} (F : 𝓢'(ℂ, ℂ)) = (G : 𝓢'(ℂ, ℂ)))
    (hAF : AF =ᵐ[volume] fun z => a z * F z)
    (hAG : AG =ᵐ[volume] fun z => a z * G z)
    (hADF : ADF =ᵐ[volume] fun z => fderiv ℝ a z v * F z) :
    ∂_{v} (AF : 𝓢'(ℂ, ℂ)) = (AG : 𝓢'(ℂ, ℂ)) + (ADF : 𝓢'(ℂ, ℂ)) := by
  ext φ
  have hφ1 : ContDiff ℝ 1 (fun z => a z * φ z) :=
    ha.mul (φ.smooth 1)
  have hφc : HasCompactSupport (fun z => a z * φ z) := hac.mul_right
  have htest := complex_L2_lineDeriv_test_contDiff_one F G v hderiv
    (fun z => a z * φ z) hφ1 hφc
  have hAGint : (∫ z, (a z * φ z) * G z) = ∫ z, φ z * AG z := by
    apply integral_congr_ae
    filter_upwards [hAG] with z hz
    rw [hz]
    ring
  have hDφ : MemLp (fun z => fderiv ℝ φ z v) 2 (volume : Measure ℂ) := by
    convert ((∂_{v} φ : 𝓢(ℂ, ℂ)).memLp 2 volume) using 1
    funext z
    exact (SchwartzMap.lineDerivOp_apply_eq_fderiv v φ z).symm
  have hIntA : Integrable (fun z => φ z * ADF z) (volume : Measure ℂ) :=
    (φ.memLp 2 volume).integrable_mul (Lp.memLp ADF)
  have hIntB : Integrable (fun z => fderiv ℝ φ z v * AF z)
      (volume : Measure ℂ) :=
    hDφ.integrable_mul (Lp.memLp AF)
  have hDprod (z : ℂ) :
      fderiv ℝ (fun z => a z * φ z) z v =
        fderiv ℝ a z v * φ z + a z * fderiv ℝ φ z v := by
    rw [fderiv_fun_mul ((ha.differentiable (by norm_num)) z) φ.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hderivInt :
      (∫ z, fderiv ℝ (fun z => a z * φ z) z v * F z) =
        (∫ z, φ z * ADF z) + (∫ z, fderiv ℝ φ z v * AF z) := by
    calc
      (∫ z, fderiv ℝ (fun z => a z * φ z) z v * F z) =
          ∫ z, (φ z * ADF z + fderiv ℝ φ z v * AF z) := by
            apply integral_congr_ae
            filter_upwards [hAF, hADF] with z hzA hzD
            rw [hDprod z, hzA, hzD]
            ring
      _ = _ := integral_add hIntA hIntB
  rw [hAGint, hderivInt] at htest
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    Lp.toTemperedDistribution_apply, add_apply,
    Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  simp only [neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    neg_mul, integral_neg, smul_eq_mul]
  rw [htest]
  abel

/-- The three `L²` product witnesses required in the preceding Leibniz
rule exist for every compact `C¹` coefficient. -/
theorem complex_L2_lineDeriv_mul_compact_C1_exists
    (F G : Lp ℂ 2 (volume : Measure ℂ))
    (a : ℂ → ℂ) (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a)
    (v : ℂ)
    (hderiv : ∂_{v} (F : 𝓢'(ℂ, ℂ)) = (G : 𝓢'(ℂ, ℂ))) :
    ∃ AF AG ADF : Lp ℂ 2 (volume : Measure ℂ),
      AF =ᵐ[volume] (fun z => a z * F z) ∧
      AG =ᵐ[volume] (fun z => a z * G z) ∧
      ADF =ᵐ[volume] (fun z => fderiv ℝ a z v * F z) ∧
      ∂_{v} (AF : 𝓢'(ℂ, ℂ)) =
        (AG : 𝓢'(ℂ, ℂ)) + (ADF : 𝓢'(ℂ, ℂ)) := by
  have haTop : MemLp a ⊤ (volume : Measure ℂ) :=
    ha.continuous.memLp_top_of_hasCompactSupport hac volume
  have hDaCont : Continuous (fun z => fderiv ℝ a z v) :=
    (ha.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDaTop : MemLp (fun z => fderiv ℝ a z v) ⊤
      (volume : Measure ℂ) :=
    hDaCont.memLp_top_of_hasCompactSupport (hac.fderiv_apply ℝ v) volume
  have hAFm : MemLp (fun z => a z * F z) 2 (volume : Measure ℂ) :=
    haTop.fun_mul (Lp.memLp F)
  have hAGm : MemLp (fun z => a z * G z) 2 (volume : Measure ℂ) :=
    haTop.fun_mul (Lp.memLp G)
  have hADFm : MemLp (fun z => fderiv ℝ a z v * F z) 2
      (volume : Measure ℂ) :=
    hDaTop.fun_mul (Lp.memLp F)
  let AF := hAFm.toLp (fun z => a z * F z)
  let AG := hAGm.toLp (fun z => a z * G z)
  let ADF := hADFm.toLp (fun z => fderiv ℝ a z v * F z)
  refine ⟨AF, AG, ADF, hAFm.coeFn_toLp, hAGm.coeFn_toLp,
    hADFm.coeFn_toLp, ?_⟩
  exact complex_L2_lineDeriv_mul_compact_C1 F G AF AG ADF a ha hac v hderiv
    hAFm.coeFn_toLp hAGm.coeFn_toLp hADFm.coeFn_toLp

#print axioms complex_L2_lineDeriv_mul_compact_C1
#print axioms complex_L2_lineDeriv_mul_compact_C1_exists

end

end SystolicGrowth
