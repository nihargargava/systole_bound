module

public import Geometry.ComplexSobolevSharpRepresentative
public import Geometry.ComplexLocalWeakDerivativeUnique
public import Geometry.ComplexRealScalarClassicalChain

@[expose] public section

/-!
# Classical gradient and Sobolev witnesses at arbitrary finite order

An actual real `H^(k+2)` cutoff has a real `C^k` representative. Each
first derivative has a genuine `L²` representative in `H^k`; distributional
uniqueness identifies it almost everywhere with the classical derivative.
-/

open MeasureTheory TemperedDistribution
open scoped ContDiff LineDeriv SchwartzMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Math.** Genuine arbitrary-order gradient extraction from a real
`H^(k+2)` cutoff, for `k≥1`. The conclusion supplies exactly the `H^k`
first-derivative witnesses needed for the nonlinear cutoff chain rule. -/
theorem complexHk_real_exists_classical_gradient_witness
    (k : ℕ) (hk : 1 ≤ k)
    (w : Lp ℂ 2 (volume : Measure ℂ))
    (hw : MemSobolev ((k : ℝ) + 2) 2 (w : 𝓢'(ℂ, ℂ)))
    (u : ℂ → ℝ) (hwu : w =ᵐ[volume] fun z => (u z : ℂ)) :
    ∃ (c : ℂ → ℝ)
      (G : Fin (Module.finrank ℝ ℂ) → Lp ℂ 2 (volume : Measure ℂ)),
      ContDiff ℝ k c ∧ w =ᵐ[volume] (fun z => (c z : ℂ)) ∧
      (∀ i, G i =ᵐ[volume]
        (fun z => ((fderiv ℝ c z ((stdOrthonormalBasis ℝ ℂ) i) : ℝ) : ℂ))) ∧
      (∀ i, MemSobolev (k : ℝ) 2 (G i : 𝓢'(ℂ, ℂ))) := by
  obtain ⟨w', c₀, hw', hw'c, hc₀⟩ :=
    complex_memSobolev_add_two_ae_contDiff k (w : 𝓢'(ℂ, ℂ)) hw
  have heq : w = w' := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure ℂ)) (p := 2))
    exact hw'
  have hwc₀ : (w : ℂ → ℂ) =ᵐ[volume] (c₀ : ℂ → ℂ) := heq ▸ hw'c
  have hrealAE : (c₀ : ℂ → ℂ) =ᵐ[volume]
      (fun z => ((c₀ z).re : ℂ)) := by
    filter_upwards [hwc₀, hwu] with z hz₀ hzu
    have hczu : c₀ z = (u z : ℂ) := hz₀.symm.trans hzu
    rw [hczu]
    simp
  have hreal : (c₀ : ℂ → ℂ) = (fun z => ((c₀ z).re : ℂ)) := by
    exact (c₀.continuous.ae_eq_iff_eq volume
      (Complex.ofRealCLM.continuous.comp
        (Complex.reCLM.continuous.comp c₀.continuous))).mp hrealAE
  let c : ℂ → ℝ := fun z => (c₀ z).re
  have hc : ContDiff ℝ k c := Complex.reCLM.contDiff.comp hc₀
  have hcone : ContDiff ℝ 1 c := hc.of_le (by exact_mod_cast hk)
  have hco : (fun z => (c z : ℂ)) = (c₀ : ℂ → ℂ) := hreal.symm
  have hDk (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev (k : ℝ) 2 (∂_{(stdOrthonormalBasis ℝ ℂ) i}
        (w : 𝓢'(ℂ, ℂ))) := by
    apply (hw.lineDerivOp (m := (stdOrthonormalBasis ℝ ℂ) i)).mono
    linarith
  have hGex (i : Fin (Module.finrank ℝ ℂ)) :
      ∃ g : Lp ℂ 2 (volume : Measure ℂ),
        ∂_{(stdOrthonormalBasis ℝ ℂ) i}
          (w : 𝓢'(ℂ, ℂ)) = (g : 𝓢'(ℂ, ℂ)) := by
    apply memSobolev_zero_iff.mp
    exact (hDk i).mono (by positivity)
  choose G hG using hGex
  refine ⟨c, G, hc, ?_, ?_, ?_⟩
  · simpa only [hco] using hwc₀
  · intro i
    have hGi := complexL2_weakDerivative_eq_fderiv_ae w (G i) (c₀ : ℂ → ℂ)
      ((stdOrthonormalBasis ℝ ℂ) i) (hc₀.of_le (by exact_mod_cast hk))
      hwc₀ (hG i)
    have hDco (z : ℂ) :
        fderiv ℝ (c₀ : ℂ → ℂ) z ((stdOrthonormalBasis ℝ ℂ) i) =
          ((fderiv ℝ c z ((stdOrthonormalBasis ℝ ℂ) i) : ℝ) : ℂ) := by
      have hEq := congrArg
        (fun f : ℂ → ℂ => fderiv ℝ f z ((stdOrthonormalBasis ℝ ℂ) i)) hco
      have hscalar : fderiv ℝ (fun q => (c q : ℂ)) z
          ((stdOrthonormalBasis ℝ ℂ) i) =
          ((fderiv ℝ c z ((stdOrthonormalBasis ℝ ℂ) i) : ℝ) : ℂ) := by
        simpa using complexRealScalar_fderiv_comp c (fun t : ℝ => t)
          hcone contDiff_id z ((stdOrthonormalBasis ℝ ℂ) i)
      rw [hscalar] at hEq
      exact hEq.symm
    filter_upwards [hGi] with z hz
    exact hz.trans (hDco z)
  · intro i
    rw [← hG i]
    exact hDk i

#print axioms complexHk_real_exists_classical_gradient_witness

end

end SystolicGrowth
