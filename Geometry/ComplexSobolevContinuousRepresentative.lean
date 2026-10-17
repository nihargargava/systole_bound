module

public import Geometry.ComplexSobolevComposition

@[expose] public section

/-!
# The continuous Sobolev representative is the actual `L²` function

The Fourier construction gives equality as tempered distributions. This file
identifies the bounded continuous function with the a.e. `L²` representative.
-/

open FourierTransform TemperedDistribution MeasureTheory Real
open scoped SchwartzMap BoundedContinuousFunction ContDiff

namespace SystolicGrowth

noncomputable section

/-- An `H²(ℂ)` distribution represented by `f : L²` is a.e. equal to a
bounded continuous function. -/
theorem complex_memSobolev_two_ae_boundedContinuous
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 2 2 w) :
    ∃ (f : Lp ℂ 2 (volume : Measure ℂ))
      (c : ℂ →ᵇ ℂ),
      w = (f : 𝓢'(ℂ, ℂ)) ∧
        (f : ℂ → ℂ) =ᵐ[volume] (c : ℂ → ℂ) := by
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp (hw.mono (by norm_num))
  obtain ⟨c, hc⟩ := complex_memSobolev_two_boundedContinuous_representation w hw
  refine ⟨f, c, hf, ?_⟩
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
  have hgC : ContDiff ℝ ∞ gC := by
    exact Complex.ofRealCLM.contDiff.comp hg
  have hgsC : HasCompactSupport gC := by
    exact hgs.comp_left Complex.ofRealCLM.map_zero
  let φ : 𝓢(ℂ, ℂ) := hgsC.toSchwartzMap hgC
  have hp := hc φ
  rw [hf, Lp.toTemperedDistribution_apply] at hp
  simpa [φ, gC, smul_eq_mul, mul_comm] using hp

#print axioms complex_memSobolev_two_ae_boundedContinuous

end

end SystolicGrowth

