module

public import Geometry.ComplexDistributionCutoffLaplacian

@[expose] public section

/-!
# Higher local Sobolev gain in complex coordinates

The order-one criterion is derived from the proved Fourier/Laplacian gain at
order `-1`: an `L²` function with `L²` coordinate derivatives has Laplacian
in `H⁻¹`, hence lies in `H¹`. This avoids assuming an integer-order weak
derivative characterization as an external API.
-/

open TemperedDistribution MeasureTheory
open scoped Laplacian LineDeriv SchwartzMap Real

namespace SystolicGrowth

noncomputable section

/-- An `L²` distribution with `L²` first directional derivatives belongs
to `H¹(ℂ)`. This is proved from the actual distributional Laplacian and
Fourier gain, not postulated as a Sobolev characterization. -/
theorem complex_memSobolev_one_of_zero_lineDerivs_zero
    (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 0 2 w)
    (hderiv : ∀ i : Fin (Module.finrank ℝ ℂ),
      MemSobolev 0 2 (∂_{(stdOrthonormalBasis ℝ ℂ) i} w)) :
    MemSobolev 1 2 w := by
  let b := stdOrthonormalBasis ℝ ℂ
  have hwNeg : MemSobolev (-1) 2 w := hw.mono (by norm_num)
  have hterm (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev (-1) 2 (∂_{b i} (∂_{b i} w)) := by
    simpa using (hderiv i).lineDerivOp (m := b i)
  have hsum (s : Finset (Fin (Module.finrank ℝ ℂ))) :
      MemSobolev (-1) 2 (∑ i ∈ s, ∂_{b i} (∂_{b i} w)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hΔNeg : MemSobolev (-1) 2 (Δ w) := by
    rw [TemperedDistribution.laplacian_eq_sum b]
    exact hsum Finset.univ
  simpa only [show (-1 : ℝ) + 2 = 1 by norm_num] using
    complex_memSobolev_add_two_of_laplacian (-1) w hwNeg hΔNeg

/-- A Schwartz cutoff preserves `H¹` on the complex coordinate plane.
The derivative formula is the genuine distributional Leibniz rule. -/
theorem complexDistribution_memSobolev_one_smulLeft
    (ζ : 𝓢(ℂ, ℂ)) (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev 1 2 w) :
    MemSobolev 1 2 (TemperedDistribution.smulLeftCLM ℂ ζ w) := by
  let b := stdOrthonormalBasis ℝ ℂ
  have hw₀ : MemSobolev 0 2 w := hw.mono (by norm_num)
  have hprod₀ := complexDistribution_memSobolev_zero_smulLeft ζ w hw₀
  have hderiv (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev 0 2
        (∂_{b i} (TemperedDistribution.smulLeftCLM ℂ ζ w)) := by
    rw [complexDistribution_lineDeriv_smulLeft]
    have hfirst := complexDistribution_memSobolev_zero_smulLeft
      (∂_{b i} ζ : 𝓢(ℂ, ℂ)) w hw₀
    have hsecond := complexDistribution_memSobolev_zero_smulLeft ζ
      (∂_{b i} w) (by simpa using (hw.lineDerivOp (m := b i)))
    exact hfirst.add hsecond
  exact complex_memSobolev_one_of_zero_lineDerivs_zero _ hprod₀ hderiv

/-- The second local elliptic step: if an `H²` distribution has localized
Laplacian in `H¹`, then the same cutoff lies in `H³`. The commutator terms
are controlled using the proved `H¹` multiplier/Leibniz rule. -/
theorem complexDistribution_memSobolev_three_cutoff
    (ζ : 𝓢(ℂ, ℂ)) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev 2 2 w)
    (hζΔ : MemSobolev 1 2
      (TemperedDistribution.smulLeftCLM ℂ ζ (Δ w))) :
    MemSobolev 3 2 (TemperedDistribution.smulLeftCLM ℂ ζ w) := by
  let b := stdOrthonormalBasis ℝ ℂ
  have hw₁ : MemSobolev 1 2 w := hw.mono (by norm_num)
  have hζw₁ := complexDistribution_memSobolev_one_smulLeft ζ w hw₁
  have hΔζw₁ := complexDistribution_memSobolev_one_smulLeft
    (Δ ζ : 𝓢(ℂ, ℂ)) w hw₁
  have hterm (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev 1 2 (TemperedDistribution.smulLeftCLM ℂ
        (∂_{b i} ζ : 𝓢(ℂ, ℂ)) (∂_{b i} w)) := by
    apply complexDistribution_memSobolev_one_smulLeft
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      (hw.lineDerivOp (m := b i))
  have hcross (s : Finset (Fin (Module.finrank ℝ ℂ))) :
      MemSobolev 1 2 (∑ i ∈ s, TemperedDistribution.smulLeftCLM ℂ
        (∂_{b i} ζ : 𝓢(ℂ, ℂ)) (∂_{b i} w)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hΔprod₁ : MemSobolev 1 2
      (Δ (TemperedDistribution.smulLeftCLM ℂ ζ w)) := by
    rw [complexDistribution_laplacian_smulLeft]
    exact (hΔζw₁.add ((hcross Finset.univ).smul (2 : ℂ))).add hζΔ
  simpa only [show (1 : ℝ) + 2 = 3 by norm_num] using
    complex_memSobolev_add_two_of_laplacian 1
      (TemperedDistribution.smulLeftCLM ℂ ζ w) hζw₁ hΔprod₁

#print axioms complex_memSobolev_one_of_zero_lineDerivs_zero
#print axioms complexDistribution_memSobolev_one_smulLeft
#print axioms complexDistribution_memSobolev_three_cutoff

end

end SystolicGrowth
