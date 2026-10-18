module

public import Geometry.ComplexSobolevHigherCutoff

@[expose] public section

/-!
# Integer Sobolev cutoff multiplication and local gain on complex charts

The basic `H⁰` and `H¹` Schwartz-multiplier rules extend to every
nonnegative integer order by two-step induction and the proved exact
distributional Laplacian product formula.
-/

open TemperedDistribution MeasureTheory
open scoped Laplacian LineDeriv SchwartzMap Real

namespace SystolicGrowth

noncomputable section

/-- Every Schwartz multiplier preserves integer-order complex-plane
Sobolev regularity. The induction uses the genuine Laplacian product rule
and the exact Fourier gain at each step. -/
theorem complexDistribution_memSobolev_nat_smulLeft
    (n : ℕ) (ζ : 𝓢(ℂ, ℂ)) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev (n : ℝ) 2 w) :
    MemSobolev (n : ℝ) 2
      (TemperedDistribution.smulLeftCLM ℂ ζ w) := by
  induction n using Nat.twoStepInduction generalizing ζ w with
  | zero =>
    have hw₀ : MemSobolev 0 2 w := by simpa only [Nat.cast_zero] using hw
    simpa only [Nat.cast_zero] using
      complexDistribution_memSobolev_zero_smulLeft ζ w hw₀
  | one =>
    have hw₁ : MemSobolev 1 2 w := by simpa only [Nat.cast_one] using hw
    simpa only [Nat.cast_one] using
      complexDistribution_memSobolev_one_smulLeft ζ w hw₁
  | more n ih ih' =>
    let b := stdOrthonormalBasis ℝ ℂ
    have hₙ : MemSobolev (n : ℝ) 2 w := hw.mono (by
      push_cast
      linarith)
    have hζw : MemSobolev (n : ℝ) 2
        (TemperedDistribution.smulLeftCLM ℂ ζ w) := ih ζ w hₙ
    have hΔw : MemSobolev (n : ℝ) 2 (Δ w) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat,
        show (n : ℝ) + 2 - 2 = (n : ℝ) by ring] using hw.laplacian
    have hΔζw : MemSobolev (n : ℝ) 2
        (TemperedDistribution.smulLeftCLM ℂ (Δ ζ : 𝓢(ℂ, ℂ)) w) :=
      ih (Δ ζ) w hₙ
    have hterm (i : Fin (Module.finrank ℝ ℂ)) :
        MemSobolev (n : ℝ) 2
          (TemperedDistribution.smulLeftCLM ℂ
            (∂_{b i} ζ : 𝓢(ℂ, ℂ)) (∂_{b i} w)) := by
      apply ih
      have hd := hw.lineDerivOp (m := b i)
      apply hd.mono
      push_cast
      linarith
    have hcross (s : Finset (Fin (Module.finrank ℝ ℂ))) :
        MemSobolev (n : ℝ) 2
          (∑ i ∈ s, TemperedDistribution.smulLeftCLM ℂ
            (∂_{b i} ζ : 𝓢(ℂ, ℂ)) (∂_{b i} w)) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi hs =>
        simp only [Finset.sum_insert hi]
        exact (hterm i).add hs
    have hζΔw : MemSobolev (n : ℝ) 2
        (TemperedDistribution.smulLeftCLM ℂ ζ (Δ w)) := ih ζ (Δ w) hΔw
    have hΔprod : MemSobolev (n : ℝ) 2
        (Δ (TemperedDistribution.smulLeftCLM ℂ ζ w)) := by
      rw [complexDistribution_laplacian_smulLeft]
      exact (hΔζw.add ((hcross Finset.univ).smul (2 : ℂ))).add hζΔw
    convert complex_memSobolev_add_two_of_laplacian (n : ℝ)
      (TemperedDistribution.smulLeftCLM ℂ ζ w) hζw hΔprod using 1
    push_cast
    ring

/-- Uniform local two-order bootstrap at every integer level: one global
derivative beyond `Hⁿ`, together with `Hⁿ` control of the cutoff Laplacian,
gives `Hⁿ⁺²` after cutoff. All lower-order commutators are accounted for by
the proved integer-order Schwartz multiplier theorem. -/
theorem complexDistribution_memSobolev_nat_add_two_cutoff
    (n : ℕ) (ζ : 𝓢(ℂ, ℂ)) (w : 𝓢'(ℂ, ℂ))
    (hw : MemSobolev ((n : ℝ) + 1) 2 w)
    (hζΔ : MemSobolev (n : ℝ) 2
      (TemperedDistribution.smulLeftCLM ℂ ζ (Δ w))) :
    MemSobolev ((n : ℝ) + 2) 2
      (TemperedDistribution.smulLeftCLM ℂ ζ w) := by
  let b := stdOrthonormalBasis ℝ ℂ
  have hwₙ : MemSobolev (n : ℝ) 2 w := hw.mono (by linarith)
  have hζw := complexDistribution_memSobolev_nat_smulLeft n ζ w hwₙ
  have hΔζw := complexDistribution_memSobolev_nat_smulLeft n
    (Δ ζ : 𝓢(ℂ, ℂ)) w hwₙ
  have hterm (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev (n : ℝ) 2
        (TemperedDistribution.smulLeftCLM ℂ
          (∂_{b i} ζ : 𝓢(ℂ, ℂ)) (∂_{b i} w)) := by
    apply complexDistribution_memSobolev_nat_smulLeft n
    simpa only [add_sub_cancel_right] using (hw.lineDerivOp (m := b i))
  have hcross (s : Finset (Fin (Module.finrank ℝ ℂ))) :
      MemSobolev (n : ℝ) 2
        (∑ i ∈ s, TemperedDistribution.smulLeftCLM ℂ
          (∂_{b i} ζ : 𝓢(ℂ, ℂ)) (∂_{b i} w)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi hs =>
      simp only [Finset.sum_insert hi]
      exact (hterm i).add hs
  have hΔprod : MemSobolev (n : ℝ) 2
      (Δ (TemperedDistribution.smulLeftCLM ℂ ζ w)) := by
    rw [complexDistribution_laplacian_smulLeft]
    exact (hΔζw.add ((hcross Finset.univ).smul (2 : ℂ))).add hζΔ
  exact complex_memSobolev_add_two_of_laplacian (n : ℝ)
    (TemperedDistribution.smulLeftCLM ℂ ζ w) hζw hΔprod

#print axioms complexDistribution_memSobolev_nat_smulLeft
#print axioms complexDistribution_memSobolev_nat_add_two_cutoff

end

end SystolicGrowth
