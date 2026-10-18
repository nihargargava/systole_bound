module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexSobolevEllipticRegularity
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

@[expose] public section

/-!
# Genuine Sobolev distributions from compact classical functions

The first-derivative Sobolev criterion follows from the actual Fourier
Laplacian gain. Compact classical functions determine their genuine `L²`
representatives, and integration by parts identifies their distributional
derivatives with the corresponding classical `L²` derivatives.
-/

open TemperedDistribution MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv Laplacian

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Math.** A distribution and all first basis derivatives in `Hˢ`
give one genuine additional Sobolev order. This is derived from the
Fourier/Laplacian gain at `s - 1`, not assumed as a characterization. -/
theorem complex_memSobolev_add_one_of_lineDerivs
    (s : ℝ) (w : 𝓢'(ℂ, ℂ)) (hw : MemSobolev s 2 w)
    (hD : ∀ i : Fin (Module.finrank ℝ ℂ),
      MemSobolev s 2 (∂_{(stdOrthonormalBasis ℝ ℂ) i} w)) :
    MemSobolev (s + 1) 2 w := by
  let b := stdOrthonormalBasis ℝ ℂ
  have hw' : MemSobolev (s - 1) 2 w := hw.mono (by linarith)
  have hterm (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev (s - 1) 2 (∂_{b i} (∂_{b i} w)) :=
    (hD i).lineDerivOp (m := b i)
  have hsum (t : Finset (Fin (Module.finrank ℝ ℂ))) :
      MemSobolev (s - 1) 2 (∑ i ∈ t, ∂_{b i} (∂_{b i} w)) := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hLap : MemSobolev (s - 1) 2 (Δ w) := by
    rw [TemperedDistribution.laplacian_eq_sum b]
    exact hsum Finset.univ
  convert complex_memSobolev_add_two_of_laplacian (s - 1) w hw' hLap using 1
  ring

/-- **Math.** A continuous compactly supported classical function has an
actual `L²` representative, constructed from its genuine integrability. -/
def complexCompactFunctionL2 (f : ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Lp ℂ 2 (volume : Measure ℂ) :=
  (hf.memLp_of_hasCompactSupport hc).toLp f

theorem complexCompactFunctionL2_coeFn (f : ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (complexCompactFunctionL2 f hf hc : ℂ → ℂ) =ᵐ[volume] f :=
  (hf.memLp_of_hasCompactSupport hc).coeFn_toLp

/-- **Math.** Genuine integration by parts against arbitrary Schwartz
tests identifies the first distributional derivative of a compact `C¹`
function with the `L²` representative of its literal classical derivative. -/
theorem complex_L2_lineDeriv_eq_of_compact_C1
    (f : ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (u du : Lp ℂ 2 (volume : Measure ℂ)) (d : ℂ)
    (hu : (u : ℂ → ℂ) =ᵐ[volume] f)
    (hdu : (du : ℂ → ℂ) =ᵐ[volume] (fun x => fderiv ℝ f x d)) :
    (∂_{d} (u : 𝓢'(ℂ, ℂ))) = (du : 𝓢'(ℂ, ℂ)) := by
  have hDf : ContDiff ℝ 0 (fun x => fderiv ℝ f x d) :=
    (hf.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply contDiff_const
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul, neg_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hprod₁ : Integrable (fun x => fderiv ℝ f x d * φ x) :=
    (hDf.continuous.mul φ.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ d).mul_right
  have hprod₂ : Integrable (fun x => f x * fderiv ℝ φ x d) :=
    (hf.continuous.mul (((φ.smooth ⊤).fderiv_right
      (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).clm_apply contDiff_const).continuous).integrable_of_hasCompactSupport hc.mul_right
  have hprod₀ : Integrable (fun x => f x * φ x) :=
    (hf.continuous.mul φ.continuous).integrable_of_hasCompactSupport hc.mul_right
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hprod₁ hprod₂ hprod₀
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => φ.differentiableAt (x := x))
  calc
    (∫ x : ℂ, -fderiv ℝ φ x d * u x) = ∫ x : ℂ, -fderiv ℝ φ x d * f x := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
    _ = -(∫ x : ℂ, f x * fderiv ℝ φ x d) := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    _ = ∫ x : ℂ, fderiv ℝ f x d * φ x := by rw [hIBP, neg_neg]
    _ = ∫ x : ℂ, φ x * du x := by
      apply integral_congr_ae
      filter_upwards [hdu] with x hx
      rw [hx, mul_comm]

/-- **Math.** Every genuinely compactly supported classical `Cᵏ`
function belongs to integer Sobolev order `k` as its ACTUAL `L²` tempered
distribution. No high-order Sobolev hypothesis is supplied. -/
theorem complexCompactFunctionL2_memSobolev
    (k : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℝ (k : ℕ) f) (hc : HasCompactSupport f) :
    MemSobolev (k : ℝ) 2 (complexCompactFunctionL2 f hf.continuous hc : 𝓢'(ℂ, ℂ)) := by
  induction k generalizing f with
  | zero =>
    simpa only [Nat.cast_zero] using
      (memSobolev_zero_iff.mpr ⟨complexCompactFunctionL2 f hf.continuous hc, rfl⟩ :
        MemSobolev 0 2 (complexCompactFunctionL2 f hf.continuous hc : 𝓢'(ℂ, ℂ)))
  | succ k ih =>
    have hle : (k : ℕ∞ω) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
    have hlow : ContDiff ℝ (k : ℕ) f := hf.of_le hle
    have hfirst : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.succ_pos k)
    have hprev := ih f hlow hc
    have hD (i : Fin (Module.finrank ℝ ℂ)) :
        MemSobolev (k : ℝ) 2
          (∂_{(stdOrthonormalBasis ℝ ℂ) i}
            (complexCompactFunctionL2 f hf.continuous hc : 𝓢'(ℂ, ℂ))) := by
      let d := (stdOrthonormalBasis ℝ ℂ) i
      have hd : ContDiff ℝ (k : ℕ) (fun x => fderiv ℝ f x d) :=
        (hf.fderiv_right (by simp only [Nat.cast_add, Nat.cast_one]; exact le_rfl)).clm_apply contDiff_const
      have hdc : HasCompactSupport (fun x => fderiv ℝ f x d) := hc.fderiv_apply ℝ d
      have hderiv := complex_L2_lineDeriv_eq_of_compact_C1 f hfirst hc
        (complexCompactFunctionL2 f hf.continuous hc)
        (complexCompactFunctionL2 (fun x => fderiv ℝ f x d) hd.continuous hdc) d
        (complexCompactFunctionL2_coeFn f hf.continuous hc)
        (complexCompactFunctionL2_coeFn _ hd.continuous hdc)
      rw [hderiv]
      exact ih _ hd hdc
    simpa only [Nat.cast_succ] using
      complex_memSobolev_add_one_of_lineDerivs (k : ℝ)
        (complexCompactFunctionL2 f hf.continuous hc) hprev hD

/-- **Math.** The constructed Sobolev witness is the actual classical
function almost everywhere, not merely an unrelated distribution. -/
theorem exists_complexCompactClassical_sobolev_representation
    (k : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℝ (k : ℕ) f) (hc : HasCompactSupport f) :
    ∃ u : Lp ℂ 2 (volume : Measure ℂ),
      (u : ℂ → ℂ) =ᵐ[volume] f ∧ MemSobolev (k : ℝ) 2 (u : 𝓢'(ℂ, ℂ)) :=
  ⟨complexCompactFunctionL2 f hf.continuous hc,
    complexCompactFunctionL2_coeFn f hf.continuous hc,
    complexCompactFunctionL2_memSobolev k f hf hc⟩

/-- **Math.** Any ACTUAL `L²` value a.e. represented by the compact
classical function inherits the derived integer Sobolev regularity.
This applies directly to the localized forcing vector in the weak PDE. -/
theorem complex_L2_memSobolev_of_compact_classical_representative
    (k : ℕ) (u : Lp ℂ 2 (volume : Measure ℂ)) (f : ℂ → ℂ)
    (hf : ContDiff ℝ (k : ℕ) f) (hc : HasCompactSupport f)
    (hu : (u : ℂ → ℂ) =ᵐ[volume] f) : MemSobolev (k : ℝ) 2 (u : 𝓢'(ℂ, ℂ)) := by
  have heq : u = complexCompactFunctionL2 f hf.continuous hc :=
    Lp.ext (hu.trans (complexCompactFunctionL2_coeFn f hf.continuous hc).symm)
  rw [heq]
  exact complexCompactFunctionL2_memSobolev k f hf hc

#print axioms complex_memSobolev_add_one_of_lineDerivs
#print axioms complex_L2_lineDeriv_eq_of_compact_C1
#print axioms complexCompactFunctionL2_memSobolev
#print axioms exists_complexCompactClassical_sobolev_representation
#print axioms complex_L2_memSobolev_of_compact_classical_representative

end

end SystolicGrowth
