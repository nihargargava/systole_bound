module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexCompactClassicalMultiplier
public import Geometry.ComplexRealScalarClassicalChain

@[expose] public section

/-!
# All-order Sobolev gain for the actual nonlinear cutoff

The literal classical derivative splits into a compact classical term
and a compact classical coefficient times the actual derivative field.
The genuine compact multiplier theorem gives the derivative Sobolev order,
and the Fourier first-derivative criterion yields the additional order.
-/

open MeasureTheory TemperedDistribution
open scoped ContDiff LineDeriv SchwartzMap

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Math.** A compact classical `Cᵏ` function gains a genuine Sobolev
order from its ACTUAL derivative splitting into compact `Cᵏ` terms and
compact `Cᵏ` multipliers of `Hᵏ` derivative fields. The conclusion is
derived by integration by parts and Fourier gain, not assumed. -/
theorem complexCompactClassical_memSobolev_add_one_of_derivative_split
    (k : ℕ) (hk : 1 ≤ k)
    (f : ℂ → ℂ) (hf : ContDiff ℝ (k : ℕ) f) (hfc : HasCompactSupport f)
    (A : Fin (Module.finrank ℝ ℂ) → ℂ → ℂ)
    (hA : ∀ i, ContDiff ℝ (k : ℕ) (A i)) (hAc : ∀ i, HasCompactSupport (A i))
    (a : ℂ → ℂ) (ha : ContDiff ℝ (k : ℕ) a) (hac : HasCompactSupport a)
    (G : Fin (Module.finrank ℝ ℂ) → Lp ℂ 2 (volume : Measure ℂ))
    (hG : ∀ i, MemSobolev (k : ℝ) 2 (G i : 𝓢'(ℂ, ℂ)))
    (hdf : ∀ i, (fun z => fderiv ℝ f z ((stdOrthonormalBasis ℝ ℂ) i))
      =ᵐ[volume] (fun z => A i z + a z * G i z)) :
    MemSobolev ((k : ℝ) + 1) 2
      (complexCompactFunctionL2 f hf.continuous hfc : 𝓢'(ℂ, ℂ)) := by
  let U := complexCompactFunctionL2 f hf.continuous hfc
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast hk)
  have hUSob : MemSobolev (k : ℝ) 2 (U : 𝓢'(ℂ, ℂ)) :=
    complexCompactFunctionL2_memSobolev k f hf hfc
  have hDSob (i : Fin (Module.finrank ℝ ℂ)) :
      MemSobolev (k : ℝ) 2 (∂_{(stdOrthonormalBasis ℝ ℂ) i} (U : 𝓢'(ℂ, ℂ))) := by
    let d := (stdOrthonormalBasis ℝ ℂ) i
    have hDf : ContDiff ℝ 0 (fun z => fderiv ℝ f z d) :=
      (hf1.fderiv_right (show (0 : ℕ∞ω) + 1 ≤ 1 by norm_num)).clm_apply contDiff_const
    have hDfc : HasCompactSupport (fun z => fderiv ℝ f z d) := hfc.fderiv_apply ℝ d
    let DU := complexCompactFunctionL2 (fun z => fderiv ℝ f z d) hDf.continuous hDfc
    let AU := complexCompactFunctionL2 (A i) (hA i).continuous (hAc i)
    obtain ⟨BU, hBU, hBUSob⟩ := complex_L2_mul_compact_contDiff_memSobolev_nat k (G i) (hG i) a ha hac
    have hDU : (DU : ℂ → ℂ) =ᵐ[volume] (fun z => fderiv ℝ f z d) :=
      complexCompactFunctionL2_coeFn _ hDf.continuous hDfc
    have hAU : (AU : ℂ → ℂ) =ᵐ[volume] A i := complexCompactFunctionL2_coeFn _ (hA i).continuous (hAc i)
    have hsum : DU = AU + BU := by
      apply Lp.ext
      filter_upwards [hDU, hAU, hBU, Lp.coeFn_add AU BU, hdf i] with z hDUz hAUz hBUz hadd hdz
      rw [hDUz, hadd, Pi.add_apply, hAUz, hBUz]
      exact hdz
    have hderiv := complex_L2_lineDeriv_eq_of_compact_C1 f hf1 hfc U DU d
      (complexCompactFunctionL2_coeFn f hf.continuous hfc) hDU
    rw [hderiv, hsum]
    have hAdd : ((AU + BU : Lp ℂ 2 (volume : Measure ℂ)) : 𝓢'(ℂ, ℂ)) =
        (AU : 𝓢'(ℂ, ℂ)) + (BU : 𝓢'(ℂ, ℂ)) :=
      (Lp.toTemperedDistributionCLM ℂ volume 2).map_add AU BU
    rw [hAdd]
    exact (complexCompactFunctionL2_memSobolev k (A i) (hA i) (hAc i)).add hBUSob
  exact complex_memSobolev_add_one_of_lineDerivs (k : ℝ) (U : 𝓢'(ℂ, ℂ)) hUSob hDSob

/-- **Math.** The literal compact nonlinear forcing gains one Sobolev
order at EVERY finite level. Its coefficient derivatives and exact
directional formula follow from the actual classical chain rule; only
the already controlled derivative fields are supplied as Sobolev inputs. -/
theorem complexRealScalar_compactCutoff_memSobolev_add_one
    (k : ℕ) (hk : 1 ≤ k) (u : ℂ → ℝ) (hu : ContDiff ℝ (k : ℕ) u)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (k + 1 : ℕ) Ψ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ (k + 1 : ℕ) χ) (hχc : HasCompactSupport χ)
    (G : Fin (Module.finrank ℝ ℂ) → Lp ℂ 2 (volume : Measure ℂ))
    (hG : ∀ i, G i =ᵐ[volume]
      (fun z => ((fderiv ℝ u z ((stdOrthonormalBasis ℝ ℂ) i) : ℝ) : ℂ)))
    (hGSob : ∀ i, MemSobolev (k : ℝ) 2 (G i : 𝓢'(ℂ, ℂ))) :
    ∃ U : Lp ℂ 2 (volume : Measure ℂ),
      U =ᵐ[volume] (fun z => χ z * ((Ψ (u z) : ℝ) : ℂ)) ∧
        MemSobolev ((k : ℝ) + 1) 2 (U : 𝓢'(ℂ, ℂ)) := by
  let b := stdOrthonormalBasis ℝ ℂ
  let f : ℂ → ℂ := fun z => χ z * ((Ψ (u z) : ℝ) : ℂ)
  let A : Fin (Module.finrank ℝ ℂ) → ℂ → ℂ := fun i z =>
    fderiv ℝ χ z (b i) * ((Ψ (u z) : ℝ) : ℂ)
  let a : ℂ → ℂ := fun z => χ z * ((deriv Ψ (u z) : ℝ) : ℂ)
  have hle : (k : ℕ∞ω) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
  have hχk : ContDiff ℝ (k : ℕ) χ := hχ.of_le hle
  have hΨk : ContDiff ℝ (k : ℕ) Ψ := hΨ.of_le hle
  have hcomp : ContDiff ℝ (k : ℕ) (fun z : ℂ => ((Ψ (u z) : ℝ) : ℂ)) :=
    complexRealScalar_contDiff_comp u Ψ hu hΨk
  have hf : ContDiff ℝ (k : ℕ) f := hχk.mul hcomp
  have hfc : HasCompactSupport f := hχc.mul_right
  have hA (i : Fin (Module.finrank ℝ ℂ)) : ContDiff ℝ (k : ℕ) (A i) :=
    ((hχ.fderiv_right (by simp only [Nat.cast_add, Nat.cast_one]; exact le_rfl)).clm_apply contDiff_const).mul hcomp
  have hAc (i : Fin (Module.finrank ℝ ℂ)) : HasCompactSupport (A i) := (hχc.fderiv_apply ℝ (b i)).mul_right
  have hΨsucc : ContDiff ℝ ((k : ℕ∞ω) + 1) Ψ := by simpa only [Nat.cast_add, Nat.cast_one] using hΨ
  have hΨderiv : ContDiff ℝ (k : ℕ) (deriv Ψ) := hΨsucc.deriv'
  have ha : ContDiff ℝ (k : ℕ) a := hχk.mul (complexRealScalar_contDiff_comp u (deriv Ψ) hu hΨderiv)
  have hac : HasCompactSupport a := hχc.mul_right
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast hk)
  have hχ1 : ContDiff ℝ 1 χ := hχk.of_le (by exact_mod_cast hk)
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨk.of_le (by exact_mod_cast hk)
  have hcomp1 : ContDiff ℝ 1 (fun z : ℂ => ((Ψ (u z) : ℝ) : ℂ)) := hcomp.of_le (by exact_mod_cast hk)
  have hdf (i : Fin (Module.finrank ℝ ℂ)) :
      (fun z => fderiv ℝ f z (b i)) =ᵐ[volume] (fun z => A i z + a z * G i z) := by
    filter_upwards [hG i] with z hz
    change fderiv ℝ (fun q => χ q * ((Ψ (u q) : ℝ) : ℂ)) z (b i) = _
    rw [fderiv_fun_mul (hχ1.differentiable (by norm_num) z) (hcomp1.differentiable (by norm_num) z)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [complexRealScalar_fderiv_comp u Ψ hu1 hΨ1 z (b i), hz]
    dsimp [A, a]
    ring
  let U := complexCompactFunctionL2 f hf.continuous hfc
  exact ⟨U, complexCompactFunctionL2_coeFn f hf.continuous hfc,
    complexCompactClassical_memSobolev_add_one_of_derivative_split k hk f hf hfc A hA hAc a ha hac G hGSob hdf⟩

/-- **Math.** An ACTUAL nonlinear forcing vector in the local weak PDE
inherits this derived regularity from its a.e. literal cutoff expression. -/
theorem complexRealScalar_actualCutoff_memSobolev_add_one
    (k : ℕ) (hk : 1 ≤ k) (u : ℂ → ℝ) (hu : ContDiff ℝ (k : ℕ) u)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ (k + 1 : ℕ) Ψ)
    (χ : ℂ → ℂ) (hχ : ContDiff ℝ (k + 1 : ℕ) χ) (hχc : HasCompactSupport χ)
    (G : Fin (Module.finrank ℝ ℂ) → Lp ℂ 2 (volume : Measure ℂ))
    (hG : ∀ i, G i =ᵐ[volume]
      (fun z => ((fderiv ℝ u z ((stdOrthonormalBasis ℝ ℂ) i) : ℝ) : ℂ)))
    (hGSob : ∀ i, MemSobolev (k : ℝ) 2 (G i : 𝓢'(ℂ, ℂ)))
    (U : Lp ℂ 2 (volume : Measure ℂ))
    (hU : U =ᵐ[volume] (fun z => χ z * ((Ψ (u z) : ℝ) : ℂ))) :
    MemSobolev ((k : ℝ) + 1) 2 (U : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨V, hV, hs⟩ := complexRealScalar_compactCutoff_memSobolev_add_one k hk u hu Ψ hΨ χ hχ hχc G hG hGSob
  have heq : V = U := Lp.ext (hV.trans hU.symm)
  rw [heq] at hs
  exact hs

#print axioms complexCompactClassical_memSobolev_add_one_of_derivative_split
#print axioms complexRealScalar_compactCutoff_memSobolev_add_one
#print axioms complexRealScalar_actualCutoff_memSobolev_add_one

end

end SystolicGrowth
