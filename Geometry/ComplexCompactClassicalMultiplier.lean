module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ComplexC1WeakProductRule
public import Geometry.ComplexCompactClassicalSobolev

@[expose] public section

/-!
# Compact classical coefficients preserve integer Sobolev regularity

The product is its actual `L²` function, so no multiplication of an
arbitrary distribution by a merely finitely differentiable function is
postulated. Higher regularity follows by induction, using the genuine
first weak Leibniz rule and the Fourier first-derivative criterion.
-/

open TemperedDistribution MeasureTheory
open scoped ContDiff SchwartzMap LineDeriv

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- **Math.** A compact `Cᵏ` coefficient times an ACTUAL `L²`-represented
`Hᵏ` field produces the genuine `L²` product in `Hᵏ`, for every natural
order. All weak derivative representatives are constructed from the
input Sobolev witness; no product regularity is assumed. -/
theorem complex_L2_mul_compact_contDiff_memSobolev_nat
    (k : ℕ) (F : Lp ℂ 2 (volume : Measure ℂ))
    (hF : MemSobolev (k : ℝ) 2 (F : 𝓢'(ℂ, ℂ)))
    (a : ℂ → ℂ) (ha : ContDiff ℝ (k : ℕ) a) (hac : HasCompactSupport a) :
    ∃ AF : Lp ℂ 2 (volume : Measure ℂ),
      (AF : ℂ → ℂ) =ᵐ[volume] (fun z => a z * F z) ∧
        MemSobolev (k : ℝ) 2 (AF : 𝓢'(ℂ, ℂ)) := by
  induction k generalizing F a with
  | zero =>
    have haTop : MemLp a ⊤ (volume : Measure ℂ) :=
      ha.continuous.memLp_top_of_hasCompactSupport hac volume
    have hAFm : MemLp (fun z => a z * F z) 2 (volume : Measure ℂ) :=
      haTop.fun_mul (Lp.memLp F)
    let AF := hAFm.toLp (fun z => a z * F z)
    refine ⟨AF, hAFm.coeFn_toLp, ?_⟩
    simpa only [Nat.cast_zero] using
      (memSobolev_zero_iff.mpr ⟨AF, rfl⟩ : MemSobolev 0 2 (AF : 𝓢'(ℂ, ℂ)))
  | succ k ih =>
    have hle : (k : ℕ∞ω) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
    have haLow : ContDiff ℝ (k : ℕ) a := ha.of_le hle
    have haOne : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast Nat.succ_pos k)
    have hFLow : MemSobolev (k : ℝ) 2 (F : 𝓢'(ℂ, ℂ)) := hF.mono (by push_cast; linarith)
    obtain ⟨AF, hAF, hAFSob⟩ := ih F hFLow a haLow hac
    have hD (i : Fin (Module.finrank ℝ ℂ)) :
        MemSobolev (k : ℝ) 2
          (∂_{(stdOrthonormalBasis ℝ ℂ) i} (AF : 𝓢'(ℂ, ℂ))) := by
      let d := (stdOrthonormalBasis ℝ ℂ) i
      have hFD : MemSobolev (k : ℝ) 2 (∂_{d} (F : 𝓢'(ℂ, ℂ))) := by
        simpa only [Nat.cast_succ, add_sub_cancel_right] using hF.lineDerivOp (m := d)
      have hFDZero : MemSobolev 0 2 (∂_{d} (F : 𝓢'(ℂ, ℂ))) :=
        hFD.mono (Nat.cast_nonneg k)
      obtain ⟨G, hG⟩ := memSobolev_zero_iff.mp hFDZero
      have hGSob : MemSobolev (k : ℝ) 2 (G : 𝓢'(ℂ, ℂ)) := by rw [← hG]; exact hFD
      obtain ⟨AG, hAG, hAGSob⟩ := ih G hGSob a haLow hac
      have hDa : ContDiff ℝ (k : ℕ) (fun z => fderiv ℝ a z d) :=
        (ha.fderiv_right (by simp only [Nat.cast_add, Nat.cast_one]; exact le_rfl)).clm_apply contDiff_const
      have hDac : HasCompactSupport (fun z => fderiv ℝ a z d) := hac.fderiv_apply ℝ d
      obtain ⟨ADF, hADF, hADFSob⟩ := ih F hFLow (fun z => fderiv ℝ a z d) hDa hDac
      have hprod := complex_L2_lineDeriv_mul_compact_C1 F G AF AG ADF a haOne hac d hG hAF hAG hADF
      rw [hprod]
      exact hAGSob.add hADFSob
    refine ⟨AF, hAF, ?_⟩
    simpa only [Nat.cast_succ] using
      complex_memSobolev_add_one_of_lineDerivs (k : ℝ) (AF : 𝓢'(ℂ, ℂ)) hAFSob hD

/-- **Math.** The actual product vector already appearing in an equation
inherits the constructed higher regularity through its a.e. identification
with the literal compact-coefficient product. -/
theorem complex_L2_product_memSobolev_of_compact_contDiff
    (k : ℕ) (F AF : Lp ℂ 2 (volume : Measure ℂ))
    (hF : MemSobolev (k : ℝ) 2 (F : 𝓢'(ℂ, ℂ)))
    (a : ℂ → ℂ) (ha : ContDiff ℝ (k : ℕ) a) (hac : HasCompactSupport a)
    (hAF : (AF : ℂ → ℂ) =ᵐ[volume] (fun z => a z * F z)) :
    MemSobolev (k : ℝ) 2 (AF : 𝓢'(ℂ, ℂ)) := by
  obtain ⟨AF', hAF', hs⟩ := complex_L2_mul_compact_contDiff_memSobolev_nat k F hF a ha hac
  have heq : AF' = AF := Lp.ext (hAF'.trans hAF.symm)
  rw [heq] at hs
  exact hs

#print axioms complex_L2_mul_compact_contDiff_memSobolev_nat
#print axioms complex_L2_product_memSobolev_of_compact_contDiff

end

end SystolicGrowth
