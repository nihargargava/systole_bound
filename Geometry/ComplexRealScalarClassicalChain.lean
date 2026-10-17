module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Classical real-scalar chain rule in complex coordinates

The scalar nonlinearity and its coefficient are genuine classical
compositions. The directional formula is obtained from their actual
Fréchet derivatives, including the real-to-complex linear embedding.
-/

open scoped ContDiff

namespace SystolicGrowth

noncomputable section

/-- **Math.** The literal real scalar composition, regarded as a
complex-valued function, has the SAME classical differentiability order. -/
theorem complexRealScalar_contDiff_comp {r : ℕ∞ω}
    (u : ℂ → ℝ) (Ψ : ℝ → ℝ) (hu : ContDiff ℝ r u) (hΨ : ContDiff ℝ r Ψ) :
    ContDiff ℝ r (fun z : ℂ => (Ψ (u z) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (hΨ.comp hu)

/-- **Math.** The actual `C¹` chain rule gives the exact directional
Fréchet derivative of the literal complex-valued scalar composition. -/
theorem complexRealScalar_fderiv_comp
    (u : ℂ → ℝ) (Ψ : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hΨ : ContDiff ℝ 1 Ψ)
    (z d : ℂ) :
    fderiv ℝ (fun q : ℂ => (Ψ (u q) : ℂ)) z d =
      ((deriv Ψ (u z) : ℝ) : ℂ) * ((fderiv ℝ u z d : ℝ) : ℂ) := by
  have hψD := (hΨ.differentiable (by norm_num) (u z)).hasDerivAt
  have huD := (hu.differentiable (by norm_num) z).hasFDerivAt
  have hD := Complex.ofRealCLM.hasFDerivAt.comp z (hψD.hasFDerivAt.comp z huD)
  have hDf := hD.fderiv
  change fderiv ℝ (fun q : ℂ => (Ψ (u q) : ℂ)) z = _ at hDf
  rw [hDf]
  simp [ContinuousLinearMap.comp_apply, Complex.ofReal_mul, mul_comm]

/-- **Math.** The literal first-derivative coefficient of a `C²` scalar
nonlinearity is `C¹` when composed with a real `C¹` coordinate function. -/
theorem complexRealScalar_deriv_contDiff_comp
    (u : ℂ → ℝ) (Ψ : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hΨ : ContDiff ℝ 2 Ψ) :
    ContDiff ℝ 1 (fun z : ℂ => ((deriv Ψ (u z) : ℝ) : ℂ)) := by
  apply complexRealScalar_contDiff_comp u (deriv Ψ) hu
  exact hΨ.deriv'

#print axioms complexRealScalar_contDiff_comp
#print axioms complexRealScalar_fderiv_comp
#print axioms complexRealScalar_deriv_contDiff_comp

end

end SystolicGrowth
