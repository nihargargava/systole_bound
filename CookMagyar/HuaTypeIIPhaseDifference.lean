module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.GeneralCubicWeyl

@[expose] public section

/-!
# Polynomial identity for Hua's off-diagonal Type-II phase

For distinct inner indices, the product of one phase with the conjugate of
another becomes a cubic phase in the outer index. This file proves the exact
polynomial coefficient calculation independently of the later divisor and
oscillatory estimates.
-/

open ComplexConjugate

namespace SystolicGrowth.CookMagyarCircle

/-- The constant coefficient cancels, and the leading coefficient is the
fixed rational leading coefficient multiplied by `l³(v³-w³)`. -/
theorem hua_typeII_polynomial_difference
    (a b c d : ℝ) (l u v w : ℕ) :
    generalCubicPolynomial a b c d (l * u * v) -
        generalCubicPolynomial a b c d (l * u * w) =
      generalCubicPolynomial
        (a * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
        (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
        (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u := by
  simp only [generalCubicPolynomial, Nat.cast_mul]
  ring

/-- Off-diagonal phase terms are an ordinary cubic phase in the outer
variable, with no constant coefficient. This exposes the frequency to which
Hua's divisor and differencing bounds must be applied. -/
theorem hua_typeII_phase_mul_conj
    (a b c d : ℝ) (l u v w : ℕ) :
    generalCubicPhase a b c d (l * u * v) *
        conj (generalCubicPhase a b c d (l * u * w)) =
      generalCubicPhase
        (a * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3))
        (b * (l : ℝ) ^ 2 * ((v : ℝ) ^ 2 - (w : ℝ) ^ 2))
        (c * (l : ℝ) * ((v : ℝ) - (w : ℝ))) 0 u := by
  unfold generalCubicPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul]
  simp
  simp only [map_ofNat]
  have hpoly := hua_typeII_polynomial_difference a b c d l u v w
  rw [← hpoly]
  push_cast
  ring

#print axioms hua_typeII_polynomial_difference
#print axioms hua_typeII_phase_mul_conj

end SystolicGrowth.CookMagyarCircle
