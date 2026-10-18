module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIIDifferencing
public import CookMagyar.HuaTypeIIExceptionalFrequency

@[expose] public section

/-!
# Hua's mixed five-shift cubic phase

In Lemma 6.3 (printed pp. 70--71), three differences in the outer index
turn the ordered Type-II pair phase into a cubic in the variable inner
index; two further inner-index differences leave a linear phase. This
file verifies the exact cubic frequency, with the fixed paired index and
all arbitrary lower coefficients retained until they cancel. It is a
pointwise algebraic ingredient, not the repeated Cauchy inequality or a
bound on the resulting sums.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- The real phase of one ordered Type-II pair, before any difference. -/
noncomputable def huaTypeIIRealPairPolynomial
    (a q l w : ℕ) (b c d : ℝ) (u v : ℕ) : ℝ :=
  generalCubicPolynomial ((a : ℝ) / q) b c d (l * u * v) -
    generalCubicPolynomial ((a : ℝ) / q) b c d (l * u * w)

/-- One positive difference in the source's outer index. -/
def huaTypeIIOuterRealDifference (F : ℕ → ℕ → ℝ) (ξ : ℕ)
    (u v : ℕ) : ℝ := F (u + ξ) v - F u v

/-- One positive difference in the variable inner index, holding the
other member `w` of the ordered pair fixed. -/
def huaTypeIIInnerRealDifference (F : ℕ → ℕ → ℝ) (η : ℕ)
    (u v : ℕ) : ℝ := F u (v + η) - F u v

/-- Three outer differences of the *original* pair polynomial eliminate
all quadratic, linear, and constant coefficients. The fixed `w³` term
remains here and is canceled by the later inner differences. -/
theorem hua_typeII_threeOuterRealDifference_eq
    (a q l w u v ξ₁ ξ₂ ξ₃ : ℕ) (b c d : ℝ) :
    huaTypeIIOuterRealDifference
      (huaTypeIIOuterRealDifference
        (huaTypeIIOuterRealDifference
          (huaTypeIIRealPairPolynomial a q l w b c d) ξ₁) ξ₂) ξ₃ u v =
      6 * ((a : ℝ) / q) * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃ *
        ((v : ℝ) ^ 3 - (w : ℝ) ^ 3) := by
  unfold huaTypeIIOuterRealDifference huaTypeIIRealPairPolynomial
    generalCubicPolynomial
  push_cast
  ring

/-- The source's mixed five-shift polynomial: three outer shifts
`ξ₁,ξ₂,ξ₃` followed by two variable-inner shifts `η₁,η₂` produce a
linear function of `v` with exact slope
`(a/q)*36*l³*ξ₁*ξ₂*ξ₃*η₁*η₂`. The held `w` and all lower original
coefficients have canceled, but the shift-dependent constant remains. -/
theorem hua_typeII_mixed_fiveShift_realPhase_eq_linear
    (a q l w u v ξ₁ ξ₂ ξ₃ η₁ η₂ : ℕ) (b c d : ℝ) :
    let F := huaTypeIIRealPairPolynomial a q l w b c d
    let G := huaTypeIIOuterRealDifference
      (huaTypeIIOuterRealDifference
        (huaTypeIIOuterRealDifference F ξ₁) ξ₂) ξ₃
    huaTypeIIInnerRealDifference
      (huaTypeIIInnerRealDifference G η₁) η₂ u v =
      ((a : ℝ) / q) * (36 * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₁ * η₂) * v +
        ((a : ℝ) / q) *
          (18 * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₁ * η₂ * (η₁ + η₂)) := by
  dsimp only
  unfold huaTypeIIInnerRealDifference
  rw [hua_typeII_threeOuterRealDifference_eq a q l w u (v + η₂ + η₁) ξ₁ ξ₂ ξ₃ b c d,
    hua_typeII_threeOuterRealDifference_eq a q l w u (v + η₂) ξ₁ ξ₂ ξ₃ b c d,
    hua_typeII_threeOuterRealDifference_eq a q l w u (v + η₁) ξ₁ ξ₂ ξ₃ b c d,
    hua_typeII_threeOuterRealDifference_eq a q l w u v ξ₁ ξ₂ ξ₃ b c d]
  push_cast
  ring

/-- Exponentiating the mixed real difference gives precisely the linear
complex cubic-phase specialization whose leading frequency is used in
Hua's fifth-shift divisor count. -/
theorem hua_typeII_mixed_fiveShift_phase_eq_linear
    (a q l w u v ξ₁ ξ₂ ξ₃ η₁ η₂ : ℕ) (b c d : ℝ) :
    let F := huaTypeIIRealPairPolynomial a q l w b c d
    let G := huaTypeIIOuterRealDifference
      (huaTypeIIOuterRealDifference
        (huaTypeIIOuterRealDifference F ξ₁) ξ₂) ξ₃
    Complex.exp (((2 * Real.pi *
      huaTypeIIInnerRealDifference
        (huaTypeIIInnerRealDifference G η₁) η₂ u v : ℝ) : ℂ) * Complex.I) =
      generalCubicPhase 0 0
        (((huaTypeIICubicShiftFrequency l
          (ξ₁, ξ₂, ξ₃, η₁, η₂) : ℕ) : ℝ) * ((a : ℝ) / q))
        (((a : ℝ) / q) *
          (18 * (l : ℝ) ^ 3 * ξ₁ * ξ₂ * ξ₃ * η₁ * η₂ * (η₁ + η₂))) v := by
  dsimp only
  rw [hua_typeII_mixed_fiveShift_realPhase_eq_linear
    a q l w u v ξ₁ ξ₂ ξ₃ η₁ η₂ b c d]
  unfold generalCubicPhase generalCubicPolynomial huaTypeIICubicShiftFrequency
  congr 1
  push_cast
  ring

#print axioms hua_typeII_threeOuterRealDifference_eq
#print axioms hua_typeII_mixed_fiveShift_realPhase_eq_linear
#print axioms hua_typeII_mixed_fiveShift_phase_eq_linear

end SystolicGrowth.CookMagyarCircle
