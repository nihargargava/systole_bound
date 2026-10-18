module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.Local

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # Nonsingular local solutions

The four-variable local-solubility theorem supplies the nonzero coordinates.
For five or more variables, an additional coordinate equal to `1` both leaves
the equation unchanged and makes the solution nonsingular: `1 ^ 3 - 1 = 0`,
whereas the derivative at `1` is `2`.
-/

/-- The derivative of the cubic map `x ↦ x ^ 3 - x`. -/
def cubicDerivative {q : ℕ} (x : ZMod q) : ZMod q :=
  3 * x ^ 2 - 1

/-- The concrete derivative agrees with the formal polynomial derivative. -/
@[simp] theorem eval_derivative_cubicPolynomial {q : ℕ} (x : ZMod q) :
    Polynomial.eval x (Polynomial.derivative (cubicPolynomial q)) =
      cubicDerivative x := by
  simp [cubicPolynomial, cubicDerivative]
  ring

/-- A solution in unit coordinates, nonsingular at at least one coordinate. -/
structure NonsingularUnitSolution (q n : ℕ) (t : ZMod q) where
  /-- The coordinates of the solution. -/
  point : Fin n → ZMod q
  /-- Every coordinate is a unit modulo `q`. -/
  isUnit_point : ∀ i, IsUnit (point i)
  /-- The diagonal cubic equation. -/
  equation : ∑ i, cubicResidue (point i) = t
  /-- At least one partial derivative is nonzero. -/
  nonsingular : ∃ i, cubicDerivative (point i) ≠ 0

/-- The derivative at the padding value `1` is nonzero modulo every `q ≥ 5`. -/
theorem cubicDerivative_one_ne_zero {q : ℕ} (hq5 : 5 ≤ q) :
    cubicDerivative (1 : ZMod q) ≠ 0 := by
  have hderivative : cubicDerivative (1 : ZMod q) = (2 : ZMod q) := by
    norm_num [cubicDerivative]
  rw [hderivative]
  intro hzero
  have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hzero
  have hq2 : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  omega

/-- Prepending the padding value `1` preserves the equation and gives an
explicit nonsingular coordinate. -/
def NonsingularUnitSolution.padOne {q n : ℕ} {t : ZMod q}
    (solution : NonsingularUnitSolution q n t) (hq5 : 5 ≤ q) :
    NonsingularUnitSolution q (n + 1) t where
  point := Fin.cons 1 solution.point
  isUnit_point := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact isUnit_one
    · simpa using solution.isUnit_point j
  equation := by
    rw [Fin.sum_univ_succ]
    simpa [cubicResidue] using solution.equation
  nonsingular := by
    refine ⟨0, ?_⟩
    simpa using cubicDerivative_one_ne_zero hq5

/-- A four-variable unit solution, padded by `1`, gives a nonsingular
five-variable solution. -/
theorem nonsingularUnitSolution_five {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (t : ZMod q) : Nonempty (NonsingularUnitSolution q 5 t) := by
  letI : Fact q.Prime := ⟨hq⟩
  rcases four_nonzero_cubic_surjective hq hq5 t with
    ⟨x₁, x₂, x₃, x₄, hx₁, hx₂, hx₃, hx₄, hequation⟩
  let point : Fin 5 → ZMod q :=
    Fin.cons 1 (Fin.cons x₁ (Fin.cons x₂ (Fin.cons x₃ (Fin.cons x₄ Fin.elim0))))
  refine ⟨{
    point := point
    isUnit_point := ?_
    equation := ?_
    nonsingular := ?_
  }⟩
  · intro i
    refine Fin.cases isUnit_one (fun i₁ ↦ ?_) i
    refine Fin.cases (isUnit_iff_ne_zero.mpr hx₁) (fun i₂ ↦ ?_) i₁
    refine Fin.cases (isUnit_iff_ne_zero.mpr hx₂) (fun i₃ ↦ ?_) i₂
    refine Fin.cases (isUnit_iff_ne_zero.mpr hx₃) (fun i₄ ↦ ?_) i₃
    exact Fin.cases (isUnit_iff_ne_zero.mpr hx₄) (fun j ↦ nomatch j) i₄
  · simp only [point, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.sum_univ_zero]
    simpa [cubicResidue, add_assoc] using hequation
  · refine ⟨0, ?_⟩
    simpa [point] using cubicDerivative_one_ne_zero hq5

/-- **Nonsingular local solubility.**  For a prime `q ≥ 5`, every target is
represented in every number `n ≥ 5` of unit variables, with at least one
nonzero partial derivative. -/
theorem nonsingularUnitSolution_exists {q n : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hn5 : 5 ≤ n) (t : ZMod q) :
    Nonempty (NonsingularUnitSolution q n t) := by
  induction n, hn5 using Nat.le_induction with
  | base => exact nonsingularUnitSolution_five hq hq5 t
  | succ n _hn ih =>
      rcases ih with ⟨solution⟩
      exact ⟨solution.padOne hq5⟩

end CookMagyarLocal
end SystolicGrowth
