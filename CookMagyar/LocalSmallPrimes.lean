module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.Local
public import Mathlib.RingTheory.Nilpotent.Basic

@[expose] public section

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # Unit solutions at the primes two and three

The local argument for `x ^ 3 - x` at the exceptional primes can be made
completely explicit.  Two elementary identities are the point:

* `f(2y + 1) + f(2y - 1) = 8 (y + 2y ^ 3)`;
* `f(1 + 3y) = 3 (2y + 9y ^ 2 + 9y ^ 3)`.

The two parameter maps on the right are permutations modulo every power of
`2` and `3`, respectively.  Thus every target divisible by `8` has a
two-variable unit solution modulo `2 ^ k`, and every target divisible by `3`
has a one-variable unit solution modulo `3 ^ k`.  In particular these apply
to the targets divisible by `24` in the Cook--Magyar application.

The proof works uniformly in the exponent; no finite computation or
unformalized lifting lemma is used.
-/

/-- A multiple of `p` is nilpotent modulo `p ^ k`. -/
theorem prime_mul_isNilpotent (p k : ℕ) (z : ZMod (p ^ k)) :
    IsNilpotent ((p : ZMod (p ^ k)) * z) := by
  refine ⟨k, ?_⟩
  rw [mul_pow]
  have hp : (p : ZMod (p ^ k)) ^ k = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [hp, zero_mul]

/-- The parameter map controlling pairs of odd variables at powers of two. -/
def twoAdicParameter {k : ℕ} (y : ZMod (2 ^ k)) : ZMod (2 ^ k) :=
  y + 2 * y ^ 3

/-- The difference quotient of `twoAdicParameter` is a unit. -/
theorem isUnit_twoAdicParameter_differenceFactor (k : ℕ)
    (x y : ZMod (2 ^ k)) :
    IsUnit (1 + 2 * (x ^ 2 + x * y + y ^ 2)) := by
  exact (prime_mul_isNilpotent 2 k (x ^ 2 + x * y + y ^ 2)).isUnit_one_add

/-- The two-adic parameter map is injective at every finite level. -/
theorem twoAdicParameter_injective (k : ℕ) :
    Function.Injective (twoAdicParameter : ZMod (2 ^ k) → ZMod (2 ^ k)) := by
  intro x y hxy
  have hfactor :
      (x - y) * (1 + 2 * (x ^ 2 + x * y + y ^ 2)) = 0 := by
    calc
      (x - y) * (1 + 2 * (x ^ 2 + x * y + y ^ 2)) =
          twoAdicParameter x - twoAdicParameter y := by
            simp only [twoAdicParameter]
            ring
      _ = 0 := sub_eq_zero.mpr hxy
  have hu := isUnit_twoAdicParameter_differenceFactor k x y
  have hzero : x - y = 0 := by
    apply hu.mul_right_cancel
    simpa using hfactor
  exact sub_eq_zero.mp hzero

/-- The two-adic parameter map is a permutation at every finite level. -/
theorem twoAdicParameter_surjective (k : ℕ) :
    Function.Surjective (twoAdicParameter : ZMod (2 ^ k) → ZMod (2 ^ k)) :=
  Finite.surjective_of_injective (twoAdicParameter_injective k)

/-- Both entries of the explicit two-adic pair are units. -/
theorem twoAdic_pair_isUnit (k : ℕ) (y : ZMod (2 ^ k)) :
    IsUnit (2 * y + 1) ∧ IsUnit (2 * y - 1) := by
  constructor
  · exact (prime_mul_isNilpotent 2 k y).isUnit_add_one
  · exact (prime_mul_isNilpotent 2 k y).isUnit_sub_one

/-- Algebraic identity behind the two-adic unit construction. -/
theorem cubicResidue_twoAdic_pair (k : ℕ) (y : ZMod (2 ^ k)) :
    cubicResidue (2 * y + 1) + cubicResidue (2 * y - 1) =
      8 * twoAdicParameter y := by
  simp only [cubicResidue, twoAdicParameter]
  ring

/-- Every multiple of eight modulo `2 ^ k` is represented by two unit
values of `x ^ 3 - x`. -/
theorem twoAdic_unit_pair (k : ℕ) (m : ZMod (2 ^ k)) :
    ∃ x₁ x₂ : ZMod (2 ^ k),
      IsUnit x₁ ∧ IsUnit x₂ ∧
        cubicResidue x₁ + cubicResidue x₂ = 8 * m := by
  rcases twoAdicParameter_surjective k m with ⟨y, hy⟩
  refine ⟨2 * y + 1, 2 * y - 1, (twoAdic_pair_isUnit k y).1,
    (twoAdic_pair_isUnit k y).2, ?_⟩
  rw [cubicResidue_twoAdic_pair, hy]

/-- Specialization of `twoAdic_unit_pair` to an integral target divisible
by `24`. -/
theorem twoAdic_unit_pair_of_dvd_twentyFour (k T : ℕ) (hT : 24 ∣ T) :
    ∃ x₁ x₂ : ZMod (2 ^ k),
      IsUnit x₁ ∧ IsUnit x₂ ∧
        cubicResidue x₁ + cubicResidue x₂ = (T : ZMod (2 ^ k)) := by
  rcases hT with ⟨u, rfl⟩
  rcases twoAdic_unit_pair k (3 * (u : ZMod (2 ^ k))) with
    ⟨x₁, x₂, hx₁, hx₂, heq⟩
  refine ⟨x₁, x₂, hx₁, hx₂, ?_⟩
  rw [heq]
  norm_num [Nat.cast_mul]
  ring

/-- The parameter map controlling a unit variable at powers of three. -/
def threeAdicParameter {k : ℕ} (y : ZMod (3 ^ k)) : ZMod (3 ^ k) :=
  2 * y + 9 * y ^ 2 + 9 * y ^ 3

/-- The difference quotient of `threeAdicParameter` is a unit. -/
theorem isUnit_threeAdicParameter_differenceFactor (k : ℕ)
    (x y : ZMod (3 ^ k)) :
    IsUnit (2 + 9 * (x + y) + 9 * (x ^ 2 + x * y + y ^ 2)) := by
  have hn : IsNilpotent
      ((3 : ZMod (3 ^ k)) * (1 + 3 * (x + y) + 3 * (x ^ 2 + x * y + y ^ 2))) :=
    prime_mul_isNilpotent 3 k _
  have hu : IsUnit
      (-(1 - 3 * (1 + 3 * (x + y) + 3 * (x ^ 2 + x * y + y ^ 2)))) :=
    hn.isUnit_one_sub.neg
  convert hu using 1
  ring

/-- The three-adic parameter map is injective at every finite level. -/
theorem threeAdicParameter_injective (k : ℕ) :
    Function.Injective (threeAdicParameter : ZMod (3 ^ k) → ZMod (3 ^ k)) := by
  intro x y hxy
  have hfactor :
      (x - y) * (2 + 9 * (x + y) + 9 * (x ^ 2 + x * y + y ^ 2)) = 0 := by
    calc
      (x - y) * (2 + 9 * (x + y) + 9 * (x ^ 2 + x * y + y ^ 2)) =
          threeAdicParameter x - threeAdicParameter y := by
            simp only [threeAdicParameter]
            ring
      _ = 0 := sub_eq_zero.mpr hxy
  have hu := isUnit_threeAdicParameter_differenceFactor k x y
  have hzero : x - y = 0 := by
    apply hu.mul_right_cancel
    simpa using hfactor
  exact sub_eq_zero.mp hzero

/-- The three-adic parameter map is a permutation at every finite level. -/
theorem threeAdicParameter_surjective (k : ℕ) :
    Function.Surjective (threeAdicParameter : ZMod (3 ^ k) → ZMod (3 ^ k)) :=
  Finite.surjective_of_injective (threeAdicParameter_injective k)

/-- Algebraic identity behind the three-adic unit construction. -/
theorem cubicResidue_one_add_three_mul (k : ℕ) (y : ZMod (3 ^ k)) :
    cubicResidue (1 + 3 * y) = 3 * threeAdicParameter y := by
  simp only [cubicResidue, threeAdicParameter]
  ring

/-- The constructed three-adic variable is a unit. -/
theorem one_add_three_mul_isUnit (k : ℕ) (y : ZMod (3 ^ k)) :
    IsUnit (1 + 3 * y) :=
  (prime_mul_isNilpotent 3 k y).isUnit_one_add

/-- Its derivative `3x² - 1` is also a unit, so the construction is
nonsingular and compatible with ordinary Hensel lifting. -/
theorem cubicDerivative_threeAdic_isUnit (k : ℕ) (x : ZMod (3 ^ k)) :
    IsUnit (3 * x ^ 2 - 1) :=
  (prime_mul_isNilpotent 3 k (x ^ 2)).isUnit_sub_one

/-- At a genuine positive power of three, the unit derivative is nonzero. -/
theorem cubicDerivative_threeAdic_ne_zero {k : ℕ} (hk : 1 ≤ k)
    (x : ZMod (3 ^ k)) : 3 * x ^ 2 - 1 ≠ 0 := by
  letI : Fact (1 < 3 ^ k) :=
    ⟨one_lt_pow₀ (by norm_num) (Nat.ne_zero_of_lt hk)⟩
  exact (cubicDerivative_threeAdic_isUnit k x).ne_zero

/-- Every multiple of three modulo `3 ^ k` is represented by a unit value
of `x ^ 3 - x`, and that solution is nonsingular. -/
theorem threeAdic_unit_nonsingular_solution (k : ℕ) (m : ZMod (3 ^ k)) :
    ∃ x : ZMod (3 ^ k),
      IsUnit x ∧ cubicResidue x = 3 * m ∧ IsUnit (3 * x ^ 2 - 1) := by
  rcases threeAdicParameter_surjective k m with ⟨y, hy⟩
  refine ⟨1 + 3 * y, one_add_three_mul_isUnit k y, ?_,
    cubicDerivative_threeAdic_isUnit k (1 + 3 * y)⟩
  rw [cubicResidue_one_add_three_mul, hy]

/-- Specialization of the nonsingular three-adic construction to an
integral target divisible by `24`. -/
theorem threeAdic_unit_nonsingular_solution_of_dvd_twentyFour
    (k T : ℕ) (hT : 24 ∣ T) :
    ∃ x : ZMod (3 ^ k),
      IsUnit x ∧ cubicResidue x = (T : ZMod (3 ^ k)) ∧
        IsUnit (3 * x ^ 2 - 1) := by
  rcases hT with ⟨u, rfl⟩
  rcases threeAdic_unit_nonsingular_solution k
    (8 * (u : ZMod (3 ^ k))) with ⟨x, hx, heq, hderiv⟩
  refine ⟨x, hx, ?_, hderiv⟩
  rw [heq]
  norm_num [Nat.cast_mul]
  ring

/-! ## Arbitrarily many variables

The remaining coordinates needed in the circle-method application may all
be set equal to `1`, which is a unit and contributes zero to the equation.
The following small interface packages that padding operation.
-/

/-- A solution of the diagonal cubic equation all of whose coordinates are
units in the residue ring. -/
structure UnitCubicSolution (q n : ℕ) (t : ZMod q) where
  /-- Coordinates of the solution. -/
  point : Fin n → ZMod q
  /-- Every coordinate is a unit. -/
  isUnit_point : ∀ i, IsUnit (point i)
  /-- The diagonal cubic equation. -/
  equation : ∑ i, cubicResidue (point i) = t

/-- Appending coordinates equal to one preserves a unit solution. -/
def UnitCubicSolution.padOnes {q n : ℕ} {t : ZMod q}
    (solution : UnitCubicSolution q n t) (extra : ℕ) :
    UnitCubicSolution q (n + extra) t where
  point := Fin.append solution.point (fun _ : Fin extra ↦ 1)
  isUnit_point := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa using solution.isUnit_point j
    · simp
  equation := by
    rw [Fin.sum_univ_add]
    simpa [cubicResidue] using solution.equation

/-- A two-entry existential solution in unit coordinates. -/
theorem unitCubicSolution_two_of_pair {q : ℕ} {t : ZMod q}
    {x₁ x₂ : ZMod q} (hx₁ : IsUnit x₁) (hx₂ : IsUnit x₂)
    (heq : cubicResidue x₁ + cubicResidue x₂ = t) :
    Nonempty (UnitCubicSolution q 2 t) := by
  let point : Fin 2 → ZMod q := ![x₁, x₂]
  refine ⟨{
    point := point
    isUnit_point := ?_
    equation := ?_
  }⟩
  · intro i
    fin_cases i
    · simpa [point] using hx₁
    · simpa [point] using hx₂
  · simpa [point, Fin.sum_univ_two] using heq

/-- Package a single unit coordinate as a one-variable solution. -/
def UnitCubicSolution.singleton {q : ℕ} {t x : ZMod q}
    (hx : IsUnit x) (heq : cubicResidue x = t) :
    UnitCubicSolution q 1 t where
  point := ![x]
  isUnit_point := by
    intro i
    fin_cases i
    simpa using hx
  equation := by
    simpa using heq

/-- A one-entry existential solution in unit coordinates. -/
theorem unitCubicSolution_one_of_solution {q : ℕ} {t x : ZMod q}
    (hx : IsUnit x) (heq : cubicResidue x = t) :
    Nonempty (UnitCubicSolution q 1 t) :=
  ⟨UnitCubicSolution.singleton hx heq⟩

/-- For every number `n ≥ 2` of variables, every multiple of eight has a
unit solution modulo every power of two. -/
theorem twoAdic_unit_solution {n : ℕ} (hn : 2 ≤ n) (k : ℕ)
    (m : ZMod (2 ^ k)) :
    Nonempty (UnitCubicSolution (2 ^ k) n (8 * m)) := by
  obtain ⟨extra, rfl : n = 2 + extra⟩ := Nat.exists_eq_add_of_le hn
  rcases twoAdic_unit_pair k m with ⟨x₁, x₂, hx₁, hx₂, heq⟩
  rcases unitCubicSolution_two_of_pair hx₁ hx₂ heq with ⟨solution⟩
  exact ⟨solution.padOnes extra⟩

/-- Cook--Magyar's divisibility condition supplies unit solutions with any
`n ≥ 2` modulo every power of two. -/
theorem twoAdic_unit_solution_of_dvd_twentyFour {n : ℕ} (hn : 2 ≤ n)
    (k T : ℕ) (hT : 24 ∣ T) :
    Nonempty (UnitCubicSolution (2 ^ k) n (T : ZMod (2 ^ k))) := by
  obtain ⟨extra, rfl : n = 2 + extra⟩ := Nat.exists_eq_add_of_le hn
  rcases twoAdic_unit_pair_of_dvd_twentyFour k T hT with
    ⟨x₁, x₂, hx₁, hx₂, heq⟩
  rcases unitCubicSolution_two_of_pair hx₁ hx₂ heq with ⟨solution⟩
  exact ⟨solution.padOnes extra⟩

/-- For every positive number of variables, every multiple of three has a
unit solution modulo every power of three.  The distinguished first
coordinate has unit cubic derivative. -/
theorem threeAdic_unit_solution {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (m : ZMod (3 ^ k)) :
    ∃ solution : UnitCubicSolution (3 ^ k) n (3 * m),
      IsUnit (3 * solution.point ⟨0, hn⟩ ^ 2 - 1) := by
  obtain ⟨extra, rfl : n = 1 + extra⟩ := Nat.exists_eq_add_of_le hn
  rcases threeAdic_unit_nonsingular_solution k m with ⟨x, hx, heq, hderiv⟩
  let solution := (UnitCubicSolution.singleton hx heq).padOnes extra
  refine ⟨solution, ?_⟩
  change IsUnit
    (3 * (Fin.append ![x] (fun _ : Fin extra ↦ (1 : ZMod (3 ^ k)))
      ⟨0, hn⟩) ^ 2 - 1)
  rw [show (⟨0, hn⟩ : Fin (1 + extra)) = Fin.castAdd extra (0 : Fin 1) by
    ext
    rfl]
  simpa using hderiv

/-- Cook--Magyar's divisibility condition supplies nonsingular unit
solutions with any positive number of variables modulo every power of
three. -/
theorem threeAdic_unit_solution_of_dvd_twentyFour {n : ℕ} (hn : 1 ≤ n)
    (k T : ℕ) (hT : 24 ∣ T) :
    ∃ solution : UnitCubicSolution (3 ^ k) n (T : ZMod (3 ^ k)),
      IsUnit (3 * solution.point ⟨0, hn⟩ ^ 2 - 1) := by
  obtain ⟨extra, rfl : n = 1 + extra⟩ := Nat.exists_eq_add_of_le hn
  rcases threeAdic_unit_nonsingular_solution_of_dvd_twentyFour k T hT with
    ⟨x, hx, heq, hderiv⟩
  let solution := (UnitCubicSolution.singleton hx heq).padOnes extra
  refine ⟨solution, ?_⟩
  change IsUnit
    (3 * (Fin.append ![x] (fun _ : Fin extra ↦ (1 : ZMod (3 ^ k)))
      ⟨0, hn⟩) ^ 2 - 1)
  rw [show (⟨0, hn⟩ : Fin (1 + extra)) = Fin.castAdd extra (0 : Fin 1) by
    ext
    rfl]
  simpa using hderiv

/-- At every positive three-power level, the preceding tuple is
nonsingular in the literal sense that its distinguished partial derivative
is nonzero. -/
theorem threeAdic_unit_solution_nonsingular {n k : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (m : ZMod (3 ^ k)) :
    ∃ solution : UnitCubicSolution (3 ^ k) n (3 * m),
      3 * solution.point ⟨0, hn⟩ ^ 2 - 1 ≠ 0 := by
  letI : Fact (1 < 3 ^ k) :=
    ⟨one_lt_pow₀ (by norm_num) (Nat.ne_zero_of_lt hk)⟩
  rcases threeAdic_unit_solution hn k m with ⟨solution, hunit⟩
  exact ⟨solution, hunit.ne_zero⟩

/-- Nonsingular form of the `24 ∣ T` local statement at positive powers
of three. -/
theorem threeAdic_unit_solution_nonsingular_of_dvd_twentyFour
    {n k T : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hT : 24 ∣ T) :
    ∃ solution : UnitCubicSolution (3 ^ k) n (T : ZMod (3 ^ k)),
      3 * solution.point ⟨0, hn⟩ ^ 2 - 1 ≠ 0 := by
  letI : Fact (1 < 3 ^ k) :=
    ⟨one_lt_pow₀ (by norm_num) (Nat.ne_zero_of_lt hk)⟩
  rcases threeAdic_unit_solution_of_dvd_twentyFour hn k T hT with
    ⟨solution, hunit⟩
  exact ⟨solution, hunit.ne_zero⟩

end CookMagyarLocal
end SystolicGrowth
