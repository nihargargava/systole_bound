module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepNineBlocks

@[expose] public section

/-!
# Arithmetic form of Hua's ordered Type-II cubic frequency

For `w < v`, the difference `v³-w³` is a positive natural number. These
lemmas turn the real leading coefficient exposed by the phase-difference
identity into the cast of that natural frequency, then factor it into the
gap and quadratic terms needed by the divisor argument. No oscillatory
estimate or denominator cancellation is asserted here.
-/

namespace SystolicGrowth.CookMagyarCircle

/-- The ordered cubic difference has the exact positive factorization used
in Hua's exceptional-frequency count. -/
theorem hua_typeII_cube_difference_factorization_and_pos
    {v w : ℕ} (h : w < v) :
    v ^ 3 - w ^ 3 = (v - w) * (v ^ 2 + v * w + w ^ 2) ∧
      0 < v ^ 3 - w ^ 3 := by
  have hfactor := nat_cube_sub_factorization (Nat.le_of_lt h)
  refine ⟨hfactor, ?_⟩
  rw [hfactor]
  have hv : 0 < v := by omega
  exact Nat.mul_pos (Nat.sub_pos_of_lt h) (by positivity)

/-- Multiplying by a positive fixed Type-II multiplier preserves both the
integer factorization and the orientation of the cubic frequency. -/
theorem hua_typeII_nat_leading_frequency_factorization_and_pos
    {l v w : ℕ} (hl : 0 < l) (h : w < v) :
    l ^ 3 * (v ^ 3 - w ^ 3) =
        (l ^ 3 * (v - w)) * (v ^ 2 + v * w + w ^ 2) ∧
      0 < l ^ 3 * (v ^ 3 - w ^ 3) := by
  obtain ⟨hfactor, hpos⟩ := hua_typeII_cube_difference_factorization_and_pos h
  constructor
  · rw [hfactor]
    ring
  · exact Nat.mul_pos (by positivity) hpos

/-- The real cubic leading coefficient is the cast of the ordered natural
frequency times the rational leading coefficient. No condition on `q` is
needed for this algebraic identity. -/
theorem hua_typeII_real_leading_frequency_eq_natCast
    (a q l v w : ℕ) (h : w < v) :
    ((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3) =
      ((l ^ 3 * (v ^ 3 - w ^ 3) : ℕ) : ℝ) * ((a : ℝ) / q) := by
  have hcube : w ^ 3 ≤ v ^ 3 := Nat.pow_le_pow_left (Nat.le_of_lt h) 3
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hcube]
  push_cast
  ring

/-- The same real coefficient with all three natural divisor factors
visible, in the ordered orientation `w < v`. -/
theorem hua_typeII_real_leading_frequency_eq_factored_natCast
    (a q l v w : ℕ) (h : w < v) :
    ((a : ℝ) / q) * (l : ℝ) ^ 3 * ((v : ℝ) ^ 3 - (w : ℝ) ^ 3) =
      (((l ^ 3 * (v - w)) * (v ^ 2 + v * w + w ^ 2) : ℕ) : ℝ) *
        ((a : ℝ) / q) := by
  rw [hua_typeII_real_leading_frequency_eq_natCast a q l v w h,
    nat_cube_sub_factorization (Nat.le_of_lt h)]
  simp only [mul_assoc]

#print axioms hua_typeII_cube_difference_factorization_and_pos
#print axioms hua_typeII_nat_leading_frequency_factorization_and_pos
#print axioms hua_typeII_real_leading_frequency_eq_natCast
#print axioms hua_typeII_real_leading_frequency_eq_factored_natCast

end SystolicGrowth.CookMagyarCircle
