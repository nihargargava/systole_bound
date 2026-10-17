module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaShift

@[expose] public section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace SystolicGrowth
namespace CookMagyarCircle

/-! # Unweighted cubic moment orthogonality

The shift estimate is stated as an integral. This module identifies its
unweighted moments with the finite solution counts already bounded in
`HuaEstimate`. -/

/-- Write the range-indexed unweighted cubic sum as a `Fin`-indexed sum. -/
theorem cubicUnweightedExpSum_eq_finSum (α : ℝ) (N : ℕ) :
    cubicUnweightedExpSum α N =
      ∑ x : Fin (N + 1), addChar α (primeCubic x.val) := by
  unfold cubicUnweightedExpSum
  exact (Fin.sum_univ_eq_sum_range
    (fun m : ℕ => addChar α (primeCubic m)) (N + 1)).symm

/-- Squaring produces the ordered two-variable cubic phase sum. -/
theorem cubicUnweightedExpSum_pow_two (α : ℝ) (N : ℕ) :
    cubicUnweightedExpSum α N ^ 2 =
      ∑ ab : Fin (N + 1) × Fin (N + 1),
        addChar α (primeCubic ab.1.val + primeCubic ab.2.val) := by
  rw [cubicUnweightedExpSum_eq_finSum, pow_two]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact (addChar_add α _ _).symm

private theorem ofReal_norm_pow_four (z : ℂ) :
    ((‖z‖ ^ 4 : ℝ) : ℂ) = z ^ 2 * conj z ^ 2 := by
  calc
    ((‖z‖ ^ 4 : ℝ) : ℂ) = (((‖z‖ : ℝ) : ℂ) ^ 2) ^ 2 := by
      push_cast
      ring
    _ = (z * conj z) ^ 2 := by rw [Complex.mul_conj']
    _ = z ^ 2 * conj z ^ 2 := by rw [mul_pow]

/-- The conjugate square is the ordered negative-frequency pair sum. -/
theorem conj_cubicUnweightedExpSum_pow_two (α : ℝ) (N : ℕ) :
    conj (cubicUnweightedExpSum α N) ^ 2 =
      ∑ ab : Fin (N + 1) × Fin (N + 1),
        negAddChar α (primeCubic ab.1.val + primeCubic ab.2.val) := by
  rw [← map_pow, cubicUnweightedExpSum_pow_two, map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  unfold addChar negAddChar
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, map_natCast, Complex.conj_ofReal,
    Complex.conj_I]
  ring

/-- Exact fourth moment, first in complex form to reuse character
orthogonality without an implicit real-to-complex coercion. -/
theorem integral_norm_cubicUnweightedExpSum_pow_four_complex (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ((‖cubicUnweightedExpSum α N‖ ^ 4 : ℝ) : ℂ)) =
        (cubicFourthSolutionCount N : ℂ) := by
  classical
  have hpoint : ∀ α : ℝ,
      ((‖cubicUnweightedExpSum α N‖ ^ 4 : ℝ) : ℂ) =
        ∑ ab : Fin (N + 1) × Fin (N + 1),
          ∑ cd : Fin (N + 1) × Fin (N + 1),
            addChar α (primeCubic ab.1.val + primeCubic ab.2.val) *
              negAddChar α (primeCubic cd.1.val + primeCubic cd.2.val) := by
    intro α
    rw [ofReal_norm_pow_four, cubicUnweightedExpSum_pow_two,
      conj_cubicUnweightedExpSum_pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    rw [Finset.mul_sum]
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _ => hpoint α)]
  rw [integral_finsetSum]
  · rw [cubicFourthSolutionCount_eq_indicator]
    push_cast
    apply Finset.sum_congr rfl
    intro ab hab
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro cd hcd
      rw [integral_addChar_mul_negAddChar]
    · intro cd hcd
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
  · intro ab hab
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

/-- The fourth moment is exactly the previously bounded ordered solution
count. -/
theorem integral_norm_cubicUnweightedExpSum_pow_four (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ‖cubicUnweightedExpSum α N‖ ^ 4) =
        (cubicFourthSolutionCount N : ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  exact integral_norm_cubicUnweightedExpSum_pow_four_complex N

/-- The fourth power of the unweighted sum is indexed by four-tuples. -/
theorem cubicUnweightedExpSum_pow_four (α : ℝ) (N : ℕ) :
    cubicUnweightedExpSum α N ^ 4 =
      ∑ x : Fin 4 → Fin (N + 1),
        addChar α (cubicFourTupleValue x) := by
  classical
  rw [cubicUnweightedExpSum_eq_finSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← addChar_sum]
  rfl

/-- The conjugate fourth power has the opposite integer frequency. -/
theorem conj_cubicUnweightedExpSum_pow_four (α : ℝ) (N : ℕ) :
    conj (cubicUnweightedExpSum α N) ^ 4 =
      ∑ x : Fin 4 → Fin (N + 1),
        negAddChar α (cubicFourTupleValue x) := by
  rw [← map_pow, cubicUnweightedExpSum_pow_four, map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact conj_addChar α (cubicFourTupleValue x)

private theorem ofReal_norm_pow_eight_unweighted (z : ℂ) :
    ((‖z‖ ^ 8 : ℝ) : ℂ) = z ^ 4 * conj z ^ 4 := by
  calc
    ((‖z‖ ^ 8 : ℝ) : ℂ) = (((‖z‖ : ℝ) : ℂ) ^ 2) ^ 4 := by
      push_cast
      ring
    _ = (z * conj z) ^ 4 := by rw [Complex.mul_conj']
    _ = z ^ 4 * conj z ^ 4 := by rw [mul_pow]

/-- The unweighted eighth moment is the exact four-tuple solution count. -/
theorem integral_norm_cubicUnweightedExpSum_pow_eight_complex (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ((‖cubicUnweightedExpSum α N‖ ^ 8 : ℝ) : ℂ)) =
        (cubicEighthSolutionCount N : ℂ) := by
  classical
  have hpoint : ∀ α : ℝ,
      ((‖cubicUnweightedExpSum α N‖ ^ 8 : ℝ) : ℂ) =
        ∑ x : Fin 4 → Fin (N + 1),
          ∑ y : Fin 4 → Fin (N + 1),
            addChar α (cubicFourTupleValue x) *
              negAddChar α (cubicFourTupleValue y) := by
    intro α
    rw [ofReal_norm_pow_eight_unweighted, cubicUnweightedExpSum_pow_four,
      conj_cubicUnweightedExpSum_pow_four, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  rw [setIntegral_congr_fun measurableSet_Icc (fun α _ => hpoint α)]
  rw [integral_finsetSum]
  · unfold cubicEighthSolutionCount
    push_cast
    apply Finset.sum_congr rfl
    intro x hx
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y hy
      rw [integral_addChar_mul_negAddChar]
    · intro y hy
      apply Continuous.integrableOn_Icc
      unfold addChar negAddChar
      fun_prop
  · intro x hx
    apply Continuous.integrableOn_Icc
    unfold addChar negAddChar
    fun_prop

theorem integral_norm_cubicUnweightedExpSum_pow_eight (N : ℕ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ‖cubicUnweightedExpSum α N‖ ^ 8) =
        (cubicEighthSolutionCount N : ℝ) := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  exact integral_norm_cubicUnweightedExpSum_pow_eight_complex N

/-- The proven fourth-moment and second-difference energy bounds feed the
actual unweighted eighth solution count, with no conditional moment input. -/
theorem cubicEighthSolutionCount_le_fourth_and_energy (N : ℕ) :
    (cubicEighthSolutionCount N : ℝ) ≤
      12 * (N + 1 : ℝ) ^ 3 * (cubicFourthSolutionCount N : ℝ) +
        256 * (N + 1 : ℝ) ^ 2 *
          (∫ α in Set.Icc (0 : ℝ) 1,
            ‖cubicSecondDifferenceTripleSum α N‖ ^ 2) := by
  simpa only [integral_norm_cubicUnweightedExpSum_pow_four,
    integral_norm_cubicUnweightedExpSum_pow_eight] using
      integral_norm_cubicUnweightedExpSum_pow_eight_le N

/-- A quantitative unweighted eighth-count estimate expressed only through
the two independently proved divisor-bound constants. -/
theorem exists_cubicEighthSolutionCount_secondDifference_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₄ E : ℝ, 0 < C₄ ∧ 0 < E ∧ ∀ N : ℕ,
      (cubicEighthSolutionCount N : ℝ) ≤
        12 * (N + 1 : ℝ) ^ 3 *
          ((N + 1 : ℝ) ^ 2 *
            (4 + 2 * C₄ * Real.rpow (2 * (N + 1 : ℝ) ^ 3) (ε / 3))) +
        256 * (N + 1 : ℝ) ^ 2 *
          (E * Real.rpow (N + 1 : ℝ) ε * (N + 1 : ℝ) ^ 3) := by
  obtain ⟨C₄, hC₄, hfour⟩ :=
    exists_cubicFourthSolutionCount_rpow_bound (by positivity : 0 < ε / 3)
  obtain ⟨E, hE, henergy⟩ :=
    exists_cubicSecondDifferenceTripleSum_energy_bound hε
  refine ⟨C₄, E, hC₄, hE, fun N => ?_⟩
  calc
    (cubicEighthSolutionCount N : ℝ) ≤
        12 * (N + 1 : ℝ) ^ 3 * (cubicFourthSolutionCount N : ℝ) +
          256 * (N + 1 : ℝ) ^ 2 *
            (∫ α in Set.Icc (0 : ℝ) 1,
              ‖cubicSecondDifferenceTripleSum α N‖ ^ 2) :=
      cubicEighthSolutionCount_le_fourth_and_energy N
    _ ≤ _ := by
      gcongr
      · exact hfour N
      · exact henergy N

/-- The second-difference argument gives the genuinely sharp unweighted
`5+ε` eighth-moment strength needed by the public weak Hua estimate. -/
theorem exists_cubicEighthSolutionCount_rpow_five_bound
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (cubicEighthSolutionCount N : ℝ) ≤
        C * Real.rpow (N + 1 : ℝ) (5 + ε) := by
  obtain ⟨C₄, E, hC₄, hE, hbound⟩ :=
    exists_cubicEighthSolutionCount_secondDifference_bound hε
  let K : ℝ := 48 + 24 * C₄ * Real.rpow 2 (ε / 3) + 256 * E
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, fun N => ?_⟩
  let X : ℝ := N + 1
  have hX : 1 ≤ X := by dsimp [X]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hX0 : 0 ≤ X := le_trans (by norm_num) hX
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hfreq : Real.rpow (2 * X ^ 3) (ε / 3) =
      Real.rpow 2 (ε / 3) * Real.rpow X ε := by
    change (2 * X ^ 3) ^ (ε / 3) =
      (2 : ℝ) ^ (ε / 3) * X ^ ε
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    rw [← Real.rpow_natCast_mul hX0 3 (ε / 3)]
    rw [show ((3 : ℕ) : ℝ) * (ε / 3) = ε by norm_num; ring]
  have hX5 : X ^ 5 ≤ Real.rpow X (5 + ε) := by
    have he : (5 : ℝ) ≤ 5 + ε := by linarith
    calc
      X ^ 5 = X ^ (5 : ℝ) := (Real.rpow_natCast X 5).symm
      _ ≤ X ^ (5 + ε) := Real.rpow_le_rpow_of_exponent_le hX he
  have hR : Real.rpow X (5 + ε) = X ^ 5 * Real.rpow X ε := by
    change X ^ (5 + ε) = X ^ 5 * X ^ ε
    rw [Real.rpow_add hXpos]
    exact congrArg (fun t : ℝ => t * X ^ ε) (Real.rpow_natCast X 5)
  have hraw := hbound N
  change (cubicEighthSolutionCount N : ℝ) ≤
    12 * X ^ 3 * (X ^ 2 * (4 + 2 * C₄ * Real.rpow (2 * X ^ 3) (ε / 3))) +
      256 * X ^ 2 * (E * Real.rpow X ε * X ^ 3) at hraw
  rw [hfreq] at hraw
  calc
    (cubicEighthSolutionCount N : ℝ) ≤
        12 * X ^ 3 *
          (X ^ 2 * (4 + 2 * C₄ *
            (Real.rpow 2 (ε / 3) * Real.rpow X ε))) +
          256 * X ^ 2 * (E * Real.rpow X ε * X ^ 3) := hraw
    _ = 48 * X ^ 5 +
        (24 * C₄ * Real.rpow 2 (ε / 3) + 256 * E) *
          Real.rpow X (5 + ε) := by rw [hR]; ring
    _ ≤ 48 * Real.rpow X (5 + ε) +
        (24 * C₄ * Real.rpow 2 (ε / 3) + 256 * E) *
          Real.rpow X (5 + ε) := by gcongr
    _ = K * Real.rpow X (5 + ε) := by dsimp [K]; ring
    _ = _ := rfl

#print axioms SystolicGrowth.CookMagyarCircle.integral_norm_cubicUnweightedExpSum_pow_four
#print axioms SystolicGrowth.CookMagyarCircle.integral_norm_cubicUnweightedExpSum_pow_eight
#print axioms SystolicGrowth.CookMagyarCircle.cubicEighthSolutionCount_le_fourth_and_energy
#print axioms SystolicGrowth.CookMagyarCircle.exists_cubicEighthSolutionCount_secondDifference_bound
#print axioms SystolicGrowth.CookMagyarCircle.exists_cubicEighthSolutionCount_rpow_five_bound

end CookMagyarCircle
end SystolicGrowth
