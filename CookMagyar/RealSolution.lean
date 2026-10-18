module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarReal

/-! # A nonsingular solution at the real place

The singular integral in the Cook--Magyar argument is supported by a very
explicit real solution.  In the normalized target window, the constant point

`x_i = (mu / n) ^ (1 / 3)`

lies in the open unit cube, solves `sum_i x_i^3 = mu`, and has nonzero
gradient.  This file records that elementary real-place input independently
of any circle-method estimates.
-/

/-- The compact real target window used after normalizing a diagonal cubic
equation by its scale. -/
def NormalizedTargetWindow (n : ℕ) (mu : ℝ) : Prop :=
  (n : ℝ) - 1 / 3 ≤ mu ∧ mu ≤ (n : ℝ) - 1 / 5

/-- A solution of the diagonal cubic equation in the open unit cube, together
with a witness that one partial derivative is nonzero. -/
structure NonsingularOpenUnitSolution (n : ℕ) (mu : ℝ) where
  point : Fin n → ℝ
  point_pos : ∀ i, 0 < point i
  point_lt_one : ∀ i, point i < 1
  equation : ∑ i, point i ^ 3 = mu
  nonsingular : ∃ i, 3 * point i ^ 2 ≠ 0

/-- The diagonal coordinate used for the explicit real solution. -/
noncomputable def diagonalCoordinate (n : ℕ) (mu : ℝ) : ℝ :=
  (mu / (n : ℝ)) ^ ((3 : ℝ)⁻¹)

theorem normalizedTarget_pos {n : ℕ} {mu : ℝ} (hn : 0 < n)
    (hmu : NormalizedTargetWindow n mu) : 0 < mu := by
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')
  rcases hmu with ⟨hlower, _hupper⟩
  norm_num at hlower ⊢
  linarith

theorem normalizedTarget_div_pos {n : ℕ} {mu : ℝ} (hn : 0 < n)
    (hmu : NormalizedTargetWindow n mu) : 0 < mu / (n : ℝ) := by
  exact div_pos (normalizedTarget_pos hn hmu) (by exact_mod_cast hn)

theorem normalizedTarget_div_lt_one {n : ℕ} {mu : ℝ} (hn : 0 < n)
    (hmu : NormalizedTargetWindow n mu) : mu / (n : ℝ) < 1 := by
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmu_lt : mu < (n : ℝ) := by
    rcases hmu with ⟨_hlower, hupper⟩
    norm_num at hupper ⊢
    linarith
  exact (div_lt_one hn_real).mpr hmu_lt

theorem diagonalCoordinate_pos {n : ℕ} {mu : ℝ} (hn : 0 < n)
    (hmu : NormalizedTargetWindow n mu) :
    0 < diagonalCoordinate n mu := by
  exact Real.rpow_pos_of_pos (normalizedTarget_div_pos hn hmu) _

theorem diagonalCoordinate_lt_one {n : ℕ} {mu : ℝ} (hn : 0 < n)
    (hmu : NormalizedTargetWindow n mu) :
    diagonalCoordinate n mu < 1 := by
  exact Real.rpow_lt_one (normalizedTarget_div_pos hn hmu).le
    (normalizedTarget_div_lt_one hn hmu) (by norm_num)

theorem diagonalCoordinate_cube {n : ℕ} {mu : ℝ} (hn : 0 < n)
    (hmu : NormalizedTargetWindow n mu) :
    diagonalCoordinate n mu ^ 3 = mu / (n : ℝ) := by
  exact Real.rpow_inv_natCast_pow (normalizedTarget_div_pos hn hmu).le
    (by norm_num)

/-- Every normalized target in the compact window has an explicit
nonsingular solution in the open unit cube. -/
theorem exists_nonsingularOpenUnitSolution {n : ℕ} {mu : ℝ}
    (hn : 0 < n) (hmu : NormalizedTargetWindow n mu) :
    Nonempty (NonsingularOpenUnitSolution n mu) := by
  let c := diagonalCoordinate n mu
  have hc_pos : 0 < c := diagonalCoordinate_pos hn hmu
  have hc_lt_one : c < 1 := diagonalCoordinate_lt_one hn hmu
  have hc_cube : c ^ 3 = mu / (n : ℝ) := diagonalCoordinate_cube hn hmu
  refine ⟨{
    point := fun _ ↦ c
    point_pos := fun _ ↦ hc_pos
    point_lt_one := fun _ ↦ hc_lt_one
    equation := ?_
    nonsingular := ?_
  }⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hc_cube]
    field_simp
  · let i : Fin n := ⟨0, hn⟩
    refine ⟨i, mul_ne_zero (by norm_num) ?_⟩
    exact pow_ne_zero _ hc_pos.ne'

end CookMagyarReal
end SystolicGrowth
