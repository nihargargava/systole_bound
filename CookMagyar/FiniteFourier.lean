module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Finite Fourier expansion of the local cubic count

This file proves the exact finite-group identity underlying the local factors
in the Cook--Magyar circle method.  It contains no analytic estimate.
-/

variable {q : ℕ} [NeZero q]

/-- The reduction modulo `q` of the polynomial `X³ - X`. -/
def cubicResidue (x : ZMod q) : ZMod q := x ^ 3 - x

/-- The sum of `X³-X` along a tuple of invertible residue classes modulo `q`. -/
def unitCubicSum {n : ℕ} (x : Fin n → (ZMod q)ˣ) : ZMod q :=
  ∑ i, cubicResidue (x i : ZMod q)

/-- The number of unit tuples modulo `q` representing `T` by a sum of
copies of `X³-X`. -/
def unitCubicSolutionCount (n : ℕ) (T : ZMod q) : ℕ :=
  ((Finset.univ : Finset (Fin n → (ZMod q)ˣ)).filter fun x ↦ unitCubicSum x = T).card

/-- The standard complex additive character on `ZMod q`. -/
noncomputable abbrev standardAdditiveCharacter : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar

/-- The one-variable complete exponential sum over the units modulo `q`. -/
noncomputable def unitCubicExponentialSum (a : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ,
    standardAdditiveCharacter (a * cubicResidue (u : ZMod q))

/-- Orthogonality of the standard character on `ZMod q`. -/
theorem sum_standardAdditiveCharacter_mul (z : ZMod q) :
    ∑ a : ZMod q, standardAdditiveCharacter (a * z) =
      if z = 0 then (q : ℂ) else 0 := by
  rw [AddChar.sum_mulShift (R := ZMod q) (R' := ℂ) z
    (ZMod.isPrimitive_stdAddChar q)]
  split_ifs <;> simp_all [ZMod.card]

private theorem standardAdditiveCharacter_sum {ι : Type*} [Fintype ι]
    (f : ι → ZMod q) :
    standardAdditiveCharacter (∑ i, f i) =
      ∏ i, standardAdditiveCharacter (f i) := by
  classical
  have aux : ∀ s : Finset ι,
      standardAdditiveCharacter (∑ i ∈ s, f i) =
        ∏ i ∈ s, standardAdditiveCharacter (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.prod_insert ha,
          AddChar.map_add_eq_mul, ih]
  simpa using aux Finset.univ

private theorem product_unitCubic_character {n : ℕ}
    (a : ZMod q) (x : Fin n → (ZMod q)ˣ) :
    (∏ i, standardAdditiveCharacter
      (a * cubicResidue (x i : ZMod q))) =
      standardAdditiveCharacter (a * unitCubicSum x) := by
  rw [← standardAdditiveCharacter_sum]
  congr 1
  simp only [unitCubicSum, Finset.mul_sum]

private theorem product_unitCubic_character_mul_target {n : ℕ}
    (a : ZMod q) (x : Fin n → (ZMod q)ˣ) (T : ZMod q) :
    (∏ i, standardAdditiveCharacter
      (a * cubicResidue (x i : ZMod q))) *
        standardAdditiveCharacter (-(a * T)) =
      standardAdditiveCharacter (a * (unitCubicSum x - T)) := by
  rw [product_unitCubic_character, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Division-free finite Fourier orthogonality formula for the unit solution
count.  The right side is the standard frequency sum, and the left side is
`q` times the exact number of solutions. -/
theorem frequencySum_eq_modulus_mul_unitCubicSolutionCount
    (n : ℕ) (T : ZMod q) :
    (∑ a : ZMod q,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * T))) =
      (q : ℂ) * (unitCubicSolutionCount n T : ℂ) := by
  classical
  calc
    (∑ a : ZMod q,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * T))) =
        ∑ a : ZMod q, ∑ x : Fin n → (ZMod q)ˣ,
          (∏ i, standardAdditiveCharacter
            (a * cubicResidue (x i : ZMod q))) *
              standardAdditiveCharacter (-(a * T)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [unitCubicExponentialSum, Fintype.sum_pow, Finset.sum_mul]
    _ = ∑ x : Fin n → (ZMod q)ˣ, ∑ a : ZMod q,
          standardAdditiveCharacter (a * (unitCubicSum x - T)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _hx
          apply Finset.sum_congr rfl
          intro a _ha
          exact product_unitCubic_character_mul_target a x T
    _ = ∑ x : Fin n → (ZMod q)ˣ,
          if unitCubicSum x = T then (q : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          simpa only [sub_eq_zero] using
            (sum_standardAdditiveCharacter_mul (unitCubicSum x - T))
    _ = (q : ℂ) * (unitCubicSolutionCount n T : ℂ) := by
          unfold unitCubicSolutionCount
          rw [Finset.natCast_card_filter]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          split_ifs <;> simp

/-- The normalized form of
`frequencySum_eq_modulus_mul_unitCubicSolutionCount`: the exact solution
count is the average of the complete exponential sums over all additive
frequencies modulo `q`. -/
theorem unitCubicSolutionCount_eq_frequencyAverage
    (n : ℕ) (T : ZMod q) :
    (unitCubicSolutionCount n T : ℂ) =
      (q : ℂ)⁻¹ *
        ∑ a : ZMod q,
          unitCubicExponentialSum a ^ n *
            standardAdditiveCharacter (-(a * T)) := by
  rw [frequencySum_eq_modulus_mul_unitCubicSolutionCount]
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  simp [hq]

end CookMagyarFiniteFourier
end SystolicGrowth
