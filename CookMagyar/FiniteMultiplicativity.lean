module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.FiniteFourier
public import Mathlib.Algebra.Group.Prod

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Chinese-remainder multiplicativity of local cubic counts

The results here are exact finite algebra.  They identify unit solutions
modulo a product of coprime moduli with pairs of unit solutions modulo the
two factors.
-/

variable {q₁ q₂ : ℕ} [NeZero q₁] [NeZero q₂]

/-- The finite type of unit tuples representing `T` by a sum of `X³-X`. -/
abbrev UnitCubicSolutions (n : ℕ) {q : ℕ} [NeZero q] (T : ZMod q) :=
  {x : Fin n → (ZMod q)ˣ // unitCubicSum x = T}

/-- The subtype cardinality agrees with the filtered count used in the
finite Fourier formula. -/
theorem card_unitCubicSolutions {q : ℕ} [NeZero q] (n : ℕ) (T : ZMod q) :
    Fintype.card (UnitCubicSolutions n T) = unitCubicSolutionCount n T := by
  classical
  simpa [UnitCubicSolutions, unitCubicSolutionCount] using
    (Fintype.card_subtype (fun x : Fin n → (ZMod q)ˣ ↦ unitCubicSum x = T))

/-- The Chinese-remainder equivalence on unit groups. -/
noncomputable def unitChineseRemainder (h : q₁.Coprime q₂) :
    (ZMod (q₁ * q₂))ˣ ≃ (ZMod q₁)ˣ × (ZMod q₂)ˣ :=
  ((Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans
    (MulEquiv.prodUnits (M := ZMod q₁) (N := ZMod q₂))).toEquiv

omit [NeZero q₁] [NeZero q₂] in
@[simp] theorem coe_unitChineseRemainder_fst (h : q₁.Coprime q₂)
    (u : (ZMod (q₁ * q₂))ˣ) :
    ((unitChineseRemainder h u).1 : ZMod q₁) =
      (ZMod.chineseRemainder h (u : ZMod (q₁ * q₂))).1 := by
  rfl

omit [NeZero q₁] [NeZero q₂] in
@[simp] theorem coe_unitChineseRemainder_snd (h : q₁.Coprime q₂)
    (u : (ZMod (q₁ * q₂))ˣ) :
    ((unitChineseRemainder h u).2 : ZMod q₂) =
      (ZMod.chineseRemainder h (u : ZMod (q₁ * q₂))).2 := by
  rfl

/-- Coordinatewise CRT for tuples of unit residue classes. -/
noncomputable def unitTupleChineseRemainder (n : ℕ) (h : q₁.Coprime q₂) :
    (Fin n → (ZMod (q₁ * q₂))ˣ) ≃
      (Fin n → (ZMod q₁)ˣ) × (Fin n → (ZMod q₂)ˣ) :=
  (Equiv.piCongrRight fun _ : Fin n ↦ unitChineseRemainder h).trans
    (Equiv.arrowProdEquivProdArrow (Fin n)
      (fun _ ↦ (ZMod q₁)ˣ) (fun _ ↦ (ZMod q₂)ˣ))

omit [NeZero q₁] [NeZero q₂] in
@[simp] theorem unitTupleChineseRemainder_fst_apply (n : ℕ)
    (h : q₁.Coprime q₂) (x : Fin n → (ZMod (q₁ * q₂))ˣ) (i : Fin n) :
    (unitTupleChineseRemainder n h x).1 i = (unitChineseRemainder h (x i)).1 := by
  rfl

omit [NeZero q₁] [NeZero q₂] in
@[simp] theorem unitTupleChineseRemainder_snd_apply (n : ℕ)
    (h : q₁.Coprime q₂) (x : Fin n → (ZMod (q₁ * q₂))ˣ) (i : Fin n) :
    (unitTupleChineseRemainder n h x).2 i = (unitChineseRemainder h (x i)).2 := by
  rfl

omit [NeZero q₁] [NeZero q₂] in
/-- `X³-X` commutes with reduction to both CRT factors. -/
theorem chineseRemainder_cubicResidue (h : q₁.Coprime q₂)
    (z : ZMod (q₁ * q₂)) :
    ZMod.chineseRemainder h (cubicResidue z) =
      (cubicResidue (ZMod.chineseRemainder h z).1,
        cubicResidue (ZMod.chineseRemainder h z).2) := by
  unfold cubicResidue
  rw [map_sub, map_pow]
  rfl

omit [NeZero q₁] [NeZero q₂] in
/-- A sum of the cubic polynomial commutes with coordinatewise CRT. -/
theorem chineseRemainder_unitCubicSum {n : ℕ} (h : q₁.Coprime q₂)
    (x : Fin n → (ZMod (q₁ * q₂))ˣ) :
    ZMod.chineseRemainder h (unitCubicSum x) =
      (unitCubicSum (unitTupleChineseRemainder n h x).1,
        unitCubicSum (unitTupleChineseRemainder n h x).2) := by
  unfold unitCubicSum
  rw [map_sum]
  simp_rw [chineseRemainder_cubicResidue]
  ext
  · rw [Prod.fst_sum]
    rfl
  · rw [Prod.snd_sum]
    rfl

omit [NeZero q₁] [NeZero q₂] in
/-- A tuple solves the congruence modulo a coprime product exactly when its
two CRT components solve the two reduced congruences. -/
theorem unitCubicSum_eq_iff_crt_components {n : ℕ}
    (h : q₁.Coprime q₂) (T : ZMod (q₁ * q₂))
    (x : Fin n → (ZMod (q₁ * q₂))ˣ) :
    unitCubicSum x = T ↔
      unitCubicSum (unitTupleChineseRemainder n h x).1 =
          (ZMod.chineseRemainder h T).1 ∧
        unitCubicSum (unitTupleChineseRemainder n h x).2 =
          (ZMod.chineseRemainder h T).2 := by
  constructor
  · intro hx
    have hmapped := congrArg (ZMod.chineseRemainder h) hx
    rw [chineseRemainder_unitCubicSum] at hmapped
    exact Prod.ext_iff.mp hmapped
  · rintro ⟨h₁, h₂⟩
    apply (ZMod.chineseRemainder h).injective
    rw [chineseRemainder_unitCubicSum]
    exact Prod.ext h₁ h₂

/-- Exact CRT equivalence between the unit solution set modulo `q₁*q₂`
and the product of the two reduced unit solution sets. -/
noncomputable def unitCubicSolutionsChineseRemainder (n : ℕ)
    (h : q₁.Coprime q₂) (T : ZMod (q₁ * q₂)) :
    UnitCubicSolutions n T ≃
      UnitCubicSolutions n (ZMod.chineseRemainder h T).1 ×
        UnitCubicSolutions n (ZMod.chineseRemainder h T).2 :=
  ((unitTupleChineseRemainder n h).subtypeEquiv
      (fun x ↦ unitCubicSum_eq_iff_crt_components h T x)).trans
    Equiv.subtypeProdEquivProd

/-- Unit cubic solution counts are multiplicative in coprime moduli.  The
targets on the right are the two reductions of `T` under CRT. -/
theorem unitCubicSolutionCount_mul_of_coprime (n : ℕ)
    (h : q₁.Coprime q₂) (T : ZMod (q₁ * q₂)) :
    unitCubicSolutionCount n T =
      unitCubicSolutionCount n (ZMod.chineseRemainder h T).1 *
        unitCubicSolutionCount n (ZMod.chineseRemainder h T).2 := by
  classical
  calc
    unitCubicSolutionCount n T = Fintype.card (UnitCubicSolutions n T) :=
      (card_unitCubicSolutions n T).symm
    _ = Fintype.card
        (UnitCubicSolutions n (ZMod.chineseRemainder h T).1 ×
          UnitCubicSolutions n (ZMod.chineseRemainder h T).2) :=
      Fintype.card_congr (unitCubicSolutionsChineseRemainder n h T)
    _ = unitCubicSolutionCount n (ZMod.chineseRemainder h T).1 *
        unitCubicSolutionCount n (ZMod.chineseRemainder h T).2 := by
      rw [Fintype.card_prod, card_unitCubicSolutions, card_unitCubicSolutions]

/-- The same multiplicativity formula for a target represented by an
integer `T`; its two CRT reductions are simply the two natural casts. -/
theorem unitCubicSolutionCount_mul_of_coprime_natCast (n T : ℕ)
    (h : q₁.Coprime q₂) :
    unitCubicSolutionCount n (T : ZMod (q₁ * q₂)) =
      unitCubicSolutionCount n (T : ZMod q₁) *
        unitCubicSolutionCount n (T : ZMod q₂) := by
  simpa using unitCubicSolutionCount_mul_of_coprime n h
    (T : ZMod (q₁ * q₂))

end CookMagyarFiniteFourier
end SystolicGrowth
