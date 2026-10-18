module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.CircleMethod
public import Mathlib.Combinatorics.Additive.CauchyDavenport
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Polynomial
open scoped Pointwise

namespace SystolicGrowth
namespace CookMagyarLocal

/-! # Local solubility of the cubic `x ^ 3 - x`

This file proves the local-solubility statement used in the singular-series
argument.  If `q >= 5` is prime, every residue modulo `q` is a sum of four
values `x ^ 3 - x`, with all four inputs nonzero.

For `q >= 13`, the proof combines the degree-three bound for the image of a
polynomial over a finite field with Cauchy--Davenport.  The remaining prime
moduli `5`, `7`, and `11` are closed finite computations evaluated by Lean's
kernel.
-/

/-- The cubic map on a residue ring. -/
def cubicResidue {q : ℕ} (x : ZMod q) : ZMod q := x ^ 3 - x

/-- Values of `x ^ 3 - x` attained at nonzero residues modulo `q`. -/
def nonzeroCubicValues (q : ℕ) [NeZero q] : Finset (ZMod q) :=
  (Finset.univ.erase 0).image cubicResidue

@[simp] theorem mem_nonzeroCubicValues {q : ℕ} [NeZero q] {y : ZMod q} :
    y ∈ nonzeroCubicValues q ↔ ∃ x : ZMod q, x ≠ 0 ∧ cubicResidue x = y := by
  simp [nonzeroCubicValues]

/-- Removing zero from the domain does not change the image: the value at
zero is also attained at `1`. -/
theorem nonzeroCubicValues_eq_image_univ (q : ℕ) [NeZero q] (hq : 1 < q) :
    nonzeroCubicValues q = Finset.univ.image cubicResidue := by
  letI : Fact (1 < q) := ⟨hq⟩
  ext y
  constructor
  · intro hy
    rcases (mem_nonzeroCubicValues.mp hy) with ⟨x, _hx, rfl⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨x, _hx, rfl⟩
    by_cases hx : x = 0
    · subst x
      exact mem_nonzeroCubicValues.mpr
        ⟨(1 : ZMod q), one_ne_zero, by simp [cubicResidue]⟩
    · exact mem_nonzeroCubicValues.mpr ⟨x, hx, rfl⟩

/-- Polynomial whose evaluation is `cubicResidue`. -/
noncomputable def cubicPolynomial (q : ℕ) : (ZMod q)[X] :=
  C 1 * X ^ 3 + C 0 * X ^ 2 + C (-1) * X + C 0

@[simp] theorem eval_cubicPolynomial {q : ℕ} (x : ZMod q) :
    Polynomial.eval x (cubicPolynomial q) = cubicResidue x := by
  simp [cubicPolynomial, cubicResidue, sub_eq_add_neg]

/-- A degree-three polynomial has at least one image value for every three
elements of the finite field. -/
theorem card_nonzeroCubicValues_lower {q : ℕ} [NeZero q] (hq : q.Prime) :
    q ≤ 3 * (nonzeroCubicValues q).card := by
  letI : Fact q.Prime := ⟨hq⟩
  have hdegree_eq : (cubicPolynomial q).degree = 3 := by
    simpa [cubicPolynomial] using
      (Polynomial.degree_cubic (R := ZMod q) (a := (1 : ZMod q))
        (b := 0) (c := -1) (d := 0) one_ne_zero)
  have hdegree : 0 < (cubicPolynomial q).degree := by
    rw [hdegree_eq]
    norm_num
  have hcard := FiniteField.card_image_polynomial_eval hdegree
  have hnatDegree : (cubicPolynomial q).natDegree = 3 := by
    simpa [cubicPolynomial] using
      (Polynomial.natDegree_cubic (R := ZMod q) (a := (1 : ZMod q))
        (b := 0) (c := -1) (d := 0) one_ne_zero)
  have himage :
      Finset.univ.image (fun x : ZMod q => Polynomial.eval x (cubicPolynomial q)) =
        nonzeroCubicValues q := by
    rw [nonzeroCubicValues_eq_image_univ q hq.one_lt]
    apply Finset.image_congr
    intro x _hx
    exact eval_cubicPolynomial x
  rw [ZMod.card, hnatDegree, himage] at hcard
  exact hcard

/-- The image contains zero, hence is nonempty. -/
theorem nonzeroCubicValues_nonempty (q : ℕ) [NeZero q] (hq : 1 < q) :
    (nonzeroCubicValues q).Nonempty := by
  letI : Fact (1 < q) := ⟨hq⟩
  refine ⟨0, mem_nonzeroCubicValues.mpr ?_⟩
  exact ⟨(1 : ZMod q), one_ne_zero, by simp [cubicResidue]⟩

/-- Cauchy--Davenport makes the fourfold sumset of the cubic image equal to
the whole field once `q >= 13`. -/
theorem fourfold_nonzeroCubicValues_eq_univ {q : ℕ} [NeZero q]
    (hq : q.Prime) (hq13 : 13 ≤ q) :
    (nonzeroCubicValues q + nonzeroCubicValues q) +
        (nonzeroCubicValues q + nonzeroCubicValues q) = Finset.univ := by
  letI : Fact q.Prime := ⟨hq⟩
  let A : Finset (ZMod q) := nonzeroCubicValues q
  have hA : A.Nonempty := nonzeroCubicValues_nonempty q hq.one_lt
  have hAA : (A + A).Nonempty := hA.add hA
  have hcardA : q ≤ 3 * A.card := card_nonzeroCubicValues_lower hq
  have hfirst := ZMod.cauchy_davenport hq hA hA
  have hsecond := ZMod.cauchy_davenport hq hAA hAA
  have hq_le_twice_cardAA_sub_one :
      q ≤ (A + A).card + (A + A).card - 1 := by
    by_cases hqAA : q ≤ A.card + A.card - 1
    · have hq_le_cardAA : q ≤ (A + A).card := by
        rw [Nat.min_eq_left hqAA] at hfirst
        exact hfirst
      omega
    · have htwo_cardA_sub_one_le : A.card + A.card - 1 ≤ (A + A).card := by
        rw [Nat.min_eq_right (Nat.le_of_not_ge hqAA)] at hfirst
        exact hfirst
      omega
  have hlower : q ≤ ((A + A) + (A + A)).card := by
    rw [Nat.min_eq_left hq_le_twice_cardAA_sub_one] at hsecond
    exact hsecond
  apply Finset.eq_univ_of_card
  have hupper : ((A + A) + (A + A)).card ≤ q := by
    simpa [ZMod.card] using
      (Finset.card_le_univ ((A + A) + (A + A)))
  change ((A + A) + (A + A)).card = Fintype.card (ZMod q)
  rw [ZMod.card]
  exact Nat.le_antisymm hupper hlower

/-- Four-variable formulation of the local-solubility conclusion. -/
def FourNonzeroCubicRepresentation (q : ℕ) (t : ZMod q) : Prop :=
  ∃ x₁ x₂ x₃ x₄ : ZMod q,
    x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧
      cubicResidue x₁ + cubicResidue x₂ +
          cubicResidue x₃ + cubicResidue x₄ = t

set_option maxRecDepth 100000 in
private theorem fourfold_nonzeroCubicValues_mod_five :
    (nonzeroCubicValues 5 + nonzeroCubicValues 5) +
        (nonzeroCubicValues 5 + nonzeroCubicValues 5) = Finset.univ := by
  decide

set_option maxRecDepth 100000 in
private theorem fourfold_nonzeroCubicValues_mod_seven :
    (nonzeroCubicValues 7 + nonzeroCubicValues 7) +
        (nonzeroCubicValues 7 + nonzeroCubicValues 7) = Finset.univ := by
  decide

set_option maxRecDepth 100000 in
private theorem fourfold_nonzeroCubicValues_mod_eleven :
    (nonzeroCubicValues 11 + nonzeroCubicValues 11) +
        (nonzeroCubicValues 11 + nonzeroCubicValues 11) = Finset.univ := by
  decide

/-- **Local cubic solubility.**  For every prime `q >= 5` and every target
`t` modulo `q`, there are four nonzero residues whose `x ^ 3 - x` values sum
to `t`. -/
theorem four_nonzero_cubic_surjective {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (t : ZMod q) : FourNonzeroCubicRepresentation q t := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  have hall :
      (nonzeroCubicValues q + nonzeroCubicValues q) +
          (nonzeroCubicValues q + nonzeroCubicValues q) = Finset.univ := by
    rcases lt_or_ge q 13 with hq_lt | hq13
    · interval_cases q
      · exact fourfold_nonzeroCubicValues_mod_five
      · norm_num at hq
      · exact fourfold_nonzeroCubicValues_mod_seven
      · norm_num at hq
      · norm_num at hq
      · norm_num at hq
      · exact fourfold_nonzeroCubicValues_mod_eleven
      · norm_num at hq
    · exact fourfold_nonzeroCubicValues_eq_univ hq hq13
  let A : Finset (ZMod q) := nonzeroCubicValues q
  have hallA : (A + A) + (A + A) = Finset.univ := by
    simpa [A] using hall
  have ht : t ∈ (A + A) + (A + A) := by
      rw [hallA]
      exact Finset.mem_univ t
  rcases Finset.mem_add.mp ht with ⟨u, hu, v, hv, huv⟩
  rcases Finset.mem_add.mp hu with ⟨a₁, ha₁, a₂, ha₂, ha⟩
  rcases Finset.mem_add.mp hv with ⟨a₃, ha₃, a₄, ha₄, hb⟩
  rcases (mem_nonzeroCubicValues.mp ha₁) with ⟨x₁, hx₁, rfl⟩
  rcases (mem_nonzeroCubicValues.mp ha₂) with ⟨x₂, hx₂, rfl⟩
  rcases (mem_nonzeroCubicValues.mp ha₃) with ⟨x₃, hx₃, rfl⟩
  rcases (mem_nonzeroCubicValues.mp ha₄) with ⟨x₄, hx₄, rfl⟩
  refine ⟨x₁, x₂, x₃, x₄, hx₁, hx₂, hx₃, hx₄, ?_⟩
  rw [← huv, ← ha, ← hb]
  abel

end CookMagyarLocal
end SystolicGrowth
