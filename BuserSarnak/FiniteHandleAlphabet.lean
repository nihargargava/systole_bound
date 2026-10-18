module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sum

@[expose] public section

/-!
# Alphabet splitting for a distinguished handle

Two distinct handle generators are separated from the literal remaining
alphabet. The explicit generator equivalence supplies the renaming interface
and proves the exact cardinality decrease needed by handle induction.
-/

namespace SystolicGrowth

noncomputable section

/-- The actual generators remaining after deleting the selected handle pair. -/
abbrev HandleRemainingAlphabet {X : Type*} (x y : X) :=
  {z : X // z ≠ x ∧ z ≠ y}

/-- The remaining alphabet is finite without requiring decidable equality
as additional mathematical data. -/
instance handleRemainingAlphabetFintype {X : Type*} [Fintype X] (x y : X) :
    Fintype (HandleRemainingAlphabet x y) := Fintype.ofFinite _

/-- Explicitly insert the selected handle pair and every remaining generator.
The Boolean handle labels `false` and `true` denote `x` and `y`, respectively. -/
def handleAlphabetEquiv {X : Type*} (x y : X) (hxy : x ≠ y) :
    Bool ⊕ HandleRemainingAlphabet x y ≃ X := by
  classical
  exact {
    toFun := fun
      | Sum.inl bit => if bit then y else x
      | Sum.inr z => z.val
    invFun := fun z =>
      if hzx : z = x then Sum.inl false
      else if hzy : z = y then Sum.inl true
      else Sum.inr ⟨z, hzx, hzy⟩
    left_inv := by
      intro z
      cases z with
      | inl bit => cases bit <;> simp [Ne.symm hxy]
      | inr z => simp [z.property.1, z.property.2]
    right_inv := by
      intro z
      by_cases hzx : z = x
      · subst z
        simp
      · by_cases hzy : z = y
        · subst z
          simp [hzx]
        · simp [hzx, hzy]
  }

/-- The first distinguished handle letter is the chosen generator `x`. -/
@[simp] theorem handleAlphabetEquiv_inl_false {X : Type*} (x y : X) (hxy : x ≠ y) :
    handleAlphabetEquiv x y hxy (Sum.inl false) = x := rfl

/-- The second distinguished handle letter is the chosen generator `y`. -/
@[simp] theorem handleAlphabetEquiv_inl_true {X : Type*} (x y : X) (hxy : x ≠ y) :
    handleAlphabetEquiv x y hxy (Sum.inl true) = y := rfl

/-- Every remaining generator is inserted by its actual subtype value. -/
@[simp] theorem handleAlphabetEquiv_inr {X : Type*} (x y : X) (hxy : x ≠ y)
    (z : HandleRemainingAlphabet x y) :
    handleAlphabetEquiv x y hxy (Sum.inr z) = z.val := rfl

/-- The inverse renaming sends `x` to the first handle letter. -/
@[simp] theorem handleAlphabetEquiv_symm_x {X : Type*} (x y : X) (hxy : x ≠ y) :
    (handleAlphabetEquiv x y hxy).symm x = Sum.inl false :=
  (handleAlphabetEquiv x y hxy).symm_apply_apply (Sum.inl false)

/-- The inverse renaming sends `y` to the second handle letter. -/
@[simp] theorem handleAlphabetEquiv_symm_y {X : Type*} (x y : X) (hxy : x ≠ y) :
    (handleAlphabetEquiv x y hxy).symm y = Sum.inl true :=
  (handleAlphabetEquiv x y hxy).symm_apply_apply (Sum.inl true)

/-- The inverse renaming preserves the exact remaining generator witness. -/
@[simp] theorem handleAlphabetEquiv_symm_remaining {X : Type*} (x y : X) (hxy : x ≠ y)
    (z : HandleRemainingAlphabet x y) :
    (handleAlphabetEquiv x y hxy).symm z.val = Sum.inr z :=
  (handleAlphabetEquiv x y hxy).symm_apply_apply (Sum.inr z)

/-- Removing a distinct handle pair decreases the alphabet size by exactly two. -/
theorem handleRemainingAlphabet_card_add_two {X : Type*} [Fintype X]
    (x y : X) (hxy : x ≠ y) :
    Fintype.card (HandleRemainingAlphabet x y) + 2 = Fintype.card X := by
  classical
  have hc := Fintype.card_congr (handleAlphabetEquiv x y hxy)
  simp only [Fintype.card_sum, Fintype.card_bool] at hc
  omega

/-- The remaining alphabet has the expected natural-subtraction cardinality. -/
theorem handleRemainingAlphabet_card_eq_sub_two {X : Type*} [Fintype X]
    (x y : X) (hxy : x ≠ y) :
    Fintype.card (HandleRemainingAlphabet x y) = Fintype.card X - 2 := by
  classical
  have hc := handleRemainingAlphabet_card_add_two x y hxy
  omega

/-- Handle extraction strictly decreases the finite alphabet induction measure. -/
theorem handleRemainingAlphabet_card_lt {X : Type*} [Fintype X]
    (x y : X) (hxy : x ≠ y) :
    Fintype.card (HandleRemainingAlphabet x y) < Fintype.card X := by
  classical
  have hc := handleRemainingAlphabet_card_add_two x y hxy
  omega

#print axioms handleAlphabetEquiv
#print axioms handleRemainingAlphabet_card_add_two
#print axioms handleRemainingAlphabet_card_lt

end

end SystolicGrowth
