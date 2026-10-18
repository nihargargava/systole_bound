module

public import BuserSarnak.BuserSarnakProjectivePostConeRootWordNielsen

@[expose] public section

/-!
# Signed-letter Nielsen programs

Programs execute their head first.  Each signed multiplication below is
expanded into the existing elementary shear and inversion constructors;
neither a new move nor an asserted automorphism is needed.
-/

namespace SystolicGrowth

noncomputable section

namespace FreeGroupNielsenProgram

variable {X : Type*}

/-- Concatenation executes the first program before the second program. -/
@[simp] theorem toEquiv_append
    (P Q : List (FreeGroupNielsenMove X)) :
    toEquiv (P ++ Q) = (toEquiv P).trans (toEquiv Q) := by
  induction P with
  | nil =>
      ext w
      rfl
  | cons move P ih =>
      ext w
      simp only [List.cons_append, toEquiv_cons, ih, MulEquiv.trans_apply]

/-- Multiply `a` on the right by a signed letter.  The Boolean convention is
`true` for the generator and `false` for its inverse. -/
def rightLetter (a : X) (letter : X × Bool) (hab : a ≠ letter.1) :
    List (FreeGroupNielsenMove X) :=
  if letter.2 then
    [.shear a letter.1 hab]
  else
    [.inversion letter.1, .shear a letter.1 hab, .inversion letter.1]

/-- The right-letter program has the stated action on its target generator. -/
@[simp] theorem rightLetter_apply_source
    (a : X) (letter : X × Bool) (hab : a ≠ letter.1) :
    toEquiv (rightLetter a letter hab) (FreeGroup.of a) =
      FreeGroup.of a *
        (if letter.2 then FreeGroup.of letter.1 else (FreeGroup.of letter.1)⁻¹) := by
  classical
  rcases letter with ⟨b, sign⟩
  cases sign <;>
    simp [rightLetter, toEquiv, FreeGroupNielsenMove.toEquiv, hab]

/-- The right-letter program fixes every generator other than its target,
including the multiplier generator. -/
@[simp] theorem rightLetter_apply_of_ne_source
    (a : X) (letter : X × Bool) (hab : a ≠ letter.1)
    (x : X) (hx : x ≠ a) :
    toEquiv (rightLetter a letter hab) (FreeGroup.of x) = FreeGroup.of x := by
  classical
  rcases letter with ⟨b, sign⟩
  cases sign
  · by_cases hxb : x = b
    · subst x
      simp [rightLetter, toEquiv, FreeGroupNielsenMove.toEquiv, Ne.symm hab]
    · simp [rightLetter, toEquiv, FreeGroupNielsenMove.toEquiv, hx, hxb]
  · simp [rightLetter, toEquiv, FreeGroupNielsenMove.toEquiv, hx]

/-- Multiply `a` on the left by a signed letter, using target inversion,
the oppositely signed right-letter program, and target inversion again. -/
def leftLetter (a : X) (letter : X × Bool) (hab : a ≠ letter.1) :
    List (FreeGroupNielsenMove X) :=
  [.inversion a] ++ rightLetter a (letter.1, !letter.2) hab ++ [.inversion a]

/-- The left-letter program has the stated action on its target generator. -/
@[simp] theorem leftLetter_apply_source
    (a : X) (letter : X × Bool) (hab : a ≠ letter.1) :
    toEquiv (leftLetter a letter hab) (FreeGroup.of a) =
      (if letter.2 then FreeGroup.of letter.1 else (FreeGroup.of letter.1)⁻¹) *
        FreeGroup.of a := by
  classical
  rcases letter with ⟨b, sign⟩
  cases sign <;>
    simp [leftLetter, toEquiv_append, toEquiv, FreeGroupNielsenMove.toEquiv,
      Ne.symm hab, rightLetter_apply_source]

/-- The left-letter program fixes every generator other than its target. -/
@[simp] theorem leftLetter_apply_of_ne_source
    (a : X) (letter : X × Bool) (hab : a ≠ letter.1)
    (x : X) (hx : x ≠ a) :
    toEquiv (leftLetter a letter hab) (FreeGroup.of x) = FreeGroup.of x := by
  classical
  simp [leftLetter, toEquiv_append, toEquiv, FreeGroupNielsenMove.toEquiv,
    hx, rightLetter_apply_of_ne_source]

end FreeGroupNielsenProgram

#print axioms FreeGroupNielsenProgram.toEquiv_append
#print axioms FreeGroupNielsenProgram.rightLetter_apply_source
#print axioms FreeGroupNielsenProgram.rightLetter_apply_of_ne_source
#print axioms FreeGroupNielsenProgram.leftLetter_apply_source
#print axioms FreeGroupNielsenProgram.leftLetter_apply_of_ne_source

end

end SystolicGrowth
