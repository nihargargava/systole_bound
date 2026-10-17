module

public import BuserSarnak.FreeGroupNielsenWordPrograms

@[expose] public section

/-!
# An elementary Nielsen extraction of one handle

For the displayed interlacing pattern, two compiled basis changes isolate
`x⁻¹ y x y⁻¹`.  On a finite alphabet, compiled inner conjugation and one
final inversion place a standard handle at the front of the residual word.
-/

namespace SystolicGrowth

noncomputable section

namespace FreeGroupNielsenProgram

variable {X : Type*}

/-- The literal interlacing pattern used to extract one orientable handle. -/
def handleExtractionWord (x y : X) (A B1 B2 C1 C2 : SignedWord X) :
    SignedWord X :=
  A ++ [(x, false)] ++ B1 ++ [(y, true)] ++ B2 ++ [(x, true)] ++
    C1 ++ [(y, false)] ++ C2

/-- The five blocks, without the two distinguished generators. -/
def handleExtractionBlocks (A B1 B2 C1 C2 : SignedWord X) : SignedWord X :=
  A ++ B1 ++ B2 ++ C1 ++ C2

/-- The two certified basis changes: first modify `y`, then modify `x`.
Both multipliers are literal avoiding words, so the move list consists only
of the original elementary shears and inversions. -/
def handleExtractionProgram (x y : X) (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    List (FreeGroupNielsenMove X) := by
  have hxparts : WordAvoids x A ∧ WordAvoids x B1 ∧ WordAvoids x B2 ∧
      WordAvoids x C1 ∧ WordAvoids x C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hx
  have hyparts : WordAvoids y A ∧ WordAvoids y B1 ∧ WordAvoids y B2 ∧
      WordAvoids y C1 ∧ WordAvoids y C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hy
  exact twoSidedWord y (FreeGroup.invRev B1) (FreeGroup.invRev B2)
      hyparts.2.1.invRev hyparts.2.2.1.invRev ++
    rightWord x (FreeGroup.invRev (C1 ++ B2))
      (hxparts.2.2.2.1.append hxparts.2.2.1).invRev

private theorem mk_singleton (letter : X × Bool) :
    FreeGroup.mk [letter] =
      (if letter.2 then FreeGroup.of letter.1 else (FreeGroup.of letter.1)⁻¹) := by
  rcases letter with ⟨x, sign⟩
  cases sign <;> rfl

/-- The first basis change eliminates the two blocks adjoining `y`.
All word-fixation claims are derived from literal avoidance. -/
theorem handleExtraction_first_apply (x y : X) (hxy : x ≠ y)
    (A B1 B2 C1 C2 : SignedWord X)
    (hyA : WordAvoids y A) (hyB1 : WordAvoids y B1) (hyB2 : WordAvoids y B2)
    (hyC1 : WordAvoids y C1) (hyC2 : WordAvoids y C2) :
    toEquiv (twoSidedWord y (FreeGroup.invRev B1) (FreeGroup.invRev B2)
        hyB1.invRev hyB2.invRev)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2)) =
      FreeGroup.mk A * (FreeGroup.of x)⁻¹ * FreeGroup.of y * FreeGroup.of x *
        FreeGroup.mk (C1 ++ B2) * (FreeGroup.of y)⁻¹ * FreeGroup.mk (B1 ++ C2) := by
  simp only [handleExtractionWord, ← FreeGroup.mul_mk, mk_singleton,
    Bool.false_eq_true, ↓reduceIte, map_mul, map_inv,
    twoSidedWord_apply_mk_of_avoids y _ _ A hyB1.invRev hyB2.invRev hyA,
    twoSidedWord_apply_mk_of_avoids y _ _ B1 hyB1.invRev hyB2.invRev hyB1,
    twoSidedWord_apply_mk_of_avoids y _ _ B2 hyB1.invRev hyB2.invRev hyB2,
    twoSidedWord_apply_mk_of_avoids y _ _ C1 hyB1.invRev hyB2.invRev hyC1,
    twoSidedWord_apply_mk_of_avoids y _ _ C2 hyB1.invRev hyB2.invRev hyC2,
    twoSidedWord_apply_of_ne_source y _ _ hyB1.invRev hyB2.invRev x hxy,
    twoSidedWord_apply_source, ← FreeGroup.inv_mk]
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]

/-- The actual elementary program isolates one handle between explicit
prefix and suffix blocks. There is no automorphism-action proof input. -/
theorem handleExtractionProgram_apply (x y : X) (hxy : x ≠ y)
    (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    toEquiv (handleExtractionProgram x y A B1 B2 C1 C2 hx hy)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2)) =
      FreeGroup.mk (A ++ C1 ++ B2) * (FreeGroup.of x)⁻¹ * FreeGroup.of y *
        FreeGroup.of x * (FreeGroup.of y)⁻¹ * FreeGroup.mk (B1 ++ C2) := by
  have hxparts : WordAvoids x A ∧ WordAvoids x B1 ∧ WordAvoids x B2 ∧
      WordAvoids x C1 ∧ WordAvoids x C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hx
  have hyparts : WordAvoids y A ∧ WordAvoids y B1 ∧ WordAvoids y B2 ∧
      WordAvoids y C1 ∧ WordAvoids y C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hy
  dsimp only [handleExtractionProgram]
  rw [toEquiv_append]
  change toEquiv (rightWord x (FreeGroup.invRev (C1 ++ B2))
      (hxparts.2.2.2.1.append hxparts.2.2.1).invRev)
    (toEquiv (twoSidedWord y (FreeGroup.invRev B1) (FreeGroup.invRev B2)
      hyparts.2.1.invRev hyparts.2.2.1.invRev)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2))) = _
  rw [handleExtraction_first_apply x y hxy A B1 B2 C1 C2
    hyparts.1 hyparts.2.1 hyparts.2.2.1 hyparts.2.2.2.1 hyparts.2.2.2.2]
  simp only [map_mul, map_inv,
    rightWord_apply_mk_of_avoids x _ A _ hxparts.1,
    rightWord_apply_mk_of_avoids x _ B1 _ hxparts.2.1,
    rightWord_apply_mk_of_avoids x _ B2 _ hxparts.2.2.1,
    rightWord_apply_mk_of_avoids x _ C1 _ hxparts.2.2.2.1,
    rightWord_apply_mk_of_avoids x _ C2 _ hxparts.2.2.2.2,
    rightWord_apply_of_ne_source x _ _ y (Ne.symm hxy),
    rightWord_apply_source, ← FreeGroup.inv_mk, ← FreeGroup.mul_mk]
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

/-- Conjugating by the evaluated prefix moves the extracted handle to the
front and puts the remaining letters in their exact new cyclic order. -/
theorem handleExtractionProgram_conjugate (x y : X) (hxy : x ≠ y)
    (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    (FreeGroup.mk (A ++ C1 ++ B2))⁻¹ *
        toEquiv (handleExtractionProgram x y A B1 B2 C1 C2 hx hy)
          (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2)) *
        FreeGroup.mk (A ++ C1 ++ B2) =
      (FreeGroup.of x)⁻¹ * FreeGroup.of y * FreeGroup.of x * (FreeGroup.of y)⁻¹ *
        FreeGroup.mk (B1 ++ C2 ++ A ++ C1 ++ B2) := by
  rw [handleExtractionProgram_apply x y hxy A B1 B2 C1 C2 hx hy]
  simp only [← FreeGroup.mul_mk, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

section FiniteAlphabet

variable [Fintype X] [DecidableEq X]

/-- Append the elementary inner program implementing the required cyclic
conjugation. The resulting program still uses only shears and inversions. -/
def handleExtractionCyclicProgram (x y : X) (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    List (FreeGroupNielsenMove X) :=
  handleExtractionProgram x y A B1 B2 C1 C2 hx hy ++
    conjugateWord (FreeGroup.invRev (A ++ C1 ++ B2))

/-- The complete elementary cyclic program produces a handle followed by
the exact residual cyclic list. -/
theorem handleExtractionCyclicProgram_apply (x y : X) (hxy : x ≠ y)
    (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    toEquiv (handleExtractionCyclicProgram x y A B1 B2 C1 C2 hx hy)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2)) =
      (FreeGroup.of x)⁻¹ * FreeGroup.of y * FreeGroup.of x * (FreeGroup.of y)⁻¹ *
        FreeGroup.mk (B1 ++ C2 ++ A ++ C1 ++ B2) := by
  rw [handleExtractionCyclicProgram, toEquiv_append]
  change toEquiv (conjugateWord (FreeGroup.invRev (A ++ C1 ++ B2)))
    (toEquiv (handleExtractionProgram x y A B1 B2 C1 C2 hx hy)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2))) = _
  rw [conjugateWord_invRev_apply]
  exact handleExtractionProgram_conjugate x y hxy A B1 B2 C1 C2 hx hy

/-- The literal output after extracting a standard positively oriented
surface handle. Its residual blocks contain neither distinguished letter. -/
def handleExtractionStandardWord (x y : X) (A B1 B2 C1 C2 : SignedWord X) :
    SignedWord X :=
  [(x, true), (y, true), (x, false), (y, false)] ++
    (B1 ++ C2 ++ A ++ C1 ++ B2)

/-- Invert the extracted `x` once so its handle has the standard orientation. -/
def handleExtractionStandardProgram (x y : X) (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    List (FreeGroupNielsenMove X) :=
  handleExtractionCyclicProgram x y A B1 B2 C1 C2 hx hy ++ [.inversion x]

/-- The finite elementary move trace maps the interlacing word to the
literal standard handle followed by the residual word. -/
theorem handleExtractionStandardProgram_apply (x y : X) (hxy : x ≠ y)
    (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    toEquiv (handleExtractionStandardProgram x y A B1 B2 C1 C2 hx hy)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2)) =
      FreeGroup.mk (handleExtractionStandardWord x y A B1 B2 C1 C2) := by
  classical
  have hxparts : WordAvoids x A ∧ WordAvoids x B1 ∧ WordAvoids x B2 ∧
      WordAvoids x C1 ∧ WordAvoids x C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hx
  have hres : WordAvoids x (B1 ++ C2 ++ A ++ C1 ++ B2) :=
    (((hxparts.2.1.append hxparts.2.2.2.2).append hxparts.1).append
      hxparts.2.2.2.1).append hxparts.2.2.1
  have hfix : toEquiv [.inversion x]
      (FreeGroup.mk (B1 ++ C2 ++ A ++ C1 ++ B2)) =
      FreeGroup.mk (B1 ++ C2 ++ A ++ C1 ++ B2) := by
    apply toEquiv_apply_mk_of_fixes_letters
    intro letter hletter
    simp [toEquiv, FreeGroupNielsenMove.toEquiv, hres letter hletter]
  have hximage : toEquiv [.inversion x] (FreeGroup.of x) = (FreeGroup.of x)⁻¹ := by
    simp [toEquiv, FreeGroupNielsenMove.toEquiv]
  have hyimage : toEquiv [.inversion x] (FreeGroup.of y) = FreeGroup.of y := by
    simp [toEquiv, FreeGroupNielsenMove.toEquiv, Ne.symm hxy]
  rw [handleExtractionStandardProgram, toEquiv_append]
  change toEquiv [.inversion x]
    (toEquiv (handleExtractionCyclicProgram x y A B1 B2 C1 C2 hx hy)
      (FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2))) = _
  rw [handleExtractionCyclicProgram_apply x y hxy A B1 B2 C1 C2 hx hy]
  simp only [map_mul, map_inv, hfix, hximage, hyimage, inv_inv]
  rw [handleExtractionStandardWord, ← FreeGroup.mul_mk]
  rfl

end FiniteAlphabet

end FreeGroupNielsenProgram

end

end SystolicGrowth

#print axioms SystolicGrowth.FreeGroupNielsenProgram.handleExtraction_first_apply
#print axioms SystolicGrowth.FreeGroupNielsenProgram.handleExtractionProgram_apply
#print axioms SystolicGrowth.FreeGroupNielsenProgram.handleExtractionProgram_conjugate
#print axioms SystolicGrowth.FreeGroupNielsenProgram.handleExtractionCyclicProgram_apply
#print axioms SystolicGrowth.FreeGroupNielsenProgram.handleExtractionStandardProgram_apply
