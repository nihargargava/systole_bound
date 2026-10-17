module

public import BuserSarnak.OrientableWicksHandleChoice
public import BuserSarnak.FreeGroupHandleExtraction

@[expose] public section

/-!
# Elementary extraction from an actual Wicks certificate

The certificate supplies the crossing and literal blocks. At most two
generator inversions normalize their signs, then the existing elementary
handle compiler places the standard handle before its exact residual word.
The residual one-vertex certificate is a separate combinatorial obligation.
-/

namespace SystolicGrowth

noncomputable section

namespace FreeGroupNielsenProgram

variable {X : Type*}

/-- Normalize the first `x` occurrence to negative and the first `y`
occurrence to positive, using only original generator-inversion moves. -/
def handleOrientationProgram (x y : X) (sx sy : Bool) :
    List (FreeGroupNielsenMove X) :=
  (if sx then [.inversion x] else []) ++
    (if sy then [] else [.inversion y])

/-- The orientation program's exact action on the first handle generator. -/
theorem handleOrientationProgram_apply_x (x y : X) (hxy : x ≠ y) (sx sy : Bool) :
    toEquiv (handleOrientationProgram x y sx sy) (FreeGroup.of x) =
      if sx then (FreeGroup.of x)⁻¹ else FreeGroup.of x := by
  classical
  cases sx <;> cases sy <;>
    simp [handleOrientationProgram, toEquiv,
      FreeGroupNielsenMove.toEquiv, hxy]

/-- The orientation program's exact action on the second handle generator. -/
theorem handleOrientationProgram_apply_y (x y : X) (hxy : x ≠ y) (sx sy : Bool) :
    toEquiv (handleOrientationProgram x y sx sy) (FreeGroup.of y) =
      if sy then FreeGroup.of y else (FreeGroup.of y)⁻¹ := by
  classical
  cases sx <;> cases sy <;>
    simp [handleOrientationProgram, toEquiv,
      FreeGroupNielsenMove.toEquiv, Ne.symm hxy]

/-- Both optional inversions fix every generator outside the selected pair. -/
theorem handleOrientationProgram_apply_other (x y : X) (sx sy : Bool)
    (z : X) (hzx : z ≠ x) (hzy : z ≠ y) :
    toEquiv (handleOrientationProgram x y sx sy) (FreeGroup.of z) = FreeGroup.of z := by
  classical
  cases sx <;> cases sy <;>
    simp [handleOrientationProgram, toEquiv,
      FreeGroupNielsenMove.toEquiv, hzx, hzy]

/-- Avoiding blocks retain their literal evaluation under sign normalization. -/
theorem handleOrientationProgram_apply_mk (x y : X) (sx sy : Bool) (block : SignedWord X)
    (hx : WordAvoids x block) (hy : WordAvoids y block) :
    toEquiv (handleOrientationProgram x y sx sy) (FreeGroup.mk block) =
      FreeGroup.mk block :=
  toEquiv_apply_mk_of_fixes_letters _ block fun letter hletter =>
    handleOrientationProgram_apply_other x y sx sy letter.1
      (hx letter hletter) (hy letter hletter)

/-- The literal alternating word before the two sign-normalizing inversions. -/
def handleExtractionSignedWord (x y : X) (sx sy : Bool)
    (A B1 B2 C1 C2 : SignedWord X) : SignedWord X :=
  A ++ [(x, sx)] ++ B1 ++ [(y, sy)] ++ B2 ++ [(x, !sx)] ++
    C1 ++ [(y, !sy)] ++ C2

private theorem mk_singleton (letter : X × Bool) :
    FreeGroup.mk [letter] =
      (if letter.2 then FreeGroup.of letter.1 else (FreeGroup.of letter.1)⁻¹) := by
  rcases letter with ⟨x, sign⟩
  cases sign <;> rfl

/-- Normalize all four handle signs while fixing the five avoiding blocks. -/
theorem handleOrientationProgram_apply_signedWord (x y : X) (hxy : x ≠ y) (sx sy : Bool)
    (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    toEquiv (handleOrientationProgram x y sx sy)
      (FreeGroup.mk (handleExtractionSignedWord x y sx sy A B1 B2 C1 C2)) =
      FreeGroup.mk (handleExtractionWord x y A B1 B2 C1 C2) := by
  have hxparts : WordAvoids x A ∧ WordAvoids x B1 ∧ WordAvoids x B2 ∧
      WordAvoids x C1 ∧ WordAvoids x C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hx
  have hyparts : WordAvoids y A ∧ WordAvoids y B1 ∧ WordAvoids y B2 ∧
      WordAvoids y C1 ∧ WordAvoids y C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hy
  simp only [handleExtractionSignedWord, handleExtractionWord, ← FreeGroup.mul_mk,
    mk_singleton, map_mul,
    handleOrientationProgram_apply_mk x y sx sy A hxparts.1 hyparts.1,
    handleOrientationProgram_apply_mk x y sx sy B1 hxparts.2.1 hyparts.2.1,
    handleOrientationProgram_apply_mk x y sx sy B2 hxparts.2.2.1 hyparts.2.2.1,
    handleOrientationProgram_apply_mk x y sx sy C1 hxparts.2.2.2.1 hyparts.2.2.2.1,
    handleOrientationProgram_apply_mk x y sx sy C2 hxparts.2.2.2.2 hyparts.2.2.2.2]
  cases sx <;> cases sy <;>
    simp [map_inv, handleOrientationProgram_apply_x, handleOrientationProgram_apply_y, hxy]

/-- Compile sign normalization followed by the exact standard-handle program. -/
def handleExtractionSignedProgram [Fintype X] [DecidableEq X]
    (x y : X) (sx sy : Bool) (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    List (FreeGroupNielsenMove X) :=
  handleOrientationProgram x y sx sy ++
    handleExtractionStandardProgram x y A B1 B2 C1 C2 hx hy

/-- The actual elementary trace maps any signed interlacing pattern to the
standard handle with the exact residual block order. -/
theorem handleExtractionSignedProgram_apply [Fintype X] [DecidableEq X]
    (x y : X) (hxy : x ≠ y) (sx sy : Bool) (A B1 B2 C1 C2 : SignedWord X)
    (hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2))
    (hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2)) :
    toEquiv (handleExtractionSignedProgram x y sx sy A B1 B2 C1 C2 hx hy)
      (FreeGroup.mk (handleExtractionSignedWord x y sx sy A B1 B2 C1 C2)) =
      FreeGroup.mk (handleExtractionStandardWord x y A B1 B2 C1 C2) := by
  rw [handleExtractionSignedProgram, toEquiv_append]
  change toEquiv (handleExtractionStandardProgram x y A B1 B2 C1 C2 hx hy)
    (toEquiv (handleOrientationProgram x y sx sy)
      (FreeGroup.mk (handleExtractionSignedWord x y sx sy A B1 B2 C1 C2))) = _
  rw [handleOrientationProgram_apply_signedWord x y hxy sx sy A B1 B2 C1 C2 hx hy,
    handleExtractionStandardProgram_apply x y hxy A B1 B2 C1 C2 hx hy]

end FreeGroupNielsenProgram

namespace OrientableWicksCertificate

open FreeGroupNielsenProgram

variable {X : Type*} [Fintype X] {w : SignedWord X}

/-- Extract one standard handle from a nonempty Wicks word by an actual
elementary move list. The certificate derives crossing, literal splitting,
block avoidance, and the evaluated action; no such conclusion is an input. -/
theorem exists_standard_handle_program_with_split (C : OrientableWicksCertificate w)
    (initial : X) :
    ∃ (x y : X) (sx sy : Bool) (A B1 B2 C1 C2 : SignedWord X)
        (moves : List (FreeGroupNielsenMove X)),
      x ≠ y ∧
      (w = A ++ (x, sx) :: (B1 ++ (y, sy) ::
        (B2 ++ (x, !sx) :: (C1 ++ (y, !sy) :: C2)))) ∧
      WordAvoids x (B1 ++ C2 ++ A ++ C1 ++ B2) ∧
      WordAvoids y (B1 ++ C2 ++ A ++ C1 ++ B2) ∧
      toEquiv moves (FreeGroup.mk w) =
        FreeGroup.mk ([(x, true), (y, true), (x, false), (y, false)] ++
          (B1 ++ C2 ++ A ++ C1 ++ B2)) := by
  classical
  obtain ⟨x, y, sx, sy, A, B1, B2, C1, C2, hxy, hsplit, havoid⟩ :=
    C.exists_alternating_blocks_avoiding initial
  have hx : WordAvoids x (handleExtractionBlocks A B1 B2 C1 C2) :=
    fun letter hletter => (havoid letter hletter).1
  have hy : WordAvoids y (handleExtractionBlocks A B1 B2 C1 C2) :=
    fun letter hletter => (havoid letter hletter).2
  have hxparts : WordAvoids x A ∧ WordAvoids x B1 ∧ WordAvoids x B2 ∧
      WordAvoids x C1 ∧ WordAvoids x C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hx
  have hyparts : WordAvoids y A ∧ WordAvoids y B1 ∧ WordAvoids y B2 ∧
      WordAvoids y C1 ∧ WordAvoids y C2 := by
    simpa only [handleExtractionBlocks, wordAvoids_append, and_assoc] using hy
  refine ⟨x, y, sx, sy, A, B1, B2, C1, C2,
    handleExtractionSignedProgram x y sx sy A B1 B2 C1 C2 hx hy, hxy, hsplit,
    (((hxparts.2.1.append hxparts.2.2.2.2).append hxparts.1).append
      hxparts.2.2.2.1).append hxparts.2.2.1,
    (((hyparts.2.1.append hyparts.2.2.2.2).append hyparts.1).append
      hyparts.2.2.2.1).append hyparts.2.2.1, ?_⟩
  have hw : w = handleExtractionSignedWord x y sx sy A B1 B2 C1 C2 := by
    simpa only [handleExtractionSignedWord, List.append_assoc,
      List.singleton_append, List.cons_append, List.nil_append] using hsplit
  rw [hw]
  exact handleExtractionSignedProgram_apply x y hxy sx sy A B1 B2 C1 C2 hx hy

/-- Every nonempty Wicks certificate has an elementary standard-handle
extraction with a residual word avoiding its two distinguished generators. -/
theorem exists_standard_handle_program (C : OrientableWicksCertificate w) (initial : X) :
    ∃ (x y : X) (A B1 B2 C1 C2 : SignedWord X) (moves : List (FreeGroupNielsenMove X)),
      x ≠ y ∧ WordAvoids x (B1 ++ C2 ++ A ++ C1 ++ B2) ∧
      WordAvoids y (B1 ++ C2 ++ A ++ C1 ++ B2) ∧
      toEquiv moves (FreeGroup.mk w) =
        FreeGroup.mk ([(x, true), (y, true), (x, false), (y, false)] ++
          (B1 ++ C2 ++ A ++ C1 ++ B2)) := by
  obtain ⟨x, y, _, _, A, B1, B2, C1, C2, moves, hxy, _, hx, hy, haction⟩ :=
    C.exists_standard_handle_program_with_split initial
  exact ⟨x, y, A, B1, B2, C1, C2, moves, hxy, hx, hy, haction⟩

end OrientableWicksCertificate

#print axioms FreeGroupNielsenProgram.handleOrientationProgram_apply_signedWord
#print axioms FreeGroupNielsenProgram.handleExtractionSignedProgram_apply
#print axioms OrientableWicksCertificate.exists_standard_handle_program_with_split
#print axioms OrientableWicksCertificate.exists_standard_handle_program

end

end SystolicGrowth
