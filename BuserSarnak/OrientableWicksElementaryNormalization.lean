module

public import BuserSarnak.FreeGroupWicksHandleProgram
public import BuserSarnak.FreeGroupNielsenProgramTransport
public import BuserSarnak.FiniteHandleAlphabet
public import BuserSarnak.SurfaceHandleRelator
public import BuserSarnak.OrientableWicksResidualCertificate

@[expose] public section

/-!
# Elementary normalization of orientable Wicks words

The induction uses actual generator inversions and shears. Recursive moves
are lifted from the strictly smaller remaining alphabet, fixing the extracted
handle. Final renaming is the explicit handle-plus-tail alphabet equivalence.
-/

namespace SystolicGrowth

universe u

open scoped commutatorElement

noncomputable section

namespace OrientableWicksCertificate

open FreeGroupNielsenProgram

/-- Assemble the extracted pair with the recursively normalized tail alphabet. -/
def handleInductiveRename {X : Type*} (x y : X) (hxy : x ≠ y) (g : ℕ)
    (tailRename : HandleRemainingAlphabet x y ≃ SurfaceGenerator g) :
    X ≃ SurfaceGenerator (g + 1) :=
  (handleAlphabetEquiv x y hxy).symm.trans
    ((Equiv.sumCongr (Equiv.refl Bool) tailRename).trans
      (surfaceHandleGeneratorEquiv g).symm)

@[simp] theorem handleInductiveRename_x {X : Type*} (x y : X) (hxy : x ≠ y) (g : ℕ)
    (tailRename : HandleRemainingAlphabet x y ≃ SurfaceGenerator g) :
    handleInductiveRename x y hxy g tailRename x = (0, false) := by
  simp [handleInductiveRename]

@[simp] theorem handleInductiveRename_y {X : Type*} (x y : X) (hxy : x ≠ y) (g : ℕ)
    (tailRename : HandleRemainingAlphabet x y ≃ SurfaceGenerator g) :
    handleInductiveRename x y hxy g tailRename y = (0, true) := by
  simp [handleInductiveRename]

/-- Actual remaining generators are inserted in the successor-indexed tail. -/
@[simp] theorem handleInductiveRename_remaining {X : Type*} (x y : X) (hxy : x ≠ y) (g : ℕ)
    (tailRename : HandleRemainingAlphabet x y ≃ SurfaceGenerator g)
    (z : HandleRemainingAlphabet x y) :
    handleInductiveRename x y hxy g tailRename z.val =
      surfaceTailGeneratorEmbedding g (tailRename z) := by
  simp [handleInductiveRename, surfaceTailGeneratorEmbedding]

private theorem lift_remaining_program_fix_x {X : Type*} (x y : X)
    (moves : List (FreeGroupNielsenMove (HandleRemainingAlphabet x y))) :
    toEquiv (liftProgram Subtype.val Subtype.val_injective moves) (FreeGroup.of x) =
      FreeGroup.of x := by
  apply liftProgram_apply_of_not_mem_range
  rintro ⟨z, hz⟩
  exact z.property.1 hz

private theorem lift_remaining_program_fix_y {X : Type*} (x y : X)
    (moves : List (FreeGroupNielsenMove (HandleRemainingAlphabet x y))) :
    toEquiv (liftProgram Subtype.val Subtype.val_injective moves) (FreeGroup.of y) =
      FreeGroup.of y := by
  apply liftProgram_apply_of_not_mem_range
  rintro ⟨z, hz⟩
  exact z.property.2 hz

/-- The lifted recursive trace fixes the first handle and has the exact old
action on the typed residual, under the explicit handle-plus-tail renaming. -/
theorem normalize_extracted_handle {X : Type*} (x y : X) (hxy : x ≠ y)
    (g : ℕ) (residual : SignedWord (HandleRemainingAlphabet x y))
    (moves : List (FreeGroupNielsenMove (HandleRemainingAlphabet x y)))
    (tailRename : HandleRemainingAlphabet x y ≃ SurfaceGenerator g)
    (htail : FreeGroup.freeGroupCongr tailRename (toEquiv moves (FreeGroup.mk residual)) =
      surfaceRelator g) :
    FreeGroup.freeGroupCongr (handleInductiveRename x y hxy g tailRename)
      (toEquiv (liftProgram Subtype.val Subtype.val_injective moves)
        (⁅FreeGroup.of x, FreeGroup.of y⁆ * FreeGroup.map Subtype.val (FreeGroup.mk residual))) =
      surfaceRelator (g + 1) := by
  rw [map_mul, map_commutatorElement,
    lift_remaining_program_fix_x x y moves, lift_remaining_program_fix_y x y moves,
    liftProgram_map, map_mul, map_commutatorElement]
  change ⁅FreeGroup.of (handleInductiveRename x y hxy g tailRename x),
      FreeGroup.of (handleInductiveRename x y hxy g tailRename y)⁆ *
    FreeGroup.map (handleInductiveRename x y hxy g tailRename)
      (FreeGroup.map Subtype.val (toEquiv moves (FreeGroup.mk residual))) = _
  rw [handleInductiveRename_x, handleInductiveRename_y, surfaceRelator_succ_handle]
  congr 1
  rw [FreeGroup.map.comp]
  have hcomp : (handleInductiveRename x y hxy g tailRename) ∘ Subtype.val =
      (surfaceTailGeneratorEmbedding g) ∘ tailRename := by
    funext z
    exact handleInductiveRename_remaining x y hxy g tailRename z
  rw [hcomp, ← FreeGroup.map.comp]
  change FreeGroup.map (surfaceTailGeneratorEmbedding g)
    (FreeGroup.freeGroupCongr tailRename (toEquiv moves (FreeGroup.mk residual))) = _
  rw [htail]

/-- Every finite one-vertex orientable Wicks word normalizes to a standard
surface relator by a terminating elementary shear/inversion program and a
genuine alphabet renaming. No classification or residual-certificate input
is assumed: the proof constructs the smaller certificate at each step. -/
theorem exists_elementary_normalization {X : Type u} [Fintype X] {w : SignedWord X}
    (C : OrientableWicksCertificate w) :
    ∃ (g : ℕ) (moves : List (FreeGroupNielsenMove X)) (rename : X ≃ SurfaceGenerator g),
      FreeGroup.freeGroupCongr rename (toEquiv moves (FreeGroup.mk w)) = surfaceRelator g := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (Y : Type u) [Fintype Y] (v : SignedWord Y), Fintype.card Y = n →
      OrientableWicksCertificate v →
      ∃ (g : ℕ) (moves : List (FreeGroupNielsenMove Y)) (rename : Y ≃ SurfaceGenerator g),
        FreeGroup.freeGroupCongr rename (toEquiv moves (FreeGroup.mk v)) = surfaceRelator g
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro Y inst v hcard D
      by_cases hzero : Fintype.card Y = 0
      · letI : IsEmpty Y := Fintype.card_eq_zero_iff.mp hzero
        have hv : v = [] := List.length_eq_zero_iff.mp (by
          rw [D.length_eq_two_mul_card, hzero])
        let rename : Y ≃ SurfaceGenerator 0 := {
          toFun := isEmptyElim
          invFun := fun z => Fin.elim0 z.1
          left_inv := fun z => isEmptyElim z
          right_inv := fun z => Fin.elim0 z.1
        }
        refine ⟨0, [], rename, ?_⟩
        rw [hv]
        simp [toEquiv, ← FreeGroup.one_eq_mk]
      · letI : Nonempty Y := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
        obtain ⟨x, y, sx, sy, A, B1, B2, C1, C2, extraction,
          hxy, hsplit, _, _, hextraction⟩ :=
          D.exists_standard_handle_program_with_split (Classical.arbitrary Y)
        let residual := D.crossingHandleResidualWord x y sx sy A B1 B2 C1 C2 hsplit
        let residualCertificate :=
          D.crossingHandleResidualWicksCertificate x y hxy sx sy A B1 B2 C1 C2 hsplit
        have hdecrease : Fintype.card (HandleRemainingAlphabet x y) < n := by
          rw [← hcard]
          exact handleRemainingAlphabet_card_lt x y hxy
        obtain ⟨g, tailMoves, tailRename, htail⟩ :=
          ih (Fintype.card (HandleRemainingAlphabet x y)) hdecrease
            (HandleRemainingAlphabet x y) residual rfl residualCertificate
        have hprojection : FreeGroup.map (Subtype.val : HandleRemainingAlphabet x y → Y)
            (FreeGroup.mk residual) = FreeGroup.mk (B1 ++ C2 ++ A ++ C1 ++ B2) := by
          rw [FreeGroup.map.mk]
          apply congrArg FreeGroup.mk
          exact D.crossingHandleResidualWord_projection x y sx sy A B1 B2 C1 C2 hsplit
        refine ⟨g + 1,
          extraction ++ liftProgram Subtype.val Subtype.val_injective tailMoves,
          handleInductiveRename x y hxy g tailRename, ?_⟩
        rw [toEquiv_append]
        change FreeGroup.freeGroupCongr (handleInductiveRename x y hxy g tailRename)
          (toEquiv (liftProgram Subtype.val Subtype.val_injective tailMoves)
            (toEquiv extraction (FreeGroup.mk v))) = _
        rw [hextraction, ← FreeGroup.mul_mk, ← hprojection]
        change FreeGroup.freeGroupCongr (handleInductiveRename x y hxy g tailRename)
          (toEquiv (liftProgram Subtype.val Subtype.val_injective tailMoves)
            (⁅FreeGroup.of x, FreeGroup.of y⁆ *
              FreeGroup.map Subtype.val (FreeGroup.mk residual))) = _
        exact normalize_extracted_handle x y hxy g residual tailMoves tailRename htail
  exact hP (Fintype.card X) X w rfl C

#print axioms handleInductiveRename
#print axioms normalize_extracted_handle
#print axioms exists_elementary_normalization

end OrientableWicksCertificate

end

end SystolicGrowth
