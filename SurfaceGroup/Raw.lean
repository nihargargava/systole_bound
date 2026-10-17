module

public import BuserSarnak.BuserSarnakCyclicCover

@[expose] public section

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete
open ReidemeisterSchreier.Discrete.Presentations

abbrev surfaceCyclicRawData (n d : ℕ) [NeZero d] :=
  (surfaceCyclicSchreierData (g := n + 1) (d := d)
    (Nat.zero_lt_succ n)).toFiniteQuotientSchreierData

def cyclicOriginalA (n : ℕ) : SurfaceGenerator (n + 1) :=
  (0, false)

def cyclicOriginalB (n : ℕ) : SurfaceGenerator (n + 1) :=
  (0, true)

def cyclicOriginalRest (n : ℕ) (handle : Fin n) (side : Bool) :
    SurfaceGenerator (n + 1) :=
  (handle.succ, side)

def surfaceCyclicQuotientEquivFin (d : ℕ) [NeZero d] :
    SurfaceCyclicQuotient d ≃ Fin d where
  toFun q := ⟨q.toAdd.val, q.toAdd.val_lt⟩
  invFun j := Multiplicative.ofAdd (j.val : ZMod d)
  left_inv q := by
    apply Multiplicative.toAdd.injective
    exact ZMod.natCast_zmod_val q.toAdd
  right_inv j := by
    apply Fin.ext
    exact ZMod.val_cast_of_lt j.isLt

@[simp] lemma surfaceCyclicQuotientEquivFin_apply_val
    (d : ℕ) [NeZero d] (q : SurfaceCyclicQuotient d) :
    (surfaceCyclicQuotientEquivFin d q).val = q.toAdd.val := rfl

@[simp] lemma surfaceCyclicQuotientEquivFin_symm_apply
    (d : ℕ) [NeZero d] (j : Fin d) :
    (surfaceCyclicQuotientEquivFin d).symm j =
      Multiplicative.ofAdd (j.val : ZMod d) := rfl

def cyclicRawExponentSum {n : ℕ} (x : SurfaceGenerator (n + 1)) :
    FreeGroup (SurfaceGenerator (n + 1)) →* Multiplicative ℤ :=
  FreeGroup.lift fun y => if y = x then Multiplicative.ofAdd 1 else 1

lemma surfaceCyclicRawData_quotientSection (n d : ℕ) [NeZero d]
    (q : SurfaceCyclicQuotient d) :
    (surfaceCyclicRawData n d).quotientSection q =
      FreeGroup.mk (List.replicate q.toAdd.val (cyclicOriginalA n, true)) := by
  rfl

lemma cyclicRawExponentSum_quotientSection (n d : ℕ) [NeZero d]
    (q : SurfaceCyclicQuotient d) (x : SurfaceGenerator (n + 1)) :
    cyclicRawExponentSum x ((surfaceCyclicRawData n d).quotientSection q) =
      if cyclicOriginalA n = x then Multiplicative.ofAdd (q.toAdd.val : ℤ) else 1 := by
  rw [surfaceCyclicRawData_quotientSection]
  simp only [cyclicRawExponentSum, FreeGroup.lift_mk]
  by_cases h : cyclicOriginalA n = x
  · simp [h]
    apply Multiplicative.toAdd.injective
    simp
  · simp [h]

lemma cyclicRaw_not_degenerate_of_ne_A (n d : ℕ) [NeZero d]
    (q : SurfaceCyclicQuotient d) (x : SurfaceGenerator (n + 1))
    (hx : x ≠ cyclicOriginalA n) :
    ¬(surfaceCyclicRawData n d).IsDegenerateSchreierSymbol (q, x) := by
  intro hdeg
  have hmap := congrArg (cyclicRawExponentSum x) hdeg
  have hleft := cyclicRawExponentSum_quotientSection n d
    ((surfaceCyclicRawData n d).transition q x) x
  have hright := cyclicRawExponentSum_quotientSection n d q x
  rw [hleft, map_mul, hright] at hmap
  have hof :
      cyclicRawExponentSum x (FreeGroup.of x) = Multiplicative.ofAdd 1 := by
    simp [cyclicRawExponentSum]
  rw [hof] at hmap
  have hone : (1 : Multiplicative ℤ) = Multiplicative.ofAdd 1 := by
    simpa [hx.symm] using hmap
  have := congrArg Multiplicative.toAdd hone
  norm_num at this

lemma cyclicOriginalB_ne_A (n : ℕ) :
    cyclicOriginalB n ≠ cyclicOriginalA n := by
  simp [cyclicOriginalA, cyclicOriginalB]

lemma cyclicOriginalRest_ne_A (n : ℕ) (handle : Fin n) (side : Bool) :
    cyclicOriginalRest n handle side ≠ cyclicOriginalA n := by
  intro h
  have hi := congrArg (fun x : SurfaceGenerator (n + 1) => x.1.val) h
  simp [cyclicOriginalRest, cyclicOriginalA] at hi

lemma surfaceCyclicRawData_quotientMap_A (n d : ℕ) [NeZero d] :
    (surfaceCyclicRawData n d).quotientMap
        (FreeGroup.of (cyclicOriginalA n)) =
      Multiplicative.ofAdd (1 : ZMod d) := by
  change surfaceCyclicQuotientMap (d := d) (Nat.zero_lt_succ n)
      (FreeGroup.of (cyclicOriginalA n)) = Multiplicative.ofAdd (1 : ZMod d)
  simp [surfaceCyclicQuotientMap, surfaceCyclicGeneratorImage,
    surfaceCyclicBaseGenerator, cyclicOriginalA]

lemma surfaceCyclicRawData_transition_A (n d : ℕ) [NeZero d]
    (sheet : Fin d) :
    (surfaceCyclicRawData n d).transition
        ((surfaceCyclicQuotientEquivFin d).symm sheet) (cyclicOriginalA n) =
      Multiplicative.ofAdd ((sheet.val + 1 : ℕ) : ZMod d) := by
  rw [FiniteQuotientSchreierData.transition_eq,
    surfaceCyclicRawData_quotientMap_A]
  apply Multiplicative.toAdd.injective
  change (sheet.val : ZMod d) + 1 = ((sheet.val + 1 : ℕ) : ZMod d)
  norm_num

lemma cyclicSheet_succ_lt_of_ne_last (d : ℕ) [NeZero d]
    (sheet : Fin d) (h : sheet ≠ cyclicLastSheet d) :
    sheet.val + 1 < d := by
  have hval : sheet.val ≠ d - 1 := by
    intro heq
    apply h
    apply Fin.ext
    simpa [cyclicLastSheet] using heq
  omega

lemma cyclicRaw_A_degenerate_of_ne_last (n d : ℕ) [NeZero d]
    (sheet : Fin d) (h : sheet ≠ cyclicLastSheet d) :
    (surfaceCyclicRawData n d).IsDegenerateSchreierSymbol
      ((surfaceCyclicQuotientEquivFin d).symm sheet, cyclicOriginalA n) := by
  let D := surfaceCyclicRawData n d
  have hsucc : sheet.val + 1 < d := cyclicSheet_succ_lt_of_ne_last d sheet h
  change D.quotientSection
      (D.transition ((surfaceCyclicQuotientEquivFin d).symm sheet)
        (cyclicOriginalA n)) =
    D.quotientSection ((surfaceCyclicQuotientEquivFin d).symm sheet) *
      FreeGroup.of (cyclicOriginalA n)
  rw [surfaceCyclicRawData_transition_A]
  rw [surfaceCyclicRawData_quotientSection,
    surfaceCyclicRawData_quotientSection]
  change FreeGroup.mk
      (List.replicate (((sheet.val + 1 : ℕ) : ZMod d).val)
        (cyclicOriginalA n, true)) =
    FreeGroup.mk
        (List.replicate ((sheet.val : ZMod d).val) (cyclicOriginalA n, true)) *
      FreeGroup.mk [(cyclicOriginalA n, true)]
  rw [ZMod.val_cast_of_lt hsucc, ZMod.val_cast_of_lt sheet.isLt,
    FreeGroup.mul_mk]
  congr 1
  induction sheet.val with
  | zero => rfl
  | succ j ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons (cyclicOriginalA n, true)) ih

lemma cyclicRaw_A_not_degenerate_last (n d : ℕ) [NeZero d] :
    ¬(surfaceCyclicRawData n d).IsDegenerateSchreierSymbol
      ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d),
        cyclicOriginalA n) := by
  let D := surfaceCyclicRawData n d
  let q := (surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d)
  intro hdeg
  have hmap := congrArg (cyclicRawExponentSum (cyclicOriginalA n)) hdeg
  have hleft := cyclicRawExponentSum_quotientSection n d
    (D.transition q (cyclicOriginalA n)) (cyclicOriginalA n)
  have hright := cyclicRawExponentSum_quotientSection n d q (cyclicOriginalA n)
  rw [hleft, map_mul, hright] at hmap
  have hof : cyclicRawExponentSum (cyclicOriginalA n)
      (FreeGroup.of (cyclicOriginalA n)) = Multiplicative.ofAdd 1 := by
    simp [cyclicRawExponentSum]
  rw [hof] at hmap
  have hadd := congrArg Multiplicative.toAdd hmap
  have hqval : q.toAdd.val = d - 1 := by
    simp [q, cyclicLastSheet]
  have htransition : (D.transition q (cyclicOriginalA n)).toAdd.val < d :=
    ZMod.val_lt _
  change ((D.transition q (cyclicOriginalA n)).toAdd.val : ℤ) =
    (q.toAdd.val : ℤ) + 1 at hadd
  rw [hqval] at hadd
  omega

abbrev SurfaceCyclicRawGenerator (n d : ℕ) [NeZero d] :=
  (surfaceCyclicRawData n d).NondegenerateSchreierSymbol

noncomputable instance surfaceCyclicRawDegeneracyDecidable
    (n d : ℕ) [NeZero d] :
    DecidablePred (surfaceCyclicRawData n d).IsDegenerateSchreierSymbol :=
  Classical.decPred _

def cyclicRawWrapA (n d : ℕ) [NeZero d] :
    SurfaceCyclicRawGenerator n d :=
  ⟨((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d),
      cyclicOriginalA n),
    cyclicRaw_A_not_degenerate_last n d⟩

def cyclicRawSheetB (n d : ℕ) [NeZero d] (sheet : Fin d) :
    SurfaceCyclicRawGenerator n d :=
  ⟨((surfaceCyclicQuotientEquivFin d).symm sheet, cyclicOriginalB n),
    cyclicRaw_not_degenerate_of_ne_A n d _ _ (cyclicOriginalB_ne_A n)⟩

def cyclicRawRest (n d : ℕ) [NeZero d]
    (sheet : Fin d) (handle : Fin n) (side : Bool) :
    SurfaceCyclicRawGenerator n d :=
  ⟨((surfaceCyclicQuotientEquivFin d).symm sheet,
      cyclicOriginalRest n handle side),
    cyclicRaw_not_degenerate_of_ne_A n d _ _
      (cyclicOriginalRest_ne_A n handle side)⟩

lemma cyclicRaw_A_eq_last_of_not_degenerate (n d : ℕ) [NeZero d]
    (q : SurfaceCyclicQuotient d)
    (h : ¬(surfaceCyclicRawData n d).IsDegenerateSchreierSymbol
      (q, cyclicOriginalA n)) :
    surfaceCyclicQuotientEquivFin d q = cyclicLastSheet d := by
  by_contra hlast
  apply h
  simpa using cyclicRaw_A_degenerate_of_ne_last n d
    (surfaceCyclicQuotientEquivFin d q) hlast

def cyclicCustomToRaw (n d : ℕ) [NeZero d] :
    CyclicSchreierGenerator n d → SurfaceCyclicRawGenerator n d
  | .wrapA => cyclicRawWrapA n d
  | .sheetB sheet => cyclicRawSheetB n d sheet
  | .rest sheet handle side => cyclicRawRest n d sheet handle side

lemma cyclicCustomToRaw_injective (n d : ℕ) [NeZero d] :
    Function.Injective (cyclicCustomToRaw n d) := by
  intro x y h
  cases x with
  | wrapA =>
      cases y with
      | wrapA => rfl
      | sheetB sheet =>
          have hs := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.2) h
          simp [cyclicCustomToRaw, cyclicRawWrapA, cyclicRawSheetB,
            cyclicOriginalA, cyclicOriginalB] at hs
      | rest sheet handle side =>
          have hi := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.1.val) h
          simp [cyclicCustomToRaw, cyclicRawWrapA, cyclicRawRest,
            cyclicOriginalA, cyclicOriginalRest] at hi
  | sheetB sheet =>
      cases y with
      | wrapA =>
          have hs := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.2) h
          simp [cyclicCustomToRaw, cyclicRawWrapA, cyclicRawSheetB,
            cyclicOriginalA, cyclicOriginalB] at hs
      | sheetB sheet' =>
          have hq := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.1) h
          have hsheet : sheet = sheet' :=
            (surfaceCyclicQuotientEquivFin d).symm.injective (by
              simpa [cyclicCustomToRaw, cyclicRawSheetB] using hq)
          rw [hsheet]
      | rest sheet' handle side =>
          have hi := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.1.val) h
          simp [cyclicCustomToRaw, cyclicRawSheetB, cyclicRawRest,
            cyclicOriginalB, cyclicOriginalRest] at hi
  | rest sheet handle side =>
      cases y with
      | wrapA =>
          have hi := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.1.val) h
          simp [cyclicCustomToRaw, cyclicRawWrapA, cyclicRawRest,
            cyclicOriginalA, cyclicOriginalRest] at hi
      | sheetB sheet' =>
          have hi := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.1.val) h
          simp [cyclicCustomToRaw, cyclicRawSheetB, cyclicRawRest,
            cyclicOriginalB, cyclicOriginalRest] at hi
      | rest sheet' handle' side' =>
          have hq := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.1) h
          have hsheet : sheet = sheet' :=
            (surfaceCyclicQuotientEquivFin d).symm.injective (by
              simpa [cyclicCustomToRaw, cyclicRawRest] using hq)
          have hi := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.1) h
          have hhandle : handle = handle' := (Fin.succ_injective (n := n)) (by
            simpa [cyclicCustomToRaw, cyclicRawRest, cyclicOriginalRest] using hi)
          have hs := congrArg
            (fun z : SurfaceCyclicRawGenerator n d => z.1.2.2) h
          have hside : side = side' := by
            simpa [cyclicCustomToRaw, cyclicRawRest, cyclicOriginalRest] using hs
          rw [hsheet, hhandle, hside]

lemma cyclicCustomToRaw_surjective (n d : ℕ) [NeZero d] :
    Function.Surjective (cyclicCustomToRaw n d) := by
  rintro ⟨⟨q, ⟨i, side⟩⟩, hnondeg⟩
  revert hnondeg
  refine Fin.cases ?_ (fun handle => ?_) i
  · intro hnondeg
    cases side
    · have hlast := cyclicRaw_A_eq_last_of_not_degenerate n d q (by
        simpa [cyclicOriginalA] using hnondeg)
      refine ⟨CyclicSchreierGenerator.wrapA, ?_⟩
      apply Subtype.ext
      simp [cyclicCustomToRaw, cyclicRawWrapA, cyclicOriginalA, ← hlast]
    · refine ⟨CyclicSchreierGenerator.sheetB
          (surfaceCyclicQuotientEquivFin d q), ?_⟩
      apply Subtype.ext
      simp [cyclicCustomToRaw, cyclicRawSheetB, cyclicOriginalB]
  · intro hnondeg
    refine ⟨CyclicSchreierGenerator.rest
        (surfaceCyclicQuotientEquivFin d q) handle side, ?_⟩
    apply Subtype.ext
    simp [cyclicCustomToRaw, cyclicRawRest, cyclicOriginalRest]

def cyclicCustomEquivRaw (n d : ℕ) [NeZero d] :
    CyclicSchreierGenerator n d ≃ SurfaceCyclicRawGenerator n d :=
  Equiv.ofBijective (cyclicCustomToRaw n d)
    ⟨cyclicCustomToRaw_injective n d, cyclicCustomToRaw_surjective n d⟩

def cyclicRawEquivCustom (n d : ℕ) [NeZero d] :
    SurfaceCyclicRawGenerator n d ≃ CyclicSchreierGenerator n d :=
  (cyclicCustomEquivRaw n d).symm

@[simp] lemma cyclicRawEquivCustom_customToRaw (n d : ℕ) [NeZero d]
    (z : CyclicSchreierGenerator n d) :
    cyclicRawEquivCustom n d (cyclicCustomToRaw n d z) = z := by
  exact (cyclicCustomEquivRaw n d).symm_apply_apply z

@[simp] lemma cyclicRawEquivCustom_wrapA (n d : ℕ) [NeZero d] :
    cyclicRawEquivCustom n d (cyclicRawWrapA n d) =
      CyclicSchreierGenerator.wrapA := by
  change cyclicRawEquivCustom n d
      (cyclicCustomToRaw n d CyclicSchreierGenerator.wrapA) = _
  exact cyclicRawEquivCustom_customToRaw n d _

@[simp] lemma cyclicRawEquivCustom_sheetB (n d : ℕ) [NeZero d]
    (sheet : Fin d) :
    cyclicRawEquivCustom n d (cyclicRawSheetB n d sheet) =
      CyclicSchreierGenerator.sheetB sheet := by
  change cyclicRawEquivCustom n d
      (cyclicCustomToRaw n d (CyclicSchreierGenerator.sheetB sheet)) = _
  exact cyclicRawEquivCustom_customToRaw n d _

@[simp] lemma cyclicRawEquivCustom_rest (n d : ℕ) [NeZero d]
    (sheet : Fin d) (handle : Fin n) (side : Bool) :
    cyclicRawEquivCustom n d (cyclicRawRest n d sheet handle side) =
      CyclicSchreierGenerator.rest sheet handle side := by
  change cyclicRawEquivCustom n d
      (cyclicCustomToRaw n d
        (CyclicSchreierGenerator.rest sheet handle side)) = _
  exact cyclicRawEquivCustom_customToRaw n d _

def cyclicRawToCustomHom (n d : ℕ) [NeZero d] :
    FreeGroup (SurfaceCyclicRawGenerator n d) →*
      FreeGroup (CyclicSchreierGenerator n d) :=
  FreeGroup.lift fun z => FreeGroup.of (cyclicRawEquivCustom n d z)

def cyclicCustomToRawHom (n d : ℕ) [NeZero d] :
    FreeGroup (CyclicSchreierGenerator n d) →*
      FreeGroup (SurfaceCyclicRawGenerator n d) :=
  FreeGroup.lift fun z => FreeGroup.of (cyclicCustomEquivRaw n d z)

@[simp] lemma cyclicRawToCustomHom_wrapA (n d : ℕ) [NeZero d] :
    cyclicRawToCustomHom n d (FreeGroup.of (cyclicRawWrapA n d)) =
      FreeGroup.of CyclicSchreierGenerator.wrapA := by
  simp [cyclicRawToCustomHom]

@[simp] lemma cyclicRawToCustomHom_sheetB (n d : ℕ) [NeZero d]
    (sheet : Fin d) :
    cyclicRawToCustomHom n d (FreeGroup.of (cyclicRawSheetB n d sheet)) =
      FreeGroup.of (CyclicSchreierGenerator.sheetB sheet) := by
  simp [cyclicRawToCustomHom]

@[simp] lemma cyclicRawToCustomHom_rest (n d : ℕ) [NeZero d]
    (sheet : Fin d) (handle : Fin n) (side : Bool) :
    cyclicRawToCustomHom n d
        (FreeGroup.of (cyclicRawRest n d sheet handle side)) =
      FreeGroup.of (CyclicSchreierGenerator.rest sheet handle side) := by
  simp [cyclicRawToCustomHom]

lemma surfaceCyclicRawData_quotientMap_of_ne_A (n d : ℕ) [NeZero d]
    (x : SurfaceGenerator (n + 1)) (hx : x ≠ cyclicOriginalA n) :
    (surfaceCyclicRawData n d).quotientMap (FreeGroup.of x) = 1 := by
  change surfaceCyclicQuotientMap (d := d) (Nat.zero_lt_succ n)
      (FreeGroup.of x) = 1
  have hx' : x ≠ ((0, false) : SurfaceGenerator (n + 1)) := by
    simpa [cyclicOriginalA] using hx
  simp [surfaceCyclicQuotientMap, surfaceCyclicGeneratorImage,
    surfaceCyclicBaseGenerator, hx']

lemma surfaceCyclicRawData_transition_of_ne_A (n d : ℕ) [NeZero d]
    (q : SurfaceCyclicQuotient d) (x : SurfaceGenerator (n + 1))
    (hx : x ≠ cyclicOriginalA n) :
    (surfaceCyclicRawData n d).transition q x = q := by
  rw [FiniteQuotientSchreierData.transition_eq,
    surfaceCyclicRawData_quotientMap_of_ne_A n d x hx, mul_one]

lemma surfaceCyclicRawData_inverseTransition_of_ne_A (n d : ℕ) [NeZero d]
    (q : SurfaceCyclicQuotient d) (x : SurfaceGenerator (n + 1))
    (hx : x ≠ cyclicOriginalA n) :
    (surfaceCyclicRawData n d).inverseTransition q x = q := by
  rw [FiniteQuotientSchreierData.inverseTransition_eq,
    surfaceCyclicRawData_quotientMap_of_ne_A n d x hx, inv_one, mul_one]

lemma surfaceCyclicRawData_transition_A_of_succ_lt (n d : ℕ) [NeZero d]
    (sheet : Fin d) (h : sheet.val + 1 < d) :
    (surfaceCyclicRawData n d).transition
        ((surfaceCyclicQuotientEquivFin d).symm sheet) (cyclicOriginalA n) =
      (surfaceCyclicQuotientEquivFin d).symm ⟨sheet.val + 1, h⟩ := by
  rw [surfaceCyclicRawData_transition_A]
  rfl

lemma surfaceCyclicRawData_transition_A_last (n d : ℕ) [NeZero d] :
    (surfaceCyclicRawData n d).transition
        ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d))
        (cyclicOriginalA n) =
      (surfaceCyclicQuotientEquivFin d).symm (cyclicFirstSheet d) := by
  rw [surfaceCyclicRawData_transition_A]
  apply Multiplicative.toAdd.injective
  change (((cyclicLastSheet d).val + 1 : ℕ) : ZMod d) =
    ((cyclicFirstSheet d).val : ZMod d)
  simp only [cyclicLastSheet, cyclicFirstSheet]
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel (NeZero.pos d)
  rw [hd]
  simp

lemma cyclicRawToCustomHom_cleanedSymbol_A_of_ne_last
    (n d : ℕ) [NeZero d] (sheet : Fin d)
    (h : sheet ≠ cyclicLastSheet d) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedSchreierSymbolWord
          ((surfaceCyclicQuotientEquivFin d).symm sheet,
            cyclicOriginalA n)) = 1 := by
  rw [(surfaceCyclicRawData n d).cleanedSchreierSymbolWord_of_degenerate
    (cyclicRaw_A_degenerate_of_ne_last n d sheet h), map_one]

lemma cyclicRawToCustomHom_cleanedSymbol_A_last
    (n d : ℕ) [NeZero d] :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedSchreierSymbolWord
          ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d),
            cyclicOriginalA n)) =
      FreeGroup.of CyclicSchreierGenerator.wrapA := by
  let h := cyclicRaw_A_not_degenerate_last n d
  rw [(surfaceCyclicRawData n d).cleanedSchreierSymbolWord_of_not_degenerate h]
  have hz :
      (⟨((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d),
          cyclicOriginalA n), h⟩ : SurfaceCyclicRawGenerator n d) =
        cyclicRawWrapA n d := Subtype.ext rfl
  rw [hz]
  exact cyclicRawToCustomHom_wrapA n d

lemma cyclicRawToCustomHom_cleanedSymbol_B
    (n d : ℕ) [NeZero d] (sheet : Fin d) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedSchreierSymbolWord
          ((surfaceCyclicQuotientEquivFin d).symm sheet,
            cyclicOriginalB n)) =
      FreeGroup.of (CyclicSchreierGenerator.sheetB sheet) := by
  let h := cyclicRaw_not_degenerate_of_ne_A n d
    ((surfaceCyclicQuotientEquivFin d).symm sheet) (cyclicOriginalB n)
    (cyclicOriginalB_ne_A n)
  rw [(surfaceCyclicRawData n d).cleanedSchreierSymbolWord_of_not_degenerate h]
  have hz :
      (⟨((surfaceCyclicQuotientEquivFin d).symm sheet, cyclicOriginalB n), h⟩ :
        SurfaceCyclicRawGenerator n d) = cyclicRawSheetB n d sheet :=
    Subtype.ext rfl
  rw [hz]
  exact cyclicRawToCustomHom_sheetB n d sheet

lemma cyclicRawToCustomHom_cleanedSymbol_rest
    (n d : ℕ) [NeZero d] (sheet : Fin d) (handle : Fin n) (side : Bool) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedSchreierSymbolWord
          ((surfaceCyclicQuotientEquivFin d).symm sheet,
            cyclicOriginalRest n handle side)) =
      FreeGroup.of (CyclicSchreierGenerator.rest sheet handle side) := by
  let h := cyclicRaw_not_degenerate_of_ne_A n d
    ((surfaceCyclicQuotientEquivFin d).symm sheet)
    (cyclicOriginalRest n handle side)
    (cyclicOriginalRest_ne_A n handle side)
  rw [(surfaceCyclicRawData n d).cleanedSchreierSymbolWord_of_not_degenerate h]
  have hz :
      (⟨((surfaceCyclicQuotientEquivFin d).symm sheet,
          cyclicOriginalRest n handle side), h⟩ : SurfaceCyclicRawGenerator n d) =
        cyclicRawRest n d sheet handle side := Subtype.ext rfl
  rw [hz]
  exact cyclicRawToCustomHom_rest n d sheet handle side

def cyclicOriginalBaseHandleWord (n : ℕ) :
    FreeGroup (SurfaceGenerator (n + 1)) :=
  FreeGroup.of (cyclicOriginalA n) * FreeGroup.of (cyclicOriginalB n) *
    (FreeGroup.of (cyclicOriginalA n))⁻¹ *
    (FreeGroup.of (cyclicOriginalB n))⁻¹

def cyclicOriginalRestHandleWord (n : ℕ) (handle : Fin n) :
    FreeGroup (SurfaceGenerator (n + 1)) :=
  FreeGroup.of (cyclicOriginalRest n handle false) *
    FreeGroup.of (cyclicOriginalRest n handle true) *
    (FreeGroup.of (cyclicOriginalRest n handle false))⁻¹ *
    (FreeGroup.of (cyclicOriginalRest n handle true))⁻¹

lemma cyclicOriginalBaseHandleWord_eq_mk (n : ℕ) :
    cyclicOriginalBaseHandleWord n = FreeGroup.mk
      [(cyclicOriginalA n, true), (cyclicOriginalB n, true),
        (cyclicOriginalA n, false), (cyclicOriginalB n, false)] := by
  rfl

lemma cyclicOriginalRestHandleWord_eq_mk (n : ℕ) (handle : Fin n) :
    cyclicOriginalRestHandleWord n handle = FreeGroup.mk
      [(cyclicOriginalRest n handle false, true),
        (cyclicOriginalRest n handle true, true),
        (cyclicOriginalRest n handle false, false),
        (cyclicOriginalRest n handle true, false)] := by
  rfl

lemma surfaceCyclicRawData_quotientMap_baseHandleWord (n d : ℕ) [NeZero d] :
    (surfaceCyclicRawData n d).quotientMap
        (cyclicOriginalBaseHandleWord n) = 1 := by
  simp only [cyclicOriginalBaseHandleWord, map_mul, map_inv,
    surfaceCyclicRawData_quotientMap_A,
    surfaceCyclicRawData_quotientMap_of_ne_A n d (cyclicOriginalB n)
      (cyclicOriginalB_ne_A n), inv_one]
  group

lemma surfaceCyclicRawData_quotientMap_restHandleWord
    (n d : ℕ) [NeZero d] (handle : Fin n) :
    (surfaceCyclicRawData n d).quotientMap
        (cyclicOriginalRestHandleWord n handle) = 1 := by
  simp only [cyclicOriginalRestHandleWord, map_mul, map_inv,
    surfaceCyclicRawData_quotientMap_of_ne_A n d
      (cyclicOriginalRest n handle false)
      (cyclicOriginalRest_ne_A n handle false),
    surfaceCyclicRawData_quotientMap_of_ne_A n d
      (cyclicOriginalRest n handle true)
      (cyclicOriginalRest_ne_A n handle true), inv_one]
  group

lemma surfaceCyclicRawData_inverseTransition_A_of_succ_lt
    (n d : ℕ) [NeZero d] (sheet : Fin d) (h : sheet.val + 1 < d) :
    (surfaceCyclicRawData n d).inverseTransition
        ((surfaceCyclicQuotientEquivFin d).symm ⟨sheet.val + 1, h⟩)
        (cyclicOriginalA n) =
      (surfaceCyclicQuotientEquivFin d).symm sheet := by
  rw [← surfaceCyclicRawData_transition_A_of_succ_lt n d sheet h]
  exact (surfaceCyclicRawData n d).inverseTransition_after_transition _ _

lemma surfaceCyclicRawData_inverseTransition_A_first
    (n d : ℕ) [NeZero d] :
    (surfaceCyclicRawData n d).inverseTransition
        ((surfaceCyclicQuotientEquivFin d).symm (cyclicFirstSheet d))
        (cyclicOriginalA n) =
      (surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d) := by
  rw [← surfaceCyclicRawData_transition_A_last n d]
  exact (surfaceCyclicRawData n d).inverseTransition_after_transition _ _

lemma cyclicRawToCustomHom_cleanedTau_base_of_succ_lt
    (n d : ℕ) [NeZero d] (sheet : Fin d) (h : sheet.val + 1 < d) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm sheet)
          (cyclicOriginalBaseHandleWord n)) =
      FreeGroup.of
          (CyclicSchreierGenerator.sheetB ⟨sheet.val + 1, h⟩) *
        (FreeGroup.of (CyclicSchreierGenerator.sheetB sheet))⁻¹ := by
  rw [cyclicOriginalBaseHandleWord_eq_mk,
    (surfaceCyclicRawData n d).cleanedTau_mk]
  simp only [FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_false,
    FiniteQuotientSchreierData.cleanedTauList_nil, map_mul, map_inv]
  rw [surfaceCyclicRawData_transition_A_of_succ_lt n d sheet h,
    surfaceCyclicRawData_transition_of_ne_A n d _ (cyclicOriginalB n)
      (cyclicOriginalB_ne_A n),
    surfaceCyclicRawData_inverseTransition_A_of_succ_lt n d sheet h,
    surfaceCyclicRawData_inverseTransition_of_ne_A n d _ (cyclicOriginalB n)
      (cyclicOriginalB_ne_A n)]
  have hlast : sheet ≠ cyclicLastSheet d := by
    intro heq
    have := congrArg Fin.val heq
    simp [cyclicLastSheet] at this
    omega
  rw [cyclicRawToCustomHom_cleanedSymbol_A_of_ne_last n d sheet hlast,
    cyclicRawToCustomHom_cleanedSymbol_B n d ⟨sheet.val + 1, h⟩,
    cyclicRawToCustomHom_cleanedSymbol_B n d sheet]
  simp

lemma cyclicRawToCustomHom_cleanedTau_base_last
    (n d : ℕ) [NeZero d] :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d))
          (cyclicOriginalBaseHandleWord n)) =
      FreeGroup.of CyclicSchreierGenerator.wrapA *
        FreeGroup.of (CyclicSchreierGenerator.sheetB (cyclicFirstSheet d)) *
        (FreeGroup.of CyclicSchreierGenerator.wrapA)⁻¹ *
        (FreeGroup.of
          (CyclicSchreierGenerator.sheetB (cyclicLastSheet d)))⁻¹ := by
  rw [cyclicOriginalBaseHandleWord_eq_mk,
    (surfaceCyclicRawData n d).cleanedTau_mk]
  simp only [FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_false,
    FiniteQuotientSchreierData.cleanedTauList_nil, map_mul, map_inv]
  rw [surfaceCyclicRawData_transition_A_last n d,
    surfaceCyclicRawData_transition_of_ne_A n d _ (cyclicOriginalB n)
      (cyclicOriginalB_ne_A n),
    surfaceCyclicRawData_inverseTransition_A_first n d,
    surfaceCyclicRawData_inverseTransition_of_ne_A n d _ (cyclicOriginalB n)
      (cyclicOriginalB_ne_A n),
    cyclicRawToCustomHom_cleanedSymbol_A_last n d,
    cyclicRawToCustomHom_cleanedSymbol_B n d (cyclicFirstSheet d),
    cyclicRawToCustomHom_cleanedSymbol_B n d (cyclicLastSheet d)]
  simp
  group

lemma cyclicRawToCustomHom_cleanedTau_restHandle
    (n d : ℕ) [NeZero d] (sheet : Fin d) (handle : Fin n) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm sheet)
          (cyclicOriginalRestHandleWord n handle)) =
      FreeGroup.of (CyclicSchreierGenerator.rest sheet handle false) *
        FreeGroup.of (CyclicSchreierGenerator.rest sheet handle true) *
        (FreeGroup.of (CyclicSchreierGenerator.rest sheet handle false))⁻¹ *
        (FreeGroup.of (CyclicSchreierGenerator.rest sheet handle true))⁻¹ := by
  rw [cyclicOriginalRestHandleWord_eq_mk,
    (surfaceCyclicRawData n d).cleanedTau_mk]
  simp only [FiniteQuotientSchreierData.cleanedTauList_cons_true,
    FiniteQuotientSchreierData.cleanedTauList_cons_false,
    FiniteQuotientSchreierData.cleanedTauList_nil, map_mul, map_inv]
  rw [surfaceCyclicRawData_transition_of_ne_A n d _ _
      (cyclicOriginalRest_ne_A n handle false),
    surfaceCyclicRawData_transition_of_ne_A n d _ _
      (cyclicOriginalRest_ne_A n handle true),
    surfaceCyclicRawData_inverseTransition_of_ne_A n d _ _
      (cyclicOriginalRest_ne_A n handle false),
    surfaceCyclicRawData_inverseTransition_of_ne_A n d _ _
      (cyclicOriginalRest_ne_A n handle true),
    cyclicRawToCustomHom_cleanedSymbol_rest n d sheet handle false,
    cyclicRawToCustomHom_cleanedSymbol_rest n d sheet handle true]
  simp
  group

lemma cyclicRawToCustomHom_cleanedTau_list_prod
    (n d : ℕ) [NeZero d] (q : SurfaceCyclicQuotient d)
    (words : List (FreeGroup (SurfaceGenerator (n + 1))))
    (hwords : ∀ w ∈ words, (surfaceCyclicRawData n d).quotientMap w = 1) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau q words.prod) =
      (words.map fun w => cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau q w)).prod := by
  induction words generalizing q with
  | nil => simp
  | cons w words ih =>
      have hw : (surfaceCyclicRawData n d).quotientMap w = 1 :=
        hwords w (List.mem_cons_self)
      have htail : ∀ z ∈ words,
          (surfaceCyclicRawData n d).quotientMap z = 1 := by
        intro z hz
        exact hwords z (List.mem_cons_of_mem w hz)
      rw [List.prod_cons, (surfaceCyclicRawData n d).cleanedTau_mul, map_mul]
      have hstate :
          (surfaceCyclicRawData n d).quotientMap
              ((surfaceCyclicRawData n d).quotientSection q * w) = q := by
        simp [map_mul, hw]
      rw [hstate, ih q htail]
      rfl

lemma cyclicRawToCustomHom_cleanedTau_restProduct
    (n d : ℕ) [NeZero d] (sheet : Fin d) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm sheet)
          ((List.ofFn fun handle : Fin n =>
            cyclicOriginalRestHandleWord n handle).prod)) =
      cyclicSchreierSheetWord n d sheet := by
  rw [cyclicRawToCustomHom_cleanedTau_list_prod]
  · rw [cyclicSchreierSheetWord, List.map_ofFn]
    apply congrArg List.prod
    rw [List.ofFn_inj]
    funext handle
    exact cyclicRawToCustomHom_cleanedTau_restHandle n d sheet handle
  · intro w hw
    rcases List.mem_ofFn.mp hw with ⟨handle, rfl⟩
    exact surfaceCyclicRawData_quotientMap_restHandleWord n d handle

lemma surfaceRelator_succ_eq_cyclicOriginalWords (n : ℕ) :
    surfaceRelator (n + 1) =
      cyclicOriginalBaseHandleWord n *
        (List.ofFn fun handle : Fin n =>
          cyclicOriginalRestHandleWord n handle).prod := by
  rw [surfaceRelator, List.ofFn_succ, List.prod_cons]
  rfl

lemma cyclicRawToCustomHom_cleanedTau_surfaceRelator_of_succ_lt
    (n d : ℕ) [NeZero d] (sheet : Fin d) (h : sheet.val + 1 < d) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm sheet)
          (surfaceRelator (n + 1))) =
      FreeGroup.of
          (CyclicSchreierGenerator.sheetB ⟨sheet.val + 1, h⟩) *
        (FreeGroup.of (CyclicSchreierGenerator.sheetB sheet))⁻¹ *
        cyclicSchreierSheetWord n d sheet := by
  rw [surfaceRelator_succ_eq_cyclicOriginalWords,
    (surfaceCyclicRawData n d).cleanedTau_mul, map_mul]
  have hstate :
      (surfaceCyclicRawData n d).quotientMap
          ((surfaceCyclicRawData n d).quotientSection
              ((surfaceCyclicQuotientEquivFin d).symm sheet) *
            cyclicOriginalBaseHandleWord n) =
        (surfaceCyclicQuotientEquivFin d).symm sheet := by
    simp [map_mul, surfaceCyclicRawData_quotientMap_baseHandleWord]
  rw [hstate, cyclicRawToCustomHom_cleanedTau_base_of_succ_lt n d sheet h,
    cyclicRawToCustomHom_cleanedTau_restProduct n d sheet]

lemma cyclicRawToCustomHom_cleanedTau_surfaceRelator_last
    (n d : ℕ) [NeZero d] :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d))
          (surfaceRelator (n + 1))) =
      FreeGroup.of CyclicSchreierGenerator.wrapA *
        FreeGroup.of (CyclicSchreierGenerator.sheetB (cyclicFirstSheet d)) *
        (FreeGroup.of CyclicSchreierGenerator.wrapA)⁻¹ *
        (FreeGroup.of
          (CyclicSchreierGenerator.sheetB (cyclicLastSheet d)))⁻¹ *
        cyclicSchreierSheetWord n d (cyclicLastSheet d) := by
  rw [surfaceRelator_succ_eq_cyclicOriginalWords,
    (surfaceCyclicRawData n d).cleanedTau_mul, map_mul]
  have hstate :
      (surfaceCyclicRawData n d).quotientMap
          ((surfaceCyclicRawData n d).quotientSection
              ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d)) *
            cyclicOriginalBaseHandleWord n) =
        (surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d) := by
    simp [map_mul, surfaceCyclicRawData_quotientMap_baseHandleWord]
  rw [hstate, cyclicRawToCustomHom_cleanedTau_base_last n d,
    cyclicRawToCustomHom_cleanedTau_restProduct n d (cyclicLastSheet d)]

lemma cyclicRawToCustomHom_cleanedTau_surfaceRelator_step
    (n d j : ℕ) [NeZero d] (h : j + 1 < d) :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm
            ⟨j, lt_trans (Nat.lt_succ_self j) h⟩)
          (surfaceRelator (n + 1))) =
      cyclicSchreierRelator n d (CyclicSchreierRelator.step j h) := by
  simpa [cyclicSchreierRelator] using
    cyclicRawToCustomHom_cleanedTau_surfaceRelator_of_succ_lt n d
      ⟨j, lt_trans (Nat.lt_succ_self j) h⟩ h

lemma cyclicRawToCustomHom_cleanedTau_surfaceRelator_final
    (n d : ℕ) [NeZero d] :
    cyclicRawToCustomHom n d
        ((surfaceCyclicRawData n d).cleanedTau
          ((surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d))
          (surfaceRelator (n + 1))) =
      cyclicSchreierRelator n d CyclicSchreierRelator.final := by
  simpa [cyclicSchreierRelator] using
    cyclicRawToCustomHom_cleanedTau_surfaceRelator_last n d

lemma cyclicCustomToRawHom_rawToCustomHom
    (n d : ℕ) [NeZero d] (w : FreeGroup (SurfaceCyclicRawGenerator n d)) :
    cyclicCustomToRawHom n d (cyclicRawToCustomHom n d w) = w := by
  let H := (cyclicCustomToRawHom n d).comp (cyclicRawToCustomHom n d)
  have hH : H = MonoidHom.id _ := by
    ext z
    simp [H, cyclicCustomToRawHom, cyclicRawToCustomHom,
      cyclicRawEquivCustom]
  exact DFunLike.congr_fun hH w

lemma cyclicRawToCustomHom_customToRawHom
    (n d : ℕ) [NeZero d] (w : FreeGroup (CyclicSchreierGenerator n d)) :
    cyclicRawToCustomHom n d (cyclicCustomToRawHom n d w) = w := by
  let H := (cyclicRawToCustomHom n d).comp (cyclicCustomToRawHom n d)
  have hH : H = MonoidHom.id _ := by
    ext z
    simp [H, cyclicCustomToRawHom, cyclicRawToCustomHom,
      cyclicRawEquivCustom]
  exact DFunLike.congr_fun hH w

lemma cyclicRawToCustomHom_maps_cleanedRelators
    (n d : ℕ) [NeZero d] :
    ∀ z ∈ (surfaceCyclicRawData n d).cleanedSchreierRelators
        ({surfaceRelator (n + 1)} :
          Set (FreeGroup (SurfaceGenerator (n + 1)))),
      RelatorEquivalent (cyclicSchreierRelators n d)
        (cyclicRawToCustomHom n d z) 1 := by
  rintro z ⟨q, r, hr, rfl⟩
  rw [Set.mem_singleton_iff.mp hr]
  let sheet := surfaceCyclicQuotientEquivFin d q
  have hq : (surfaceCyclicQuotientEquivFin d).symm sheet = q :=
    (surfaceCyclicQuotientEquivFin d).symm_apply_apply q
  rw [← hq]
  by_cases hlast : sheet = cyclicLastSheet d
  · rw [hlast, cyclicRawToCustomHom_cleanedTau_surfaceRelator_final]
    exact RelatorEquivalent.of_mem
      ⟨CyclicSchreierRelator.final, rfl⟩
  · have hsucc : sheet.val + 1 < d :=
      cyclicSheet_succ_lt_of_ne_last d sheet hlast
    have heq :
        cyclicRawToCustomHom n d
            ((surfaceCyclicRawData n d).cleanedTau
              ((surfaceCyclicQuotientEquivFin d).symm sheet)
              (surfaceRelator (n + 1))) =
          cyclicSchreierRelator n d
            (CyclicSchreierRelator.step sheet.val hsucc) := by
      simpa using cyclicRawToCustomHom_cleanedTau_surfaceRelator_step
        n d sheet.val hsucc
    rw [heq]
    exact RelatorEquivalent.of_mem
      ⟨CyclicSchreierRelator.step sheet.val hsucc, rfl⟩

lemma cyclicCustomToRawHom_maps_relators
    (n d : ℕ) [NeZero d] :
    ∀ s ∈ cyclicSchreierRelators n d,
      RelatorEquivalent
        ((surfaceCyclicRawData n d).cleanedSchreierRelators
          ({surfaceRelator (n + 1)} :
            Set (FreeGroup (SurfaceGenerator (n + 1)))))
        (cyclicCustomToRawHom n d s) 1 := by
  rintro s ⟨rel, rfl⟩
  cases rel with
  | step j h =>
      let q := (surfaceCyclicQuotientEquivFin d).symm
        ⟨j, lt_trans (Nat.lt_succ_self j) h⟩
      let tauWord := (surfaceCyclicRawData n d).cleanedTau q
        (surfaceRelator (n + 1))
      have hforward : cyclicRawToCustomHom n d tauWord =
          cyclicSchreierRelator n d (CyclicSchreierRelator.step j h) := by
        exact cyclicRawToCustomHom_cleanedTau_surfaceRelator_step n d j h
      have hback : cyclicCustomToRawHom n d
            (cyclicSchreierRelator n d (CyclicSchreierRelator.step j h)) =
          tauWord := by
        calc
          cyclicCustomToRawHom n d
              (cyclicSchreierRelator n d (CyclicSchreierRelator.step j h)) =
              cyclicCustomToRawHom n d (cyclicRawToCustomHom n d tauWord) :=
                congrArg (cyclicCustomToRawHom n d) hforward.symm
          _ = tauWord := cyclicCustomToRawHom_rawToCustomHom n d tauWord
      rw [hback]
      exact RelatorEquivalent.of_mem
        ⟨q, surfaceRelator (n + 1), Set.mem_singleton _, rfl⟩
  | final =>
      let q := (surfaceCyclicQuotientEquivFin d).symm (cyclicLastSheet d)
      let tauWord := (surfaceCyclicRawData n d).cleanedTau q
        (surfaceRelator (n + 1))
      have hforward : cyclicRawToCustomHom n d tauWord =
          cyclicSchreierRelator n d CyclicSchreierRelator.final := by
        exact cyclicRawToCustomHom_cleanedTau_surfaceRelator_final n d
      have hback : cyclicCustomToRawHom n d
            (cyclicSchreierRelator n d CyclicSchreierRelator.final) =
          tauWord := by
        calc
          cyclicCustomToRawHom n d
              (cyclicSchreierRelator n d CyclicSchreierRelator.final) =
              cyclicCustomToRawHom n d (cyclicRawToCustomHom n d tauWord) :=
                congrArg (cyclicCustomToRawHom n d) hforward.symm
          _ = tauWord := cyclicCustomToRawHom_rawToCustomHom n d tauWord
      rw [hback]
      exact RelatorEquivalent.of_mem
        ⟨q, surfaceRelator (n + 1), Set.mem_singleton _, rfl⟩

def surfaceCyclicCleanedTietzeEquivCyclicSchreier
    (n d : ℕ) [NeZero d] :
    TietzeEquiv
      ((surfaceCyclicRawData n d).cleanedSchreierRelators
        ({surfaceRelator (n + 1)} :
          Set (FreeGroup (SurfaceGenerator (n + 1)))))
      (cyclicSchreierRelators n d) :=
  TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    (fun z => FreeGroup.of (cyclicRawEquivCustom n d z))
    (fun y => FreeGroup.of (cyclicCustomEquivRaw n d y))
    (by
      intro z hz
      change RelatorEquivalent (cyclicSchreierRelators n d)
        (cyclicRawToCustomHom n d z) 1
      exact cyclicRawToCustomHom_maps_cleanedRelators n d z hz)
    (by
      intro s hs
      change RelatorEquivalent
        ((surfaceCyclicRawData n d).cleanedSchreierRelators
          ({surfaceRelator (n + 1)} :
            Set (FreeGroup (SurfaceGenerator (n + 1)))))
        (cyclicCustomToRawHom n d s) 1
      exact cyclicCustomToRawHom_maps_relators n d s hs)
    (by
      intro z
      change RelatorEquivalent
        ((surfaceCyclicRawData n d).cleanedSchreierRelators
          ({surfaceRelator (n + 1)} :
            Set (FreeGroup (SurfaceGenerator (n + 1)))))
        (cyclicCustomToRawHom n d
          (cyclicRawToCustomHom n d (FreeGroup.of z)))
        (FreeGroup.of z)
      exact RelatorEquivalent.of_eq
        (cyclicCustomToRawHom_rawToCustomHom n d (FreeGroup.of z)))
    (by
      intro y
      change RelatorEquivalent (cyclicSchreierRelators n d)
        (cyclicRawToCustomHom n d
          (cyclicCustomToRawHom n d (FreeGroup.of y)))
        (FreeGroup.of y)
      exact RelatorEquivalent.of_eq
        (cyclicRawToCustomHom_customToRawHom n d (FreeGroup.of y)))

noncomputable def surfaceCyclicRawPresentedEquivCyclicSchreier
    (n d : ℕ) [NeZero d] :
    PresentedGroup
        (surfaceCyclicSchreierRelators (g := n + 1) (d := d)
          (Nat.zero_lt_succ n)) ≃*
      PresentedGroup (cyclicSchreierRelators n d) := by
  let D := surfaceCyclicRawData n d
  let R : Set (FreeGroup (SurfaceGenerator (n + 1))) :=
    {surfaceRelator (n + 1)}
  exact
    (D.deleteDegenerateSchreierGenerators R).trans
      ((Presented.ofNormalClosureEq
        (R := D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)
        (S := D.cleanedSchreierRelators R)
        (congrArg Subgroup.normalClosure
          (D.presentationRelatorsAfterDeletingDegenerate_eq_cleaned R))).trans
        (surfaceCyclicCleanedTietzeEquivCyclicSchreier n d).presentedEquiv)

/-- The kernel of the degree-`d` cyclic map from the genus-`n+1` surface
group is the standard surface group of genus `1 + d*n`. -/
noncomputable def surfaceCyclicKernelEquivSurface
    (n d : ℕ) [NeZero d] :
    (surfaceCyclicPresentedHom (g := n + 1) (d := d)
        (Nat.zero_lt_succ n)).ker ≃*
      SurfaceGroup (1 + d * n) :=
  (surfaceCyclicRawPresentedEquivKernel
      (g := n + 1) (d := d) (Nat.zero_lt_succ n)).symm.trans
    ((surfaceCyclicRawPresentedEquivCyclicSchreier n d).trans
      ((cyclicSchreierPresentedEquivSurface n d).trans
        (cyclicSurfacePresentedEquivStandard n d)))

end
end SystolicGrowth
