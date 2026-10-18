module

public import SurfaceGroup.Tietze

@[expose] public section

namespace SystolicGrowth

noncomputable section

open ReidemeisterSchreier.Discrete.Presentations
open scoped commutatorElement

/-- Generators of the surface-style target of the cyclic Schreier calculation:
one base handle and `d` copies of each of the remaining `n` handles. -/
inductive CyclicSurfaceGenerator (n d : ℕ) where
  | base (side : Bool)
  | rest (sheet : Fin d) (handle : Fin n) (side : Bool)
  deriving DecidableEq

/-- The nondegenerate generators in the cyclic Schreier presentation. -/
inductive CyclicSchreierGenerator (n d : ℕ) where
  | wrapA
  | sheetB (sheet : Fin d)
  | rest (sheet : Fin d) (handle : Fin n) (side : Bool)
  deriving DecidableEq

def cyclicFirstSheet (d : ℕ) [NeZero d] : Fin d :=
  ⟨0, NeZero.pos d⟩

def cyclicLastSheet (d : ℕ) [NeZero d] : Fin d :=
  ⟨d - 1, Nat.sub_lt (NeZero.pos d) zero_lt_one⟩

@[simp] lemma cyclicFirstSheet_val (d : ℕ) [NeZero d] :
    (cyclicFirstSheet d).val = 0 := rfl

@[simp] lemma cyclicLastSheet_val (d : ℕ) [NeZero d] :
    (cyclicLastSheet d).val = d - 1 := rfl

def cyclicSurfaceSheetWord (n d : ℕ) (sheet : Fin d) :
    FreeGroup (CyclicSurfaceGenerator n d) :=
  (List.ofFn fun handle : Fin n =>
    FreeGroup.of (CyclicSurfaceGenerator.rest sheet handle false) *
      FreeGroup.of (CyclicSurfaceGenerator.rest sheet handle true) *
      (FreeGroup.of (CyclicSurfaceGenerator.rest sheet handle false))⁻¹ *
      (FreeGroup.of (CyclicSurfaceGenerator.rest sheet handle true))⁻¹).prod

def cyclicSurfaceSheetWordNat (n d : ℕ) (j : ℕ) :
    FreeGroup (CyclicSurfaceGenerator n d) :=
  if h : j < d then cyclicSurfaceSheetWord n d ⟨j, h⟩ else 1

def cyclicSurfaceRelator (n d : ℕ) :
    FreeGroup (CyclicSurfaceGenerator n d) :=
  FreeGroup.of (CyclicSurfaceGenerator.base false) *
    FreeGroup.of (CyclicSurfaceGenerator.base true) *
    (FreeGroup.of (CyclicSurfaceGenerator.base false))⁻¹ *
    (FreeGroup.of (CyclicSurfaceGenerator.base true))⁻¹ *
    cyclicPrefixProduct (cyclicSurfaceSheetWordNat n d) d

def cyclicSchreierSheetWord (n d : ℕ) (sheet : Fin d) :
    FreeGroup (CyclicSchreierGenerator n d) :=
  (List.ofFn fun handle : Fin n =>
    FreeGroup.of (CyclicSchreierGenerator.rest sheet handle false) *
      FreeGroup.of (CyclicSchreierGenerator.rest sheet handle true) *
      (FreeGroup.of (CyclicSchreierGenerator.rest sheet handle false))⁻¹ *
      (FreeGroup.of (CyclicSchreierGenerator.rest sheet handle true))⁻¹).prod

def cyclicSchreierSheetWordNat (n d : ℕ) (j : ℕ) :
    FreeGroup (CyclicSchreierGenerator n d) :=
  if h : j < d then cyclicSchreierSheetWord n d ⟨j, h⟩ else 1

def cyclicSchreierBNat (n d : ℕ) (j : ℕ) :
    FreeGroup (CyclicSchreierGenerator n d) :=
  if h : j < d then FreeGroup.of (.sheetB ⟨j, h⟩) else 1

@[simp] lemma cyclicSchreierBNat_zero (n d : ℕ) [NeZero d] :
    cyclicSchreierBNat n d 0 =
      FreeGroup.of (.sheetB (cyclicFirstSheet d)) := by
  rw [cyclicSchreierBNat, dif_pos (NeZero.pos d)]
  congr 2

inductive CyclicSchreierRelator (d : ℕ) where
  | step (j : ℕ) (valid : j + 1 < d)
  | final

def cyclicSchreierRelator (n d : ℕ) [NeZero d] :
    CyclicSchreierRelator d → FreeGroup (CyclicSchreierGenerator n d)
  | .step j h =>
      FreeGroup.of (.sheetB ⟨j + 1, h⟩) *
        (FreeGroup.of (.sheetB ⟨j, lt_trans (Nat.lt_succ_self j) h⟩))⁻¹ *
        cyclicSchreierSheetWord n d ⟨j, lt_trans (Nat.lt_succ_self j) h⟩
  | .final =>
      FreeGroup.of .wrapA *
        FreeGroup.of (.sheetB (cyclicFirstSheet d)) *
        (FreeGroup.of .wrapA)⁻¹ *
        (FreeGroup.of (.sheetB (cyclicLastSheet d)))⁻¹ *
        cyclicSchreierSheetWord n d (cyclicLastSheet d)

def cyclicSchreierRelators (n d : ℕ) [NeZero d] :
    Set (FreeGroup (CyclicSchreierGenerator n d)) :=
  Set.range (cyclicSchreierRelator n d)

def cyclicSchreierToSurface (n d : ℕ) :
    CyclicSchreierGenerator n d → FreeGroup (CyclicSurfaceGenerator n d)
  | .wrapA => FreeGroup.of (.base false)
  | .sheetB sheet =>
      cyclicRecurrenceNormalForm (FreeGroup.of (.base true))
        (cyclicSurfaceSheetWordNat n d) sheet.val
  | .rest sheet handle side => FreeGroup.of (.rest sheet handle side)

def cyclicSurfaceToSchreier (n d : ℕ) [NeZero d] :
    CyclicSurfaceGenerator n d → FreeGroup (CyclicSchreierGenerator n d)
  | .base false => FreeGroup.of .wrapA
  | .base true => FreeGroup.of (.sheetB (cyclicFirstSheet d))
  | .rest sheet handle side => FreeGroup.of (.rest sheet handle side)

lemma cyclicSchreierToSurface_sheetWord (n d : ℕ) (sheet : Fin d) :
    FreeGroup.lift (cyclicSchreierToSurface n d)
        (cyclicSchreierSheetWord n d sheet) =
      cyclicSurfaceSheetWord n d sheet := by
  rw [cyclicSchreierSheetWord, cyclicSurfaceSheetWord, map_list_prod]
  apply congrArg List.prod
  rw [List.map_ofFn, List.ofFn_inj]
  funext handle
  simp [map_mul, map_inv, FreeGroup.lift_apply_of,
    cyclicSchreierToSurface]

lemma cyclicSurfaceToSchreier_sheetWord (n d : ℕ) [NeZero d] (sheet : Fin d) :
    FreeGroup.lift (cyclicSurfaceToSchreier n d)
        (cyclicSurfaceSheetWord n d sheet) =
      cyclicSchreierSheetWord n d sheet := by
  rw [cyclicSchreierSheetWord, cyclicSurfaceSheetWord, map_list_prod]
  apply congrArg List.prod
  rw [List.map_ofFn, List.ofFn_inj]
  funext handle
  simp [map_mul, map_inv, FreeGroup.lift_apply_of,
    cyclicSurfaceToSchreier]

lemma cyclicSchreierToSurface_sheetWordNat (n d j : ℕ) :
    FreeGroup.lift (cyclicSchreierToSurface n d)
        (cyclicSchreierSheetWordNat n d j) =
      cyclicSurfaceSheetWordNat n d j := by
  by_cases h : j < d
  · simp [cyclicSchreierSheetWordNat, cyclicSurfaceSheetWordNat, h,
      cyclicSchreierToSurface_sheetWord]
  · simp [cyclicSchreierSheetWordNat, cyclicSurfaceSheetWordNat, h]

lemma cyclicSurfaceToSchreier_sheetWordNat (n d j : ℕ) [NeZero d] :
    FreeGroup.lift (cyclicSurfaceToSchreier n d)
        (cyclicSurfaceSheetWordNat n d j) =
      cyclicSchreierSheetWordNat n d j := by
  by_cases h : j < d
  · simp [cyclicSchreierSheetWordNat, cyclicSurfaceSheetWordNat, h,
      cyclicSurfaceToSchreier_sheetWord]
  · simp [cyclicSchreierSheetWordNat, cyclicSurfaceSheetWordNat, h]

lemma cyclicSurfaceToSchreier_prefixProduct (n d j : ℕ) [NeZero d] :
    FreeGroup.lift (cyclicSurfaceToSchreier n d)
        (cyclicPrefixProduct (cyclicSurfaceSheetWordNat n d) j) =
      cyclicPrefixProduct (cyclicSchreierSheetWordNat n d) j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [cyclicPrefixProduct_succ, cyclicPrefixProduct_succ, map_mul, ih,
        cyclicSurfaceToSchreier_sheetWordNat]

lemma cyclicSurfaceToSchreier_recurrence (n d j : ℕ) [NeZero d] :
    FreeGroup.lift (cyclicSurfaceToSchreier n d)
        (cyclicRecurrenceNormalForm (FreeGroup.of (.base true))
          (cyclicSurfaceSheetWordNat n d) j) =
      cyclicRecurrenceNormalForm (cyclicSchreierBNat n d 0)
        (cyclicSchreierSheetWordNat n d) j := by
  induction j with
  | zero =>
      rw [cyclicRecurrenceNormalForm_zero, cyclicRecurrenceNormalForm_zero]
      simp only [FreeGroup.lift_apply_of, cyclicSurfaceToSchreier,
        cyclicSchreierBNat, dif_pos (NeZero.pos d)]
      congr 2
  | succ j ih =>
      rw [cyclicRecurrenceNormalForm_succ, cyclicRecurrenceNormalForm_succ,
        map_mul, map_inv, cyclicSurfaceToSchreier_sheetWordNat, ih]

lemma cyclicSchreier_step_relatorEquivalent (n d j : ℕ) [NeZero d]
    (h : j + 1 < d) :
    RelatorEquivalent (cyclicSchreierRelators n d)
      (cyclicSchreierBNat n d (j + 1) *
        (cyclicSchreierBNat n d j)⁻¹ *
        cyclicSchreierSheetWordNat n d j) 1 := by
  have hj : j < d := lt_trans (Nat.lt_succ_self j) h
  have hmem : cyclicSchreierRelator n d (CyclicSchreierRelator.step j h) ∈
      cyclicSchreierRelators n d :=
    ⟨CyclicSchreierRelator.step j h, rfl⟩
  simpa [cyclicSchreierBNat, cyclicSchreierSheetWordNat,
    cyclicSchreierRelator, h, hj] using RelatorEquivalent.of_mem hmem

lemma cyclicSchreier_final_relatorEquivalent (n d : ℕ) [NeZero d] :
    RelatorEquivalent (cyclicSchreierRelators n d)
      (FreeGroup.of (.wrapA : CyclicSchreierGenerator n d) *
        cyclicSchreierBNat n d 0 *
        (FreeGroup.of (.wrapA : CyclicSchreierGenerator n d))⁻¹ *
        (cyclicSchreierBNat n d (d - 1))⁻¹ *
        cyclicSchreierSheetWordNat n d (d - 1)) 1 := by
  have hzero : 0 < d := NeZero.pos d
  have hlast : d - 1 < d := Nat.sub_lt hzero zero_lt_one
  have hmem : cyclicSchreierRelator n d CyclicSchreierRelator.final ∈
      cyclicSchreierRelators n d :=
    ⟨CyclicSchreierRelator.final, rfl⟩
  simpa [cyclicSchreierBNat, cyclicSchreierSheetWordNat,
    cyclicSchreierRelator, hzero, hlast, cyclicFirstSheet, cyclicLastSheet] using
      RelatorEquivalent.of_mem hmem

lemma cyclicSchreier_final_maps_to_surfaceRelator (n d : ℕ) [NeZero d] :
    FreeGroup.lift (cyclicSchreierToSurface n d)
        (cyclicSchreierRelator n d .final) =
      cyclicSurfaceRelator n d := by
  simp only [cyclicSchreierRelator, map_mul, map_inv,
    FreeGroup.lift_apply_of, cyclicSchreierToSurface,
    cyclicSchreierToSurface_sheetWord, cyclicFirstSheet_val,
    cyclicLastSheet_val]
  rw [cyclicRecurrenceNormalForm_zero, cyclicRecurrenceNormalForm]
  have hlast : d - 1 < d := Nat.sub_lt (NeZero.pos d) zero_lt_one
  have hW : cyclicSurfaceSheetWord n d (cyclicLastSheet d) =
      cyclicSurfaceSheetWordNat n d (d - 1) := by
    rw [cyclicSurfaceSheetWordNat, dif_pos hlast]
    congr 1
  have hprefix : cyclicPrefixProduct (cyclicSurfaceSheetWordNat n d) d =
      cyclicPrefixProduct (cyclicSurfaceSheetWordNat n d) (d - 1) *
        cyclicSurfaceSheetWordNat n d (d - 1) := by
    rw [← cyclicPrefixProduct_succ]
    congr 1
    exact (Nat.sub_add_cancel (NeZero.pos d)).symm
  rw [cyclicSurfaceRelator, hW, hprefix]
  group

lemma cyclicSchreier_maps_relators (n d : ℕ) [NeZero d] :
    ∀ r ∈ cyclicSchreierRelators n d,
      RelatorEquivalent ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d)))
        (FreeGroup.lift (cyclicSchreierToSurface n d) r) 1 := by
  intro r hr
  rcases hr with ⟨rel, rfl⟩
  cases rel with
  | step j h =>
      apply RelatorEquivalent.of_eq
      simp only [cyclicSchreierRelator, map_mul, map_inv,
        FreeGroup.lift_apply_of, cyclicSchreierToSurface,
        cyclicSchreierToSurface_sheetWord]
      rw [cyclicRecurrenceNormalForm_succ]
      have hj : j < d := lt_trans (Nat.lt_succ_self j) h
      simp only [cyclicSurfaceSheetWordNat, dif_pos hj]
      have hsheet :
          (⟨j, lt_trans (Nat.lt_succ_self j) h⟩ : Fin d) = ⟨j, hj⟩ :=
        Fin.ext rfl
      rw [hsheet]
      group
  | final =>
      exact (RelatorEquivalent.of_eq
        (cyclicSchreier_final_maps_to_surfaceRelator n d)).trans
          (RelatorEquivalent.of_mem (Set.mem_singleton _))

lemma cyclicSurface_maps_relator (n d : ℕ) [NeZero d] :
    ∀ r ∈ ({cyclicSurfaceRelator n d} :
      Set (FreeGroup (CyclicSurfaceGenerator n d))),
      RelatorEquivalent (cyclicSchreierRelators n d)
        (FreeGroup.lift (cyclicSurfaceToSchreier n d) r) 1 := by
  intro r hr
  rw [Set.mem_singleton_iff.mp hr]
  have hstep : ∀ j, j < d - 1 →
      RelatorEquivalent (cyclicSchreierRelators n d)
        (cyclicSchreierBNat n d (j + 1) *
          (cyclicSchreierBNat n d j)⁻¹ *
          cyclicSchreierSheetWordNat n d j) 1 := by
    intro j hj
    exact cyclicSchreier_step_relatorEquivalent n d j (by omega)
  have hfinal := cyclicSchreier_final_relatorEquivalent n d
  have hcollapsed := cyclicFinalRelator_relatorEquivalent_of_lt
    (FreeGroup.of (.wrapA : CyclicSchreierGenerator n d))
    (cyclicSchreierBNat n d) (cyclicSchreierSheetWordNat n d)
    (d - 1) hstep hfinal
  have hd : d - 1 + 1 = d := Nat.sub_add_cancel (NeZero.pos d)
  have hmap :
      FreeGroup.lift (cyclicSurfaceToSchreier n d)
          (cyclicSurfaceRelator n d) =
        FreeGroup.of (.wrapA : CyclicSchreierGenerator n d) *
          cyclicSchreierBNat n d 0 *
          (FreeGroup.of (.wrapA : CyclicSchreierGenerator n d))⁻¹ *
          (cyclicSchreierBNat n d 0)⁻¹ *
          cyclicPrefixProduct (cyclicSchreierSheetWordNat n d) d := by
    simp only [cyclicSurfaceRelator, map_mul, map_inv,
      FreeGroup.lift_apply_of, cyclicSurfaceToSchreier,
      cyclicSurfaceToSchreier_prefixProduct, cyclicSchreierBNat_zero]
  rw [hmap]
  simpa [hd] using hcollapsed

lemma cyclicSchreier_from_to (n d : ℕ) [NeZero d] :
    ∀ z : CyclicSchreierGenerator n d,
      RelatorEquivalent (cyclicSchreierRelators n d)
        (FreeGroup.lift (cyclicSurfaceToSchreier n d)
          (cyclicSchreierToSurface n d z))
        (FreeGroup.of z) := by
  intro z
  cases z with
  | wrapA =>
      change RelatorEquivalent (cyclicSchreierRelators n d)
        (FreeGroup.of CyclicSchreierGenerator.wrapA)
        (FreeGroup.of CyclicSchreierGenerator.wrapA)
      exact RelatorEquivalent.refl _ _
  | rest sheet handle side =>
      change RelatorEquivalent (cyclicSchreierRelators n d)
        (FreeGroup.of (CyclicSchreierGenerator.rest sheet handle side))
        (FreeGroup.of (CyclicSchreierGenerator.rest sheet handle side))
      exact RelatorEquivalent.refl _ _
  | sheetB sheet =>
      have hstep : ∀ j, j < sheet.val →
          RelatorEquivalent (cyclicSchreierRelators n d)
            (cyclicSchreierBNat n d (j + 1) *
              (cyclicSchreierBNat n d j)⁻¹ *
              cyclicSchreierSheetWordNat n d j) 1 := by
        intro j hj
        apply cyclicSchreier_step_relatorEquivalent n d j
        exact lt_of_le_of_lt (Nat.succ_le_iff.mpr hj) sheet.isLt
      have hrec := cyclicRecurrence_relatorEquivalent_of_lt
        (cyclicSchreierBNat n d) (cyclicSchreierSheetWordNat n d)
        sheet.val hstep sheet.val le_rfl
      have hrec' : RelatorEquivalent (cyclicSchreierRelators n d)
          (FreeGroup.of (.sheetB sheet))
          (cyclicRecurrenceNormalForm (cyclicSchreierBNat n d 0)
            (cyclicSchreierSheetWordNat n d) sheet.val) := by
        simpa [cyclicSchreierBNat, sheet.isLt] using hrec
      exact (RelatorEquivalent.of_eq
        (cyclicSurfaceToSchreier_recurrence n d sheet.val)).trans hrec'.symm

lemma cyclicSurface_to_from (n d : ℕ) [NeZero d] :
    ∀ y : CyclicSurfaceGenerator n d,
      RelatorEquivalent ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d)))
        (FreeGroup.lift (cyclicSchreierToSurface n d)
          (cyclicSurfaceToSchreier n d y))
        (FreeGroup.of y) := by
  intro y
  cases y with
  | base side =>
      cases side
      · change RelatorEquivalent ({cyclicSurfaceRelator n d} : _)
          (FreeGroup.of (CyclicSurfaceGenerator.base false))
          (FreeGroup.of (CyclicSurfaceGenerator.base false))
        exact RelatorEquivalent.refl _ _
      · change RelatorEquivalent ({cyclicSurfaceRelator n d} : _)
          (cyclicRecurrenceNormalForm
            (FreeGroup.of (CyclicSurfaceGenerator.base true))
            (cyclicSurfaceSheetWordNat n d) (cyclicFirstSheet d).val)
          (FreeGroup.of (CyclicSurfaceGenerator.base true))
        rw [cyclicFirstSheet_val, cyclicRecurrenceNormalForm_zero]
  | rest sheet handle side =>
      change RelatorEquivalent ({cyclicSurfaceRelator n d} : _)
        (FreeGroup.of (CyclicSurfaceGenerator.rest sheet handle side))
        (FreeGroup.of (CyclicSurfaceGenerator.rest sheet handle side))
      exact RelatorEquivalent.refl _ _

def cyclicSchreierTietzeEquivSurface (n d : ℕ) [NeZero d] :
    TietzeEquiv (cyclicSchreierRelators n d)
      ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d))) :=
  TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    (cyclicSchreierToSurface n d) (cyclicSurfaceToSchreier n d)
    (cyclicSchreier_maps_relators n d) (cyclicSurface_maps_relator n d)
    (cyclicSchreier_from_to n d) (cyclicSurface_to_from n d)

noncomputable def cyclicSchreierPresentedEquivSurface (n d : ℕ) [NeZero d] :
    PresentedGroup (cyclicSchreierRelators n d) ≃*
      PresentedGroup ({cyclicSurfaceRelator n d} :
        Set (FreeGroup (CyclicSurfaceGenerator n d))) :=
  (cyclicSchreierTietzeEquivSurface n d).presentedEquiv

end
end SystolicGrowth
