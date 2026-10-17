module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphFreeGenerators
public import BuserSarnak.OrientableWicksNielsen
public import Mathlib.Data.List.FinRange

@[expose] public section

/-!
# Literal quadratic peripheral letters of the actual boundary graph

The original cyclic side list is read backwards, as required by Mathlib's
fundamental-group multiplication. Only the actually selected physical tree
edges are deleted. Every remaining physical edge occurs positively at its
original lower side index and negatively at its original paired side index.

This supplies literal occurrence data, not an assumed one-vertex Wicks
certificate. The vertex-orbit condition remains a separate geometric proof.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The actual oriented side letter, deleting exactly selected physical tree edges. -/
def intrinsicBoundaryPeripheralSideLetter (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    Option (B.IntrinsicBoundaryNonTreeEdge × Bool) := by
  classical
  exact if ht : B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge
    then none else
      some (⟨B.intrinsicBoundaryPhysicalEdge i, ht⟩,
        if i < B.intrinsicCyclicPairing i then true else false)

/-- Literal signed peripheral letters in the original reversed time order. -/
def intrinsicBoundaryPeripheralLetters (B : DirichletBoundarySegments X o) :
    SignedWord B.IntrinsicBoundaryNonTreeEdge :=
  (List.ofFn (fun i : Fin B.intrinsicBoundaryRadialCuts.card => i)).reverse.filterMap
    B.intrinsicBoundaryPeripheralSideLetter

private theorem peripheral_physicalEdge_val (B : DirichletBoundarySegments X o)
    (a : B.IntrinsicBoundaryPhysicalEdge) : B.intrinsicBoundaryPhysicalEdge a.val = a := by
  classical
  apply Subtype.ext
  simp only [intrinsicBoundaryPhysicalEdge, dif_pos a.property]

/-- No side other than a genuinely selected physical tree side is deleted. -/
@[simp]
theorem intrinsicBoundaryPeripheralSideLetter_eq_none_iff
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryPeripheralSideLetter i = none ↔
      B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge := by
  classical
  by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge
  · simp [intrinsicBoundaryPeripheralSideLetter, ht]
  · simp [intrinsicBoundaryPeripheralSideLetter, ht]

/-- A positive non-tree occurrence is witnessed by its exact original canonical side. -/
@[simp]
theorem intrinsicBoundaryPeripheralSideLetter_positive
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralSideLetter e.val.val = some (e, true) := by
  classical
  have he := peripheral_physicalEdge_val B e.val
  have ht : B.intrinsicBoundaryPhysicalEdge e.val.val ∉ range B.intrinsicBoundaryTreePhysicalEdge := by
    rw [he]
    exact e.property
  simp only [intrinsicBoundaryPeripheralSideLetter, dif_neg ht, if_pos e.val.property]
  exact congrArg some (Prod.ext (Subtype.ext he) rfl)

/-- Pairing preserves the physical letter and flips its literal sign. -/
theorem intrinsicBoundaryPeripheralSideLetter_pair
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryPeripheralSideLetter (B.intrinsicCyclicPairing i) =
      (B.intrinsicBoundaryPeripheralSideLetter i).map
        (fun letter => (letter.1, !letter.2)) := by
  classical
  by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge
  · simp only [intrinsicBoundaryPeripheralSideLetter, B.intrinsicBoundaryPhysicalEdge_pair,
      dif_pos ht, Option.map_none]
  · by_cases hi : i < B.intrinsicCyclicPairing i
    · have hp : ¬ B.intrinsicCyclicPairing i <
          B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
        rw [B.intrinsicCyclicPairing_involutive]
        exact not_lt_of_ge hi.le
      simp only [intrinsicBoundaryPeripheralSideLetter, B.intrinsicBoundaryPhysicalEdge_pair,
        dif_neg ht, if_pos hi, if_neg hp, Option.map_some, Bool.not_true]
    · have hp : B.intrinsicCyclicPairing i <
          B.intrinsicCyclicPairing (B.intrinsicCyclicPairing i) := by
        rw [B.intrinsicCyclicPairing_involutive]
        exact lt_of_le_of_ne (le_of_not_gt hi) (B.intrinsicCyclicPairing_ne_self i)
      simp only [intrinsicBoundaryPeripheralSideLetter, B.intrinsicBoundaryPhysicalEdge_pair,
        dif_neg ht, if_neg hi, if_pos hp, Option.map_some, Bool.not_false]

/-- The negative occurrence is the original paired side, not a replacement dart. -/
@[simp]
theorem intrinsicBoundaryPeripheralSideLetter_negative
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralSideLetter (B.intrinsicCyclicPairing e.val.val) =
      some (e, false) := by
  rw [intrinsicBoundaryPeripheralSideLetter_pair, intrinsicBoundaryPeripheralSideLetter_positive]
  rfl

/-- Positive occurrences have precisely their original canonical cyclic index. -/
theorem intrinsicBoundaryPeripheralSideLetter_some_true_iff
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralSideLetter i = some (e, true) ↔ i = e.val.val := by
  classical
  constructor
  · intro h
    by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge
    · rw [intrinsicBoundaryPeripheralSideLetter, dif_pos ht] at h
      cases h
    · by_cases hi : i < B.intrinsicCyclicPairing i
      · simp only [intrinsicBoundaryPeripheralSideLetter, dif_neg ht, if_pos hi,
          Option.some.injEq, Prod.mk.injEq, and_true] at h
        have hval := congrArg (fun a : B.IntrinsicBoundaryNonTreeEdge => a.val.val) h
        simpa only [intrinsicBoundaryPhysicalEdge, dif_pos hi] using hval
      · simp only [intrinsicBoundaryPeripheralSideLetter, dif_neg ht, if_neg hi,
          Option.some.injEq, Prod.mk.injEq] at h
        cases h.2
  · rintro rfl
    exact B.intrinsicBoundaryPeripheralSideLetter_positive e

/-- Negative occurrences have precisely their original involutively paired cyclic index. -/
theorem intrinsicBoundaryPeripheralSideLetter_some_false_iff
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralSideLetter i = some (e, false) ↔
      i = B.intrinsicCyclicPairing e.val.val := by
  classical
  constructor
  · intro h
    by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge
    · rw [intrinsicBoundaryPeripheralSideLetter, dif_pos ht] at h
      cases h
    · by_cases hi : i < B.intrinsicCyclicPairing i
      · simp only [intrinsicBoundaryPeripheralSideLetter, dif_neg ht, if_pos hi,
          Option.some.injEq, Prod.mk.injEq] at h
        cases h.2
      · simp only [intrinsicBoundaryPeripheralSideLetter, dif_neg ht, if_neg hi,
          Option.some.injEq, Prod.mk.injEq, and_true] at h
        have hval := congrArg (fun a : B.IntrinsicBoundaryNonTreeEdge => a.val.val) h
        have hp : B.intrinsicCyclicPairing i = e.val.val := by
          simpa only [intrinsicBoundaryPhysicalEdge, dif_neg hi] using hval
        exact (B.intrinsicCyclicPairing_involutive i).symm.trans
          (congrArg B.intrinsicCyclicPairing hp)
  · rintro rfl
    exact B.intrinsicBoundaryPeripheralSideLetter_negative e

/-- Each retained literal signed occurrence has a unique original side index. -/
theorem intrinsicBoundaryPeripheralSideLetter_some_iff
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    B.intrinsicBoundaryPeripheralSideLetter i = some letter ↔
      i = if letter.2 then letter.1.val.val else B.intrinsicCyclicPairing letter.1.val.val := by
  rcases letter with ⟨e, sign⟩
  cases sign
  · exact B.intrinsicBoundaryPeripheralSideLetter_some_false_iff i e
  · exact B.intrinsicBoundaryPeripheralSideLetter_some_true_iff i e

/-- Recover the actual original cyclic side from a signed physical non-tree letter. -/
def intrinsicBoundaryPeripheralSignedOriginalSide (B : DirichletBoundarySegments X o)
    (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) : Fin B.intrinsicBoundaryRadialCuts.card :=
  if letter.2 then letter.1.val.val else B.intrinsicCyclicPairing letter.1.val.val

private theorem peripheral_sideLetter_map_originalSide
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    (B.intrinsicBoundaryPeripheralSideLetter i).map B.intrinsicBoundaryPeripheralSignedOriginalSide =
      if decide (B.intrinsicBoundaryPhysicalEdge i ∉ range B.intrinsicBoundaryTreePhysicalEdge)
        then some i else none := by
  classical
  cases hs : B.intrinsicBoundaryPeripheralSideLetter i with
  | none =>
    have ht := (B.intrinsicBoundaryPeripheralSideLetter_eq_none_iff i).mp hs
    simp only [Option.map_none, ht, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
  | some letter =>
    have ht : B.intrinsicBoundaryPhysicalEdge i ∉ range B.intrinsicBoundaryTreePhysicalEdge := by
      intro ht
      have hn := (B.intrinsicBoundaryPeripheralSideLetter_eq_none_iff i).mpr ht
      rw [hs] at hn
      cases hn
    have hi : i = B.intrinsicBoundaryPeripheralSignedOriginalSide letter :=
      (B.intrinsicBoundaryPeripheralSideLetter_some_iff i letter).mp hs
    simpa [ht] using congrArg some hi.symm

/-- The recovered side list is literally the reversed original list with only tree sides removed. -/
theorem intrinsicBoundaryPeripheralLetters_originalSide_list
    (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryPeripheralLetters.map B.intrinsicBoundaryPeripheralSignedOriginalSide =
      (List.ofFn (fun i : Fin B.intrinsicBoundaryRadialCuts.card => i)).reverse.filter
        (fun i => decide (B.intrinsicBoundaryPhysicalEdge i ∉
          range B.intrinsicBoundaryTreePhysicalEdge)) := by
  classical
  rw [intrinsicBoundaryPeripheralLetters, List.map_filterMap]
  simp only [peripheral_sideLetter_map_originalSide]
  rw [← List.filterMap_eq_filter]
  apply List.filterMap_congr
  intro i _
  unfold Option.guard
  by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∉ range B.intrinsicBoundaryTreePhysicalEdge <;>
    simp [ht]

/-- Every signed non-tree letter occurs in the original literal peripheral list. -/
theorem intrinsicBoundaryPeripheralLetters_mem
    (B : DirichletBoundarySegments X o) (letter : B.IntrinsicBoundaryNonTreeEdge × Bool) :
    letter ∈ B.intrinsicBoundaryPeripheralLetters := by
  rw [intrinsicBoundaryPeripheralLetters, List.mem_filterMap]
  refine ⟨if letter.2 then letter.1.val.val else B.intrinsicCyclicPairing letter.1.val.val,
    ?_, (B.intrinsicBoundaryPeripheralSideLetter_some_iff _ letter).mpr rfl⟩
  simp only [List.mem_reverse, List.mem_ofFn]
  exact ⟨_, rfl⟩

/-- No literal signed occurrence repeats; this is before free reduction. -/
theorem intrinsicBoundaryPeripheralLetters_nodup (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryPeripheralLetters.Nodup := by
  apply List.Nodup.filterMap (fun i j letter hi hj => ?_)
    (List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id))
  exact ((B.intrinsicBoundaryPeripheralSideLetter_some_iff i letter).mp hi).trans
    ((B.intrinsicBoundaryPeripheralSideLetter_some_iff j letter).mp hj).symm

private theorem peripheral_signedOccurrenceCount_eq_count
    {A : Type*} [DecidableEq A] [BEq A] [LawfulBEq A]
    (e : A) (sign : Bool) (word : SignedWord A) :
    signedOccurrenceCount e sign word = word.count (e, sign) := by
  rw [signedOccurrenceCount, List.count_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro letter _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, beq_iff_eq, Prod.ext_iff]

/-- Each physical non-tree letter occurs exactly once with either requested orientation. -/
theorem intrinsicBoundaryPeripheralLetters_signedOccurrenceCount
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) (sign : Bool) :
    signedOccurrenceCount e sign B.intrinsicBoundaryPeripheralLetters = 1 := by
  classical
  rw [peripheral_signedOccurrenceCount_eq_count]
  exact List.count_eq_one_of_mem B.intrinsicBoundaryPeripheralLetters_nodup
    (B.intrinsicBoundaryPeripheralLetters_mem (e, sign))

private theorem peripheral_filterMap_mk (B : DirichletBoundarySegments X o)
    (sides : List (Fin B.intrinsicBoundaryRadialCuts.card)) :
    FreeGroup.mk (sides.filterMap B.intrinsicBoundaryPeripheralSideLetter) =
      (sides.map B.intrinsicBoundaryFreeSideWord).prod := by
  classical
  induction sides with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons i sides ih =>
    by_cases ht : B.intrinsicBoundaryPhysicalEdge i ∈ range B.intrinsicBoundaryTreePhysicalEdge
    · simp only [List.filterMap_cons, intrinsicBoundaryPeripheralSideLetter, dif_pos ht,
        List.map_cons, List.prod_cons, intrinsicBoundaryFreeSideWord, one_mul, ih]
    · by_cases hi : i < B.intrinsicCyclicPairing i
      · simp only [List.filterMap_cons, intrinsicBoundaryPeripheralSideLetter, dif_neg ht,
          if_pos hi, List.map_cons, List.prod_cons, intrinsicBoundaryFreeSideWord]
        rw [← List.singleton_append, ← FreeGroup.mul_mk, ih]
        rfl
      · simp only [List.filterMap_cons, intrinsicBoundaryPeripheralSideLetter, dif_neg ht,
          if_neg hi, List.map_cons, List.prod_cons, intrinsicBoundaryFreeSideWord]
        rw [← List.singleton_append, ← FreeGroup.mul_mk, ih]
        rfl

/-- The literal signed word evaluates exactly to the original reversed perimeter word. -/
theorem intrinsicBoundaryPeripheralLetters_mk (B : DirichletBoundarySegments X o) :
    FreeGroup.mk B.intrinsicBoundaryPeripheralLetters = B.intrinsicBoundaryPerimeterFreeWord := by
  rw [intrinsicBoundaryPeripheralLetters, peripheral_filterMap_mk,
    List.map_reverse, List.map_ofFn]
  rfl

/-- Literal peripheral positions are exactly the physical signed non-tree letters. -/
def intrinsicBoundaryPeripheralOccurrenceEquiv (B : DirichletBoundarySegments X o) :
    Fin B.intrinsicBoundaryPeripheralLetters.length ≃ B.IntrinsicBoundaryNonTreeEdge × Bool :=
  Equiv.ofBijective B.intrinsicBoundaryPeripheralLetters.get
    ⟨List.nodup_iff_injective_get.mp B.intrinsicBoundaryPeripheralLetters_nodup,
      fun letter => List.mem_iff_get.mp (B.intrinsicBoundaryPeripheralLetters_mem letter)⟩

/-- Position of the unique original positive occurrence in the reversed retained list. -/
def intrinsicBoundaryPeripheralPositivePosition (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryNonTreeEdge) : Fin B.intrinsicBoundaryPeripheralLetters.length :=
  B.intrinsicBoundaryPeripheralOccurrenceEquiv.symm (e, true)

/-- Position of the unique original paired negative occurrence in the retained list. -/
def intrinsicBoundaryPeripheralNegativePosition (B : DirichletBoundarySegments X o)
    (e : B.IntrinsicBoundaryNonTreeEdge) : Fin B.intrinsicBoundaryPeripheralLetters.length :=
  B.intrinsicBoundaryPeripheralOccurrenceEquiv.symm (e, false)

@[simp]
theorem intrinsicBoundaryPeripheralPositivePosition_spec
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralLetters.get (B.intrinsicBoundaryPeripheralPositivePosition e) =
      (e, true) := B.intrinsicBoundaryPeripheralOccurrenceEquiv.apply_symm_apply _

@[simp]
theorem intrinsicBoundaryPeripheralNegativePosition_spec
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralLetters.get (B.intrinsicBoundaryPeripheralNegativePosition e) =
      (e, false) := B.intrinsicBoundaryPeripheralOccurrenceEquiv.apply_symm_apply _

/-- Original side provenance of a retained literal position. -/
def intrinsicBoundaryPeripheralOriginalSide (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryPeripheralLetters.length) : Fin B.intrinsicBoundaryRadialCuts.card :=
  B.intrinsicBoundaryPeripheralSignedOriginalSide (B.intrinsicBoundaryPeripheralLetters.get i)

/-- Decoding the actual original side recovers the untouched literal occurrence. -/
theorem intrinsicBoundaryPeripheralOriginalSide_spec
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryPeripheralLetters.length) :
    B.intrinsicBoundaryPeripheralSideLetter (B.intrinsicBoundaryPeripheralOriginalSide i) =
      some (B.intrinsicBoundaryPeripheralLetters.get i) :=
  (B.intrinsicBoundaryPeripheralSideLetter_some_iff _ _).mpr rfl

@[simp]
theorem intrinsicBoundaryPeripheralOriginalSide_positive
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralOriginalSide (B.intrinsicBoundaryPeripheralPositivePosition e) =
      e.val.val := by
  rw [intrinsicBoundaryPeripheralOriginalSide, intrinsicBoundaryPeripheralPositivePosition_spec]
  rfl

@[simp]
theorem intrinsicBoundaryPeripheralOriginalSide_negative
    (B : DirichletBoundarySegments X o) (e : B.IntrinsicBoundaryNonTreeEdge) :
    B.intrinsicBoundaryPeripheralOriginalSide (B.intrinsicBoundaryPeripheralNegativePosition e) =
      B.intrinsicCyclicPairing e.val.val := by
  rw [intrinsicBoundaryPeripheralOriginalSide, intrinsicBoundaryPeripheralNegativePosition_spec]
  rfl

/-- Pair literal positions by the original physical side reversal. -/
def intrinsicBoundaryPeripheralPartner (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryPeripheralLetters.length) : Fin B.intrinsicBoundaryPeripheralLetters.length :=
  B.intrinsicBoundaryPeripheralOccurrenceEquiv.symm
    ((B.intrinsicBoundaryPeripheralLetters.get i).1, !(B.intrinsicBoundaryPeripheralLetters.get i).2)

@[simp]
theorem intrinsicBoundaryPeripheralPartner_spec
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryPeripheralLetters.length) :
    B.intrinsicBoundaryPeripheralLetters.get (B.intrinsicBoundaryPeripheralPartner i) =
      ((B.intrinsicBoundaryPeripheralLetters.get i).1, !(B.intrinsicBoundaryPeripheralLetters.get i).2) :=
  B.intrinsicBoundaryPeripheralOccurrenceEquiv.apply_symm_apply _

/-- The occurrence partner is exactly the original involutive cyclic side pairing. -/
theorem intrinsicBoundaryPeripheralOriginalSide_partner
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryPeripheralLetters.length) :
    B.intrinsicBoundaryPeripheralOriginalSide (B.intrinsicBoundaryPeripheralPartner i) =
      B.intrinsicCyclicPairing (B.intrinsicBoundaryPeripheralOriginalSide i) := by
  rw [intrinsicBoundaryPeripheralOriginalSide, intrinsicBoundaryPeripheralPartner_spec]
  change B.intrinsicBoundaryPeripheralSignedOriginalSide
      ((B.intrinsicBoundaryPeripheralLetters.get i).1, !(B.intrinsicBoundaryPeripheralLetters.get i).2) =
    B.intrinsicCyclicPairing
      (B.intrinsicBoundaryPeripheralSignedOriginalSide (B.intrinsicBoundaryPeripheralLetters.get i))
  generalize B.intrinsicBoundaryPeripheralLetters.get i = letter
  rcases letter with ⟨e, sign⟩
  cases sign
  · exact (B.intrinsicCyclicPairing_involutive e.val.val).symm
  · rfl

/-- The literal quadratic word has two positions for each actual non-tree letter. -/
theorem intrinsicBoundaryPeripheralLetters_length (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryPeripheralLetters.length = 2 * Fintype.card B.IntrinsicBoundaryNonTreeEdge := by
  have h := Fintype.card_congr B.intrinsicBoundaryPeripheralOccurrenceEquiv
  simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm] using h

/-- Every retained literal occurrence is the displayed positive or negative occurrence. -/
theorem intrinsicBoundaryPeripheralPositions_exhaustive
    (B : DirichletBoundarySegments X o) (i : Fin B.intrinsicBoundaryPeripheralLetters.length) :
    i = B.intrinsicBoundaryPeripheralPositivePosition (B.intrinsicBoundaryPeripheralLetters.get i).1 ∨
      i = B.intrinsicBoundaryPeripheralNegativePosition (B.intrinsicBoundaryPeripheralLetters.get i).1 := by
  cases hs : (B.intrinsicBoundaryPeripheralLetters.get i).2
  · right
    apply B.intrinsicBoundaryPeripheralOccurrenceEquiv.injective
    change B.intrinsicBoundaryPeripheralLetters.get i =
      B.intrinsicBoundaryPeripheralLetters.get
        (B.intrinsicBoundaryPeripheralNegativePosition (B.intrinsicBoundaryPeripheralLetters.get i).1)
    rw [intrinsicBoundaryPeripheralNegativePosition_spec]
    exact Prod.ext rfl hs
  · left
    apply B.intrinsicBoundaryPeripheralOccurrenceEquiv.injective
    change B.intrinsicBoundaryPeripheralLetters.get i =
      B.intrinsicBoundaryPeripheralLetters.get
        (B.intrinsicBoundaryPeripheralPositivePosition (B.intrinsicBoundaryPeripheralLetters.get i).1)
    rw [intrinsicBoundaryPeripheralPositivePosition_spec]
    exact Prod.ext rfl hs

#print axioms intrinsicBoundaryPeripheralSideLetter_some_iff
#print axioms intrinsicBoundaryPeripheralLetters_nodup
#print axioms intrinsicBoundaryPeripheralLetters_signedOccurrenceCount
#print axioms intrinsicBoundaryPeripheralLetters_mk
#print axioms intrinsicBoundaryPeripheralLetters_originalSide_list
#print axioms intrinsicBoundaryPeripheralOriginalSide_partner
#print axioms intrinsicBoundaryPeripheralPositions_exhaustive

end

end SystolicGrowth.DirichletBoundarySegments
