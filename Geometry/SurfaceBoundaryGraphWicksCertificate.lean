module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceBoundaryGraphPeripheralLetters

@[expose] public section

/-!
# Boundary-permutation data for the actual punctured spine

The unreduced polygon-side successor, followed by the actual side pairing,
preserves the terminal vertex of the paired-side graph. This is the local
incidence identity needed before contracting the actual spanning tree.
-/

open Set UpperHalfPlane
open scoped Pointwise UpperHalfPlane

namespace SystolicGrowth.DirichletBoundarySegments

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {o : ℍ}

/-- The literal original perimeter order, before removing any tree sides. -/
def intrinsicBoundaryOriginalSideOrder (B : DirichletBoundarySegments X o) :
    List (Fin B.intrinsicBoundaryRadialCuts.card) :=
  (List.ofFn (fun i : Fin B.intrinsicBoundaryRadialCuts.card => i)).reverse

private theorem originalSideOrder_nodup (B : DirichletBoundarySegments X o) :
    B.intrinsicBoundaryOriginalSideOrder.Nodup := by
  exact List.nodup_reverse.mpr (List.nodup_ofFn.mpr Function.injective_id)

private theorem originalSideOrder_formPerm (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryOriginalSideOrder.formPerm i =
      (finRotate B.intrinsicBoundaryRadialCuts.card).symm i := by
  have hpos : 0 < B.intrinsicBoundaryRadialCuts.card :=
    lt_of_lt_of_le (by decide : 0 < 3) B.three_le_intrinsicBoundaryRadialCuts_card
  letI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨hpos.ne'⟩
  rw [intrinsicBoundaryOriginalSideOrder, List.formPerm_reverse]
  have hbase : (List.ofFn (fun j : Fin B.intrinsicBoundaryRadialCuts.card => j)).formPerm =
      finRotate B.intrinsicBoundaryRadialCuts.card := by
    let l := List.ofFn (fun j : Fin B.intrinsicBoundaryRadialCuts.card => j)
    apply Equiv.ext
    intro j
    have hj : j.val < l.length := by
      change j.val < (List.ofFn (fun k : Fin B.intrinsicBoundaryRadialCuts.card => k)).length
      rw [List.length_ofFn]
      exact j.isLt
    have hstep := List.formPerm_apply_getElem l
      (List.nodup_ofFn.mpr Function.injective_id) j.val hj
    have hleft : l[j.val] = j := by simp [l]
    have hmod : (j.val + 1) % l.length < l.length :=
      Nat.mod_lt _ (by simpa [l] using hpos)
    have hright : l[(j.val + 1) % l.length]'hmod =
        finRotate B.intrinsicBoundaryRadialCuts.card j := by
      simp only [l, List.getElem_ofFn]
      apply Fin.ext
      simp [finRotate_apply, Fin.add_def]
    rw [hleft, hright] at hstep
    exact hstep
  rw [hbase]
  rfl

/-- The side-pairing permutation on literal polygon side indices. -/
def intrinsicBoundarySidePairingPerm (B : DirichletBoundarySegments X o) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) where
  toFun := B.intrinsicCyclicPairing
  invFun := B.intrinsicCyclicPairing
  left_inv := B.intrinsicCyclicPairing_involutive
  right_inv := B.intrinsicCyclicPairing_involutive

/-- The original polygon's vertex transition: cross the paired side, then
advance once in the reversed perimeter order. -/
def intrinsicBoundaryOriginalVertexPerm (B : DirichletBoundarySegments X o) :
    Equiv.Perm (Fin B.intrinsicBoundaryRadialCuts.card) :=
  B.intrinsicBoundaryOriginalSideOrder.formPerm * B.intrinsicBoundarySidePairingPerm

/-- This transition preserves the actual terminal vertex in the physical
paired-side realization. -/
theorem intrinsicBoundaryOriginalVertexPerm_preserves_sideEnd
    (B : DirichletBoundarySegments X o)
    (i : Fin B.intrinsicBoundaryRadialCuts.card) :
    B.intrinsicBoundaryGraphSideEnd (B.intrinsicBoundaryOriginalVertexPerm i) =
      B.intrinsicBoundaryGraphSideEnd i := by
  letI : NeZero B.intrinsicBoundaryRadialCuts.card := ⟨
    (lt_of_lt_of_le (by decide : 0 < 3)
      B.three_le_intrinsicBoundaryRadialCuts_card).ne'⟩
  change B.intrinsicBoundaryGraphSideStart
      (finRotate B.intrinsicBoundaryRadialCuts.card
        (B.intrinsicBoundaryOriginalVertexPerm i)) =
    B.intrinsicBoundaryGraphSideStart (finRotate B.intrinsicBoundaryRadialCuts.card i)
  change B.intrinsicBoundaryGraphSideStart
      (finRotate B.intrinsicBoundaryRadialCuts.card
        (B.intrinsicBoundaryOriginalSideOrder.formPerm
          (B.intrinsicCyclicPairing i))) = _
  rw [B.originalSideOrder_formPerm]
  simpa only [Equiv.apply_symm_apply, intrinsicBoundaryGraphSideEnd] using
    (B.intrinsicBoundaryGraphSide_pair_endpoints i).1

#print axioms intrinsicBoundaryOriginalVertexPerm_preserves_sideEnd

end

end SystolicGrowth.DirichletBoundarySegments
