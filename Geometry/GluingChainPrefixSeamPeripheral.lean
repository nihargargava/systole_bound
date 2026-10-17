module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainPrefixVanKampen
public import Geometry.GluingChainPrefixPolarBoundary
public import Geometry.GluingChainPrefixRightFundamentalGroup
public import Geometry.GluingSeamFundamentalGroup

@[expose] public section

/-!
# Peripheral classes on an adjacent retained-prefix seam

The actual positive turn of the overlap is the outgoing positive boundary
class on the left and the inverse of the retained incoming positive class on
the right. The basepoints and all maps below are the literal cover maps.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

abbrev Internal.GluingChainPrefixSeamPeripheralHelpers.prefixCoverLeft (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) := P.gluedChainPrefixCoverSide k j true

abbrev Internal.GluingChainPrefixSeamPeripheralHelpers.prefixCoverRight (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) := P.gluedChainPrefixCoverSide k j false

abbrev Internal.GluingChainPrefixSeamPeripheralHelpers.prefixCoverOverlap (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) := P.gluedChainPrefixCoverOverlap k j

/-- The literal retained-overlap inclusion into the left cover side. -/
def gluedChainPrefixOverlapLeftInclusion
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) :
    C(↥(P.gluedChainPrefixCoverOverlap k j),
      ↥(P.gluedChainPrefixCoverSide k j true)) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal retained-overlap inclusion into the right cover side. -/
def gluedChainPrefixOverlapRightInclusion
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) :
    C(↥(P.gluedChainPrefixCoverOverlap k j),
      ↥(P.gluedChainPrefixCoverSide k j false)) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- At angle one, the overlap-to-left-side inclusion is the actual
basepoint used by the retained-prefix left group equivalence. -/
theorem gluedChainPrefixPeripheralLeftBasepoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixOverlapLeftInclusion k j
        (P.gluedChainPrefixSeamBasepoint k j (by omega) 1) =
      P.gluedChainPrefixLeftCoverBasepoint k j (by omega)
        (P.gluedChainPrefixRightPolarBoundaryMap j 1) := by
  apply Subtype.ext
  apply Subtype.ext
  exact (P.gluedChainPrefixRightPolarBoundaryMap_val_eq_seam j 1).symm

/-- The adjacent closed intersection identifies the incoming point of the
next original component with the same overlap basepoint on the right side. -/
theorem gluedChainPrefixPeripheralRightBasepoint
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixOverlapRightInclusion k j
        (P.gluedChainPrefixSeamBasepoint k j (by omega) 1) =
      P.gluedChainPrefixRightCoverSideInclusion k j
        (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk
          (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)) := by
  apply Subtype.ext
  apply Subtype.ext
  have hedge : gluingChainEdgeRight j = gluingChainEdgeLeft k := by
    apply Fin.ext
    simp [gluingChainEdgeRight, gluingChainEdgeLeft]
    omega
  calc
    (P.gluedSeamCircleInclusion j 1).1 =
        P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight j) 1 :=
      P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint j
    _ = P.gluedMk ⟨gluingChainEdgeLeft k,
        P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1⟩ := by
      rw [hedge]
      rfl
    _ = ((P.gluedChainPrefixRightCoverSideInclusion k j
        (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk
          (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1))).1).1 := by
      rfl

theorem gluedChainPrefixPeripheralLeftBasepoint_explicit
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixOverlapLeftInclusion k j
        (P.gluedChainPrefixCoverOverlapHomeomorph k j (by omega)
          (P.gluedSeamCircleInclusion j 1)) =
      P.gluedChainPrefixLeftCoverBasepoint k j (by omega)
        (P.gluedChainPrefixRightPolarBoundaryMap j 1) := by
  simpa only [gluedChainPrefixSeamBasepoint] using
    P.gluedChainPrefixPeripheralLeftBasepoint k j hjk

theorem gluedChainPrefixPeripheralRightBasepoint_explicit
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixOverlapRightInclusion k j
        (P.gluedChainPrefixCoverOverlapHomeomorph k j (by omega)
          (P.gluedSeamCircleInclusion j 1)) =
      P.gluedChainPrefixRightCoverSideInclusion k j
        (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk
          (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)) := by
  simpa only [gluedChainPrefixSeamBasepoint] using
    P.gluedChainPrefixPeripheralRightBasepoint k j hjk

/-- The seam loop written with its canonical overlap-homeomorphism endpoint.
This is definitionally the one-turn loop used by the overlap cyclic marking. -/
def gluedChainPrefixPeripheralOverlapOneTurnPath
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    Path
      (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk
        (P.gluedSeamCircleInclusion j 1))
      (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk
        (P.gluedSeamCircleInclusion j 1)) :=
  (P.gluedSeamOneTurnLoop j 1).map
    (P.gluedChainPrefixCoverOverlapHomeomorph k j hjk).continuous_toFun

theorem gluedChainPrefixPeripheralOverlapOneTurnPath_eq
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val < k.val) :
    P.gluedChainPrefixPeripheralOverlapOneTurnPath k j hjk =
      P.gluedChainPrefixOverlapOneTurnLoop k j hjk 1 := rfl

/-- The seam's positive one-turn, included in the left cover side and based
at the unchanged outgoing prefix point, is its literal included prefix loop. -/
theorem gluedChainPrefixPeripheralLeftPath
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    ((P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega)).map
      (P.gluedChainPrefixOverlapLeftInclusion k j).continuous).cast
        (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk).symm
        (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk).symm =
      ((P.gluedChainPrefixRightPolarBoundaryLoop j).map
        (P.gluedChainPrefixInclusion j).continuous).map
          (P.gluedChainPrefixLeftCoverSideHomeomorph k j (by omega)).continuous_toFun := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe]
  apply Subtype.ext
  apply Subtype.ext
  change (P.gluedSeamCircleInclusion j (circleOneTurnLoop 1 t)).1 =
    (P.gluedChainPrefixRightPolarBoundaryMap j (circleOneTurnLoop 1 t)).val
  exact (P.gluedChainPrefixRightPolarBoundaryMap_val_eq_seam j
    (circleOneTurnLoop 1 t)).symm

set_option backward.isDefEq.respectTransparency false in
/-- After the actual left based equivalence, the overlap's positive turn is
exactly the previous prefix's outgoing positive polar loop. -/
theorem gluedChainPrefixPeripheralLeftGenerator
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixLeftCoverFundamentalGroupEquiv k j (by omega)
        (P.gluedChainPrefixRightPolarBoundaryMap j 1)
      (FundamentalGroup.mapOfEq
        (P.gluedChainPrefixOverlapLeftInclusion k j)
        (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega))))) =
      ⟦P.gluedChainPrefixRightPolarBoundaryLoop j⟧ := by
  let E := P.gluedChainPrefixLeftCoverFundamentalGroupEquiv k j (by omega)
    (P.gluedChainPrefixRightPolarBoundaryMap j 1)
  have hback : E.symm (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (P.gluedChainPrefixRightPolarBoundaryLoop j))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((P.gluedChainPrefixRightPolarBoundaryLoop j).map
          (P.gluedChainPrefixInclusion j).continuous).map
            (P.gluedChainPrefixLeftCoverSideHomeomorph k j (by omega)).continuous_toFun)) :=
    P.gluedChainPrefixLeftCoverFundamentalGroupEquiv_symm_apply_loop k j (by omega)
      (P.gluedChainPrefixRightPolarBoundaryMap j 1)
      (P.gluedChainPrefixRightPolarBoundaryLoop j)
  have hclass :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega)).map
          (P.gluedChainPrefixOverlapLeftInclusion k j).continuous).cast
            (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk).symm
            (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk).symm)) =
        E.symm (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (P.gluedChainPrefixRightPolarBoundaryLoop j))) := by
    rw [hback]
    exact congrArg (fun p => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
      (P.gluedChainPrefixPeripheralLeftPath k j hjk)
  rw [FundamentalGroup.mapOfEq_apply]
  change E (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega)).map
        (P.gluedChainPrefixOverlapLeftInclusion k j).continuous).cast
          (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk).symm
          (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk).symm))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (P.gluedChainPrefixRightPolarBoundaryLoop j))
  calc
    _ = E (E.symm (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (P.gluedChainPrefixRightPolarBoundaryLoop j)))) :=
      congrArg E hclass
    _ = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (P.gluedChainPrefixRightPolarBoundaryLoop j)) :=
      E.apply_symm_apply _

/-- On the right, the same positive overlap turn is the inverse of the
unchanged incoming positive polar loop of the next original component. -/
theorem gluedChainPrefixPeripheralRightPath
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    ((P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega)).map
      (P.gluedChainPrefixOverlapRightInclusion k j).continuous).cast
        (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk).symm
        (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk).symm =
      (((P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm).map
        (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk).continuous_toFun).map
          (P.gluedChainPrefixRightCoverSideInclusion k j).continuous := by
  rcases k with ⟨kval, hkle⟩
  have hval : kval = j.val + 1 := hjk.symm
  subst kval
  apply Path.ext
  funext t
  simp only [Path.cast_coe]
  apply Subtype.ext
  apply Subtype.ext
  have hseam := congrArg (fun p => p t)
    (P.gluedSeamOneTurnLoop_map_eq_incomingRetainedPolarBoundaryLoop_symm j)
  change (P.gluedSeamOneTurnLoop j 1 t).1 =
    ((((circleOneTurnLoop 1).map
      (P.gluedIncomingRetainedPolarBoundaryMap (gluingChainEdgeRight j)).continuous).symm).cast
        (P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint j)
        (P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint j)) t
  exact hseam

set_option backward.isDefEq.respectTransparency false in
/-- The actual adjacent-component based equivalence sends the overlap's
positive turn to the inverse incoming polar class. -/
theorem gluedChainPrefixPeripheralRightGenerator
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
        (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
      (FundamentalGroup.mapOfEq
        (P.gluedChainPrefixOverlapRightInclusion k j)
        (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega))))) =
      ⟦(P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm⟧ := by
  let E := P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
    (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
  have hback : E.symm (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((((P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm).map
          (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk).continuous_toFun).map
            (P.gluedChainPrefixRightCoverSideInclusion k j).continuous)) :=
    P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv_symm_apply_loop k j hjk
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
      (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm
  have hclass :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega)).map
          (P.gluedChainPrefixOverlapRightInclusion k j).continuous).cast
            (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk).symm
            (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk).symm)) =
        E.symm (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm)) := by
    rw [hback]
    exact congrArg (fun p => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
      (P.gluedChainPrefixPeripheralRightPath k j hjk)
  rw [FundamentalGroup.mapOfEq_apply]
  change E (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega)).map
        (P.gluedChainPrefixOverlapRightInclusion k j).continuous).cast
          (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk).symm
          (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk).symm))) =
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm)
  calc
    _ = E (E.symm (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm))) :=
      congrArg E hclass
    _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm) :=
      E.apply_symm_apply _

/-- The canonical cyclic generator of the actual overlap, included into the
left cover side, is the previous prefix's outgoing positive class. -/
theorem gluedChainPrefixPeripheralLeftCanonicalGenerator
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixLeftCoverFundamentalGroupEquiv k j (by omega)
        (P.gluedChainPrefixRightPolarBoundaryMap j 1)
      (FundamentalGroup.mapOfEq
        (P.gluedChainPrefixOverlapLeftInclusion k j)
        (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk)
        ((P.gluedChainPrefixOverlapFreeEquiv k j (by omega) 1).symm
          (FreeGroup.of ()))) =
      ⟦P.gluedChainPrefixRightPolarBoundaryLoop j⟧ := by
  rw [P.gluedChainPrefixOverlapFreeEquiv_symm_of k j (by omega) 1]
  change P.gluedChainPrefixLeftCoverFundamentalGroupEquiv k j (by omega)
      (P.gluedChainPrefixRightPolarBoundaryMap j 1)
      (FundamentalGroup.mapOfEq
        (P.gluedChainPrefixOverlapLeftInclusion k j)
        (P.gluedChainPrefixPeripheralLeftBasepoint_explicit k j hjk)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega))))) = _
  exact P.gluedChainPrefixPeripheralLeftGenerator k j hjk

/-- The same canonical overlap generator, included into the right side, is
the inverse incoming class of the next retained component. -/
theorem gluedChainPrefixPeripheralRightCanonicalGenerator
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
        (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
      (FundamentalGroup.mapOfEq
        (P.gluedChainPrefixOverlapRightInclusion k j)
        (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk)
        ((P.gluedChainPrefixOverlapFreeEquiv k j (by omega) 1).symm
          (FreeGroup.of ()))) =
      ⟦(P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k)).symm⟧ := by
  rw [P.gluedChainPrefixOverlapFreeEquiv_symm_of k j (by omega) 1]
  change P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
      (FundamentalGroup.mapOfEq
        (P.gluedChainPrefixOverlapRightInclusion k j)
        (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.gluedChainPrefixPeripheralOverlapOneTurnPath k j (by omega))))) = _
  exact P.gluedChainPrefixPeripheralRightGenerator k j hjk

#print axioms gluedChainPrefixPeripheralLeftBasepoint
#print axioms gluedChainPrefixPeripheralRightBasepoint
#print axioms gluedChainPrefixPeripheralLeftPath
#print axioms gluedChainPrefixPeripheralLeftGenerator
#print axioms gluedChainPrefixPeripheralRightPath
#print axioms gluedChainPrefixPeripheralRightGenerator
#print axioms gluedChainPrefixPeripheralLeftCanonicalGenerator
#print axioms gluedChainPrefixPeripheralRightCanonicalGenerator

end

end ExerciseGluingPreparation
