module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterNativeSidePaths
public import Geometry.SurfaceTwoCenterPolarCutTransport
public import Geometry.SurfaceTwoCenterPuncturedComponentCover

@[expose] public section

/-!
# Transfer of a marked local factor to the native carrier

The local annulus marking is transported first across the actual punctured
carrier equivalence and then along the literal left connector. The prescribed
cut, rather than a substitute connector, identifies the right peripheral loop.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups Topology unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)} {U : Set ℂ}

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** Transfer a marking of the actual local-disk ambient carrier, based at a
common endpoint of two literal local paths, to the native small-left polar
basepoint. The joined paths must represent the actual prescribed small cut;
the conclusion marks the right positive loop conjugated along that cut. -/
theorem exists_componentTwoCenterSmallPolarMarkedFreeEquiv_of_localMarkedLoops
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (r : ℝ) (hr1 : 1 < r)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (leftPath : Path
      (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1 hpMap hqMap
        true ρ hρ hρr hsmall 1) z)
    (rightPath : Path
      (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1 hpMap hqMap
        false ρ hρ hρr hsmall 1) z)
    (hL : P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1 =
      (P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap)
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
          (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1
            hpMap hqMap true ρ hρ hρr hsmall 1)))
    (hR : P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1 =
      (P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap)
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
          (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1
            hpMap hqMap false ρ hρ hρr hsmall 1)))
    (hjoined :
      (((leftPath.trans rightPath.symm).map
        (((P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap).comp
          (twoOpenCoverAmalgamInclusion
            (embeddedTwoPunctureLocalDiskRelativeSide f p q r))).continuous)).cast
          hL hR).Homotopic
        (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr))
    {G : Type*} [Group G]
    (eAmbient : FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q) z.1 ≃* G)
    (leftWord rightWord : G)
    (heL : eAmbient (FundamentalGroup.map
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)) z
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (leftPath.symm.trans
            (((circleOneTurnLoop 1).map
              (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1
                hpMap hqMap true ρ hρ hρr hsmall).continuous).trans leftPath))))) =
      leftWord)
    (heR : eAmbient (FundamentalGroup.map
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)) z
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (rightPath.symm.trans
            (((circleOneTurnLoop 1).map
              (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1
                hpMap hqMap false ρ hρ hρr hsmall).continuous).trans rightPath))))) =
      rightWord) :
    ∃ eSmall : FundamentalGroup (P.CenterPuncturedChainComponent i)
        (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1) ≃* G,
      eSmall (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr))) = leftWord ∧
      eSmall (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) = rightWord := by
  let L := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1 hpMap hqMap
    true ρ hρ hρr hsmall
  let R := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r hr1 hpMap hqMap
    false ρ hρ hρr hsmall
  let localInclusion := twoOpenCoverAmalgamInclusion
    (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
  let F : C({w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r},
      P.CenterPuncturedChainComponent i) :=
    (P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap).comp localInclusion
  let H := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hpMap hqMap
  let E := fundamentalGroupHomeomorphEquiv H.symm z.1
  have hbase : F z = H.symm z.1 := by
    apply Subtype.ext
    rfl
  let pNative : Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (H.symm z.1) :=
    ((leftPath.map F.continuous).cast
      (by simpa [F, localInclusion] using hL) hbase)
  let qNative : Path (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1)
      (H.symm z.1) :=
    ((rightPath.map F.continuous).cast
      (by simpa [F, localInclusion] using hR) hbase)
  let T := FundamentalGroup.fundamentalGroupMulEquivOfPath pNative
  let eSmall := T.trans (E.symm.trans eAmbient)
  let localLeftTurn : Path (L 1) (L 1) :=
    (circleOneTurnLoop 1).map L.continuous
  let localRightTurn : Path (R 1) (R 1) :=
    (circleOneTurnLoop 1).map R.continuous
  let localLeftConjugate : Path z z :=
    leftPath.symm.trans (localLeftTurn.trans leftPath)
  let localRightConjugate : Path z z :=
    rightPath.symm.trans (localRightTurn.trans rightPath)
  let cut := P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr
  let nativeLeftTurn := P.componentTwoCenterSmallPolarBoundaryLoop i true ρ hρ hρr
  let nativeRightTurn := P.componentTwoCenterSmallPolarBoundaryLoop i false ρ hρ hρr
  have hleftTurn : (localLeftTurn.map F.continuous).cast
      (by simpa [F, localInclusion] using hL)
      (by simpa [F, localInclusion] using hL) = nativeLeftTurn := by
    dsimp [localLeftTurn, L, F, localInclusion, nativeLeftTurn,
      componentTwoCenterSmallPolarBoundaryLoop]
    exact P.twoCenterSmallPolarRelativeLocalDisk_oneTurn_map
      i f p q r hr1 hpMap hqMap true ρ hρ hρr hsmall
  have hrightTurn : (localRightTurn.map F.continuous).cast
      (by simpa [F, localInclusion] using hR)
      (by simpa [F, localInclusion] using hR) = nativeRightTurn := by
    dsimp [localRightTurn, R, F, localInclusion, nativeRightTurn,
      componentTwoCenterSmallPolarBoundaryLoop]
    exact P.twoCenterSmallPolarRelativeLocalDisk_oneTurn_map
      i f p q r hr1 hpMap hqMap false ρ hρ hρr hsmall
  have hcutPath : cut.Homotopic
      (pNative.trans qNative.symm) := by
    have hpaths : pNative.trans qNative.symm =
        ((leftPath.trans rightPath.symm).map F.continuous).cast hL hR := by
      apply Path.ext
      funext t
      simp [pNative, qNative, Path.map_coe,
        Path.trans_apply, Function.comp_apply]
    rw [hpaths]
    exact hjoined.symm
  have hleftTransport :
      T (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk nativeLeftTurn)) =
        FundamentalGroup.map F z
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk localLeftConjugate)) := by
    rw [← hleftTurn]
    exact fundamentalGroupMulEquivOfPath_map_conjugate_loop_cast
      F hL leftPath localLeftTurn
  have hrightTransport :
      T (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
        (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) =
        FundamentalGroup.map F z
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk localRightConjugate)) := by
    have hTcut :
        T (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (qNative.symm.trans (nativeRightTurn.trans qNative))) := by
      have hgeneric :
          T (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (pNative.symm.trans
              ((P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr).trans
                pNative))) := by
        change FundamentalGroup.fundamentalGroupMulEquivOfPath pNative
            ⟦P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr⟧ = _
        exact fundamentalGroupMulEquivOfPath_apply_generic pNative _
      have hassoc : FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            (pNative.symm.trans
              ((P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr).trans
                pNative))) =
          FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk
              (pNative.symm.trans
                (cut.trans ((nativeRightTurn.trans cut.symm).trans pNative)))) := by
        apply congrArg FundamentalGroup.fromPath
        simp only [componentRightSmallPolarBoundaryLoopAlongCut, cut,
          nativeRightTurn, Path.Homotopic.Quotient.mk_trans,
          Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.trans_assoc]
      exact hgeneric.trans (hassoc.trans
        (fundamentalGroup_conjugateCut_eq_of_homotopic
          pNative qNative cut nativeRightTurn hcutPath))
    have hrightViaPath :
        FundamentalGroup.fundamentalGroupMulEquivOfPath qNative
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk nativeRightTurn)) =
        FundamentalGroup.map F z
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk localRightConjugate)) := by
      rw [← hrightTurn]
      exact fundamentalGroupMulEquivOfPath_map_conjugate_loop_cast
        F hR rightPath localRightTurn
    calc
      _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (qNative.symm.trans (nativeRightTurn.trans qNative))) := hTcut
      _ = FundamentalGroup.fundamentalGroupMulEquivOfPath qNative
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk nativeRightTurn)) := by
            change Path.Homotopic.Quotient.mk
                (qNative.symm.trans (nativeRightTurn.trans qNative)) =
              FundamentalGroup.fundamentalGroupMulEquivOfPath qNative
                ⟦nativeRightTurn⟧
            exact (fundamentalGroupMulEquivOfPath_apply_generic
              qNative nativeRightTurn).symm
      _ = _ := hrightViaPath
  have hEleft : E
      (FundamentalGroup.map localInclusion z
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk localLeftConjugate))) =
      T (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk nativeLeftTurn)) := by
    calc
      _ = FundamentalGroup.map F z
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk localLeftConjugate)) := by
            exact P.internalCenterPuncturedAmbientInverseEquiv_localLoop
              i f p q hi hnext hpMap hqMap r z localLeftConjugate
      _ = _ := hleftTransport.symm
  have hEright : E
      (FundamentalGroup.map localInclusion z
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk localRightConjugate))) =
      T (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))) := by
    calc
      _ = FundamentalGroup.map F z
          (FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk localRightConjugate)) := by
            exact P.internalCenterPuncturedAmbientInverseEquiv_localLoop
              i f p q hi hnext hpMap hqMap r z localRightConjugate
      _ = _ := hrightTransport.symm
  refine ⟨eSmall, ?_, ?_⟩
  · change eAmbient (E.symm
      (T (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk nativeLeftTurn)))) = leftWord
    rw [← hEleft, E.symm_apply_apply, heL]
  · change eAmbient (E.symm
      (T (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (P.componentRightSmallPolarBoundaryLoopAlongCut i ρ hρ hρr))))) = rightWord
    rw [← hEright, E.symm_apply_apply, heR]

end
end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterSmallPolarMarkedFreeEquiv_of_localMarkedLoops
