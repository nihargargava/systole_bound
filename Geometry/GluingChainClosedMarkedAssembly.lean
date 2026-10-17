module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ExerciseGeometryFoundation
public import Geometry.GluingChainVanKampenEquiv
public import Geometry.SurfaceRelatorConcatenation
public import Geometry.FundamentalGroupPointEquality

@[expose] public section

/-!
# Close the native marked chain at its last endpoint

The final seam is the actual overlap of the original retained prefix and
last retained component. Its positive turn is outgoing on the prefix and
inverse incoming on the endpoint. A genuine marking of that prefix therefore
closes to the standard surface group with the sum genus. The prefix marking
is an intermediate induction input, not an assumed final geometric input.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The original seam group is cyclic on its actual positive turn. -/
def gluedChainClosedOverlapFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    FundamentalGroup ↥(P.gluedMk '' P.seamNeighborhood k)
      (P.gluedSeamCircleInclusion k 1) ≃* FreeGroup Unit :=
  (P.gluedSeamCircleFundamentalGroupEquiv k 1).trans
    (circleFundamentalGroupFreeEquiv 1)

theorem gluedChainClosedOverlapFreeEquiv_oneTurn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainClosedOverlapFreeEquiv k ⟦P.gluedSeamOneTurnLoop k 1⟧ =
      FreeGroup.of () := by
  change circleFundamentalGroupFreeEquiv 1
    (P.gluedSeamCircleFundamentalGroupEquiv k 1
      ⟦(circleOneTurnLoop 1).map (P.gluedSeamCircleInclusion k).continuous⟧) = _
  rw [P.gluedSeamCircleFundamentalGroupEquiv_map_loop,
    circleFundamentalGroupFreeEquiv_oneTurn]

theorem gluedChainClosedOverlapFreeEquiv_symm_of
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    (P.gluedChainClosedOverlapFreeEquiv k).symm (FreeGroup.of ()) =
      ⟦P.gluedSeamOneTurnLoop k 1⟧ := by
  rw [← P.gluedChainClosedOverlapFreeEquiv_oneTurn k]
  exact (P.gluedChainClosedOverlapFreeEquiv k).symm_apply_apply _

/-- **Math.** The seam point is the unchanged prefix outgoing basepoint in its collar. -/
theorem gluedChainClosedPeripheralLeftBasepoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainCoverOverlapInclusion k true (P.gluedSeamCircleInclusion k 1) =
      P.gluedChainPrefixInclusion k (P.gluedChainPrefixRightPolarBoundaryMap k 1) := by
  apply Subtype.ext
  exact (P.gluedChainPrefixRightPolarBoundaryMap_val_eq_seam k 1).symm

/-- **Math.** On the other side it is the actual positive incoming suffix basepoint. -/
theorem gluedChainClosedPeripheralRightBasepoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainCoverOverlapInclusion k false (P.gluedSeamCircleInclusion k 1) =
      P.gluedChainSuffixInclusion k (P.gluedChainSuffixLeftPolarBoundaryMap k 1) := by
  apply Subtype.ext
  exact P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint k

/-- **Math.** The literal overlap path, viewed on the left, is the included outgoing
prefix loop; the only adjustment is the proved endpoint equality. -/
theorem gluedChainClosedPeripheralLeftPath
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ((P.gluedSeamOneTurnLoop k 1).map
      (P.gluedChainCoverOverlapInclusion k true).continuous).cast
        (P.gluedChainClosedPeripheralLeftBasepoint k).symm
        (P.gluedChainClosedPeripheralLeftBasepoint k).symm =
      (P.gluedChainPrefixRightPolarBoundaryLoop k).map
        (P.gluedChainPrefixInclusion k).continuous := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact (P.gluedChainPrefixRightPolarBoundaryMap_val_eq_seam k
    (circleOneTurnLoop 1 t)).symm

/-- **Math.** Reflection across the original seam turns its positive loop into the
inverse incoming suffix loop, with no newly chosen boundary parametrization. -/
theorem gluedChainClosedPeripheralRightPath
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    ((P.gluedSeamOneTurnLoop k 1).map
      (P.gluedChainCoverOverlapInclusion k false).continuous).cast
        (P.gluedChainClosedPeripheralRightBasepoint k).symm
        (P.gluedChainClosedPeripheralRightBasepoint k).symm =
      (P.gluedChainSuffixLeftPolarBoundaryLoop k).symm.map
        (P.gluedChainSuffixInclusion k).continuous := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact congrArg (fun p => p t)
    (P.gluedSeamOneTurnLoop_map_eq_incomingRetainedPolarBoundaryLoop_symm k)

/-- **Math.** The actual left-side group map reads the seam as the positive outgoing
prefix class. -/
theorem gluedChainClosedPeripheralLeftGenerator
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainPrefixFundamentalGroupEquiv k
        (P.gluedChainPrefixRightPolarBoundaryMap k 1)
      (FundamentalGroup.mapOfEq (P.gluedChainCoverOverlapInclusion k true)
        (P.gluedChainClosedPeripheralLeftBasepoint k)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.gluedSeamOneTurnLoop k 1)))) =
      ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ := by
  let E := P.gluedChainPrefixFundamentalGroupEquiv k
    (P.gluedChainPrefixRightPolarBoundaryMap k 1)
  have hclass :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((P.gluedSeamOneTurnLoop k 1).map
          (P.gluedChainCoverOverlapInclusion k true).continuous).cast
            (P.gluedChainClosedPeripheralLeftBasepoint k).symm
            (P.gluedChainClosedPeripheralLeftBasepoint k).symm)) =
        E.symm ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ := by
    rw [P.gluedChainPrefixFundamentalGroupEquiv_symm_apply_loop]
    exact congrArg (fun p => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
      (P.gluedChainClosedPeripheralLeftPath k)
  rw [FundamentalGroup.mapOfEq_apply]
  change E (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((P.gluedSeamOneTurnLoop k 1).map
        (P.gluedChainCoverOverlapInclusion k true).continuous).cast
          (P.gluedChainClosedPeripheralLeftBasepoint k).symm
          (P.gluedChainClosedPeripheralLeftBasepoint k).symm))) = _
  exact (congrArg E hclass).trans (E.apply_symm_apply _)

/-- **Math.** The actual right-side group map reads that same seam as the inverse
positive incoming suffix class. -/
theorem gluedChainClosedPeripheralRightGenerator
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) :
    P.gluedChainSuffixFundamentalGroupEquiv k
        (P.gluedChainSuffixLeftPolarBoundaryMap k 1)
      (FundamentalGroup.mapOfEq (P.gluedChainCoverOverlapInclusion k false)
        (P.gluedChainClosedPeripheralRightBasepoint k)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.gluedSeamOneTurnLoop k 1)))) =
      ⟦(P.gluedChainSuffixLeftPolarBoundaryLoop k).symm⟧ := by
  let E := P.gluedChainSuffixFundamentalGroupEquiv k
    (P.gluedChainSuffixLeftPolarBoundaryMap k 1)
  have hclass :
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (((P.gluedSeamOneTurnLoop k 1).map
          (P.gluedChainCoverOverlapInclusion k false).continuous).cast
            (P.gluedChainClosedPeripheralRightBasepoint k).symm
            (P.gluedChainClosedPeripheralRightBasepoint k).symm)) =
        E.symm ⟦(P.gluedChainSuffixLeftPolarBoundaryLoop k).symm⟧ := by
    rw [P.gluedChainSuffixFundamentalGroupEquiv_symm_apply_loop]
    exact congrArg (fun p => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
      (P.gluedChainClosedPeripheralRightPath k)
  rw [FundamentalGroup.mapOfEq_apply]
  change E (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (((P.gluedSeamOneTurnLoop k 1).map
        (P.gluedChainCoverOverlapInclusion k false).continuous).cast
          (P.gluedChainClosedPeripheralRightBasepoint k).symm
          (P.gluedChainClosedPeripheralRightBasepoint k).symm))) = _
  exact (congrArg E hclass).trans (E.apply_symm_apply _)

/-- **Math.** Two actual inverse-relator peripheral markings identify the canonical
native full-chain amalgam with the standard closed surface group. -/
def gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (prefixGenus suffixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix k)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eLast : FundamentalGroup ↥(P.gluedChainSuffix k)
      (P.gluedChainSuffixLeftPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator suffixGenus))
    (hLast : eLast ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧ =
      (surfaceRelator suffixGenus)⁻¹) :
    FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k 1).val ≃*
      SurfaceGroup (prefixGenus + suffixGenus) := by
  let φ := P.gluedChainCoverOverlapGroupMap k 1
  let ψ := surfaceClosedPeripheralBaseMap
    (surfaceRelator prefixGenus) (surfaceRelator suffixGenus)
  let eH := P.gluedChainClosedOverlapFreeEquiv k
  let eG : ∀ b : Bool,
      P.gluedChainCoverSideGroup k 1 b ≃*
        surfaceClosedPeripheralFactor (SurfaceGenerator prefixGenus)
          (SurfaceGenerator suffixGenus) b := by
    intro b
    cases b
    · exact (fundamentalGroupBasepointEquivOfEq
        (P.gluedChainClosedPeripheralRightBasepoint k)).trans
          ((P.gluedChainSuffixFundamentalGroupEquiv k
            (P.gluedChainSuffixLeftPolarBoundaryMap k 1)).trans eLast)
    · exact (fundamentalGroupBasepointEquivOfEq
        (P.gluedChainClosedPeripheralLeftBasepoint k)).trans
          ((P.gluedChainPrefixFundamentalGroupEquiv k
            (P.gluedChainPrefixRightPolarBoundaryMap k 1)).trans ePrev)
  have hcompatible : ∀ b : Bool,
      eG b (φ b (eH.symm (FreeGroup.of ()))) = ψ b (FreeGroup.of ()) := by
    intro b
    have hseam := P.gluedChainClosedOverlapFreeEquiv_symm_of k
    cases b
    · change eLast ((P.gluedChainSuffixFundamentalGroupEquiv k
        (P.gluedChainSuffixLeftPolarBoundaryMap k 1))
        (fundamentalGroupBasepointEquivOfEq
          (P.gluedChainClosedPeripheralRightBasepoint k)
          (FundamentalGroup.map (P.gluedChainCoverOverlapInclusion k false)
            (P.gluedSeamCircleInclusion k 1)
            ((P.gluedChainClosedOverlapFreeEquiv k).symm (FreeGroup.of ()))))) = _
      rw [hseam, fundamentalGroupBasepointEquivOfEq_apply_map]
      calc
        _ = eLast ⟦(P.gluedChainSuffixLeftPolarBoundaryLoop k).symm⟧ :=
          congrArg eLast (P.gluedChainClosedPeripheralRightGenerator k)
        _ = (ψ false) (FreeGroup.of ()) := by
          change eLast ((⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧)⁻¹) = _
          rw [map_inv, hLast, inv_inv]
          simp only [ψ, surfaceClosedPeripheralBaseMap, FreeGroup.lift_apply_of]
    · change ePrev ((P.gluedChainPrefixFundamentalGroupEquiv k
        (P.gluedChainPrefixRightPolarBoundaryMap k 1))
        (fundamentalGroupBasepointEquivOfEq
          (P.gluedChainClosedPeripheralLeftBasepoint k)
          (FundamentalGroup.map (P.gluedChainCoverOverlapInclusion k true)
            (P.gluedSeamCircleInclusion k 1)
            ((P.gluedChainClosedOverlapFreeEquiv k).symm (FreeGroup.of ()))))) = _
      rw [hseam, fundamentalGroupBasepointEquivOfEq_apply_map]
      exact (congrArg ePrev (P.gluedChainClosedPeripheralLeftGenerator k)).trans
        (by simpa only [ψ, surfaceClosedPeripheralBaseMap, FreeGroup.lift_apply_of]
          using hPrev)
  exact (P.gluedChainCoverFundamentalGroupEquiv k 1).symm.trans
    ((groupAmalgamDiagramEquiv φ ψ eH eG
      (groupAmalgamDiagram_compatible_of_freeUnit φ ψ eH eG hcompatible)).trans
        (surfaceClosedPeripheralSurfaceGroupEquiv prefixGenus suffixGenus))

/-- **Math.** The closed-chain marking retains the literal inclusion of the
prefix collar factor and its prescribed inverse-relator marking. -/
theorem gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking_left
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (prefixGenus suffixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix k)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eLast : FundamentalGroup ↥(P.gluedChainSuffix k)
      (P.gluedChainSuffixLeftPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator suffixGenus))
    (hLast : eLast ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧ =
      (surfaceRelator suffixGenus)⁻¹)
    (γ : P.gluedChainCoverSideGroup k 1 true) :
    P.gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking k
      prefixGenus suffixGenus ePrev hPrev eLast hLast
        (P.gluedChainCoverSideGroupMap k 1 true γ) =
      surfaceClosedPeripheralSurfaceGroupEquiv prefixGenus suffixGenus
        (Monoid.PushoutI.of true
          (ePrev (P.gluedChainPrefixFundamentalGroupEquiv k
            (P.gluedChainPrefixRightPolarBoundaryMap k 1)
            (fundamentalGroupBasepointEquivOfEq
              (P.gluedChainClosedPeripheralLeftBasepoint k) γ)))) := by
  rw [← P.gluedChainCoverFundamentalGroupEquiv_of k 1 true γ]
  simp only [gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, groupAmalgamDiagramEquiv_of]

/-- **Math.** The closed-chain marking likewise retains the literal
endpoint collar inclusion and its inverse incoming polar convention. -/
theorem gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking_right
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (prefixGenus suffixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix k)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eLast : FundamentalGroup ↥(P.gluedChainSuffix k)
      (P.gluedChainSuffixLeftPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator suffixGenus))
    (hLast : eLast ⟦P.gluedChainSuffixLeftPolarBoundaryLoop k⟧ =
      (surfaceRelator suffixGenus)⁻¹)
    (γ : P.gluedChainCoverSideGroup k 1 false) :
    P.gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking k
      prefixGenus suffixGenus ePrev hPrev eLast hLast
        (P.gluedChainCoverSideGroupMap k 1 false γ) =
      surfaceClosedPeripheralSurfaceGroupEquiv prefixGenus suffixGenus
        (Monoid.PushoutI.of false
          (eLast (P.gluedChainSuffixFundamentalGroupEquiv k
            (P.gluedChainSuffixLeftPolarBoundaryMap k 1)
            (fundamentalGroupBasepointEquivOfEq
              (P.gluedChainClosedPeripheralRightBasepoint k) γ)))) := by
  rw [← P.gluedChainCoverFundamentalGroupEquiv_of k 1 false γ]
  simp only [gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, groupAmalgamDiagramEquiv_of]

/-- **Math.** Close the actual final endpoint using its already constructed native
inverse-relator marking; only the retained-prefix induction mark is supplied. -/
def gluedChainClosedMarkedSurfaceGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1))
    (hk : k.val + 2 = n) (prefixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix k)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
      (surfaceRelator prefixGenus)⁻¹) :
    FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k 1).val ≃*
      SurfaceGroup (prefixGenus + genera (gluingChainEdgeRight k)) :=
  P.gluedChainClosedMarkedSurfaceGroupEquivOfSuffixMarking k
    prefixGenus (genera (gluingChainEdgeRight k)) ePrev hPrev
    (Classical.choose (P.exists_lastRetainedSuffixPolarMarkedFreeEquiv k hk))
    (Classical.choose_spec (P.exists_lastRetainedSuffixPolarMarkedFreeEquiv k hk))

/-- **Math.** The original full glued chain has the sum-genus marking at
every native basepoint. Both the prefix and endpoint markings are constructed
internally, using the actual retained-piece induction and last-seam closure. -/
def gluedChainFullMarkedSurfaceGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (hn : 2 ≤ n)
    (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier) :
    FundamentalGroup P.GluedCarrier x ≃* SurfaceGroup g := by
  let k : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hk : k.val + 2 = n := by dsimp [k]; omega
  let ePrev := Classical.choose (P.exists_retainedPrefixPolarMarkedFreeEquiv k)
  have hPrev := Classical.choose_spec (P.exists_retainedPrefixPolarMarkedFreeEquiv k)
  let E := P.gluedChainClosedMarkedSurfaceGroupEquiv k hk
    (gluingChainPrefixGenus genera k) ePrev hPrev
  have hgenus : gluingChainPrefixGenus genera k + genera (gluingChainEdgeRight k) = g :=
    (gluingChainPrefixGenus_add_last genera k hk).trans hsum
  have E' : FundamentalGroup P.GluedCarrier (P.gluedSeamCircleInclusion k 1).val ≃*
      SurfaceGroup g := E.trans (MulEquiv.cast (M := SurfaceGroup) hgenus)
  letI : ConnectedSpace P.GluedCarrier :=
    { toPreconnectedSpace := P.gluedCarrierPreconnectedSpace
      toNonempty := ⟨x⟩ }
  letI : PathConnectedSpace P.GluedCarrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact (FundamentalGroup.fundamentalGroupMulEquivOfPath
    (PathConnectedSpace.somePath x (P.gluedSeamCircleInclusion k 1).val)).trans E'

#print axioms gluedChainFullMarkedSurfaceGroupEquiv
#print axioms gluedChainClosedMarkedSurfaceGroupEquiv

end
end SystolicGrowth.ExerciseGluingPreparation
