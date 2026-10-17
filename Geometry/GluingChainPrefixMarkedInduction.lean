module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Geometry.FundamentalGroupPointEquality
public import Geometry.GluingChainPrefixPolarBoundary
public import Geometry.GluingChainPrefixSeamPeripheral
public import Geometry.SurfaceRelatorConcatenation
public import Geometry.SurfaceTwoBoundaryCyclicAmalgam
public import Geometry.SurfaceRetainedPolarBoundary

@[expose] public section

/-!
# Marked genus induction for native retained prefixes

This file assembles the actual retained-prefix Van Kampen diagram with the
ordered peripheral marking of each original component. The successor step
keeps the actual cut as its basepoint-transport path.
-/

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem fundamentalGroupMulEquivOfPath_symm_apply_conjugate
    {Y : Type*} [TopologicalSpace Y] {x y : Y}
    (p : Path x y) (q : Path y y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (p.trans (q.trans p.symm))) := by
  simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath,
    CategoryTheory.Iso.conj, CategoryTheory.Iso.homCongr,
    CategoryTheory.Groupoid.isoEquivHom]
  change (Path.Homotopic.Quotient.mk p).trans
      ((Path.Homotopic.Quotient.mk q).trans
        (Path.Homotopic.Quotient.mk p).symm) =
    Path.Homotopic.Quotient.mk (p.trans (q.trans p.symm))
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroup_mapOfEq_id_comp_map
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) :
    (FundamentalGroup.mapOfEq (ContinuousMap.id Y) h).comp
      (FundamentalGroup.map f x) = FundamentalGroup.mapOfEq f h := by
  have h' : (ContinuousMap.id Y) (f x) = y := by simpa using h
  ext γ
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  change FundamentalGroup.mapOfEq (ContinuousMap.id Y) h
      (FundamentalGroup.map f x ⟦p⟧) = FundamentalGroup.mapOfEq f h ⟦p⟧
  rw [FundamentalGroup.map_apply, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  have hmapId (q : Path.Homotopic.Quotient (f x) (f x)) :
      q.map (ContinuousMap.id Y) = q := by
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
    rfl
  change ((Path.Homotopic.Quotient.mk (p.map f.continuous)).map
      (ContinuousMap.id Y)).cast h'.symm h'.symm =
    (Path.Homotopic.Quotient.mk (p.map f.continuous)).cast h.symm h.symm
  rw [hmapId]

theorem quotient_mk_cut_conjugate_cast
    {Y : Type*} [TopologicalSpace Y] {x y x' : Y}
    (p : Path x y) (q : Path y y) (h : x' = x) :
    Path.Homotopic.Quotient.mk ((p.cast h rfl).trans
      (q.trans (p.cast h rfl).symm)) =
    (Path.Homotopic.Quotient.mk (p.trans (q.trans p.symm))).cast h h := by
  cases h
  rfl

theorem pathQuotient_map_trans
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y z : X} (p : Path.Homotopic.Quotient x y)
    (q : Path.Homotopic.Quotient y z) (f : C(X, Y)) :
    (p.trans q).map f = (p.map f).trans (q.map f) := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  exact congrArg Quotient.mk'' (p.map_trans q f.continuous)

theorem pathQuotient_map_symm
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (p : Path.Homotopic.Quotient x y) (f : C(X, Y)) :
    p.symm.map f = (p.map f).symm := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
  exact congrArg Quotient.mk'' (p.map_symm f.continuous)

/-- The seam point is exactly the incoming boundary point of the next
component when viewed in the retained prefix. -/
theorem gluedChainPrefixSuccessorCutPath_start
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    P.gluedChainPrefixSeamCircleMap k j (by omega) 1 =
      P.gluedChainPrefixLastComponentInclusion k
        (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1) := by
  let i := gluingChainEdgeLeft k
  have hedge : gluingChainEdgeRight j = i := by
    apply Fin.ext
    simp only [gluingChainEdgeRight]
    exact hjk
  apply Subtype.ext
  change (P.gluedSeamCircleInclusion j 1).1 = _
  rw [P.gluedSeamCircleInclusion_one_eq_incomingRetainedBasepoint j, hedge]
  rfl

/-- The literal cut inside the new component gives the based path from the
old seam point to the new outgoing boundary point in the retained prefix. -/
def gluedChainPrefixSuccessorCutPath
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    Path (P.gluedChainPrefixSeamCircleMap k j (by omega) 1)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) :=
  ((P.componentRetainedTwoCenterCutBasedPath (gluingChainEdgeLeft k)).map
    (P.gluedChainPrefixLastComponentInclusion k).continuous).cast
      (P.gluedChainPrefixSuccessorCutPath_start k j hjk) rfl

/-- Rebasing the new outgoing loop back along the native prefix cut is the
literal cut-conjugated component loop. -/
theorem gluedChainPrefixSuccessorCutPath_conjugates_boundary
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val) :
    Path.Homotopic.Quotient.mk
        ((P.gluedChainPrefixSuccessorCutPath k j hjk).trans
          ((P.gluedChainPrefixRightPolarBoundaryLoop k).trans
            (P.gluedChainPrefixSuccessorCutPath k j hjk).symm)) =
      (Path.Homotopic.Quotient.mk
        ((P.componentRetainedRightPolarBoundaryLoopAlongCut
          (gluingChainEdgeLeft k)).map
            (P.gluedChainPrefixLastComponentInclusion k).continuous)).cast
              (P.gluedChainPrefixSuccessorCutPath_start k j hjk)
              (P.gluedChainPrefixSuccessorCutPath_start k j hjk) := by
  rw [P.gluedChainPrefixRightPolarBoundaryLoop_eq_map]
  let inc := P.gluedChainPrefixLastComponentInclusion k
  change Path.Homotopic.Quotient.mk
      (((P.componentRetainedTwoCenterCutBasedPath
        (gluingChainEdgeLeft k)).map inc.continuous).cast
          (P.gluedChainPrefixSuccessorCutPath_start k j hjk) rfl |>.trans
        (((P.componentRetainedRightPolarBoundaryLoop
          (gluingChainEdgeLeft k)).map inc.continuous).trans
          (((P.componentRetainedTwoCenterCutBasedPath
            (gluingChainEdgeLeft k)).map inc.continuous).cast
              (P.gluedChainPrefixSuccessorCutPath_start k j hjk) rfl).symm)) = _
  rw [quotient_mk_cut_conjugate_cast]
  congr 1
  simp only [Path.Homotopic.Quotient.mk_map,
    Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm,
    componentRetainedRightPolarBoundaryLoopAlongCut]
  rw [pathQuotient_map_trans, pathQuotient_map_trans]
  rw [← pathQuotient_map_symm]

set_option backward.isDefEq.respectTransparency false in
/-- The native seam amalgam inherits the old-prefix and new-component
markings, yielding the freely generated prefix mark before transporting its
basepoint along the actual retained cut. -/
def gluedChainPrefixSuccessorSeamMarkedFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (prefixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix j)
      (P.gluedChainPrefixRightPolarBoundaryMap j 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop j⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eComp : FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k))
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1) ≃*
        FreeGroup (SurfaceGenerator (genera (gluingChainEdgeLeft k)) ⊕ Unit))
    (hIncoming : eComp ⟦P.componentRetainedLeftPolarBoundaryLoop
        (gluingChainEdgeLeft k)⟧ = FreeGroup.of (Sum.inr ())) :
    FundamentalGroup ↥(P.gluedChainPrefix k)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) 1).val ≃*
      FreeGroup (SurfaceGenerator
        (prefixGenus + genera (gluingChainEdgeLeft k))) := by
  let U := P.gluedChainPrefixCoverSide k j true
  let V := P.gluedChainPrefixCoverSide k j false
  let q := P.gluedChainPrefixSeamBasepoint k j (by omega) 1
  let φ := twoOpenCoverAmalgamSideMap U V q
  letI : ∀ b : Bool, Group (twoOpenCoverAmalgamSideGroup U V q b) :=
    fun b => twoOpenCoverAmalgamSideGroup_group U V q b
  let ψ := surfacePrefixPeripheralBaseMap
    (B := SurfaceGenerator (genera (gluingChainEdgeLeft k)))
    (surfaceRelator prefixGenus)
  let eH := P.gluedChainPrefixOverlapFreeEquiv k j (by omega) 1
  have hLeftBase : twoOpenCoverAmalgamOverlapLeft U V q =
      P.gluedChainPrefixLeftCoverBasepoint k j (by omega)
        (P.gluedChainPrefixRightPolarBoundaryMap j 1) := by
    exact P.gluedChainPrefixPeripheralLeftBasepoint k j hjk
  have hRightBase : twoOpenCoverAmalgamOverlapRight U V q =
      P.gluedChainPrefixRightCoverSideInclusion k j
        (P.gluedChainPrefixSuffixComponentHomeomorph k j hjk
          (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)) := by
    exact P.gluedChainPrefixPeripheralRightBasepoint k j hjk
  let eG : ∀ b : Bool,
      twoOpenCoverAmalgamSideGroup U V q b ≃*
        surfacePrefixPeripheralFactor (SurfaceGenerator prefixGenus)
          (SurfaceGenerator (genera (gluingChainEdgeLeft k))) b := by
    intro b
    cases b
    · exact (fundamentalGroupBasepointEquivOfEq hRightBase).trans
        ((P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv
          k j hjk (P.componentRetainedLeftPolarBoundaryMap
            (gluingChainEdgeLeft k) 1)).trans eComp)
    · exact (fundamentalGroupBasepointEquivOfEq hLeftBase).trans
        ((P.gluedChainPrefixLeftCoverFundamentalGroupEquiv
          k j (by omega) (P.gluedChainPrefixRightPolarBoundaryMap j 1)).trans ePrev)
  have hcompatible : ∀ b : Bool,
      eG b (φ b (eH.symm (FreeGroup.of ()))) = ψ b (FreeGroup.of ()) := by
    intro b
    cases b
    · change eComp ((P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv
        k j hjk (P.componentRetainedLeftPolarBoundaryMap
          (gluingChainEdgeLeft k) 1))
        (fundamentalGroupBasepointEquivOfEq hRightBase
          (FundamentalGroup.map (P.gluedChainPrefixOverlapRightInclusion k j)
            q (eH.symm (FreeGroup.of ()))))) = _
      erw [fundamentalGroupBasepointEquivOfEq_apply_map]
      erw [P.gluedChainPrefixPeripheralRightCanonicalGenerator k j hjk]
      change eComp
        ((FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (P.componentRetainedLeftPolarBoundaryLoop (gluingChainEdgeLeft k))))⁻¹) = _
      simp only [map_inv, ψ, surfacePrefixPeripheralBaseMap,
        FreeGroup.lift_apply_of]
      exact congrArg Inv.inv hIncoming
    · change ePrev ((P.gluedChainPrefixLeftCoverFundamentalGroupEquiv
        k j (by omega) (P.gluedChainPrefixRightPolarBoundaryMap j 1))
        (fundamentalGroupBasepointEquivOfEq hLeftBase
          (FundamentalGroup.map (P.gluedChainPrefixOverlapLeftInclusion k j)
            q (eH.symm (FreeGroup.of ()))))) = _
      erw [fundamentalGroupBasepointEquivOfEq_apply_map]
      erw [P.gluedChainPrefixPeripheralLeftCanonicalGenerator k j hjk]
      simpa [ψ, surfacePrefixPeripheralBaseMap] using hPrev
  let d := groupAmalgamDiagramEquiv φ ψ eH eG
    (groupAmalgamDiagram_compatible_of_freeUnit φ ψ eH eG hcompatible)
  exact (P.gluedChainPrefixCoverFundamentalGroupEquiv k j hjk 1).symm.trans
    (d.trans (surfacePrefixPeripheralGenusEquiv
      prefixGenus (genera (gluingChainEdgeLeft k))))

set_option backward.isDefEq.respectTransparency false in
/-- The native right factor includes a component loop into the new prefix,
with exactly the equality cast from the seam to its incoming point. -/
theorem gluedChainPrefixSuccessorRightFactor_toAmbient
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (p : Path (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)) :
    twoOpenCoverSideToAmbient
      (P.gluedChainPrefixCoverSide k j true)
      (P.gluedChainPrefixCoverSide k j false)
      (P.gluedChainPrefixSeamBasepoint k j (by omega) 1) false
      ((fundamentalGroupBasepointEquivOfEq
        (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk)).symm
        ((P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
          (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)).symm
            ⟦p⟧)) =
      ⟦(p.map (P.gluedChainPrefixLastComponentInclusion k).continuous).cast
        (P.gluedChainPrefixSuccessorCutPath_start k j hjk)
        (P.gluedChainPrefixSuccessorCutPath_start k j hjk)⟧ := by
  erw [P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv_symm_apply_loop,
    fundamentalGroupBasepointEquivOfEq_symm_apply_loop]
  change FundamentalGroup.map
    (twoOpenCoverAmalgamInclusion (P.gluedChainPrefixCoverSide k j false))
    (twoOpenCoverAmalgamOverlapRight _ _ _)
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _)) = _
  erw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The seam marking preserves the actual included right component factor. -/
theorem gluedChainPrefixSuccessorSeamMarkedFreeEquiv_rightFactor
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (prefixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix j)
      (P.gluedChainPrefixRightPolarBoundaryMap j 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop j⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eComp : FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k))
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1) ≃*
        FreeGroup (SurfaceGenerator (genera (gluingChainEdgeLeft k)) ⊕ Unit))
    (hIncoming : eComp ⟦P.componentRetainedLeftPolarBoundaryLoop
        (gluingChainEdgeLeft k)⟧ = FreeGroup.of (Sum.inr ()))
    (γ : FundamentalGroup ↥(P.gluedChainPrefixCoverSide k j false)
      (twoOpenCoverAmalgamOverlapRight
        (P.gluedChainPrefixCoverSide k j true)
        (P.gluedChainPrefixCoverSide k j false)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) 1))) :
    P.gluedChainPrefixSuccessorSeamMarkedFreeEquiv k j hjk prefixGenus
      ePrev hPrev eComp hIncoming
      (twoOpenCoverSideToAmbient
        (P.gluedChainPrefixCoverSide k j true)
        (P.gluedChainPrefixCoverSide k j false)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) 1) false γ) =
    surfacePrefixPeripheralGenusEquiv prefixGenus (genera (gluingChainEdgeLeft k))
      (Monoid.PushoutI.of false
        (eComp (P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
          (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)
          (fundamentalGroupBasepointEquivOfEq
            (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk) γ)))) := by
  unfold gluedChainPrefixSuccessorSeamMarkedFreeEquiv
  simp only [MulEquiv.trans_apply]
  erw [← P.gluedChainPrefixCoverFundamentalGroupEquiv_of k j hjk 1 false γ,
    MulEquiv.symm_apply_apply, groupAmalgamDiagramEquiv_of]

/-- Rebase the new prefix marking along the literal retained-component cut
to the outgoing boundary, so it is ready for the next attachment. -/
def gluedChainPrefixSuccessorMarkedFreeEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (prefixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix j)
      (P.gluedChainPrefixRightPolarBoundaryMap j 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop j⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eComp : FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k))
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1) ≃*
        FreeGroup (SurfaceGenerator (genera (gluingChainEdgeLeft k)) ⊕ Unit))
    (hIncoming : eComp ⟦P.componentRetainedLeftPolarBoundaryLoop
        (gluingChainEdgeLeft k)⟧ = FreeGroup.of (Sum.inr ())) :
    FundamentalGroup ↥(P.gluedChainPrefix k)
      (P.gluedChainPrefixRightPolarBoundaryMap k 1) ≃*
        FreeGroup (SurfaceGenerator
          (prefixGenus + genera (gluingChainEdgeLeft k))) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
    (P.gluedChainPrefixSuccessorCutPath k j hjk)).symm.trans
      (P.gluedChainPrefixSuccessorSeamMarkedFreeEquiv k j hjk prefixGenus
        ePrev hPrev eComp hIncoming)

set_option backward.isDefEq.respectTransparency false in
/-- The successor retains the exact inverse ordered relator at its outgoing
boundary. No genus of the eventual closed chain is assumed in this step. -/
theorem gluedChainPrefixSuccessorMarkedFreeEquiv_boundary
    (P : ExerciseGluingPreparation C g n genera X)
    (k j : Fin (n - 1)) (hjk : j.val + 1 = k.val)
    (prefixGenus : ℕ)
    (ePrev : FundamentalGroup ↥(P.gluedChainPrefix j)
      (P.gluedChainPrefixRightPolarBoundaryMap j 1) ≃*
        FreeGroup (SurfaceGenerator prefixGenus))
    (hPrev : ePrev ⟦P.gluedChainPrefixRightPolarBoundaryLoop j⟧ =
      (surfaceRelator prefixGenus)⁻¹)
    (eComp : FundamentalGroup (P.ChainComponent (gluingChainEdgeLeft k))
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1) ≃*
        FreeGroup (SurfaceGenerator (genera (gluingChainEdgeLeft k)) ⊕ Unit))
    (hIncoming : eComp ⟦P.componentRetainedLeftPolarBoundaryLoop
        (gluingChainEdgeLeft k)⟧ = FreeGroup.of (Sum.inr ()))
    (hOutgoing : eComp ⟦P.componentRetainedRightPolarBoundaryLoopAlongCut
        (gluingChainEdgeLeft k)⟧ =
      (FreeGroup.of (Sum.inr ()) * FreeGroup.map Sum.inl
        (surfaceRelator (genera (gluingChainEdgeLeft k))))⁻¹) :
    P.gluedChainPrefixSuccessorMarkedFreeEquiv k j hjk prefixGenus
        ePrev hPrev eComp hIncoming ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧ =
      (surfaceRelator (prefixGenus + genera (gluingChainEdgeLeft k)))⁻¹ := by
  change P.gluedChainPrefixSuccessorSeamMarkedFreeEquiv k j hjk prefixGenus
    ePrev hPrev eComp hIncoming
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath
      (P.gluedChainPrefixSuccessorCutPath k j hjk)).symm
      ⟦P.gluedChainPrefixRightPolarBoundaryLoop k⟧) = _
  erw [fundamentalGroupMulEquivOfPath_symm_apply_conjugate,
    P.gluedChainPrefixSuccessorCutPath_conjugates_boundary k j hjk,
    ← Path.Homotopic.Quotient.mk_cast]
  let p := P.componentRetainedRightPolarBoundaryLoopAlongCut (gluingChainEdgeLeft k)
  let E := P.gluedChainPrefixSuccessorSeamMarkedFreeEquiv k j hjk prefixGenus
    ePrev hPrev eComp hIncoming
  let γ := (fundamentalGroupBasepointEquivOfEq
    (P.gluedChainPrefixPeripheralRightBasepoint_explicit k j hjk)).symm
    ((P.gluedChainPrefixRightCoverComponentFundamentalGroupEquiv k j hjk
      (P.componentRetainedLeftPolarBoundaryMap (gluingChainEdgeLeft k) 1)).symm ⟦p⟧)
  have hfactor := P.gluedChainPrefixSuccessorSeamMarkedFreeEquiv_rightFactor
    k j hjk prefixGenus ePrev hPrev eComp hIncoming γ
  have hfactor' : E
      (twoOpenCoverSideToAmbient
        (P.gluedChainPrefixCoverSide k j true)
        (P.gluedChainPrefixCoverSide k j false)
        (P.gluedChainPrefixSeamBasepoint k j (by omega) 1) false γ) =
      surfacePrefixPeripheralGenusEquiv prefixGenus (genera (gluingChainEdgeLeft k))
        (Monoid.PushoutI.of false (eComp ⟦p⟧)) := by
    simpa only [γ, MulEquiv.apply_symm_apply] using hfactor
  refine (congrArg E
    (P.gluedChainPrefixSuccessorRightFactor_toAmbient k j hjk p).symm).trans
      (hfactor'.trans ?_)
  erw [hOutgoing]
  exact surfacePrefixPeripheralGenusEquiv_outgoing
    prefixGenus (genera (gluingChainEdgeLeft k))

#print axioms fundamentalGroupMulEquivOfPath_symm_apply_conjugate
#print axioms fundamentalGroup_mapOfEq_id_comp_map
#print axioms quotient_mk_cut_conjugate_cast
#print axioms pathQuotient_map_trans
#print axioms pathQuotient_map_symm
#print axioms gluedChainPrefixSuccessorCutPath
#print axioms gluedChainPrefixSuccessorCutPath_start
#print axioms gluedChainPrefixSuccessorCutPath_conjugates_boundary
#print axioms gluedChainPrefixSuccessorSeamMarkedFreeEquiv
#print axioms gluedChainPrefixSuccessorRightFactor_toAmbient
#print axioms gluedChainPrefixSuccessorSeamMarkedFreeEquiv_rightFactor
#print axioms gluedChainPrefixSuccessorMarkedFreeEquiv
#print axioms gluedChainPrefixSuccessorMarkedFreeEquiv_boundary

end
end ExerciseGluingPreparation
end SystolicGrowth
