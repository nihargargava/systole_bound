module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedTwoPunctureBoundaryWord
public import Geometry.SurfaceTwoBoundaryCyclicAmalgam

@[expose] public section

/-!
# Mark the actual disk/exterior amalgam

The actual annulus has one positive circle generator. Its exterior image is
the inverse marked handle word and its local image is the literal lower/upper
word. These two proved diagrams give the genuine cyclic-amalgam marking.
-/

open Set
open scoped ContinuousMap Topology

namespace SystolicGrowth

noncomputable section

variable {k : ℕ} {X : ClosedHyperbolicSurface k} {U : Set ℂ}

/-- The actual annulus angle whose normalized coordinate is the right
crossing used by the local two-generator marking. -/
def embeddedTwoPunctureMarkedAnnulusDirection
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (hpq : p ≠ q) (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) : Circle :=
  let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
    (zero_lt_one.trans hr1) hpq hpre hqre
  let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
    (zero_lt_one.trans hr1)
    (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1)
  twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2
    ((inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1)

section Diagram

variable (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
  (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
  (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
  (ha1 : a < 1) (hr1 : 1 < r)
  (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
  (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
  (hpq : p ≠ q) (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)

local notation "θR" => embeddedTwoPunctureMarkedAnnulusDirection p q a r ha ha1 hr1
  hpq hpre hqre
local notation "boundary" => embeddedTwoPunctureRelativeBoundaryCircle
  f hf p q a r ha ha1 hr1 haU hrU
local notation "zR" => boundary θR
local notation "exterior" => embeddedTwoPunctureExteriorRelativeSide f p q a haU
local notation "localDisk" => embeddedTwoPunctureLocalDiskRelativeSide f p q r

/-- The actual exterior and coordinate-local markings at one literal
annulus point. The exterior marking is the already constructed smaller
exterior marking, transported by its actual homeomorphism. -/
def embeddedTwoPunctureMarkedFactorEquiv {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (b : Bool) :
    twoOpenCoverAmalgamSideGroup exterior localDisk zR b ≃*
      surfaceTwoBoundaryCyclicFactor A b :=
  match b with
  | true => (embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU θR).trans eE
  | false => embeddedTwoPunctureRelativeLocalDiskFreeEquiv f hf p q r
      (zero_lt_one.trans hr1) hrU
      (((le_max_left _ _).trans_lt ha).trans (ha1.trans hr1))
      (((le_max_right _ _).trans_lt ha).trans (ha1.trans hr1))
      hpq hpre hqre (twoOpenCoverAmalgamOverlapRight exterior localDisk zR)
      (embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
        f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre)

/-- The actual positive annulus generator has the two correct factor
images. The local boundary word is proved from the native chart, not an
additional presentation premise. -/
theorem embeddedTwoPunctureMarkedFactorEquiv_generator {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) (b : Bool) :
    embeddedTwoPunctureMarkedFactorEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE b
      (twoOpenCoverAmalgamSideMap exterior localDisk zR b
        ((embeddedTwoPunctureRelativeOverlapFreeEquiv
          f hf p q a r ha ha1 hr1 haU hrU θR).symm (FreeGroup.of ()))) =
      surfaceTwoBoundaryCyclicBaseMap w b (FreeGroup.of ()) := by
  let turn : FundamentalGroup (↥(exterior ∩ localDisk)) zR :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      ((circleOneTurnLoop θR).map (boundary).continuous))
  have hturn : (embeddedTwoPunctureRelativeOverlapFreeEquiv
      f hf p q a r ha ha1 hr1 haU hrU θR).symm (FreeGroup.of ()) = turn :=
    embeddedTwoPunctureRelativeOverlapFreeEquiv_symm_of
      f hf p q a r ha ha1 hr1 haU hrU θR
  rw [hturn]
  cases b
  · dsimp only [embeddedTwoPunctureMarkedFactorEquiv, twoOpenCoverAmalgamSideMap,
      surfaceTwoBoundaryCyclicBaseMap]
    rw [FreeGroup.lift_apply_of]
    exact embeddedTwoPunctureRelativeBoundaryCircle_localDiskFreeWord
      f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre
  · dsimp only [embeddedTwoPunctureMarkedFactorEquiv, MulEquiv.trans_apply,
      twoOpenCoverAmalgamSideMap, surfaceTwoBoundaryCyclicBaseMap]
    rw [FreeGroup.lift_apply_of]
    have hleft : FundamentalGroup.map
        (twoOpenCoverAmalgamOverlapLeft exterior localDisk) zR turn =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (((circleOneTurnLoop θR).map (boundary).continuous).map
            (twoOpenCoverAmalgamOverlapLeft exterior localDisk).continuous)) := by
      change FundamentalGroup.map
        (twoOpenCoverAmalgamOverlapLeft exterior localDisk) zR
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk _)) = _
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    rw [hleft]
    exact (congrArg eE (embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv_oneTurn
      hball f hf p q a r ha ha1 hr1 haU hrU θR)).trans hE

/-- Literal based diagram compatibility, established on the genuine
positive generator of the actual cyclic overlap. -/
theorem embeddedTwoPunctureMarkedFactorEquiv_compatible {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) :
    ∀ b, (embeddedTwoPunctureMarkedFactorEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE b).toMonoidHom.comp
        (twoOpenCoverAmalgamSideMap exterior localDisk zR b) =
      (surfaceTwoBoundaryCyclicBaseMap w b).comp
        (embeddedTwoPunctureRelativeOverlapFreeEquiv
          f hf p q a r ha ha1 hr1 haU hrU θR).toMonoidHom := by
  apply groupAmalgamDiagram_compatible_of_freeUnit
  intro b
  exact embeddedTwoPunctureMarkedFactorEquiv_generator
    hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE b

/-- Mark the actual based disk/exterior amalgam by handles and the retained
lower puncture, through the literal annulus factor maps. -/
def embeddedTwoPunctureMarkedAmalgamEquiv {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) :
    embeddedTwoPunctureOpenCoverBasedAmalgam f p q a r haU zR ≃*
      FreeGroup (A ⊕ Unit) :=
  (groupAmalgamDiagramEquiv
    (twoOpenCoverAmalgamSideMap exterior localDisk zR)
    (surfaceTwoBoundaryCyclicBaseMap w)
    (embeddedTwoPunctureRelativeOverlapFreeEquiv
      f hf p q a r ha ha1 hr1 haU hrU θR)
    (embeddedTwoPunctureMarkedFactorEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE)
    (embeddedTwoPunctureMarkedFactorEquiv_compatible
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE)).trans
      (surfaceTwoBoundaryCyclicAmalgamEquiv w)

/-- The marked actual amalgam preserves every literal factor image before
the already proved cyclic elimination is applied. -/
theorem embeddedTwoPunctureMarkedAmalgamEquiv_of {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) (b : Bool) (ξ : twoOpenCoverAmalgamSideGroup exterior localDisk zR b) :
    embeddedTwoPunctureMarkedAmalgamEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE
      (Monoid.PushoutI.of b ξ) =
      surfaceTwoBoundaryCyclicAmalgamEquiv w
        (Monoid.PushoutI.of b (embeddedTwoPunctureMarkedFactorEquiv
          hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE b ξ)) := by
  simp only [embeddedTwoPunctureMarkedAmalgamEquiv, MulEquiv.trans_apply,
    groupAmalgamDiagramEquiv_of]

/-- The actual twice-punctured ambient surface inherits the marked free
presentation through its genuine embedded open-cover van Kampen map.
Dirichlet and connectivity witnesses are constructed from the original
surface, not supplied as new presentation hypotheses. -/
def embeddedTwoPunctureAmbientMarkedFreeEquiv {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) :
    FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q) zR.1 ≃*
      FreeGroup (A ⊕ Unit) := by
  let hrep := Quotient.exists_rep (embeddedCoordinatePunctureCenter hball f)
  let o := Classical.choose hrep
  have ho := Classical.choose_spec hrep
  have hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier) := ho.symm
  let V := embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv
    hball f hf p q a r ha ha1 hr1 haU hrU o hcenter (X.dirichletBoundarySegments o)
    hpre hqre hpq (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1) zR
  exact V.symm.trans (embeddedTwoPunctureMarkedAmalgamEquiv
    hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE)

/-- The ambient marking reads each actual included factor by its literal
factor marking and the proved cyclic elimination, without a new conjugator. -/
theorem embeddedTwoPunctureAmbientMarkedFreeEquiv_factor {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) (b : Bool) (ξ : twoOpenCoverAmalgamSideGroup exterior localDisk zR b) :
    embeddedTwoPunctureAmbientMarkedFreeEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE
      (twoOpenCoverSideToAmbient exterior localDisk zR b ξ) =
      surfaceTwoBoundaryCyclicAmalgamEquiv w
        (Monoid.PushoutI.of b (embeddedTwoPunctureMarkedFactorEquiv
          hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE b ξ)) := by
  let hrep := Quotient.exists_rep (embeddedCoordinatePunctureCenter hball f)
  let o := Classical.choose hrep
  have ho := Classical.choose_spec hrep
  have hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier) := ho.symm
  let V := embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv
    hball f hf p q a r ha ha1 hr1 haU hrU o hcenter (X.dirichletBoundarySegments o)
    hpre hqre hpq (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1) zR
  change embeddedTwoPunctureMarkedAmalgamEquiv
    hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE
      (V.symm (twoOpenCoverSideToAmbient exterior localDisk zR b ξ)) = _
  have hV : V (Monoid.PushoutI.of b ξ) =
      twoOpenCoverSideToAmbient exterior localDisk zR b ξ :=
    embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv_of
      hball f hf p q a r ha ha1 hr1 haU hrU o hcenter (X.dirichletBoundarySegments o)
      hpre hqre hpq (((le_max_left _ _).trans_lt ha).trans ha1)
      (((le_max_right _ _).trans_lt ha).trans ha1) zR b ξ
  rw [← hV, V.symm_apply_apply]
  exact embeddedTwoPunctureMarkedAmalgamEquiv_of
    hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE b ξ

/-- Retain the actual upper puncture instead of the lower one. This is the
same native van Kampen presentation with the proved alternate elimination. -/
def embeddedTwoPunctureAmbientMarkedUpperFreeEquiv {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) :
    FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q) zR.1 ≃*
      FreeGroup (A ⊕ Unit) :=
  (embeddedTwoPunctureAmbientMarkedFreeEquiv
    hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE).trans
      ((surfaceTwoBoundaryCyclicAmalgamEquiv w).symm.trans
        (surfaceTwoBoundaryCyclicUpperAmalgamEquiv w))

/-- The alternate elimination also preserves each actual factor map. -/
theorem embeddedTwoPunctureAmbientMarkedUpperFreeEquiv_factor {A : Type}
    (eE : FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θR) ≃*
        FreeGroup A) (w : FreeGroup A)
    (hE : eE ⟦(circleOneTurnLoop θR).map
      (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ =
        w⁻¹) (b : Bool) (ξ : twoOpenCoverAmalgamSideGroup exterior localDisk zR b) :
    embeddedTwoPunctureAmbientMarkedUpperFreeEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE w hE
      (twoOpenCoverSideToAmbient exterior localDisk zR b ξ) =
      surfaceTwoBoundaryCyclicUpperAmalgamEquiv w
        (Monoid.PushoutI.of b (embeddedTwoPunctureMarkedFactorEquiv
          hball f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre eE b ξ)) := by
  simp only [embeddedTwoPunctureAmbientMarkedUpperFreeEquiv, MulEquiv.trans_apply,
    embeddedTwoPunctureAmbientMarkedFreeEquiv_factor, MulEquiv.symm_apply_apply]

end Diagram

end
end SystolicGrowth

#print axioms SystolicGrowth.embeddedTwoPunctureMarkedFactorEquiv_generator
#print axioms SystolicGrowth.embeddedTwoPunctureMarkedFactorEquiv_compatible
#print axioms SystolicGrowth.embeddedTwoPunctureMarkedAmalgamEquiv
#print axioms SystolicGrowth.embeddedTwoPunctureAmbientMarkedFreeEquiv
#print axioms SystolicGrowth.embeddedTwoPunctureAmbientMarkedFreeEquiv_factor
#print axioms SystolicGrowth.embeddedTwoPunctureAmbientMarkedUpperFreeEquiv
#print axioms SystolicGrowth.embeddedTwoPunctureAmbientMarkedUpperFreeEquiv_factor
