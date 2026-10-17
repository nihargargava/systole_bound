module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterPolarCutTransport
public import Geometry.SurfaceTwoCenterSmallPolarCircles
public import Geometry.SurfaceTwoCenterDiskChart
public import Geometry.SurfaceTwoCenterCutRadialAxis
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Radius-angle rectangles for the two-center connector

The actual radius homotopy is a homotopy of the polar circle maps in the
original two-center-punctured component. Applying the path-homotopy square
to an arbitrary circle arc gives the exact connector-rectangle relation:
inner arc followed by radial motion at its terminal angle is homotopic to
radial motion at its initial angle followed by the outer arc.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- A radius-angle square in the actual punctured component moves a circle
arc through the literal family of polar circles. -/
theorem twoCenterPolarRadiusAngleConnector_homotopic
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ₀ ρ₁ : ℝ) (h₀ : 0 < ρ₀) (h₁ : 0 < ρ₁)
    (h₀r : ρ₀ ≤ gluingRadius C g) (h₁r : ρ₁ ≤ gluingRadius C g)
    {θ₀ θ₁ : Circle} (γ : Path θ₀ θ₁) :
    (((γ.map (P.twoCenterPolarBoundaryMap i b ρ₀ h₀ h₀r).continuous).trans
        ((P.twoCenterPolarRadiusHomotopy i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r).evalAt θ₁)).Homotopic
      (((P.twoCenterPolarRadiusHomotopy i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r).evalAt θ₀).trans
        (γ.map (P.twoCenterPolarBoundaryMap i b ρ₁ h₁ h₁r).continuous))) := by
  exact Path.Homotopic.map_trans_evalAt
    (P.twoCenterPolarRadiusHomotopy i b ρ₀ ρ₁ h₀ h₁ h₀r h₁r) γ

/-- Specialization to the connector from the angle-one basepoint to a chosen
cut direction. -/
theorem twoCenterPolarLeftConnector_radius_homotopy
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) (θ : Circle) :
    (((Circle.path 1 θ).map
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous).trans
        ((P.twoCenterPolarRadiusHomotopy i b ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl).evalAt θ)).Homotopic
      (((P.twoCenterPolarRadiusHomotopy i b ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl).evalAt 1).trans
        ((Circle.path 1 θ).map
          (P.twoCenterPolarBoundaryMap i b (gluingRadius C g)
            P.radius_pos le_rfl).continuous)) := by
  exact P.twoCenterPolarRadiusAngleConnector_homotopic i b ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl (Circle.path 1 θ)

/-- Specialization to the connector from a chosen cut direction to the
angle-one basepoint, with the actual radius track orientation made explicit. -/
theorem twoCenterPolarRightConnector_radius_homotopy
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (b : Bool)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) (θ : Circle) :
    (((Circle.path θ 1).map
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr).continuous).trans
        ((P.twoCenterPolarRadiusHomotopy i b ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl).evalAt 1)).Homotopic
      (((P.twoCenterPolarRadiusHomotopy i b ρ (gluingRadius C g)
          hρ P.radius_pos hρr le_rfl).evalAt θ).trans
        ((Circle.path θ 1).map
          (P.twoCenterPolarBoundaryMap i b (gluingRadius C g)
            P.radius_pos le_rfl).continuous)) := by
  exact P.twoCenterPolarRadiusAngleConnector_homotopic i b ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl (Circle.path θ 1)

/-- The connector obtained after sliding each outer polar arc to the chosen
small radius, leaving the two cut-direction radial tracks adjacent to the
actual center cut. -/
def componentTwoCenterSmallDiskConnectorCandidate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1) := by
  let θL := P.componentTwoCenterCutLeftAngle i
  let θR := P.componentTwoCenterCutRightAngle i
  let leftArc := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true ρ hρ hρr).continuous
  let rightArc := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false ρ hρ hρr).continuous
  let leftRad := (P.twoCenterPolarRadiusHomotopy i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl).evalAt θL
  let rightRad := (P.twoCenterPolarRadiusHomotopy i false
    (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr).evalAt θR
  have hcutL : P.twoCenterPolarBoundaryMap i true
      (gluingRadius C g) P.radius_pos le_rfl θL =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
    rw [twoCenterPolarBoundaryMap_gluingRadius_left]
    exact (P.componentTwoCenterCutLeftAngle_spec i).trans
      (congrArg (P.componentPunctureInclusion i) (by rfl))
  have hcutR : P.twoCenterPolarBoundaryMap i false
      (gluingRadius C g) P.radius_pos le_rfl θR =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
    rw [twoCenterPolarBoundaryMap_gluingRadius_right]
    exact (P.componentTwoCenterCutRightAngle_spec i).trans
      (congrArg (P.componentPunctureInclusion i) (by rfl))
  let core := ((P.componentTwoCenterCutArc i).map
      (P.componentPunctureInclusion i).continuous).cast hcutL hcutR
  exact (leftArc.trans leftRad).trans (core.trans (rightRad.trans rightArc))

/-- The reassembled connector after applying the two radius-angle squares:
small left basepoint to the original left circle, across the original cut,
then back along the small right basepoint track. -/
def componentTwoCenterSmallDiskConnectorReassembled
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1) := by
  let θL := P.componentTwoCenterCutLeftAngle i
  let θR := P.componentTwoCenterCutRightAngle i
  let leftBase := (P.twoCenterPolarRadiusHomotopy i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl).evalAt 1
  let leftOuter := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true (gluingRadius C g)
      P.radius_pos le_rfl).continuous
  let rightBase := (P.twoCenterPolarRadiusHomotopy i false
    (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr).evalAt 1
  let rightOuter := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false (gluingRadius C g)
      P.radius_pos le_rfl).continuous
  have hcutL : P.twoCenterPolarBoundaryMap i true
      (gluingRadius C g) P.radius_pos le_rfl θL =
        P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
    simpa only [twoCenterPolarBoundaryMap_gluingRadius_left] using
      P.componentTwoCenterCutLeftAngle_spec i
  have hcutR : P.twoCenterPolarBoundaryMap i false
      (gluingRadius C g) P.radius_pos le_rfl θR =
        P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
    simpa only [twoCenterPolarBoundaryMap_gluingRadius_right] using
      P.componentTwoCenterCutRightAngle_spec i
  let core := ((P.componentTwoCenterCutArc i).map
      (P.componentPunctureInclusion i).continuous).cast hcutL hcutR
  exact (leftBase.trans leftOuter).trans
    (core.trans (rightOuter.trans rightBase))

/-- Sliding each circle connector through the actual polar-radius homotopy
turns the disk-route candidate into the reassembled connector.  The exact
endpoint-cast comparison with `componentTwoCenterSmallPolarCutBasedPath` is
kept separate: that path stores its radius tracks cast to the component
boundary maps, while this square is stated at the literal gluing-radius maps. -/
theorem componentTwoCenterSmallDiskConnectorCandidate_homotopic_reassembled
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr).Homotopic
      (P.componentTwoCenterSmallDiskConnectorReassembled i ρ hρ hρr) := by
  let θL := P.componentTwoCenterCutLeftAngle i
  let θR := P.componentTwoCenterCutRightAngle i
  let leftArc := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true ρ hρ hρr).continuous
  let leftRad := (P.twoCenterPolarRadiusHomotopy i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl).evalAt θL
  let leftBase := (P.twoCenterPolarRadiusHomotopy i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl).evalAt 1
  let leftOuter := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true (gluingRadius C g)
      P.radius_pos le_rfl).continuous
  let rightArc := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false ρ hρ hρr).continuous
  let rightRad := (P.twoCenterPolarRadiusHomotopy i false
    (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr).evalAt θR
  let rightBase := (P.twoCenterPolarRadiusHomotopy i false
    (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr).evalAt 1
  let rightOuter := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false (gluingRadius C g)
      P.radius_pos le_rfl).continuous
  have hcutL : P.twoCenterPolarBoundaryMap i true
      (gluingRadius C g) P.radius_pos le_rfl θL =
        P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
    simpa only [twoCenterPolarBoundaryMap_gluingRadius_left] using
      P.componentTwoCenterCutLeftAngle_spec i
  have hcutR : P.twoCenterPolarBoundaryMap i false
      (gluingRadius C g) P.radius_pos le_rfl θR =
        P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
    simpa only [twoCenterPolarBoundaryMap_gluingRadius_right] using
      P.componentTwoCenterCutRightAngle_spec i
  let core := ((P.componentTwoCenterCutArc i).map
      (P.componentPunctureInclusion i).continuous).cast hcutL hcutR
  have hLeft := P.twoCenterPolarLeftConnector_radius_homotopy
    i true ρ hρ hρr θL
  have hRight := P.twoCenterPolarRadiusAngleConnector_homotopic
    i false (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr
    (Circle.path θR 1)
  have hmain :
      ((leftArc.trans leftRad).trans (core.trans (rightRad.trans rightArc))).Homotopic
        (((leftBase.trans leftOuter).trans (core.trans (rightOuter.trans rightBase)))) := by
    exact hLeft.hcomp ((Path.Homotopic.refl core).hcomp hRight.symm)
  change ((leftArc.trans leftRad).trans (core.trans (rightRad.trans rightArc))).Homotopic _
  exact hmain

set_option backward.isDefEq.respectTransparency false in
/-- Keep the original cut's association while exposing its three literal
pieces at the gluing-radius polar endpoints. Casts do not alter path values. -/
private theorem componentTwoCenterCutBasedPath_cast_gluingRadius
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (P.componentTwoCenterCutBasedPath i).cast
        (P.twoCenterPolarBoundaryMap_gluingRadius_one_left i)
        (P.twoCenterPolarBoundaryMap_gluingRadius_one_right i) =
      (((Circle.path 1 (P.componentTwoCenterCutLeftAngle i)).map
          (P.twoCenterPolarBoundaryMap i true (gluingRadius C g)
            P.radius_pos le_rfl).continuous).trans
        (((P.componentTwoCenterCutArc i).map
            (P.componentPunctureInclusion i).continuous).cast
          (by
            rw [P.twoCenterPolarBoundaryMap_gluingRadius_left]
            exact P.componentTwoCenterCutLeftAngle_spec i)
          (by
            rw [P.twoCenterPolarBoundaryMap_gluingRadius_right]
            exact P.componentTwoCenterCutRightAngle_spec i))).trans
        ((Circle.path (P.componentTwoCenterCutRightAngle i) 1).map
          (P.twoCenterPolarBoundaryMap i false (gluingRadius C g)
            P.radius_pos le_rfl).continuous) := by
  apply Path.ext
  funext t
  simp [Path.cast_coe, Path.trans_apply, componentTwoCenterCutBasedPath,
    componentTwoCenterCutLeftConnector, componentTwoCenterCutRightConnector,
    P.twoCenterPolarBoundaryMap_gluingRadius_left,
    P.twoCenterPolarBoundaryMap_gluingRadius_right]

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed shrinking connector is homotopic to the radius-angle
candidate in the original punctured component, with both original basepoints
and the literal cut retained. Disk containment is a separate geometric step. -/
theorem componentTwoCenterSmallPolarCutBasedPath_homotopic_candidate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr).Homotopic
      (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
  let θL := P.componentTwoCenterCutLeftAngle i
  let θR := P.componentTwoCenterCutRightAngle i
  let leftBase := (P.twoCenterPolarRadiusHomotopy i true ρ
    (gluingRadius C g) hρ P.radius_pos hρr le_rfl).evalAt 1
  let leftOuter := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true (gluingRadius C g)
      P.radius_pos le_rfl).continuous
  let rightBase := (P.twoCenterPolarRadiusHomotopy i false
    (gluingRadius C g) ρ P.radius_pos hρ le_rfl hρr).evalAt 1
  let rightOuter := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false (gluingRadius C g)
      P.radius_pos le_rfl).continuous
  have hcutL : P.twoCenterPolarBoundaryMap i true
      (gluingRadius C g) P.radius_pos le_rfl θL =
        P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
    rw [P.twoCenterPolarBoundaryMap_gluingRadius_left]
    exact P.componentTwoCenterCutLeftAngle_spec i
  have hcutR : P.twoCenterPolarBoundaryMap i false
      (gluingRadius C g) P.radius_pos le_rfl θR =
        P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
    rw [P.twoCenterPolarBoundaryMap_gluingRadius_right]
    exact P.componentTwoCenterCutRightAngle_spec i
  let core := ((P.componentTwoCenterCutArc i).map
    (P.componentPunctureInclusion i).continuous).cast hcutL hcutR
  have hOldReassembled : Path.Homotopic.Quotient.mk
      (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr) =
      Path.Homotopic.Quotient.mk
        (P.componentTwoCenterSmallDiskConnectorReassembled i ρ hρ hρr) := by
    rw [P.componentTwoCenterSmallPolarCutBasedPath_eq_radius_cut i ρ hρ hρr,
      componentTwoCenterCutBasedPath_cast_gluingRadius]
    change Path.Homotopic.Quotient.mk
        ((leftBase.trans ((leftOuter.trans core).trans rightOuter)).trans
          ((P.twoCenterPolarRadiusHomotopy i false ρ (gluingRadius C g)
            hρ P.radius_pos hρr le_rfl).evalAt 1).symm) =
      Path.Homotopic.Quotient.mk
        ((leftBase.trans leftOuter).trans (core.trans (rightOuter.trans rightBase)))
    rw [P.twoCenterPolarRadiusHomotopy_evalAt_symm]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
    rfl
  exact Path.Homotopic.Quotient.eq.mp
    (hOldReassembled.trans
      (Path.Homotopic.Quotient.eq.mpr
        (P.componentTwoCenterSmallDiskConnectorCandidate_homotopic_reassembled
          i ρ hρ hρr)).symm)

/-- The small-arc connector stays in any set containing the complete actual
center segment and both actual small polar circles. The radial pieces use
the chosen cut angles, not an assumed containment of the radius-`r` disks. -/
theorem componentTwoCenterSmallDiskConnectorCandidate_mem
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    {D : Set (X i).Carrier}
    (hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈ D)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈ D) :
    ∀ t : I, (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈ D := by
  have hgeod : ∀ z ∈ Vendored.RiemannDynamics.geodSeg (P.centers i).1
      (P.componentCenterClosestDeck i • (P.centers i).2),
      (Quotient.mk'' z : (X i).Carrier) ∈ D := by
    intro z hz
    rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact hsegment ⟨s, hs⟩
  have hleft : ∀ t : I,
      (((P.twoCenterPolarRadiusHomotopy i true ρ (gluingRadius C g)
        hρ P.radius_pos hρr le_rfl).evalAt (P.componentTwoCenterCutLeftAngle i)) t).val ∈ D := by
    intro t
    let s := (1 - (t : ℝ)) * ρ + (t : ℝ) * gluingRadius C g
    have hs : 0 < s := by
      dsimp [s]
      nlinarith [mul_nonneg t.2.1 (sub_nonneg.mpr hρr)]
    have hsr : s ≤ gluingRadius C g := by
      dsimp [s]
      nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr hρr)]
    exact hgeod _ (P.componentTwoCenterLeftPolarRadius_mem_centerGeodesic i hs hsr)
  have hright : ∀ t : I,
      (((P.twoCenterPolarRadiusHomotopy i false (gluingRadius C g) ρ
        P.radius_pos hρ le_rfl hρr).evalAt (P.componentTwoCenterCutRightAngle i)) t).val ∈ D := by
    intro t
    let s := (1 - (t : ℝ)) * gluingRadius C g + (t : ℝ) * ρ
    have hs : 0 < s := by
      dsimp [s]
      nlinarith [mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr hρr)]
    have hsr : s ≤ gluingRadius C g := by
      dsimp [s]
      nlinarith [mul_nonneg t.2.1 (sub_nonneg.mpr hρr)]
    let δ := P.componentCenterClosestDeck i
    let w := gluingPolarPoint (P.centers i).2 (P.componentTwoCenterCutRightAngle i) s
    have hproj : (Quotient.mk'' (δ • w) : (X i).Carrier) = Quotient.mk'' w := by
      apply Quotient.sound
      exact MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit_iff.mpr ⟨δ, rfl⟩)
    have hmem := hgeod _
      (P.componentTwoCenterRightPolarRadius_mem_centerGeodesic i hs hsr)
    have hpolar : δ • w = gluingPolarPoint
        (P.componentCenterClosestDeck i • (P.centers i).2)
        (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 *
          P.componentTwoCenterCutRightAngle i) s :=
      gluingPolarPoint_smul (↑δ) (P.centers i).2
        (P.componentTwoCenterCutRightAngle i) s
    rw [← hpolar] at hmem
    change (Quotient.mk'' (δ • w) : (X i).Carrier) ∈ D at hmem
    rw [hproj] at hmem
    exact hmem
  have htrans {a b c : P.CenterPuncturedChainComponent i}
      (γ : Path a b) (η : Path b c)
      (hγ : ∀ t : I, (γ t).val ∈ D) (hη : ∀ t : I, (η t).val ∈ D) :
      ∀ t : I, ((γ.trans η) t).val ∈ D := by
    intro t
    have ht : (γ.trans η) t ∈ Set.range γ ∪ Set.range η := by
      rw [← Path.trans_range]
      exact Set.mem_range_self t
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · rw [← hs]
      exact hγ s
    · rw [← hs]
      exact hη s
  unfold componentTwoCenterSmallDiskConnectorCandidate
  apply htrans
  · apply htrans
    · intro t
      exact hsmall true (Circle.path 1 (P.componentTwoCenterCutLeftAngle i) t)
    · exact hleft
  · apply htrans
    · intro t
      exact hsegment (P.componentTwoCenterCutCoordinate i t)
    · apply htrans
      · exact hright
      · intro t
        exact hsmall false (Circle.path (P.componentTwoCenterCutRightAngle i) 1 t)

/-- Choose actual small polar circles and an actual connector inside an
embedded chart containing the complete center segment. The original
prescribed connector is homotopic to this disk-contained candidate. -/
theorem exists_componentTwoCenterSmallChartPolarCirclesAndConnector
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (hleft : (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f)
    (hright : (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f)
    (hsegment : ∀ t : I, P.componentCenterGeodPoint i t ∈
      embeddedCoordinatePunctureDisk f) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g),
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ t : I, (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
        embeddedCoordinatePunctureDisk f) ∧
      (P.componentTwoCenterSmallPolarCutBasedPath i ρ hρ hρr).Homotopic
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
  obtain ⟨ρ, hρ, hρr, hsmall, _htransport⟩ :=
    P.exists_componentTwoCenterSmallChartPolarCircles i hU hball f hf hleft hright
  exact ⟨ρ, hρ, hρr, hsmall,
    P.componentTwoCenterSmallDiskConnectorCandidate_mem i ρ hρ hρr hsegment hsmall,
    P.componentTwoCenterSmallPolarCutBasedPath_homotopic_candidate i ρ hρ hρr⟩

end
end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterPolarRadiusAngleConnector_homotopic
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterPolarLeftConnector_radius_homotopy
#print axioms SystolicGrowth.ExerciseGluingPreparation.twoCenterPolarRightConnector_radius_homotopy
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterSmallDiskConnectorCandidate_homotopic_reassembled
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterSmallPolarCutBasedPath_homotopic_candidate
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterSmallDiskConnectorCandidate_mem
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterSmallChartPolarCirclesAndConnector
