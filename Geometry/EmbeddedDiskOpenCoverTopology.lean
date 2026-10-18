module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedTwoPunctureDiskOpenCover
public import Geometry.SurfaceEmbeddedDiskExterior
public import Geometry.EmbeddedTwoPunctureLocalDiskModel
public import Geometry.TwoPuncturedDiskOuterTraversal

@[expose] public section

/-!
# The topology of the actual embedded-disk cover

The smaller-disk exterior is identified with the already retracted open
exterior by the identity on original quotient points. Its physical free
presentation and the annulus overlap group are constructed, not premises.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane ContinuousMap

namespace SystolicGrowth

noncomputable section

variable {α : Type*} [TopologicalSpace α] [T2Space α] {U : Set ℂ}

omit [T2Space α] in
/-- The compact closed-disk image is precisely the image of its norm sublevel. -/
theorem embeddedTwoPunctureClosedDiskImage_eq_image (f : C(U, α)) (a : ℝ)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    embeddedTwoPunctureClosedDiskImage f a haU = f '' {z : U | ‖(z : ℂ)‖ ≤ a} := by
  ext x
  exact embeddedTwoPunctureClosedDiskImage_mem_iff f a haU x

/-- Both punctures are already excluded by the closed disk, so the open
cover exterior is literally the smaller closed-disk exterior. -/
def embeddedDiskOpenCoverExteriorHomeomorph (f : C(U, α)) (p q : U)
    (a : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    embeddedTwoPunctureExterior f p q a haU ≃ₜ embeddedCoordinateClosedDiskExterior f a :=
  Homeomorph.setCongr (by
    rw [embeddedTwoPunctureExterior, embeddedTwoPunctureClosedDiskImage_eq_image]
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, ?_⟩
      constructor
      · intro hxp
        exact hx ⟨p, (le_max_left _ _).trans ha.le, hxp.symm⟩
      · intro hxq
        exact hx ⟨q, (le_max_right _ _).trans ha.le, hxq.symm⟩)

omit [T2Space α] in
/-- The overlap of the actual embedded cover is path connected through its
literal annulus homeomorphism and actual radial-circle paths. -/
theorem embeddedDiskOpenCoverOverlap_pathConnected (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U) (a r : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    PathConnectedSpace ↥(embeddedTwoPunctureExterior f p q a haU ∩
      embeddedTwoPunctureLocalDisk f p q r) := by
  have ha0 : 0 ≤ a := (norm_nonneg (p : ℂ)).trans
    ((le_max_left _ _).trans ha.le)
  letI := complexAnnulus_pathConnected a r 1 ha0 zero_lt_one ha1 hr1
  let H := embeddedTwoPunctureAnnulusHomeomorph f hf p q ha haU hrU
  exact H.surjective.pathConnectedSpace H.continuous

/-- The actual overlap's group is the genuine coordinate-circle group;
the forward map is the inverse literal chart followed by normalization. -/
def embeddedDiskOpenCoverOverlapFundamentalGroupEquiv (f : C(U, α))
    (hf : Topology.IsOpenEmbedding (f : U → α)) (p q : U) (a r : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (z : ↥(embeddedTwoPunctureExterior f p q a haU ∩
      embeddedTwoPunctureLocalDisk f p q r)) :
    FundamentalGroup ↥(embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r) z ≃*
      FundamentalGroup Circle
        (complexAnnulusCircleRetraction a r
          ((norm_nonneg (p : ℂ)).trans ((le_max_left _ _).trans ha.le))
          ((embeddedTwoPunctureAnnulusHomeomorph f hf p q ha haU hrU).symm z)) := by
  have ha0 : 0 ≤ a := (norm_nonneg (p : ℂ)).trans
    ((le_max_left _ _).trans ha.le)
  let H := (embeddedTwoPunctureAnnulusHomeomorph f hf p q ha haU hrU).symm
  let F : C(↥(embeddedTwoPunctureExterior f p q a haU ∩
      embeddedTwoPunctureLocalDisk f p q r), complexAnnulus a r) := ⟨H, H.continuous⟩
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv H.toHomotopyEquiv
  let eH : FundamentalGroup ↥(embeddedTwoPunctureExterior f p q a haU ∩
      embeddedTwoPunctureLocalDisk f p q r) z ≃* FundamentalGroup (complexAnnulus a r) (F z) :=
    MulEquiv.ofBijective (FundamentalGroup.map F z)
      (e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
        (FundamentalGroupoid.mk z))
  exact eH.trans
    (complexAnnulusCircleFundamentalGroupEquiv a r 1 ha0 zero_lt_one ha1 hr1 (H z))

section Surface

variable {g : ℕ} {X : ClosedHyperbolicSurface g}
  (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))

/-- The open exterior of the actual two-puncture cover is path connected
on the original surface, using its constructed disk retraction and spine. -/
theorem embeddedDiskOpenCoverExterior_pathConnected
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o) :
    PathConnectedSpace (embeddedTwoPunctureExterior f p q a haU) := by
  have ha0 : 0 ≤ a := (norm_nonneg (p : ℂ)).trans
    ((le_max_left _ _).trans ha.le)
  letI := embeddedSurfaceClosedDiskExterior_pathConnected hball f hf a ha0 ha1 o hcenter B
  let H := (embeddedDiskOpenCoverExteriorHomeomorph f p q a ha haU).symm
  exact H.surjective.pathConnectedSpace H.continuous

/-- The actual open exterior has its genuine physical free basis. -/
def embeddedDiskOpenCoverExteriorFreeEquiv
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (z : embeddedTwoPunctureExterior f p q a haU) :
    FundamentalGroup (embeddedTwoPunctureExterior f p q a haU) z ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  have ha0 : 0 ≤ a := (norm_nonneg (p : ℂ)).trans
    ((le_max_left _ _).trans ha.le)
  let H := embeddedDiskOpenCoverExteriorHomeomorph f p q a ha haU
  let F : C(embeddedTwoPunctureExterior f p q a haU,
      embeddedCoordinateClosedDiskExterior f a) := ⟨H, H.continuous⟩
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv H.toHomotopyEquiv
  let eH : FundamentalGroup (embeddedTwoPunctureExterior f p q a haU) z ≃*
      FundamentalGroup (embeddedCoordinateClosedDiskExterior f a) (F z) :=
    MulEquiv.ofBijective (FundamentalGroup.map F z)
      (e.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
        (FundamentalGroupoid.mk z))
  exact eH.trans
    (embeddedSurfaceClosedDiskExteriorFreeEquiv hball f hf a ha0 ha1 o hcenter B (H z))

end Surface

section Boundary

variable {g : ℕ} {X : ClosedHyperbolicSurface g}

/-- The literal unit-coordinate circle in the actual annular overlap. Its
parameter is unchanged, rather than normalized after entering the chart. -/
def embeddedDiskOpenCoverOverlapBoundaryCircle
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    C(Circle, ↥(embeddedTwoPunctureExterior f p q a haU ∩
      embeddedTwoPunctureLocalDisk f p q r)) := by
  let H := embeddedTwoPunctureAnnulusHomeomorph f hf p q ha haU hrU
  have hA (θ : Circle) : (θ : ℂ) ∈ complexAnnulus a r := by
    change a < ‖(θ : ℂ)‖ ∧ ‖(θ : ℂ)‖ < r
    rw [Circle.norm_coe]
    exact ⟨ha1, hr1⟩
  let A : C(Circle, complexAnnulus a r) :=
    ⟨fun θ => ⟨(θ : ℂ), hA θ⟩,
      (continuous_subtype_val : Continuous (fun θ : Circle => (θ : ℂ))).subtype_mk hA⟩
  exact (⟨H, H.continuous⟩ : C(complexAnnulus a r, _)).comp A

/-- The literal boundary-circle inclusion induces the actual based overlap
equivalence. This uses the annulus radial homotopy and the actual chart map,
not an assumed winding or simply-connected-cover assertion. -/
def embeddedDiskOpenCoverOverlapBoundaryFundamentalGroupEquiv
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    FundamentalGroup Circle θ ≃*
      FundamentalGroup ↥(embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r)
        (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ) := by
  have ha0 : 0 ≤ a := (norm_nonneg (p : ℂ)).trans
    ((le_max_left _ _).trans ha.le)
  let H := embeddedTwoPunctureAnnulusHomeomorph f hf p q ha haU hrU
  let e := (complexAnnulusCircleHomotopyEquiv a r 1 ha0 zero_lt_one ha1 hr1).symm.trans
    H.toHomotopyEquiv
  have hmap : e.toFun =
      embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU := by
    apply ContinuousMap.ext
    intro φ
    apply Subtype.ext
    change f ⟨(1 : ℝ) • (φ : ℂ), _⟩ = f ⟨(φ : ℂ), _⟩
    simp only [one_smul]
  have hbij : Function.Bijective (FundamentalGroup.map
      (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) θ) := by
    rw [← hmap]
    exact (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk θ) (FundamentalGroupoid.mk θ)
  exact MulEquiv.ofBijective (FundamentalGroup.map
    (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) θ) hbij

/-- The positive one-turn is the literal included overlap loop under this
equivalence, at the original unit-coordinate boundary basepoint. -/
theorem embeddedDiskOpenCoverOverlapBoundaryFundamentalGroupEquiv_oneTurn
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    embeddedDiskOpenCoverOverlapBoundaryFundamentalGroupEquiv
      f hf p q a r ha ha1 hr1 haU hrU θ ⟦circleOneTurnLoop θ⟧ =
        ⟦(circleOneTurnLoop θ).map
          (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU).continuous⟧ := by
  rfl

/-- The actual annulus-to-exterior side map, expressed in the smaller
closed-disk exterior by the literal identity homeomorphism. -/
def embeddedDiskOpenCoverOverlapToClosedExterior
    (f : C(U, X.Carrier)) (p q : U) (a r : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    C(↥(embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r),
      embeddedCoordinateClosedDiskExterior f a) := by
  let H := embeddedDiskOpenCoverExteriorHomeomorph f p q a ha haU
  exact (⟨H, H.continuous⟩ : C(embeddedTwoPunctureExterior f p q a haU, _)).comp
    ⟨fun z => ⟨z.1, z.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The literal overlap boundary maps to the existing literal exterior
boundary circle, preserving both its basepoint and positive parameter. -/
theorem embeddedDiskOpenCoverOverlapToClosedExterior_boundaryCircle
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a r : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    (embeddedDiskOpenCoverOverlapToClosedExterior f p q a r ha haU).comp
        (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) =
      embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  rfl

/-- The overlap-to-exterior group map sends its literal positive unit-circle
loop to the already marked smaller-exterior boundary loop, with no rebase. -/
theorem embeddedDiskOpenCoverOverlapToClosedExterior_oneTurn
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a r : ℝ)
    (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    FundamentalGroup.map (embeddedDiskOpenCoverOverlapToClosedExterior f p q a r ha haU)
      (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ)
      ⟦(circleOneTurnLoop θ).map
        (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU).continuous⟧ =
        (⟦(circleOneTurnLoop θ).map
          (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ :
          FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
            (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θ)) := by
  rfl

/-- The literal annulus-to-local-disk side map keeps the original surface
point and merely forgets its exterior membership. -/
def embeddedDiskOpenCoverOverlapToLocalDisk
    (f : C(U, X.Carrier)) (p q : U) (a r : ℝ)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    C(↥(embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r),
      ↥(embeddedTwoPunctureLocalDisk f p q r)) :=
  ⟨fun z => ⟨z.1, z.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The actual annulus boundary enters the local chart at its unchanged
coordinate `θ`, rather than at an inverse-defined peripheral representative. -/
theorem embeddedDiskOpenCoverOverlapToLocalDisk_boundaryCoordinate
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    (embeddedTwoPunctureLocalDiskCoordinateHomeomorph f hf p q r hrU
      (embeddedDiskOpenCoverOverlapToLocalDisk f p q a r haU
        (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ)) :
        ℂ) = (θ : ℂ) := by
  let z : U := ⟨(θ : ℂ), hrU (by
    simpa only [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe] using hr1.le)⟩
  have hz : z ∈ embeddedTwoPunctureLocalDiskDomain p q r := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [z, Circle.norm_coe] using hr1
    · intro hzp
      have hnorm := congrArg (fun w : U => ‖(w : ℂ)‖) hzp
      have hp : ‖(p : ℂ)‖ < 1 := ((le_max_left _ _).trans_lt ha).trans ha1
      simp only [z, Circle.norm_coe] at hnorm
      linarith
    · intro hzq
      have hnorm := congrArg (fun w : U => ‖(w : ℂ)‖) hzq
      have hq : ‖(q : ℂ)‖ < 1 := ((le_max_right _ _).trans_lt ha).trans ha1
      simp only [z, Circle.norm_coe] at hnorm
      linarith
  let Z : {w : U // w ∈ embeddedTwoPunctureLocalDiskDomain p q r} := ⟨z, hz⟩
  have hpoint : embeddedDiskOpenCoverOverlapToLocalDisk f p q a r haU
      (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ) =
      ⟨f Z.1, (embeddedTwoPunctureLocalDisk_eq_image_domain f hf.injective p q r).symm ▸
        ⟨Z.1, Z.2, rfl⟩⟩ := by
    apply Subtype.ext
    rfl
  rw [hpoint, embeddedTwoPunctureLocalDiskCoordinateHomeomorph_chartPoint]
  rfl

/-- Positive scaling preserves the strict radius gap between both original
punctures and the unchanged unit-coordinate annulus boundary. -/
theorem embeddedTwoPunctureParameters_abs_lt_inv
    (p q : U) {r : ℝ} (hr : 0 < r)
    (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1) :
    |embeddedTwoPunctureLowerParameter p q r| < r⁻¹ ∧
      |embeddedTwoPunctureUpperParameter p q r| < r⁻¹ := by
  have hpim : |(p : ℂ).im| < 1 := (Complex.abs_im_le_norm _).trans_lt hp
  have hqim : |(q : ℂ).im| < 1 := (Complex.abs_im_le_norm _).trans_lt hq
  have hpdiv : |(p : ℂ).im / r| < r⁻¹ := by
    rw [abs_div, abs_of_pos hr, ← one_div]
    exact div_lt_div_of_pos_right hpim hr
  have hqdiv : |(q : ℂ).im / r| < r⁻¹ := by
    rw [abs_div, abs_of_pos hr, ← one_div]
    exact div_lt_div_of_pos_right hqim hr
  simp only [abs_lt, embeddedTwoPunctureLowerParameter,
    embeddedTwoPunctureUpperParameter] at hpdiv hqdiv ⊢
  constructor
  · exact ⟨lt_min hpdiv.1 hqdiv.1,
      (min_le_left _ _).trans_lt hpdiv.2⟩
  · exact ⟨hpdiv.1.trans_le (le_max_left _ _), max_lt hpdiv.2 hqdiv.2⟩

/-- The actual local side of the annulus boundary, expressed in the standard
disk coordinates, is exactly the positive outer circle of radius `1/r`. -/
theorem embeddedDiskOpenCoverOverlapToLocalDisk_normalizedBoundary
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    (⟨embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r
        (zero_lt_one.trans hr1) hrU hpre hqre,
      (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r
        (zero_lt_one.trans hr1) hrU hpre hqre).continuous⟩ : C(_, _)).comp
      ((embeddedDiskOpenCoverOverlapToLocalDisk f p q a r haU).comp
        (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU)) =
      twoPuncturedDiskOuterBoundaryCircle (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) r⁻¹
        ((embeddedTwoPunctureParameters_abs_lt_inv p q (zero_lt_one.trans hr1)
          (((le_max_left _ _).trans_lt ha).trans ha1)
          (((le_max_right _ _).trans_lt ha).trans ha1)).1)
        ((embeddedTwoPunctureParameters_abs_lt_inv p q (zero_lt_one.trans hr1)
          (((le_max_left _ _).trans_lt ha).trans ha1)
          (((le_max_right _ _).trans_lt ha).trans ha1)).2)
        ((inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1) := by
  apply ContinuousMap.ext
  intro θ
  apply Subtype.ext
  change (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r
      (zero_lt_one.trans hr1) hrU hpre hqre
        (embeddedDiskOpenCoverOverlapToLocalDisk f p q a r haU
          (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ)) :
        ℂ) = ((r⁻¹ : ℝ) : ℂ) * (θ : ℂ)
  rw [embeddedTwoPunctureLocalDiskUnitHomeomorph_apply]
  rw [embeddedDiskOpenCoverOverlapToLocalDisk_boundaryCoordinate]
  rw [Complex.real_smul]

#print axioms embeddedDiskOpenCoverOverlapToClosedExterior_boundaryCircle
#print axioms embeddedDiskOpenCoverOverlapToClosedExterior_oneTurn
#print axioms embeddedDiskOpenCoverOverlapBoundaryFundamentalGroupEquiv
#print axioms embeddedDiskOpenCoverOverlapBoundaryFundamentalGroupEquiv_oneTurn
#print axioms embeddedDiskOpenCoverOverlapToLocalDisk_boundaryCoordinate
#print axioms embeddedDiskOpenCoverOverlapToLocalDisk_normalizedBoundary

end Boundary

#print axioms embeddedDiskOpenCoverExteriorFreeEquiv
#print axioms embeddedDiskOpenCoverExterior_pathConnected
#print axioms embeddedDiskOpenCoverOverlapFundamentalGroupEquiv

end

end SystolicGrowth
