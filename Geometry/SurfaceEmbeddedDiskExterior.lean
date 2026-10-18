module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterDiskChart
public import Geometry.EmbeddedCoordinatePunctureRetraction
public import Geometry.SurfaceBoundaryGraphFreeBasis

@[expose] public section

/-!
# The actual disk exterior and its physical free presentation

The embedded two-center disk has a complement homotopy equivalent to the
original surface punctured at the disk center. The induced presentation uses
the actual Dirichlet spine and its actual rooted connector. Boundary winding
is not inferred merely from the existence of this free presentation.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane ContinuousMap

namespace SystolicGrowth

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
  (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
  (f : C(U, X.Carrier))

/-- The literal coordinate unit circle lies outside the deleted open disk. -/
def embeddedSurfaceDiskBoundaryCircle
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) :
    C(Circle, embeddedCoordinatePunctureExterior f) := by
  let circlePoint : Circle → U := fun θ =>
    ⟨(θ : ℂ), hball (by simpa using (Circle.norm_coe θ).le)⟩
  have hpoint : Continuous circlePoint :=
    (continuous_subtype_val : Continuous (fun θ : Circle => (θ : ℂ))).subtype_mk _
  have hnot : ∀ θ : Circle, f (circlePoint θ) ∉ embeddedCoordinatePunctureDisk f := by
    intro θ
    rintro ⟨z, hz, heq⟩
    have hzθ : (z : ℂ) = (θ : ℂ) := congrArg Subtype.val (hf.injective heq)
    change ‖(z : ℂ)‖ < 1 at hz
    rw [hzθ, Circle.norm_coe] at hz
    exact (lt_irrefl (1 : ℝ)) hz
  exact ⟨fun θ => ⟨f (circlePoint θ), hnot θ⟩,
    (f.continuous.comp hpoint).subtype_mk hnot⟩

/-- This boundary is its original quotient point, with no reparametrization. -/
@[simp]
theorem embeddedSurfaceDiskBoundaryCircle_val
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (θ : Circle) :
    (embeddedSurfaceDiskBoundaryCircle hball f hf θ).1 =
      f ⟨(θ : ℂ), hball (by simpa using (Circle.norm_coe θ).le)⟩ := rfl

/-- Equal removed points identify the chart puncture with the original
one-center-punctured quotient by the identity on quotient points. -/
def embeddedSurfaceDiskPunctureHomeomorph (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) :
    {y : X.Carrier // y ≠ embeddedCoordinatePunctureCenter hball f} ≃ₜ
      X.CenterPuncturedCarrier o :=
  Homeomorph.setCongr (by rw [hcenter])

/-- The disk exterior's actual inclusion into the original punctured
surface induces a based equivalence. -/
def embeddedSurfaceDiskExteriorFundamentalGroupEquiv
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (q : embeddedCoordinatePunctureExterior f) :
    FundamentalGroup (embeddedCoordinatePunctureExterior f) q ≃*
      FundamentalGroup (X.CenterPuncturedCarrier o)
        (embeddedSurfaceDiskPunctureHomeomorph hball f o hcenter
          (embeddedCoordinatePunctureInclusion hball f q)) := by
  let H := embeddedSurfaceDiskPunctureHomeomorph hball f o hcenter
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv H.toHomotopyEquiv
  exact (embeddedCoordinatePunctureFundamentalGroupEquiv hball f hf q).trans
    (MulEquiv.ofBijective (FundamentalGroup.map ⟨H, H.continuous⟩
      (embeddedCoordinatePunctureInclusion hball f q))
      (e.fullyFaithfulFunctor.map_bijective
        (FundamentalGroupoid.mk (embeddedCoordinatePunctureInclusion hball f q))
        (FundamentalGroupoid.mk (embeddedCoordinatePunctureInclusion hball f q))))

/-- A physical free basis for the actual disk exterior at any exterior point.
The rebase is the explicit root-to-point path on the actual boundary graph. -/
def embeddedSurfaceDiskExteriorFreeEquiv
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (q : embeddedCoordinatePunctureExterior f) :
    FundamentalGroup (embeddedCoordinatePunctureExterior f) q ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  let p := embeddedSurfaceDiskPunctureHomeomorph hball f o hcenter
    (embeddedCoordinatePunctureInclusion hball f q)
  let graphPoint := B.intrinsicBoundaryGraphSpineHomeomorph.symm
    (X.dirichletSpineRetraction o p)
  exact (embeddedSurfaceDiskExteriorFundamentalGroupEquiv hball f hf o hcenter q).trans
    ((B.intrinsicBoundaryGraphFundamentalGroupEquiv p).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath
        (B.intrinsicBoundaryGraphRootedPath B.intrinsicBoundaryPeripheralRoot graphPoint).symm).trans
          (B.intrinsicBoundaryGraphFundamentalGroupFreeEquiv B.intrinsicBoundaryPeripheralRoot)))

/-- The actual one-center-punctured surface is path connected by its
constructed Dirichlet-spine homotopy and physical rooted graph paths. -/
theorem surfaceCenterPuncturedPathConnected (o : ℍ)
    (B : DirichletBoundarySegments X o) : PathConnectedSpace (X.CenterPuncturedCarrier o) := by
  let r := B.intrinsicBoundaryPeripheralRoot
  letI : PathConnectedSpace B.IntrinsicBoundaryGraph :=
    { nonempty := ⟨B.intrinsicBoundaryGraphVertexInclusion r⟩
      joined := fun x y => ⟨(B.intrinsicBoundaryGraphRootedPath r x).symm.trans
        (B.intrinsicBoundaryGraphRootedPath r y)⟩ }
  exact pathConnectedSpace_of_homotopyEquiv
    ((X.dirichletSpineHomotopyEquiv o).trans
      B.intrinsicBoundaryGraphSpineHomeomorph.symm.toHomotopyEquiv)

/-- The actual unit-disk exterior is path connected; no connectivity of a
replacement carrier is used. -/
theorem embeddedSurfaceDiskExterior_pathConnected
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o) :
    PathConnectedSpace (embeddedCoordinatePunctureExterior f) := by
  letI := surfaceCenterPuncturedPathConnected o B
  exact pathConnectedSpace_of_homotopyEquiv
    ((embeddedCoordinatePunctureHomotopyEquiv hball f hf).trans
      (embeddedSurfaceDiskPunctureHomeomorph hball f o hcenter).toHomotopyEquiv)

/-- The open exterior used by van Kampen has an actual physical free
presentation, through its constructed radial retraction. -/
def embeddedSurfaceClosedDiskExteriorFreeEquiv
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (q : embeddedCoordinateClosedDiskExterior f a) :
    FundamentalGroup (embeddedCoordinateClosedDiskExterior f a) q ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge :=
  (embeddedCoordinateClosedDiskExteriorFundamentalGroupEquiv hball f hf a ha ha1 q).trans
    (embeddedSurfaceDiskExteriorFreeEquiv hball f hf o hcenter B
      (embeddedCoordinateClosedDiskExteriorRetraction hball f hf a ha q))

/-- The genuine open exterior is path connected by the same actual
deformation, as required by the local-disk van Kampen cover. -/
theorem embeddedSurfaceClosedDiskExterior_pathConnected
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o) :
    PathConnectedSpace (embeddedCoordinateClosedDiskExterior f a) := by
  letI := embeddedSurfaceDiskExterior_pathConnected hball f hf o hcenter B
  exact pathConnectedSpace_of_homotopyEquiv
    (embeddedCoordinateClosedDiskExteriorHomotopyEquiv hball f hf a ha ha1)

/-- The original unit boundary in the smaller open exterior, through the
literal identity inclusion used by the disk-cover deformation retraction. -/
def embeddedSurfaceClosedDiskExteriorBoundaryCircle
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (a : ℝ) (ha1 : a < 1) :
    C(Circle, embeddedCoordinateClosedDiskExterior f a) :=
  (embeddedCoordinateClosedDiskExteriorInclusion f a ha1).comp
    (embeddedSurfaceDiskBoundaryCircle hball f hf)

/-- At the literal boundary basepoint, inclusion into the smaller exterior
is a based group equivalence, constructed from the actual relative retraction. -/
def embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (θ : Circle) :
    FundamentalGroup (embeddedCoordinatePunctureExterior f)
        (embeddedSurfaceDiskBoundaryCircle hball f hf θ) ≃*
      FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
        (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θ) := by
  let H := (embeddedCoordinateClosedDiskExteriorHomotopyEquiv hball f hf a ha ha1).symm
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv H
  exact MulEquiv.ofBijective
    (FundamentalGroup.map (embeddedCoordinateClosedDiskExteriorInclusion f a ha1)
      (embeddedSurfaceDiskBoundaryCircle hball f hf θ))
    (e.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk (embeddedSurfaceDiskBoundaryCircle hball f hf θ))
      (FundamentalGroupoid.mk (embeddedSurfaceDiskBoundaryCircle hball f hf θ)))

/-- Inclusion preserves the untouched positive boundary loop exactly; no
basepoint-changing path or winding sign is silently introduced. -/
theorem embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv_oneTurn
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (θ : Circle) :
    embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv
      hball f hf a ha ha1 θ
        ⟦(circleOneTurnLoop θ).map (embeddedSurfaceDiskBoundaryCircle hball f hf).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ := by
  rfl

#print axioms embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv
#print axioms embeddedSurfaceClosedDiskExteriorBoundaryInclusionFundamentalGroupEquiv_oneTurn

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual two-center disk has a genuine free exterior presentation.
Both original centers are inside the same disk; the puncture used for the
exterior presentation is the literal midpoint of their full lifted segment. -/
theorem exists_componentTwoCenterDiskExteriorFreePresentation
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ (U : Set ℂ) (_hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
      (f : C(U, (X i).Carrier)),
      Topology.IsOpenEmbedding (f : U → (X i).Carrier) ∧
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈ embeddedCoordinatePunctureDisk f ∧
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈ embeddedCoordinatePunctureDisk f ∧
      ∃ e : ℂ ≃ₜ ℍ, (∀ z : U, f z = (X i).orbitProjection (e z.1)) ∧
        e 0 = P.componentLiftedCenterGeodPoint i
          ⟨1 / 2, by constructor <;> norm_num⟩ ∧
        embeddedCoordinatePunctureCenter hball f = (Quotient.mk'' (e 0) : (X i).Carrier) ∧
        ∀ q : embeddedCoordinatePunctureExterior f,
          Nonempty (FundamentalGroup (embeddedCoordinatePunctureExterior f) q ≃*
            FreeGroup ((X i).dirichletBoundarySegments (e 0)).IntrinsicBoundaryNonTreeEdge) := by
  obtain ⟨U, hU, hball, F, hF, hL, hR, e, he, hm⟩ :=
    P.exists_componentTwoCenterEmbeddedDiskChart i
  let f : C(U, (X i).Carrier) := ⟨F, hF.continuous⟩
  have hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' (e 0) : (X i).Carrier) := he (embeddedCoordinatePunctureOrigin hball)
  refine ⟨U, hU, hball, f, hF, hL, hR, e, he, hm, hcenter, ?_⟩
  intro q
  exact ⟨embeddedSurfaceDiskExteriorFreeEquiv hball f hF (e 0) hcenter
    ((X i).dirichletBoundarySegments (e 0)) q⟩

#print axioms exists_componentTwoCenterDiskExteriorFreePresentation

end ExerciseGluingPreparation

#print axioms embeddedSurfaceDiskExteriorFreeEquiv
#print axioms embeddedSurfaceClosedDiskExteriorFreeEquiv
#print axioms embeddedSurfaceClosedDiskExterior_pathConnected

end

end SystolicGrowth
