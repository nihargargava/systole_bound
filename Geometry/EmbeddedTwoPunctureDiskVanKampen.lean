module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedDiskOpenCoverTopology
public import Geometry.EmbeddedTwoPunctureLocalDiskModel
public import Geometry.TwoPuncturedDiskFreePresentation
public import Geometry.TwoOpenCoverAmalgamEquiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Van Kampen for the actual embedded two-puncture cover

The exterior and local disk are taken as relative preimages in the original
two-punctured surface carrier. Their overlap is the literal annulus image.
The canonical based amalgam map preserves the actual side and overlap maps.
-/

open Set UpperHalfPlane
open scoped ContinuousMap

namespace SystolicGrowth

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}

/-- The original surface with its two actual chart-center images removed. -/
abbrev embeddedTwoPunctureAmbientPoint (f : C(U, X.Carrier)) (p q : U) :=
  {x : X.Carrier // x ∈ embeddedTwoPunctureAmbient f p q}

/-- The exterior cover member as a preimage in the actual punctured carrier. -/
def embeddedTwoPunctureExteriorRelativeSide (f : C(U, X.Carrier)) (p q : U)
    (a : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    Set (embeddedTwoPunctureAmbientPoint f p q) :=
  (Subtype.val : embeddedTwoPunctureAmbientPoint f p q → X.Carrier) ⁻¹'
    embeddedTwoPunctureExterior f p q a haU

/-- The local-disk cover member as a preimage in the actual punctured carrier. -/
def embeddedTwoPunctureLocalDiskRelativeSide (f : C(U, X.Carrier)) (p q : U)
    (r : ℝ) : Set (embeddedTwoPunctureAmbientPoint f p q) :=
  (Subtype.val : embeddedTwoPunctureAmbientPoint f p q → X.Carrier) ⁻¹'
    embeddedTwoPunctureLocalDisk f p q r

/-- The relative overlap of the actual exterior and local-disk members. -/
abbrev embeddedTwoPunctureRelativeOverlap (f : C(U, X.Carrier)) (p q : U)
    (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :=
  embeddedTwoPunctureExteriorRelativeSide f p q a haU ∩
    embeddedTwoPunctureLocalDiskRelativeSide f p q r

theorem embeddedTwoPunctureExteriorRelativeSide_isOpen (f : C(U, X.Carrier))
    (p q : U) (a : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    IsOpen (embeddedTwoPunctureExteriorRelativeSide f p q a haU) :=
  (embeddedTwoPunctureExterior_isOpen f p q a haU).preimage continuous_subtype_val

theorem embeddedTwoPunctureLocalDiskRelativeSide_isOpen (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (r : ℝ) :
    IsOpen (embeddedTwoPunctureLocalDiskRelativeSide f p q r) :=
  (embeddedTwoPunctureLocalDisk_isOpen f hf p q r).preimage continuous_subtype_val

/-- The actual exterior subtype is homeomorphic to its relative preimage. -/
def embeddedTwoPunctureExteriorRelativeHomeomorph (f : C(U, X.Carrier))
    (p q : U) (a : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU} ≃ₜ
      {z : X.Carrier // z ∈ embeddedTwoPunctureExterior f p q a haU} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z := ⟨⟨z.1, z.2.2⟩, z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual local-disk subtype is homeomorphic to its relative preimage. -/
def embeddedTwoPunctureLocalDiskRelativeHomeomorph (f : C(U, X.Carrier))
    (p q : U) (r : ℝ) :
    {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} ≃ₜ
      {z : X.Carrier // z ∈ embeddedTwoPunctureLocalDisk f p q r} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z := ⟨⟨z.1, z.2.2⟩, z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Literal chart coordinates and positive scaling identify the native
local factor of the surface cover with the twice-punctured unit disk. -/
def embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} ≃ₜ
      twoPuncturedUnitDiskPoint (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) :=
  (embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r).trans
    (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r hr hrU hpre hqre)

/-- The actual local factor has its canonical free presentation at any
basepoint whose literal normalized coordinate lies in the side overlap.
The basepoint condition only selects the two existing geometric side maps. -/
def embeddedTwoPunctureRelativeLocalDiskFreeEquiv
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hp : ‖(p : ℂ)‖ < r) (hq : ‖(q : ℂ)‖ < r) (hpq : p ≠ q)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hz : embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre z ∈
        twoPuncturedDiskRelativeOverlap (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) :
    FundamentalGroup {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} z ≃* FreeGroup Bool := by
  let H := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    f hf p q r hr hrU hpre hqre
  obtain ⟨hα, hα1, hβ, hβ1⟩ := embeddedTwoPunctureParameters_bounds p q r hr hp hq
  have hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r hr hpq hpre hqre
  exact (fundamentalGroupHomeomorphEquiv H z).trans
    (twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ ⟨H z, hz⟩)

/-- The relative overlap has its literal homeomorphism to the actual annular
overlap in the original surface. -/
def embeddedTwoPunctureRelativeOverlapHomeomorph (f : C(U, X.Carrier))
    (p q : U) (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} ≃ₜ
      {z : X.Carrier // z ∈
        embeddedTwoPunctureExterior f p q a haU ∩
          embeddedTwoPunctureLocalDisk f p q r} where
  toFun z := ⟨z.1.1, ⟨z.2.1, z.2.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1.2⟩, ⟨z.2.1, z.2.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual cover members cover the punctured ambient carrier. -/
theorem embeddedTwoPunctureAmbientRelative_cover (f : C(U, X.Carrier))
    (p q : U) (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (har : a < r) :
    embeddedTwoPunctureExteriorRelativeSide f p q a haU ∪
      embeddedTwoPunctureLocalDiskRelativeSide f p q r = Set.univ := by
  have hcover := embeddedTwoPuncture_exterior_union_local_eq_ambient f p q har haU
  ext z
  change (z.1 ∈ embeddedTwoPunctureExterior f p q a haU ∨
    z.1 ∈ embeddedTwoPunctureLocalDisk f p q r) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact (Set.ext_iff.mp hcover z.1).mp z.2

theorem embeddedTwoPunctureExteriorRelativeSide_pathConnected
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a : ℝ)
    (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o) :
    PathConnectedSpace
      {z : embeddedTwoPunctureAmbientPoint f p q //
        z ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU} := by
  letI : PathConnectedSpace
      {z : X.Carrier // z ∈ embeddedTwoPunctureExterior f p q a haU} :=
    embeddedDiskOpenCoverExterior_pathConnected hball f hf p q a hamax ha1 haU o hcenter B
  exact Function.Surjective.pathConnectedSpace
    (embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU).symm.surjective
    (embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU).symm.continuous

theorem embeddedTwoPunctureLocalDiskRelativeSide_pathConnected
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < r) (hq : ‖(q : ℂ)‖ < r) :
    PathConnectedSpace
      {z : embeddedTwoPunctureAmbientPoint f p q //
        z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} := by
  letI : PathConnectedSpace
      {z : X.Carrier // z ∈ embeddedTwoPunctureLocalDisk f p q r} :=
    embeddedTwoPunctureLocalDisk_pathConnected f hf p q r hr hrU
      hpre hqre hpq hp hq
  exact Function.Surjective.pathConnectedSpace
    (embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r).symm.surjective
    (embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r).symm.continuous

theorem embeddedTwoPunctureRelativeOverlap_pathConnected
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    PathConnectedSpace
      {z : embeddedTwoPunctureAmbientPoint f p q //
        z ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} := by
  letI : PathConnectedSpace
      {z : X.Carrier // z ∈
        embeddedTwoPunctureExterior f p q a haU ∩
          embeddedTwoPunctureLocalDisk f p q r} :=
    embeddedDiskOpenCoverOverlap_pathConnected f hf p q a r hamax ha1 hr1 haU hrU
  exact Function.Surjective.pathConnectedSpace
    (embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm.surjective
    (embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm.continuous

theorem embeddedTwoPunctureExteriorRelativeSide_isPathConnected
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a : ℝ)
    (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o) :
    IsPathConnected (embeddedTwoPunctureExteriorRelativeSide f p q a haU) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact embeddedTwoPunctureExteriorRelativeSide_pathConnected
    hball f hf p q a hamax ha1 haU o hcenter B

theorem embeddedTwoPunctureLocalDiskRelativeSide_isPathConnected
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < r) (hq : ‖(q : ℂ)‖ < r) :
    IsPathConnected (embeddedTwoPunctureLocalDiskRelativeSide f p q r) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact embeddedTwoPunctureLocalDiskRelativeSide_pathConnected
    f hf p q r hr hrU hpre hqre hpq hp hq

theorem embeddedTwoPunctureRelativeOverlap_isPathConnected
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    IsPathConnected (embeddedTwoPunctureRelativeOverlap f p q a r haU) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact embeddedTwoPunctureRelativeOverlap_pathConnected
    f hf p q a r hamax ha1 hr1 haU hrU

/-- The actual based amalgam of the relative exterior and local-disk groups. -/
abbrev embeddedTwoPunctureOpenCoverBasedAmalgam (f : C(U, X.Carrier))
    (p q : U) (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU}) :=
  twoOpenCoverFundamentalGroupAmalgam
    (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
    (embeddedTwoPunctureLocalDiskRelativeSide f p q r) z

/-- The canonical actual van Kampen equivalence for the embedded cover in
the original punctured surface carrier. -/
def embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U)
    (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU}) :
    embeddedTwoPunctureOpenCoverBasedAmalgam f p q a r haU z ≃*
      FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q) z.1 := by
  have hr : 0 < r := zero_lt_one.trans hr1
  have hpr : ‖(p : ℂ)‖ < r := hp.trans hr1
  have hqr : ‖(q : ℂ)‖ < r := hq.trans hr1
  have har : a < r := ha1.trans hr1
  exact twoOpenCoverFundamentalGroupAmalgamEquiv
    (embeddedTwoPunctureExteriorRelativeSide_isOpen f p q a haU)
    (embeddedTwoPunctureLocalDiskRelativeSide_isOpen f hf p q r)
    (embeddedTwoPunctureAmbientRelative_cover f p q a r haU har)
    (embeddedTwoPunctureExteriorRelativeSide_isPathConnected
      hball f hf p q a hamax ha1 haU o hcenter B)
    (embeddedTwoPunctureLocalDiskRelativeSide_isPathConnected
      f hf p q r hr hrU hpre hqre hpq hpr hqr)
    (embeddedTwoPunctureRelativeOverlap_isPathConnected
      f hf p q a r hamax ha1 hr1 haU hrU)
    z

@[simp]
theorem embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv_of
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U)
    (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU})
    (b : Bool) (γ : twoOpenCoverAmalgamSideGroup
      (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
      (embeddedTwoPunctureLocalDiskRelativeSide f p q r) z b) :
    embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv
      hball f hf p q a r hamax ha1 hr1 haU hrU o hcenter B
      hpre hqre hpq hp hq z (Monoid.PushoutI.of b γ) =
        twoOpenCoverSideToAmbient
          (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r) z b γ := by
  exact twoOpenCoverFundamentalGroupAmalgamEquiv_of
    (embeddedTwoPunctureExteriorRelativeSide_isOpen f p q a haU)
    (embeddedTwoPunctureLocalDiskRelativeSide_isOpen f hf p q r)
    (embeddedTwoPunctureAmbientRelative_cover f p q a r haU (ha1.trans hr1))
    (embeddedTwoPunctureExteriorRelativeSide_isPathConnected
      hball f hf p q a hamax ha1 haU o hcenter B)
    (embeddedTwoPunctureLocalDiskRelativeSide_isPathConnected f hf p q r
      (zero_lt_one.trans hr1) hrU hpre hqre hpq (hp.trans hr1) (hq.trans hr1))
    (embeddedTwoPunctureRelativeOverlap_isPathConnected f hf p q a r
      hamax ha1 hr1 haU hrU) z b γ

@[simp]
theorem embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv_base
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U)
    (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU})
    (γ : FundamentalGroup
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} z) :
    embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv
      hball f hf p q a r hamax ha1 hr1 haU hrU o hcenter B
      hpre hqre hpq hp hq z
      (Monoid.PushoutI.base
        (twoOpenCoverAmalgamSideMap
          (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r) z) γ) =
        twoOpenCoverOverlapToAmbient
          (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r) z γ := by
  exact twoOpenCoverFundamentalGroupAmalgamEquiv_base
    (embeddedTwoPunctureExteriorRelativeSide_isOpen f p q a haU)
    (embeddedTwoPunctureLocalDiskRelativeSide_isOpen f hf p q r)
    (embeddedTwoPunctureAmbientRelative_cover f p q a r haU (ha1.trans hr1))
    (embeddedTwoPunctureExteriorRelativeSide_isPathConnected
      hball f hf p q a hamax ha1 haU o hcenter B)
    (embeddedTwoPunctureLocalDiskRelativeSide_isPathConnected f hf p q r
      (zero_lt_one.trans hr1) hrU hpre hqre hpq (hp.trans hr1) (hq.trans hr1))
    (embeddedTwoPunctureRelativeOverlap_isPathConnected f hf p q a r
      hamax ha1 hr1 haU hrU) z γ

/-- Literal inclusion of the full exterior into the punctured ambient
carrier. -/
def embeddedTwoPunctureExteriorToAmbientPoint (f : C(U, X.Carrier))
    (p q : U) (a : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    C({z : X.Carrier // z ∈ embeddedTwoPunctureExterior f p q a haU},
      embeddedTwoPunctureAmbientPoint f p q) where
  toFun z := ⟨z.1, z.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Literal inclusion of the full local disk into the punctured ambient
carrier. -/
def embeddedTwoPunctureLocalDiskToAmbientPoint (f : C(U, X.Carrier))
    (p q : U) (r : ℝ) :
    C({z : X.Carrier // z ∈ embeddedTwoPunctureLocalDisk f p q r},
      embeddedTwoPunctureAmbientPoint f p q) where
  toFun z := ⟨z.1, z.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The actual annular overlap includes literally into the punctured
ambient carrier. -/
def embeddedTwoPunctureOverlapToAmbientPoint (f : C(U, X.Carrier))
    (p q : U) (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    C({z : X.Carrier // z ∈
        embeddedTwoPunctureExterior f p q a haU ∩
          embeddedTwoPunctureLocalDisk f p q r},
      embeddedTwoPunctureAmbientPoint f p q) where
  toFun z := ⟨z.1, z.2.1.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Forgetting the ambient subtype commutes with the literal exterior
inclusion. -/
theorem embeddedTwoPunctureExteriorRelativeHomeomorph_inclusion
    (f : C(U, X.Carrier)) (p q : U) (a : ℝ)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    (twoOpenCoverAmalgamInclusion
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)).comp
      ((embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU).symm :
        C({z : X.Carrier // z ∈ embeddedTwoPunctureExterior f p q a haU},
          {z : embeddedTwoPunctureAmbientPoint f p q //
            z ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU})) =
      embeddedTwoPunctureExteriorToAmbientPoint f p q a haU := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- Forgetting the ambient subtype commutes with the literal local-disk
inclusion. -/
theorem embeddedTwoPunctureLocalDiskRelativeHomeomorph_inclusion
    (f : C(U, X.Carrier)) (p q : U) (r : ℝ) :
    (twoOpenCoverAmalgamInclusion
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)).comp
      ((embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r).symm :
        C({z : X.Carrier // z ∈ embeddedTwoPunctureLocalDisk f p q r},
          {z : embeddedTwoPunctureAmbientPoint f p q //
            z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})) =
      embeddedTwoPunctureLocalDiskToAmbientPoint f p q r := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- The relative-overlap inclusion agrees with the literal actual overlap
inclusion. -/
theorem embeddedTwoPunctureRelativeOverlapHomeomorph_inclusion
    (f : C(U, X.Carrier)) (p q : U) (a r : ℝ)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) :
    (twoOpenCoverAmalgamInclusion
        (embeddedTwoPunctureRelativeOverlap f p q a r haU)).comp
      ((embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm :
        C({z : X.Carrier // z ∈
            embeddedTwoPunctureExterior f p q a haU ∩
              embeddedTwoPunctureLocalDisk f p q r},
          {z : embeddedTwoPunctureAmbientPoint f p q //
            z ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU})) =
      embeddedTwoPunctureOverlapToAmbientPoint f p q a r haU := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- The actual relative exterior group has the physical free basis imported
from the genuine punctured-surface exterior. -/
noncomputable def embeddedTwoPunctureRelativeExteriorFreeEquiv
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U) (a : ℝ)
    (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a) (ha1 : a < 1)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU}) :
    FundamentalGroup
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU} z ≃*
      FreeGroup B.IntrinsicBoundaryNonTreeEdge := by
  let H := embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU
  let F : C(
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU},
      {w : X.Carrier // w ∈ embeddedTwoPunctureExterior f p q a haU}) :=
    ⟨H, H.continuous⟩
  let e : ({w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU} ≃ₕ
      {w : X.Carrier // w ∈ embeddedTwoPunctureExterior f p q a haU}) :=
    H.toHomotopyEquiv
  let hff := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hbij : Function.Bijective (FundamentalGroup.map F z) :=
    hff.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
      (FundamentalGroupoid.mk z)
  let eGroup : FundamentalGroup
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU} z ≃*
      FundamentalGroup
        {w : X.Carrier // w ∈ embeddedTwoPunctureExterior f p q a haU} (F z) :=
    MulEquiv.ofBijective (FundamentalGroup.map F z) hbij
  exact eGroup.trans (embeddedDiskOpenCoverExteriorFreeEquiv
    hball f hf p q a hamax ha1 haU o hcenter B (H z))

/-- The actual relative annulus overlap group is the genuine coordinate-circle
group, with the basepoint transported by the actual chart and relative-side
homeomorphisms. -/
noncomputable def embeddedTwoPunctureRelativeOverlapCircleFundamentalGroupEquiv
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU}) :
    FundamentalGroup
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} z ≃*
      FundamentalGroup Circle
        (complexAnnulusCircleRetraction a r
          ((norm_nonneg (p : ℂ)).trans ((le_max_left _ _).trans hamax.le))
          ((embeddedTwoPunctureAnnulusHomeomorph f hf p q hamax haU hrU).symm
            ((embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU) z))) := by
  have ha0 : 0 ≤ a := (norm_nonneg (p : ℂ)).trans
    ((le_max_left _ _).trans hamax.le)
  let H := embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU
  let F : C(
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU},
      {w : X.Carrier // w ∈
        embeddedTwoPunctureExterior f p q a haU ∩
          embeddedTwoPunctureLocalDisk f p q r}) := ⟨H, H.continuous⟩
  let e : ({w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} ≃ₕ
      {w : X.Carrier // w ∈
        embeddedTwoPunctureExterior f p q a haU ∩
          embeddedTwoPunctureLocalDisk f p q r}) := H.toHomotopyEquiv
  let hff := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hbij : Function.Bijective (FundamentalGroup.map F z) :=
    hff.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk z)
      (FundamentalGroupoid.mk z)
  let eGroup : FundamentalGroup
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} z ≃*
      FundamentalGroup
        {w : X.Carrier // w ∈
          embeddedTwoPunctureExterior f p q a haU ∩
            embeddedTwoPunctureLocalDisk f p q r} (F z) :=
    MulEquiv.ofBijective (FundamentalGroup.map F z) hbij
  exact eGroup.trans (embeddedDiskOpenCoverOverlapFundamentalGroupEquiv
    f hf p q a r hamax ha1 hr1 haU hrU (F z))

/-- The unchanged positive coordinate boundary, in the native relative
overlap carrier used by the actual van Kampen diagram. -/
def embeddedTwoPunctureRelativeBoundaryCircle
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    C(Circle, {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU}) :=
  (⟨(embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm,
    (embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm.continuous⟩ :
      C(_, _)).comp
    (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU)

/-- The native relative overlap is generated by the literal positive
boundary circle. The equivalence's forward map is that literal inclusion. -/
def embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    FundamentalGroup Circle θ ≃*
      FundamentalGroup {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU}
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ) := by
  let G := embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU
  let H := (embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm
  let F : C(_, _) := ⟨H, H.continuous⟩
  have hG : Function.Bijective (FundamentalGroup.map G θ) :=
    (embeddedDiskOpenCoverOverlapBoundaryFundamentalGroupEquiv
      f hf p q a r ha ha1 hr1 haU hrU θ).bijective
  let hff := FundamentalGroupoidFunctor.equivOfHomotopyEquiv H.toHomotopyEquiv
  have hF : Function.Bijective (FundamentalGroup.map F (G θ)) :=
    hff.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk (G θ)) (FundamentalGroupoid.mk (G θ))
  have hcomp : FundamentalGroup.map
      (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) θ =
      (FundamentalGroup.map F (G θ)).comp (FundamentalGroup.map G θ) := by
    ext ξ
    obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective ξ
    rfl
  exact MulEquiv.ofBijective
    (FundamentalGroup.map
      (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) θ)
    (by rw [hcomp]; exact hF.comp hG)

/-- Its positive generator is the literal included one-turn loop, without
an inverse-defined representative or a basepoint-change premise. -/
theorem embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv_oneTurn
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv
      f hf p q a r ha ha1 hr1 haU hrU θ ⟦circleOneTurnLoop θ⟧ =
        ⟦(circleOneTurnLoop θ).map
          (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU).continuous⟧ := by
  rfl

/-- Mark the actual annulus overlap by its literal positive boundary turn.
This is the cyclic overlap marking used by the based surface amalgam. -/
def embeddedTwoPunctureRelativeOverlapFreeEquiv
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    FundamentalGroup {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU}
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ) ≃*
      FreeGroup Unit :=
  (embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv
    f hf p q a r ha ha1 hr1 haU hrU θ).symm.trans
      (circleFundamentalGroupFreeEquiv θ)

/-- The actual included positive circle, not an inverse-defined loop,
is sent to the positive free singleton generator. -/
theorem embeddedTwoPunctureRelativeOverlapFreeEquiv_oneTurn
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    embeddedTwoPunctureRelativeOverlapFreeEquiv
      f hf p q a r ha ha1 hr1 haU hrU θ
      ⟦(circleOneTurnLoop θ).map
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU).continuous⟧ =
      FreeGroup.of () := by
  let E := embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv
    f hf p q a r ha ha1 hr1 haU hrU θ
  have hturn := embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv_oneTurn
    f hf p q a r ha ha1 hr1 haU hrU θ
  have h := congrArg (fun ξ => circleFundamentalGroupFreeEquiv θ (E.symm ξ)) hturn
  change circleFundamentalGroupFreeEquiv θ (E.symm _) = _
  calc
    _ = circleFundamentalGroupFreeEquiv θ
        (E.symm (E (⟦circleOneTurnLoop θ⟧ : FundamentalGroup Circle θ))) := h.symm
    _ = circleFundamentalGroupFreeEquiv θ ⟦circleOneTurnLoop θ⟧ :=
      congrArg (circleFundamentalGroupFreeEquiv θ) (E.symm_apply_apply _)
    _ = FreeGroup.of () := circleFundamentalGroupFreeEquiv_oneTurn θ

/-- Evaluating the inverse cyclic marking at the generator recovers the
same literal positive boundary loop for checking the amalgam diagram. -/
theorem embeddedTwoPunctureRelativeOverlapFreeEquiv_symm_of
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    (embeddedTwoPunctureRelativeOverlapFreeEquiv
      f hf p q a r ha ha1 hr1 haU hrU θ).symm (FreeGroup.of ()) =
      ⟦(circleOneTurnLoop θ).map
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU).continuous⟧ := by
  apply (embeddedTwoPunctureRelativeOverlapFreeEquiv
    f hf p q a r ha ha1 hr1 haU hrU θ).injective
  rw [MulEquiv.apply_symm_apply, embeddedTwoPunctureRelativeOverlapFreeEquiv_oneTurn]

/-- The native local side sends the literal relative annulus boundary to the
same local chart boundary used by the normalized outer-circle comparison. -/
theorem embeddedTwoPunctureRelativeBoundaryCircle_localSide
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    ((⟨embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r,
        (embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r).continuous⟩ : C(_, _)).comp
      (twoOpenCoverAmalgamOverlapRight
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r))).comp
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) =
      (embeddedDiskOpenCoverOverlapToLocalDisk f p q a r haU).comp
        (embeddedDiskOpenCoverOverlapBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) := by
  apply ContinuousMap.ext
  intro θ
  rfl

/-- The native local side, in its literal normalized coordinates, sends the
same annulus boundary to the actual positive outer circle. -/
theorem embeddedTwoPunctureRelativeBoundaryCircle_normalizedLocalSide
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    (⟨embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r
        (zero_lt_one.trans hr1) hrU hpre hqre,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r
        (zero_lt_one.trans hr1) hrU hpre hqre).continuous⟩ : C(_, _)).comp
      ((twoOpenCoverAmalgamOverlapRight
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)).comp
          (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU)) =
      twoPuncturedDiskOuterBoundaryCircle (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) r⁻¹
        ((embeddedTwoPunctureParameters_abs_lt_inv p q (zero_lt_one.trans hr1)
          (((le_max_left _ _).trans_lt ha).trans ha1)
          (((le_max_right _ _).trans_lt ha).trans ha1)).1)
        ((embeddedTwoPunctureParameters_abs_lt_inv p q (zero_lt_one.trans hr1)
          (((le_max_left _ _).trans_lt ha).trans ha1)
          (((le_max_right _ _).trans_lt ha).trans ha1)).2)
        ((inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1) := by
  rw [← embeddedDiskOpenCoverOverlapToLocalDisk_normalizedBoundary
    f hf p q a r ha ha1 hr1 haU hrU hpre hqre]
  apply ContinuousMap.ext
  intro θ
  rfl

/-- The actual right crossing of the annulus boundary is an admissible
basepoint for the two geometric local factors. Its overlap membership is
proved from the literal outer-circle construction, not supplied as input. -/
theorem embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (hpq : p ≠ q)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
      (zero_lt_one.trans hr1) hpq hpre hqre
    let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
      (zero_lt_one.trans hr1)
      (((le_max_left _ _).trans_lt ha).trans ha1)
      (((le_max_right _ _).trans_lt ha).trans ha1)
    let hR := (inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1
    let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
    embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r
      (zero_lt_one.trans hr1) hrU hpre hqre
      (twoOpenCoverAmalgamOverlapRight
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ)) ∈
      twoPuncturedDiskRelativeOverlap (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) := by
  dsimp only
  let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
    (zero_lt_one.trans hr1) hpq hpre hqre
  let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
    (zero_lt_one.trans hr1)
    (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1)
  let hR := (inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1
  let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
  have hcircle := congrArg (fun F : C(Circle, _) => F θ)
    (embeddedTwoPunctureRelativeBoundaryCircle_normalizedLocalSide
      f hf p q a r ha ha1 hr1 haU hrU hpre hqre)
  have hcircle' : embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre
      (twoOpenCoverAmalgamOverlapRight
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ)) =
      twoPuncturedDiskOuterBoundaryCircle (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) r⁻¹ hnorms.1 hnorms.2 hR θ := hcircle
  rw [hcircle']
  have hpoint : twoPuncturedDiskOuterBoundaryCircle
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r) r⁻¹ hnorms.1 hnorms.2 hR θ =
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hnorms.1 hnorms.2 hR).1 := by
    have h := twoPuncturedDiskOuterRightToLeftArc_apply
      hαβ hnorms.1 hnorms.2 hR 0
    simpa [θ, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph] using h.symm
  rw [hpoint]
  exact (twoPuncturedDiskOuterRightOverlapPoint hαβ hnorms.1 hnorms.2 hR).2

/-- The native exterior side sends that same positive relative boundary to
the untouched smaller-exterior boundary already marked by the inverse
surface relator. Both sides use one common annulus basepoint. -/
theorem embeddedTwoPunctureRelativeBoundaryCircle_exteriorSide
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    ((⟨embeddedDiskOpenCoverExteriorHomeomorph f p q a ha haU,
        (embeddedDiskOpenCoverExteriorHomeomorph f p q a ha haU).continuous⟩ : C(_, _)).comp
      ((⟨embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU,
          (embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU).continuous⟩ : C(_, _)).comp
        (twoOpenCoverAmalgamOverlapLeft
          (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)))).comp
      (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU) =
      embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 := by
  apply ContinuousMap.ext
  intro θ
  rfl

/-- The exterior factor at the literal overlap boundary point is identified
with the actual smaller closed-disk exterior at that same boundary point.
This transports its proved inverse-relator marking without a conjugator. -/
def embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    FundamentalGroup {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureExteriorRelativeSide f p q a haU}
      (twoOpenCoverAmalgamOverlapLeft
        (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ)) ≃*
      FundamentalGroup (embeddedCoordinateClosedDiskExterior f a)
        (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1 θ) :=
  fundamentalGroupHomeomorphEquiv
    ((embeddedTwoPunctureExteriorRelativeHomeomorph f p q a haU).trans
      (embeddedDiskOpenCoverExteriorHomeomorph f p q a ha haU))
    (twoOpenCoverAmalgamOverlapLeft
      (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
      (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
      (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU θ))

/-- The native exterior-side generator is sent to the unchanged positive
smaller-exterior loop already used by the actual inverse-relator marking. -/
theorem embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv_oneTurn
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (θ : Circle) :
    embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv
      hball f hf p q a r ha ha1 hr1 haU hrU θ
      ⟦((circleOneTurnLoop θ).map
        (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 hr1 haU hrU).continuous).map
          (twoOpenCoverAmalgamOverlapLeft
            (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
            (embeddedTwoPunctureLocalDiskRelativeSide f p q r)).continuous⟧ =
      ⟦(circleOneTurnLoop θ).map
        (embeddedSurfaceClosedDiskExteriorBoundaryCircle hball f hf a ha1).continuous⟧ := by
  rfl

/-- A concrete point of the actual annular overlap, obtained by mapping the
positive real coordinate `1` through the chart annulus homeomorphism. -/
def embeddedTwoPunctureOpenCoverAnnulusBasepoint
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    {z : X.Carrier // z ∈
      embeddedTwoPunctureExterior f p q a haU ∩
        embeddedTwoPunctureLocalDisk f p q r} :=
  embeddedTwoPunctureAnnulusHomeomorph f hf p q hamax haU hrU
    ⟨1, by
      change a < ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ < r
      simpa using ⟨ha1, hr1⟩⟩

/-- The same annulus basepoint represented in the relative overlap subtype of
the original two-punctured surface. -/
def embeddedTwoPunctureOpenCoverRelativeAnnulusBasepoint
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) :
    {z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureRelativeOverlap f p q a r haU} :=
  (embeddedTwoPunctureRelativeOverlapHomeomorph f p q a r haU).symm
    (embeddedTwoPunctureOpenCoverAnnulusBasepoint f hf p q a r hamax
      ha1 hr1 haU hrU)

/-- The actual based van Kampen equivalence for the exterior/local-disk cover,
based at the image of the annulus coordinate `1`. -/
noncomputable def embeddedTwoPunctureDiskVanKampenAtAnnulusBasepoint
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U) (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U)
    (a r : ℝ) (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U) (o : ℍ)
    (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) (hpq : p ≠ q)
    (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1) :
    embeddedTwoPunctureOpenCoverBasedAmalgam f p q a r haU
        (embeddedTwoPunctureOpenCoverRelativeAnnulusBasepoint f hf p q a r
          hamax ha1 hr1 haU hrU) ≃*
      FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q)
        (embeddedTwoPunctureOpenCoverRelativeAnnulusBasepoint f hf p q a r
          hamax ha1 hr1 haU hrU).1 :=
  embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv hball f hf p q
    a r hamax ha1 hr1 haU hrU o hcenter B hpre hqre hpq hp hq _

/-- From a genuine open chart containing the closed unit disk, obtain actual
nested radii and the based relative-cover van Kampen equivalence. -/
theorem exists_embeddedTwoPunctureDiskVanKampenAtAnnulusBasepoint
    (hU : IsOpen U) (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, X.Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → X.Carrier)) (p q : U)
    (hpq : p ≠ q) (hp : ‖(p : ℂ)‖ < 1) (hq : ‖(q : ℂ)‖ < 1)
    (o : ℍ) (hcenter : embeddedCoordinatePunctureCenter hball f =
      (Quotient.mk'' o : X.Carrier)) (B : DirichletBoundarySegments X o)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    ∃ (a r : ℝ) (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
      (hrU : Metric.closedBall (0 : ℂ) r ⊆ U),
      ∃ (hamax : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a),
        ∃ (ha1 : a < 1), ∃ (hr1 : 1 < r),
          Nonempty (embeddedTwoPunctureOpenCoverBasedAmalgam f p q a r haU
              (embeddedTwoPunctureOpenCoverRelativeAnnulusBasepoint f hf p q
                a r hamax ha1 hr1 haU hrU) ≃*
            FundamentalGroup (embeddedTwoPunctureAmbientPoint f p q)
              (embeddedTwoPunctureOpenCoverRelativeAnnulusBasepoint f hf p q
                a r hamax ha1 hr1 haU hrU).1) := by
  obtain ⟨a, r, haU, hrU, hamax, ha1, hr1, _hfpq, _hEopen, _hDopen,
      _hcover, _hoverlap, _hannulus⟩ :=
    exists_embeddedTwoPunctureDiskOpenCover hU hball f hf p q hpq hp hq
  refine ⟨a, r, haU, hrU, hamax, ha1, hr1, ?_⟩
  exact ⟨embeddedTwoPunctureDiskVanKampenAtAnnulusBasepoint
    hball f hf p q a r hamax ha1 hr1 haU hrU o hcenter B
    hpre hqre hpq hp hq⟩

#print axioms embeddedTwoPunctureOpenCoverFundamentalGroupAmalgamEquiv
#print axioms embeddedTwoPunctureRelativeExteriorFreeEquiv
#print axioms embeddedTwoPunctureRelativeOverlapCircleFundamentalGroupEquiv
#print axioms exists_embeddedTwoPunctureDiskVanKampenAtAnnulusBasepoint
#print axioms embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv
#print axioms embeddedTwoPunctureRelativeBoundaryFundamentalGroupEquiv_oneTurn
#print axioms embeddedTwoPunctureRelativeOverlapFreeEquiv
#print axioms embeddedTwoPunctureRelativeOverlapFreeEquiv_oneTurn
#print axioms embeddedTwoPunctureRelativeOverlapFreeEquiv_symm_of
#print axioms embeddedTwoPunctureRelativeBoundaryCircle_localSide
#print axioms embeddedTwoPunctureRelativeBoundaryCircle_exteriorSide
#print axioms embeddedTwoPunctureRelativeLocalDiskFreeEquiv
#print axioms embeddedTwoPunctureRelativeBoundaryCircle_normalizedLocalSide
#print axioms embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
#print axioms embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv
#print axioms embeddedTwoPunctureRelativeExteriorBoundaryGroupEquiv_oneTurn

end

end SystolicGrowth
