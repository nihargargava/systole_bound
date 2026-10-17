module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoOpenCoverAmalgamEquiv
public import Geometry.TwoPuncturedDiskOpenCover
public import Geometry.TwoPuncturedDiskSideCircle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Van Kampen for the actual twice-punctured unit disk

The lower and upper sets are literal preimages of the two actual sides in the
twice-punctured disk. Their based group amalgam maps canonically to the
fundamental group of that original carrier.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth

noncomputable section

/-- The actual twice-punctured disk as a topological carrier. -/
abbrev twoPuncturedUnitDiskPoint (α β : ℝ) :=
  {z : ℂ // z ∈ twoPuncturedUnitDisk α β}

/-- The lower open set, defined as the preimage of the actual lower side in
the twice-punctured disk carrier. -/
def twoPuncturedDiskLowerRelativeSide (α β : ℝ) :
    Set (twoPuncturedUnitDiskPoint α β) :=
  (Subtype.val : twoPuncturedUnitDiskPoint α β → ℂ) ⁻¹'
    twoPuncturedDiskLowerSide α β

/-- The upper open set, defined as the preimage of the actual upper side in
the twice-punctured disk carrier. -/
def twoPuncturedDiskUpperRelativeSide (α β : ℝ) :
    Set (twoPuncturedUnitDiskPoint α β) :=
  (Subtype.val : twoPuncturedUnitDiskPoint α β → ℂ) ⁻¹'
    twoPuncturedDiskUpperSide α β

/-- The literal relative overlap of the two open sides. -/
abbrev twoPuncturedDiskRelativeOverlap (α β : ℝ) :=
  twoPuncturedDiskLowerRelativeSide α β ∩ twoPuncturedDiskUpperRelativeSide α β

theorem twoPuncturedDiskLowerRelativeSide_isOpen (α β : ℝ) :
    IsOpen (twoPuncturedDiskLowerRelativeSide α β) :=
  (twoPuncturedDiskLowerSide_isOpen α β).preimage continuous_subtype_val

theorem twoPuncturedDiskUpperRelativeSide_isOpen (α β : ℝ) :
    IsOpen (twoPuncturedDiskUpperRelativeSide α β) :=
  (twoPuncturedDiskUpperSide_isOpen α β).preimage continuous_subtype_val

/-- The actual lower and upper preimages cover every point of the punctured
disk carrier. -/
theorem twoPuncturedDisk_relativeCover {α β : ℝ} (hαβ : α < β) :
    twoPuncturedDiskLowerRelativeSide α β ∪ twoPuncturedDiskUpperRelativeSide α β =
      Set.univ := by
  ext z
  change (z.1 ∈ twoPuncturedDiskLowerSide α β ∨
      z.1 ∈ twoPuncturedDiskUpperSide α β) ↔ True
  constructor
  · intro _
    trivial
  · intro _
    exact (Set.ext_iff.mp (twoPuncturedDisk_lower_upper_cover hαβ) z.1).mp z.2

/-- The lower relatively open side is homeomorphic to the actual full lower
side, by forgetting only the ambient disk subtype. -/
def twoPuncturedDiskLowerSideHomeomorph {α β : ℝ} (hαβ : α < β) :
    {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskLowerRelativeSide α β} ≃ₜ
      {z : ℂ // z ∈ twoPuncturedDiskLowerSide α β} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z := ⟨⟨z.1, twoPuncturedDiskLowerSide_subset_domain hαβ z.2⟩, z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The upper relatively open side is homeomorphic to the actual full upper
side, by forgetting only the ambient disk subtype. -/
def twoPuncturedDiskUpperSideHomeomorph {α β : ℝ} (hαβ : α < β) :
    {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskUpperRelativeSide α β} ≃ₜ
      {z : ℂ // z ∈ twoPuncturedDiskUpperSide α β} where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z := ⟨⟨z.1, twoPuncturedDiskUpperSide_subset_domain hαβ z.2⟩, z.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The relative overlap is homeomorphic to the actual open strip in the
complex plane. -/
def twoPuncturedDiskOverlapHomeomorph {α β : ℝ} (hαβ : α < β) :
    {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β} ≃ₜ
      {z : ℂ // z ∈ twoPuncturedDiskOverlap α β} where
  toFun z := ⟨z.1.1, by
    have hsides : z.1.1 ∈
        twoPuncturedDiskLowerSide α β ∩ twoPuncturedDiskUpperSide α β :=
      ⟨z.2.1, z.2.2⟩
    exact (Set.ext_iff.mp (twoPuncturedDisk_overlap_eq_strip hαβ) z.1.1).mp hsides⟩
  invFun z := by
    have hsides : z.1 ∈
        twoPuncturedDiskLowerSide α β ∩ twoPuncturedDiskUpperSide α β := by
      exact (Set.ext_iff.mp (twoPuncturedDisk_overlap_eq_strip hαβ) z.1).mpr z.2
    exact ⟨⟨z.1, twoPuncturedDiskLowerSide_subset_domain hαβ hsides.1⟩,
      ⟨hsides.1, hsides.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The lower relative side is path connected by its homeomorphism to the
actual punctured lower base. -/
theorem twoPuncturedDiskLowerRelativeSide_pathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    PathConnectedSpace
      {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskLowerRelativeSide α β} := by
  letI : PathConnectedSpace {z : ℂ // z ∈ twoPuncturedDiskLowerSide α β} := by
    change PathConnectedSpace
      (puncturedBaseAt (twoPuncturedDiskLowerBase α β)
        (twoPuncturedDiskLeftCenter α))
    exact twoPuncturedDiskLowerSide_pathConnected hα hα1 hαβ
  exact Function.Surjective.pathConnectedSpace
    (twoPuncturedDiskLowerSideHomeomorph hαβ).symm.surjective
    (twoPuncturedDiskLowerSideHomeomorph hαβ).symm.continuous

/-- The upper relative side is path connected by its homeomorphism to the
actual punctured upper base. -/
theorem twoPuncturedDiskUpperRelativeSide_pathConnected {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    PathConnectedSpace
      {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskUpperRelativeSide α β} := by
  letI : PathConnectedSpace {z : ℂ // z ∈ twoPuncturedDiskUpperSide α β} := by
    change PathConnectedSpace
      (puncturedBaseAt (twoPuncturedDiskUpperBase α β)
        (twoPuncturedDiskRightCenter β))
    exact twoPuncturedDiskUpperSide_pathConnected hβ hβ1 hαβ
  exact Function.Surjective.pathConnectedSpace
    (twoPuncturedDiskUpperSideHomeomorph hαβ).symm.surjective
    (twoPuncturedDiskUpperSideHomeomorph hαβ).symm.continuous

theorem twoPuncturedDiskLowerRelativeSide_isPathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    IsPathConnected (twoPuncturedDiskLowerRelativeSide α β) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact twoPuncturedDiskLowerRelativeSide_pathConnected hα hα1 hαβ

theorem twoPuncturedDiskUpperRelativeSide_isPathConnected {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    IsPathConnected (twoPuncturedDiskUpperRelativeSide α β) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact twoPuncturedDiskUpperRelativeSide_pathConnected hβ hβ1 hαβ

/-- The actual relative overlap is path connected via its homeomorphism to
the convex open strip. -/
theorem twoPuncturedDiskRelativeOverlap_pathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) :
    PathConnectedSpace
      {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskRelativeOverlap α β} := by
  letI : PathConnectedSpace {z : ℂ // z ∈ twoPuncturedDiskOverlap α β} :=
    twoPuncturedDiskOverlap_pathConnected hα hα1 hβ hβ1 hαβ
  exact Function.Surjective.pathConnectedSpace
    (twoPuncturedDiskOverlapHomeomorph hαβ).symm.surjective
    (twoPuncturedDiskOverlapHomeomorph hαβ).symm.continuous

theorem twoPuncturedDiskRelativeOverlap_isPathConnected {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) : IsPathConnected (twoPuncturedDiskRelativeOverlap α β) := by
  rw [isPathConnected_iff_pathConnectedSpace]
  exact twoPuncturedDiskRelativeOverlap_pathConnected hα hα1 hβ hβ1 hαβ

/-- The actual relative overlap has trivial fundamental group at each of its
points, because it is homeomorphic to the actual convex strip. -/
theorem twoPuncturedDiskRelativeOverlap_fundamentalGroup_subsingleton
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    Subsingleton (FundamentalGroup
      {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskRelativeOverlap α β} q) := by
  let e := (twoPuncturedDiskOverlapHomeomorph hαβ).toHomotopyEquiv
  let h := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  have hbij : Function.Bijective (FundamentalGroup.map e.toFun q) :=
    h.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk q)
      (FundamentalGroupoid.mk q)
  letI : Subsingleton
      (FundamentalGroup (twoPuncturedDiskOverlap α β) (e.toFun q)) :=
    twoPuncturedDiskOverlap_fundamentalGroup_subsingleton
      hα hα1 hβ hβ1 hαβ (e.toFun q)
  refine ⟨fun a b => hbij.injective ?_⟩
  exact Subsingleton.elim _ _

/-- The literal inclusion of the full lower side into the actual punctured
disk carrier. -/
def twoPuncturedDiskLowerSideToDisk {α β : ℝ} (hαβ : α < β) :
    C({z : ℂ // z ∈ twoPuncturedDiskLowerSide α β},
      twoPuncturedUnitDiskPoint α β) where
  toFun z := ⟨z.1, twoPuncturedDiskLowerSide_subset_domain hαβ z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The literal inclusion of the full upper side into the actual punctured
disk carrier. -/
def twoPuncturedDiskUpperSideToDisk {α β : ℝ} (hαβ : α < β) :
    C({z : ℂ // z ∈ twoPuncturedDiskUpperSide α β},
      twoPuncturedUnitDiskPoint α β) where
  toFun z := ⟨z.1, twoPuncturedDiskUpperSide_subset_domain hαβ z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Forgetting the disk subtype commutes with the literal lower inclusion. -/
theorem twoPuncturedDiskLowerSideHomeomorph_inclusion {α β : ℝ} (hαβ : α < β) :
    (twoOpenCoverAmalgamInclusion (twoPuncturedDiskLowerRelativeSide α β)).comp
        ((twoPuncturedDiskLowerSideHomeomorph hαβ).symm :
          C({z : ℂ // z ∈ twoPuncturedDiskLowerSide α β},
            {z : twoPuncturedUnitDiskPoint α β //
              z ∈ twoPuncturedDiskLowerRelativeSide α β})) =
      twoPuncturedDiskLowerSideToDisk hαβ := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- Forgetting the disk subtype commutes with the literal upper inclusion. -/
theorem twoPuncturedDiskUpperSideHomeomorph_inclusion {α β : ℝ} (hαβ : α < β) :
    (twoOpenCoverAmalgamInclusion (twoPuncturedDiskUpperRelativeSide α β)).comp
        ((twoPuncturedDiskUpperSideHomeomorph hαβ).symm :
          C({z : ℂ // z ∈ twoPuncturedDiskUpperSide α β},
            {z : twoPuncturedUnitDiskPoint α β //
              z ∈ twoPuncturedDiskUpperRelativeSide α β})) =
      twoPuncturedDiskUpperSideToDisk hαβ := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- The actual based side-group amalgam over the relative overlap. -/
abbrev twoPuncturedDiskBasedAmalgam (α β : ℝ)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :=
  twoOpenCoverFundamentalGroupAmalgam
    (twoPuncturedDiskLowerRelativeSide α β)
    (twoPuncturedDiskUpperRelativeSide α β) q

/-- The canonical actual van Kampen equivalence from the relative-side
amalgam to the fundamental group of the original twice-punctured disk. -/
def twoPuncturedDiskFundamentalGroupAmalgamEquiv {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskBasedAmalgam α β q ≃*
      FundamentalGroup (twoPuncturedUnitDiskPoint α β) q.1 :=
  twoOpenCoverFundamentalGroupAmalgamEquiv
    (twoPuncturedDiskLowerRelativeSide_isOpen α β)
    (twoPuncturedDiskUpperRelativeSide_isOpen α β)
    (twoPuncturedDisk_relativeCover hαβ)
    (twoPuncturedDiskLowerRelativeSide_isPathConnected hα hα1 hαβ)
    (twoPuncturedDiskUpperRelativeSide_isPathConnected hβ hβ1 hαβ)
    (twoPuncturedDiskRelativeOverlap_isPathConnected hα hα1 hβ hβ1 hαβ)
    q

/-- Each factor of the actual amalgam is sent to precisely its literal
inclusion-induced homomorphism into the original disk group. -/
@[simp]
theorem twoPuncturedDiskFundamentalGroupAmalgamEquiv_of {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (b : Bool) (γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q b) :
    twoPuncturedDiskFundamentalGroupAmalgamEquiv hα hα1 hβ hβ1 hαβ q
      (Monoid.PushoutI.of b γ) =
        twoOpenCoverSideToAmbient (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q b γ := by
  exact twoOpenCoverFundamentalGroupAmalgamEquiv_of
    (twoPuncturedDiskLowerRelativeSide_isOpen α β)
    (twoPuncturedDiskUpperRelativeSide_isOpen α β)
    (twoPuncturedDisk_relativeCover hαβ)
    (twoPuncturedDiskLowerRelativeSide_isPathConnected hα hα1 hαβ)
    (twoPuncturedDiskUpperRelativeSide_isPathConnected hβ hβ1 hαβ)
    (twoPuncturedDiskRelativeOverlap_isPathConnected hα hα1 hβ hβ1 hαβ)
    q b γ

/-- The overlap factor is carried to the literal ambient inclusion map. -/
@[simp]
theorem twoPuncturedDiskFundamentalGroupAmalgamEquiv_base {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (γ : FundamentalGroup
      {z : twoPuncturedUnitDiskPoint α β //
        z ∈ twoPuncturedDiskRelativeOverlap α β} q) :
    twoPuncturedDiskFundamentalGroupAmalgamEquiv hα hα1 hβ hβ1 hαβ q
      (Monoid.PushoutI.base (twoOpenCoverAmalgamSideMap
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q) γ) =
      twoOpenCoverOverlapToAmbient (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q γ := by
  exact twoOpenCoverFundamentalGroupAmalgamEquiv_base
    (twoPuncturedDiskLowerRelativeSide_isOpen α β)
    (twoPuncturedDiskUpperRelativeSide_isOpen α β)
    (twoPuncturedDisk_relativeCover hαβ)
    (twoPuncturedDiskLowerRelativeSide_isPathConnected hα hα1 hαβ)
    (twoPuncturedDiskUpperRelativeSide_isPathConnected hβ hβ1 hαβ)
    (twoPuncturedDiskRelativeOverlap_isPathConnected hα hα1 hβ hβ1 hαβ)
    q γ

end

end SystolicGrowth
