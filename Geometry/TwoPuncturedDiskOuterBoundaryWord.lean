module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoPuncturedDiskGeometricGenerators
public import Geometry.TwoPuncturedDiskOuterTraversal

@[expose] public section

/-!
# The actual outer-boundary word of the twice-punctured disk

This module compares the literal outer boundary traversal with the two
positive peripheral generators supplied by the actual half-disk retractions.
The connector is kept as the specific straight path in the open overlap.
-/

open Set
open scoped ContinuousMap Topology unitInterval

namespace SystolicGrowth

noncomputable section

def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.pathIntoSubtype {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    {x y : Y} (p : Path x y) (hmem : ∀ t, p t ∈ A) :
    Path (⟨x, p.source ▸ hmem 0⟩ : {z : Y // z ∈ A})
      (⟨y, p.target ▸ hmem 1⟩ : {z : Y // z ∈ A}) where
  toFun t := ⟨p t, hmem t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- Include the literal relative overlap into the upper side. -/
def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper {α β : ℝ} :
    C({z : twoPuncturedUnitDiskPoint α β //
        z ∈ twoPuncturedDiskRelativeOverlap α β},
      twoPuncturedDiskUpperRelativePoint α β) where
  toFun q := ⟨q.1, q.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Include the literal relative overlap into the lower side. -/
def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower {α β : ℝ} :
    C({z : twoPuncturedUnitDiskPoint α β //
        z ∈ twoPuncturedDiskRelativeOverlap α β},
      twoPuncturedDiskLowerRelativePoint α β) where
  toFun q := ⟨q.1, q.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The actual upper-side radial normalization, written on its literal
relative carrier. -/
noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β) :
    C(twoPuncturedDiskUpperRelativePoint α β, Circle) := by
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  let E := twoPuncturedDiskUpperSideHomotopyEquiv hβ hβ1 hαβ
  exact ⟨fun z => E (H z), E.continuous.comp H.continuous_toFun⟩

set_option backward.isDefEq.respectTransparency false in
private theorem twoPuncturedDiskOuterUpperRadialMap_apply {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (z : twoPuncturedDiskUpperRelativePoint α β) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ z =
      convexPuncturedUnitDirection (z.1.1 - twoPuncturedDiskRightCenter β)
        (by
          intro hz
          exact z.2.2 (sub_eq_zero.mp hz)) := by
  change (twoPuncturedDiskUpperSideHomotopyEquiv hβ hβ1 hαβ
    (twoPuncturedDiskUpperSideHomeomorph hαβ z)) = _
  rw [twoPuncturedDiskUpperSideHomotopyEquiv_apply]
  rfl

private theorem twoPuncturedDiskOuterCutVectors_reflect {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskRightCenter β =
      -star ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskRightCenter β) := by
  apply Complex.ext
  · simp [twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterLeftCutPoint,
      twoPuncturedDiskOuterCutHeight, twoPuncturedDiskRightCenter]
  · simp [twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterLeftCutPoint,
      twoPuncturedDiskOuterCutHeight, twoPuncturedDiskRightCenter]
    ring

noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRightDirection
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Circle := convexPuncturedUnitDirection
      ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskRightCenter β) (by
          intro hz
          exact (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).2.2.2
            (sub_eq_zero.mp hz))

noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperLeftDirection
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Circle := convexPuncturedUnitDirection
      ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskRightCenter β) (by
          intro hz
          exact (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).2.2.2
            (sub_eq_zero.mp hz))

private theorem twoPuncturedDiskOuterUpperRightDirection_re_pos
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    0 < (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRightDirection hαβ hαR hβR hR : ℂ).re := by
  let v := (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 -
    twoPuncturedDiskRightCenter β
  have hv : v ≠ 0 := by
    intro hz
    exact (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).2.2.2
      (sub_eq_zero.mp hz)
  have hs : 0 < twoPuncturedDiskOuterCutHalfWidth α β R :=
    twoPuncturedDiskOuterCutHalfWidth_pos hαβ hαR hβR
  have hvr : v.re = twoPuncturedDiskOuterCutHalfWidth α β R := by
    simp [v, twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterCutHeight,
      twoPuncturedDiskRightCenter]
  change 0 < (‖v‖⁻¹ • v).re
  have hcoord : (‖v‖⁻¹ • v).re = ‖v‖⁻¹ * v.re := by
    change ((↑(‖v‖⁻¹) : ℂ) * v).re = _
    rw [Complex.mul_re]
    simp
  rw [hcoord, hvr]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hv)) hs

private theorem twoPuncturedDiskOuterUpperDirections_reflect
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperLeftDirection hαβ hαR hβR hR : ℂ) =
      -star (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRightDirection hαβ hαR hβR hR : ℂ) := by
  have hvec := twoPuncturedDiskOuterCutVectors_reflect hαβ hαR hβR hR
  change ‖(twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskRightCenter β‖⁻¹ •
        ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
          twoPuncturedDiskRightCenter β) = _
  rw [hvec, norm_neg, norm_star]
  rw [smul_neg]
  congr 1
  simp [Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRightDirection, convexPuncturedUnitDirection]

private theorem twoPuncturedDiskOuterUpperRadialMap_endpoints
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)) =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRightDirection hαβ hαR hβR hR ∧
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)) =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperLeftDirection hαβ hαR hβR hR := by
  constructor <;> rw [twoPuncturedDiskOuterUpperRadialMap_apply]
  · congr 1
  · congr 1

/-- Radial normalization of the literal upper outer arc, with its endpoint
proofs tied to the overlap's chosen inclusions. -/
noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let arc := twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR
  let hArc := fun t => twoPuncturedDiskOuterRightToLeftArc_mem_upperRelativeSide
    hαβ hαR hβR hR t
  let arcSide := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.pathIntoSubtype arc hArc
  have hpointR : qR.1 = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qR, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  have hpointL : qL.1 = twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qL, twoPuncturedDiskOuterLeftOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  let arcStart : twoPuncturedDiskUpperRelativePoint α β :=
    ⟨twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR, arc.source ▸ hArc 0⟩
  let arcFinish : twoPuncturedDiskUpperRelativePoint α β :=
    ⟨twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR, arc.target ▸ hArc 1⟩
  have hstart : twoPuncturedDiskUpperRelativePointOfOverlap qR = arcStart := by
    apply Subtype.ext
    exact hpointR
  have hfinish : twoPuncturedDiskUpperRelativePointOfOverlap qL = arcFinish := by
    apply Subtype.ext
    exact hpointL
  exact (arcSide.cast hstart hfinish).map
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ).continuous

/-- Radial normalization of the actual straight overlap connector, included
in the upper side. -/
noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let chord := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR).map
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper.continuous
  have hchord : twoPuncturedDiskUpperRelativePointOfOverlap qR =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper qR := by
    apply Subtype.ext
    rfl
  have hchord' : twoPuncturedDiskUpperRelativePointOfOverlap qL =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper qL := by
    apply Subtype.ext
    rfl
  exact (chord.cast hchord hchord').map
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ).continuous

/-- The upper cap boundary: positive outer arc, then the straight overlap
chord back to the right cut point. -/
def twoPuncturedDiskOuterUpperCapLoop {α β R : ℝ}
    (_hα : -1 < α) (_hα1 : α < 1) (_hβ : -1 < β) (_hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path
      (twoPuncturedDiskUpperRelativePointOfOverlap
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR))
      (twoPuncturedDiskUpperRelativePointOfOverlap
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let arc := twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR
  let hArc := fun t => twoPuncturedDiskOuterRightToLeftArc_mem_upperRelativeSide
    hαβ hαR hβR hR t
  let arcSide := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.pathIntoSubtype arc hArc
  have hpointR : qR.1 = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qR, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  have hpointL : qL.1 = twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qL, twoPuncturedDiskOuterLeftOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  let arcStart : twoPuncturedDiskUpperRelativePoint α β :=
    ⟨twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR, arc.source ▸ hArc 0⟩
  let arcFinish : twoPuncturedDiskUpperRelativePoint α β :=
    ⟨twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR, arc.target ▸ hArc 1⟩
  have hstart : twoPuncturedDiskUpperRelativePointOfOverlap qR = arcStart := by
    apply Subtype.ext
    exact hpointR
  have hfinish' : twoPuncturedDiskUpperRelativePointOfOverlap qL =
      arcFinish := by
    apply Subtype.ext
    exact hpointL
  let chord := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR).map
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper.continuous
  have hchord : twoPuncturedDiskUpperRelativePointOfOverlap qR =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper qR := by
    apply Subtype.ext
    rfl
  have hchord' : twoPuncturedDiskUpperRelativePointOfOverlap qL =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper qL := by
    apply Subtype.ext
    rfl
  exact arcSide.cast hstart hfinish' |>.trans
    (chord.cast hchord hchord').symm

/-- The lower cap boundary: the overlap chord, then the positive outer arc
back to the right cut point. -/
def twoPuncturedDiskOuterLowerCapLoop {α β R : ℝ}
    (_hα : -1 < α) (_hα1 : α < 1) (_hβ : -1 < β) (_hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path
      (twoPuncturedDiskLowerRelativePointOfOverlap
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR))
      (twoPuncturedDiskLowerRelativePointOfOverlap
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let arc := twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR
  let hArc := fun t => twoPuncturedDiskOuterLeftToRightArc_mem_lowerRelativeSide
    hαβ hαR hβR hR t
  let arcSide := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.pathIntoSubtype arc hArc
  have hpointL : qL.1 = twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qL, twoPuncturedDiskOuterLeftOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  have hpointR : qR.1 = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qR, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  let arcStart : twoPuncturedDiskLowerRelativePoint α β :=
    ⟨twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR, arc.source ▸ hArc 0⟩
  let arcFinish : twoPuncturedDiskLowerRelativePoint α β :=
    ⟨twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR, arc.target ▸ hArc 1⟩
  have hstart : twoPuncturedDiskLowerRelativePointOfOverlap qL = arcStart := by
    apply Subtype.ext
    exact hpointL
  have hfinish : twoPuncturedDiskLowerRelativePointOfOverlap qR = arcFinish := by
    apply Subtype.ext
    exact hpointR
  let chord := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR).map
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower.continuous
  have hchord : twoPuncturedDiskLowerRelativePointOfOverlap qR =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower qR := by
    apply Subtype.ext
    rfl
  have hchord' : twoPuncturedDiskLowerRelativePointOfOverlap qL =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower qL := by
    apply Subtype.ext
    rfl
  exact (chord.cast hchord hchord').trans
    (arcSide.cast hstart hfinish)

/-- The upper outer arc stays on the circle of radius `R`. -/
private theorem twoPuncturedDiskOuterRightToLeftArc_norm {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    ‖(twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1‖ = R := by
  rw [twoPuncturedDiskOuterRightToLeftArc_apply,
    twoPuncturedDiskOuterBoundaryCircle_val]
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos,
    Circle.norm_coe, mul_one]

/-- The upper outer arc lies at or above the horizontal cut. -/
private theorem twoPuncturedDiskOuterRightToLeftArc_height_ge_cut {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    twoPuncturedDiskOuterCutHeight α β ≤
      (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1.im := by
  rw [twoPuncturedDiskOuterRightToLeftArc_im]
  rw [← twoPuncturedDiskOuterRightDirection_im_scaled hαβ hαR hβR hR]
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  exact mul_le_mul_of_nonneg_left
    (circle_path_im_ge_source_of_re_pos_reflection
      (twoPuncturedDiskOuterRightDirection_re_pos hαβ hαR hβR hR)
      (twoPuncturedDiskOuterLeftDirection_val_eq_neg_star_right
        hαβ hαR hβR hR) t)
    (le_of_lt hRpos)

/-- The radial direction of the actual upper outer arc about the retained
upper puncture never reaches the downward vertical pole. -/
theorem twoPuncturedDiskOuterRightToLeftArc_direction_ne_negI {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    convexPuncturedUnitDirection
      ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1 -
        twoPuncturedDiskRightCenter β)
      (by
        intro hz
        exact (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).2.2.2
          (sub_eq_zero.mp hz)) ≠
      (⟨-Complex.I, by
        change (-Complex.I) ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm]
        rw [norm_neg, Complex.norm_I]⟩ : Circle) := by
  let z := (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1
  let v := z - twoPuncturedDiskRightCenter β
  have hz : v ≠ 0 := by
    intro hv
    apply (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).2.2.2
    exact sub_eq_zero.mp hv
  intro hd
  have hval : ‖v‖⁻¹ • v = -Complex.I := by
    have h := congrArg (fun θ : Circle => (θ : ℂ)) hd
    change ‖v‖⁻¹ • v = -Complex.I at h
    exact h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hvscaled : v = ‖v‖ • (-Complex.I) := by
    calc
      v = ‖v‖ • (‖v‖⁻¹ • v) := by
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = ‖v‖ • (-Complex.I) := congrArg (fun w : ℂ => ‖v‖ • w) hval
  have hvre : v.re = 0 := by rw [hvscaled]; simp
  have hvim : v.im < 0 := by
    have hcoord := congrArg Complex.im hvscaled
    have hsimp : (‖v‖ • -Complex.I).im = -‖v‖ := by
      change ((‖v‖ : ℂ) * (-Complex.I)).im = -‖v‖
      rw [Complex.mul_im]
      simp
    have hvcoord : v.im = -‖v‖ := hcoord.trans hsimp
    rw [hvcoord]
    exact neg_lt_zero.mpr (norm_pos_iff.mpr hz)
  have hzre : z.re = 0 := by
    simpa [v, twoPuncturedDiskRightCenter] using hvre
  have hzim : z.im < β := by
    simpa [v, twoPuncturedDiskRightCenter] using hvim
  have hnorm : ‖z‖ = R := by
    exact twoPuncturedDiskOuterRightToLeftArc_norm hαβ hαR hβR hR t
  have habs : |z.im| = R := by
    have hzrepr : z = (0 : ℝ) + z.im * Complex.I := by
      apply Complex.ext
      · simp [hzre]
      · simp
    rw [hzrepr, Complex.norm_add_mul_I] at hnorm
    simpa [Real.sqrt_sq_eq_abs] using hnorm
  rcases eq_or_eq_neg_of_abs_eq habs with hy | hy
  · have hβRlt : β < R := (abs_lt.mp hβR).2
    linarith [hzim]
  · have hcut := (twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR).1
    have harc := twoPuncturedDiskOuterRightToLeftArc_height_ge_cut
      hαβ hαR hβR hR t
    rw [hy] at harc
    linarith

/-- The literal overlap connector is the straight segment between its two
cut points after forgetting the subtype presentation. -/
private theorem twoPuncturedDiskOuterOverlapConnector_val {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    ((twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1) =
    Path.segment
        (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1
        (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 t := by
  change (Path.segment
    (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1
    (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 t) = _
  rfl

/-- Every point of the literal chord has the cut height. -/
private theorem twoPuncturedDiskOuterOverlapConnector_im {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
      ((twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1).im =
      twoPuncturedDiskOuterCutHeight α β := by
  rw [twoPuncturedDiskOuterOverlapConnector_val]
  rw [Path.segment_apply, AffineMap.lineMap_apply]
  simp [twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterLeftCutPoint,
    twoPuncturedDiskOuterCutHeight]

/-- A point on the unit circle other than `-1` belongs to the slit plane. -/
private theorem circle_mem_slitPlane_of_ne_negOne {z : Circle} (hz : z ≠ -1) :
    (z : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (z : ℂ).im = 0
  · left
    have hsq : (z : ℂ).re ^ 2 = 1 := by
      have h := Circle.normSq_coe z
      rw [Complex.normSq_apply, him] at h
      nlinarith
    have habs : |(z : ℂ).re| = 1 := by
      have hsqabs : |(z : ℂ).re| ^ 2 = 1 := by simpa [sq_abs] using hsq
      have hnonneg := abs_nonneg (z : ℂ).re
      nlinarith
    rcases eq_or_eq_neg_of_abs_eq habs with hre | hre
    · simp [hre]
    · exfalso
      apply hz
      apply Circle.ext
      apply Complex.ext
      · simp [hre]
      · simp [him]
  · exact Or.inr him

/-- Rotating a unit-circle path away from its pole places it in the standard
slit plane. -/
private theorem circle_mul_mem_slitPlane_of_ne_pole (u pole z : Circle)
    (hu : u * pole = -1) (hz : z ≠ pole) :
    ((u * z : Circle) : ℂ) ∈ Complex.slitPlane := by
  apply circle_mem_slitPlane_of_ne_negOne
  intro heq
  apply hz
  exact mul_left_cancel (heq.trans hu.symm)

/-- The actual connector's radial direction about the upper puncture avoids
the upward vertical pole. -/
theorem twoPuncturedDiskOuterOverlapConnector_direction_ne_I {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    convexPuncturedUnitDirection
      (((twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1) -
        twoPuncturedDiskRightCenter β)
      (by
        intro hz
        exact (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.2.2.2
          (sub_eq_zero.mp hz)) ≠
      (⟨Complex.I, by
        change Complex.I ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, Complex.norm_I]⟩ : Circle) := by
  let z := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1
  let v := z - twoPuncturedDiskRightCenter β
  have hz : v ≠ 0 := by
    intro hv
    apply (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.2.2.2
    exact sub_eq_zero.mp hv
  intro hd
  have hval : ‖v‖⁻¹ • v = Complex.I := by
    have h := congrArg (fun θ : Circle => (θ : ℂ)) hd
    change ‖v‖⁻¹ • v = Complex.I at h
    exact h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hvscaled : v = ‖v‖ • Complex.I := by
    calc
      v = ‖v‖ • (‖v‖⁻¹ • v) := by
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = ‖v‖ • Complex.I := congrArg (fun w : ℂ => ‖v‖ • w) hval
  have hvim : 0 < v.im := by
    have hcoord := congrArg Complex.im hvscaled
    have hsimp : (‖v‖ • Complex.I).im = ‖v‖ := by
      change ((‖v‖ : ℂ) * Complex.I).im = ‖v‖
      rw [Complex.mul_im]
      simp
    rw [hsimp] at hcoord
    linarith [norm_pos_iff.mpr hz]
  have hzim : z.im < β := by
    rw [twoPuncturedDiskOuterOverlapConnector_im hαβ hαR hβR hR t]
    dsimp [twoPuncturedDiskOuterCutHeight]
    linarith
  have hvim' : v.im < 0 := by
    simpa [v, twoPuncturedDiskRightCenter] using hzim
  linarith

private theorem twoPuncturedDiskOuterUpperArcDirectionPath_ne_negI
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath hβ hβ1 hαβ hαR hβR hR t ≠
      (⟨-Complex.I, by
        change (-Complex.I) ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_I]⟩ : Circle) := by
  change convexPuncturedUnitDirection
    ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1 -
      twoPuncturedDiskRightCenter β)
    (by
      intro hz
      exact (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).2.2.2
        (sub_eq_zero.mp hz)) ≠ _
  exact twoPuncturedDiskOuterRightToLeftArc_direction_ne_negI
    hαβ hαR hβR hR t

private theorem twoPuncturedDiskOuterUpperChordDirectionPath_ne_I
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath hβ hβ1 hαβ hαR hβR hR t ≠
      (⟨Complex.I, by
        change Complex.I ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, Complex.norm_I]⟩ : Circle) := by
  change convexPuncturedUnitDirection
    (((twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1) -
      twoPuncturedDiskRightCenter β)
    (by
      intro hz
      exact (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.2.2.2
        (sub_eq_zero.mp hz)) ≠ _
  exact twoPuncturedDiskOuterOverlapConnector_direction_ne_I
    hαβ hαR hβR hR t

private theorem circle_im_gt_neg_one_of_re_pos {θ : Circle}
    (hre : 0 < (θ : ℂ).re) : -1 < (θ : ℂ).im := by
  have hsum : (θ : ℂ).re ^ 2 + (θ : ℂ).im ^ 2 = 1 := by
    have h := Circle.normSq_coe θ
    rw [Complex.normSq_apply] at h
    nlinarith
  by_contra h
  have him : (θ : ℂ).im ≤ -1 := le_of_not_gt h
  have himsq : 1 ≤ (θ : ℂ).im ^ 2 := by nlinarith
  have hre2 : 0 < (θ : ℂ).re ^ 2 := sq_pos_of_pos hre
  nlinarith

private theorem circle_im_lt_one_of_re_pos {θ : Circle}
    (hre : 0 < (θ : ℂ).re) : (θ : ℂ).im < 1 := by
  have hsum : (θ : ℂ).re ^ 2 + (θ : ℂ).im ^ 2 = 1 := by
    have h := Circle.normSq_coe θ
    rw [Complex.normSq_apply] at h
    nlinarith
  by_contra h
  have him : 1 ≤ (θ : ℂ).im := le_of_not_gt h
  have himsq : 1 ≤ (θ : ℂ).im ^ 2 := by nlinarith
  have hre2 : 0 < (θ : ℂ).re ^ 2 := sq_pos_of_pos hre
  nlinarith

private theorem circle_path_ne_negI_of_re_pos_reflection {θ φ : Circle}
    (hθ : 0 < (θ : ℂ).re) (hφ : (φ : ℂ) = -star (θ : ℂ))
    (t : unitInterval) :
    Circle.path θ φ t ≠ (⟨-Complex.I, by
      change (-Complex.I) ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_I]⟩ : Circle) := by
  intro heq
  have him := congrArg (fun z : Circle => (z : ℂ).im) heq
  have hpath : ((Circle.path θ φ t : Circle) : ℂ).im = -1 := by
    simpa using him
  have hge := circle_path_im_ge_source_of_re_pos_reflection hθ hφ t
  linarith [circle_im_gt_neg_one_of_re_pos hθ]

private theorem circle_path_ne_I_of_re_pos_reflection {θ φ : Circle}
    (hθ : 0 < (θ : ℂ).re) (hφ : (φ : ℂ) = -star (θ : ℂ))
    (t : unitInterval) :
    Circle.path φ θ t ≠ (⟨Complex.I, by
      change Complex.I ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm, Complex.norm_I]⟩ : Circle) := by
  intro heq
  have him := congrArg (fun z : Circle => (z : ℂ).im) heq
  have hpath : ((Circle.path φ θ t : Circle) : ℂ).im = 1 := by
    simpa using him
  have hle := circle_path_im_le_source_of_re_pos_reflection hθ hφ t
  linarith [circle_im_lt_one_of_re_pos hθ]

private theorem twoPuncturedDiskOuterUpperArcDirectionPath_homotopic_circlePath
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath hβ hβ1 hαβ hαR hβR hR).Homotopic
      (Circle.path
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
          (twoPuncturedDiskUpperRelativePointOfOverlap
            (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
          (twoPuncturedDiskUpperRelativePointOfOverlap
            (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
    (twoPuncturedDiskUpperRelativePointOfOverlap qR)
  let φ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
    (twoPuncturedDiskUpperRelativePointOfOverlap qL)
  have hend := twoPuncturedDiskOuterUpperRadialMap_endpoints
    hβ hβ1 hαβ hαR hβR hR
  have hθ : 0 < (θ : ℂ).re := by
    dsimp [θ, qR]
    rw [hend.1]
    exact twoPuncturedDiskOuterUpperRightDirection_re_pos hαβ hαR hβR hR
  have hφ : (φ : ℂ) = -star (θ : ℂ) := by
    dsimp [θ, φ, qR, qL]
    rw [hend.2, hend.1]
    exact twoPuncturedDiskOuterUpperDirections_reflect hαβ hαR hβR hR
  let u : Circle := ⟨-Complex.I, by
    change (-Complex.I) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_I]⟩
  have hu : u * u = -1 := by
    apply Circle.ext
    change (-Complex.I) * (-Complex.I) = (-1 : ℂ)
    simp
  apply circle_paths_homotopic_of_mem_rotatedSlitPlane
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath hβ hβ1 hαβ hαR hβR hR)
    (Circle.path θ φ) u
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (twoPuncturedDiskOuterUpperArcDirectionPath_ne_negI
        hβ hβ1 hαβ hαR hβR hR t)
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (circle_path_ne_negI_of_re_pos_reflection hθ hφ t)

private theorem twoPuncturedDiskOuterUpperChordDirectionPath_symm_homotopic_circlePath
    {α β R : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath hβ hβ1 hαβ hαR hβR hR).symm.Homotopic
      (Circle.path
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
          (twoPuncturedDiskUpperRelativePointOfOverlap
            (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)))
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
          (twoPuncturedDiskUpperRelativePointOfOverlap
            (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
    (twoPuncturedDiskUpperRelativePointOfOverlap qR)
  let φ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
    (twoPuncturedDiskUpperRelativePointOfOverlap qL)
  have hend := twoPuncturedDiskOuterUpperRadialMap_endpoints
    hβ hβ1 hαβ hαR hβR hR
  have hθ : 0 < (θ : ℂ).re := by
    dsimp [θ, qR]
    rw [hend.1]
    exact twoPuncturedDiskOuterUpperRightDirection_re_pos hαβ hαR hβR hR
  have hφ : (φ : ℂ) = -star (θ : ℂ) := by
    dsimp [θ, φ, qR, qL]
    rw [hend.2, hend.1]
    exact twoPuncturedDiskOuterUpperDirections_reflect hαβ hαR hβR hR
  let u : Circle := ⟨Complex.I, by
    change Complex.I ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, Complex.norm_I]⟩
  have hu : u * u = -1 := by
    apply Circle.ext
    change Complex.I * Complex.I = (-1 : ℂ)
    simp
  apply circle_paths_homotopic_of_mem_rotatedSlitPlane
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath hβ hβ1 hαβ hαR hβR hR).symm
    (Circle.path φ θ) u
  · intro t
    change ((u * Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath hβ hβ1
      hαβ hαR hβR hR (σ t) : Circle) : ℂ) ∈ Complex.slitPlane
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (twoPuncturedDiskOuterUpperChordDirectionPath_ne_I
        hβ hβ1 hαβ hαR hβR hR (σ t))
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (circle_path_ne_I_of_re_pos_reflection hθ hφ t)

private theorem twoPuncturedDiskOuterUpperCapLoop_map_eq_directionPieces
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterUpperCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR).map
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ).continuous =
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath hβ hβ1 hαβ hαR hβR hR).trans
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath hβ hβ1 hαβ hαR hβR hR).symm := by
  apply Path.ext
  funext t
  simp [twoPuncturedDiskOuterUpperCapLoop,
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath,
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath,
    Path.map_trans, Path.map_symm]

/-- After the actual upper-side radial retraction, the cap boundary is one
positive turn.  This is the geometric winding calculation for the cap: its
outer arc and reversed overlap chord lie in opposite slit-plane charts and
deform to the two complementary positive Circle arcs. -/
theorem twoPuncturedDiskOuterUpperCapLoop_radialMap_homotopic_oneTurn
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    ((twoPuncturedDiskOuterUpperCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR).map
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ).continuous).Homotopic
      (circleOneTurnLoop (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
        (twoPuncturedDiskUpperRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
    (twoPuncturedDiskUpperRelativePointOfOverlap qR)
  let φ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ
    (twoPuncturedDiskUpperRelativePointOfOverlap qL)
  have hend := twoPuncturedDiskOuterUpperRadialMap_endpoints
    hβ hβ1 hαβ hαR hβR hR
  have hθ : 0 < (θ : ℂ).re := by
    dsimp [θ, qR]
    rw [hend.1]
    exact twoPuncturedDiskOuterUpperRightDirection_re_pos hαβ hαR hβR hR
  have hφ : (φ : ℂ) = -star (θ : ℂ) := by
    dsimp [θ, φ, qR, qL]
    rw [hend.2, hend.1]
    exact twoPuncturedDiskOuterUpperDirections_reflect hαβ hαR hβR hR
  have hneq : θ ≠ φ := by
    intro heq
    have hre := congrArg (fun z : Circle => (z : ℂ).re) heq
    rw [hφ] at hre
    have hzero : (θ : ℂ).re = 0 := by
      have hre' : (θ : ℂ).re = -(θ : ℂ).re := by simpa using hre
      linarith
    linarith
  have harc : (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperArcDirectionPath
      hβ hβ1 hαβ hαR hβR hR).Homotopic (Circle.path θ φ) := by
    simpa [θ, φ] using
      twoPuncturedDiskOuterUpperArcDirectionPath_homotopic_circlePath
        hβ hβ1 hαβ hαR hβR hR
  have hchord : (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperChordDirectionPath
      hβ hβ1 hαβ hαR hβR hR).symm.Homotopic (Circle.path φ θ) := by
    simpa [θ, φ] using
      twoPuncturedDiskOuterUpperChordDirectionPath_symm_homotopic_circlePath
        hβ hβ1 hαβ hαR hβR hR
  have hturn := circlePath_trans_circlePath_homotopic_oneTurn hneq
  change ((twoPuncturedDiskOuterUpperCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR).map
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ).continuous).Homotopic
    (circleOneTurnLoop θ)
  rw [twoPuncturedDiskOuterUpperCapLoop_map_eq_directionPieces
    hα hα1 hβ hβ1 hαβ hαR hβR hR]
  exact (harc.hcomp hchord).trans hturn

#print axioms twoPuncturedDiskOuterUpperCapLoop_radialMap_homotopic_oneTurn

/-- The upper cap maps to the positive side generator under the actual
relative-side free-group equivalence. -/
theorem twoPuncturedDiskOuterUpperCapLoop_sideFreeGenerator
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)
      ⟦twoPuncturedDiskOuterUpperCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR⟧ =
        FreeGroup.of () := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let base := twoPuncturedDiskUpperRelativePointOfOverlap qR
  let H : twoPuncturedDiskUpperRelativePoint α β ≃ₜ
      puncturedBaseAt (twoPuncturedDiskUpperBase α β)
        (twoPuncturedDiskRightCenter β) := twoPuncturedDiskUpperSideHomeomorph hαβ
  let E := twoPuncturedDiskUpperSideHomotopyEquiv hβ hβ1 hαβ
  let z := H base
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ base
  let cap := twoPuncturedDiskOuterUpperCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR
  have hradial := twoPuncturedDiskOuterUpperCapLoop_radialMap_homotopic_oneTurn
    hα hα1 hβ hβ1 hαβ hαR hβR hR
  have hhome : fundamentalGroupHomeomorphEquiv H base ⟦cap⟧ =
      ⟦cap.map H.continuous⟧ := by
    change FundamentalGroup.map (H : C(twoPuncturedDiskUpperRelativePoint α β,
      puncturedBaseAt (twoPuncturedDiskUpperBase α β)
        (twoPuncturedDiskRightCenter β))) base ⟦cap⟧ = _
    dsimp [cap, base, qR]
    rw [FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
  have hside : twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ z
      ⟦cap.map H.continuous⟧ = ⟦circleOneTurnLoop θ⟧ := by
    change FundamentalGroup.map E.toFun z ⟦cap.map H.continuous⟧ = _
    dsimp [cap, base, qR]
    rw [FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    have hpath : (cap.map H.continuous).map E.continuous =
        cap.map (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap hβ hβ1 hαβ).continuous := by
      apply Path.ext
      funext t
      rfl
    rw [hpath]
    exact Path.Homotopic.Quotient.eq.mpr
      (by simpa [θ, z, base, qR, H, E, Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterUpperRadialMap] using hradial)
  change circleFundamentalGroupFreeEquiv θ
    (twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ z
      (fundamentalGroupHomeomorphEquiv H base ⟦cap⟧)) = FreeGroup.of ()
  rw [hhome, hside]
  exact circleFundamentalGroupFreeEquiv_oneTurn θ

#print axioms twoPuncturedDiskOuterUpperCapLoop_sideFreeGenerator

/-- The actual lower-side radial normalization. -/
noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β) :
    C(twoPuncturedDiskLowerRelativePoint α β, Circle) := by
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  let E := twoPuncturedDiskLowerSideHomotopyEquiv hα hα1 hαβ
  exact ⟨fun z => E (H z), E.continuous.comp H.continuous_toFun⟩

set_option backward.isDefEq.respectTransparency false in
private theorem twoPuncturedDiskOuterLowerRadialMap_apply {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β)
    (z : twoPuncturedDiskLowerRelativePoint α β) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ z =
      convexPuncturedUnitDirection (z.1.1 - twoPuncturedDiskLeftCenter α)
        (by
          intro hz
          exact z.1.2.2.1 (sub_eq_zero.mp hz)) := by
  change (twoPuncturedDiskLowerSideHomotopyEquiv hα hα1 hαβ
    (twoPuncturedDiskLowerSideHomeomorph hαβ z)) = _
  rw [twoPuncturedDiskLowerSideHomotopyEquiv_apply]
  rfl

noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRightDirection
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) : Circle := convexPuncturedUnitDirection
      ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskLeftCenter α) (by
          intro hz
          exact (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).2.2.1
            (sub_eq_zero.mp hz))

noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerLeftDirection
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) : Circle := convexPuncturedUnitDirection
      ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskLeftCenter α) (by
          intro hz
          exact (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).2.2.1
            (sub_eq_zero.mp hz))

private theorem twoPuncturedDiskOuterLowerRightDirection_re_pos
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) :
    0 < (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRightDirection hαβ hαR hβR hR : ℂ).re := by
  let v := (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 -
    twoPuncturedDiskLeftCenter α
  have hv : v ≠ 0 := by
    intro hz
    exact (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).2.2.1
      (sub_eq_zero.mp hz)
  have hw : 0 < twoPuncturedDiskOuterCutHalfWidth α β R :=
    twoPuncturedDiskOuterCutHalfWidth_pos hαβ hαR hβR
  have hvre : v.re = twoPuncturedDiskOuterCutHalfWidth α β R := by
    simp [v, twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterCutHeight,
      twoPuncturedDiskLeftCenter]
  change 0 < (‖v‖⁻¹ • v).re
  have hmul : (‖v‖⁻¹ • v).re = ‖v‖⁻¹ * v.re := by
    change ((↑(‖v‖⁻¹) : ℂ) * v).re = _
    rw [Complex.mul_re]
    simp
  rw [hmul, hvre]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hv)) hw

private theorem twoPuncturedDiskOuterLowerDirections_reflect
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) :
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerLeftDirection hαβ hαR hβR hR : ℂ) =
      -star (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRightDirection hαβ hαR hβR hR : ℂ) := by
  have hvec :
      (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
          twoPuncturedDiskLeftCenter α =
        -star ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 -
          twoPuncturedDiskLeftCenter α) := by
    apply Complex.ext
    · simp [twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterLeftCutPoint,
        twoPuncturedDiskOuterCutHeight, twoPuncturedDiskLeftCenter]
    · simp [twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterLeftCutPoint,
        twoPuncturedDiskOuterCutHeight, twoPuncturedDiskLeftCenter]
      ring
  change ‖(twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
        twoPuncturedDiskLeftCenter α‖⁻¹ •
        ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 -
          twoPuncturedDiskLeftCenter α) = _
  rw [hvec, norm_neg, norm_star, smul_neg]
  congr 1
  simp [Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRightDirection, convexPuncturedUnitDirection]

private theorem twoPuncturedDiskOuterLowerRadialMap_endpoints
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)) =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRightDirection hαβ hαR hβR hR ∧
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)) =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerLeftDirection hαβ hαR hβR hR := by
  constructor <;> rw [twoPuncturedDiskOuterLowerRadialMap_apply]
  · congr 1
  · congr 1

/-- Radial normalization of the forward overlap chord in the lower side. -/
noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let chord := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR).map
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower.continuous
  have hstart : twoPuncturedDiskLowerRelativePointOfOverlap qR =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower qR := by
    apply Subtype.ext
    rfl
  have hfinish : twoPuncturedDiskLowerRelativePointOfOverlap qL =
      Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower qL := by
    apply Subtype.ext
    rfl
  exact (chord.cast hstart hfinish).map
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ).continuous

/-- Radial normalization of the actual lower outer arc. -/
noncomputable def Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)))
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let arc := twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR
  let hArc := fun t => twoPuncturedDiskOuterLeftToRightArc_mem_lowerRelativeSide
    hαβ hαR hβR hR t
  let arcSide := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.pathIntoSubtype arc hArc
  have hpointR : qR.1 = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qR, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  have hpointL : qL.1 = twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [qL, twoPuncturedDiskOuterLeftOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  let arcStart : twoPuncturedDiskLowerRelativePoint α β :=
    ⟨twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR, arc.source ▸ hArc 0⟩
  let arcFinish : twoPuncturedDiskLowerRelativePoint α β :=
    ⟨twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR, arc.target ▸ hArc 1⟩
  have hstart : twoPuncturedDiskLowerRelativePointOfOverlap qL = arcStart := by
    apply Subtype.ext
    exact hpointL
  have hfinish : twoPuncturedDiskLowerRelativePointOfOverlap qR = arcFinish := by
    apply Subtype.ext
    exact hpointR
  exact (arcSide.cast hstart hfinish).map
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ).continuous

private theorem twoPuncturedDiskOuterLeftToRightArc_norm {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    ‖(twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1‖ = R := by
  rw [twoPuncturedDiskOuterLeftToRightArc_apply,
    twoPuncturedDiskOuterBoundaryCircle_val]
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos,
    Circle.norm_coe, mul_one]

private theorem twoPuncturedDiskOuterLeftToRightArc_height_le_cut {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1.im ≤
      twoPuncturedDiskOuterCutHeight α β := by
  rw [twoPuncturedDiskOuterLeftToRightArc_im]
  rw [← twoPuncturedDiskOuterRightDirection_im_scaled hαβ hαR hβR hR]
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  exact mul_le_mul_of_nonneg_left
    (circle_path_im_le_source_of_re_pos_reflection
      (twoPuncturedDiskOuterRightDirection_re_pos hαβ hαR hβR hR)
      (twoPuncturedDiskOuterLeftDirection_val_eq_neg_star_right
        hαβ hαR hβR hR) t)
    (le_of_lt hRpos)

/-- The actual lower-side chord direction stays above the lower center, so
it avoids the downward pole. -/
private theorem twoPuncturedDiskOuterLowerChordDirectionPath_ne_negI
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath hα hα1 hαβ hαR hβR hR t ≠
      (⟨-Complex.I, by
        change (-Complex.I) ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_I]⟩ : Circle) := by
  change convexPuncturedUnitDirection
    (((twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1) -
      twoPuncturedDiskLeftCenter α)
    (by
      intro hz
      exact (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.2.2.1
        (sub_eq_zero.mp hz)) ≠ _
  let z := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.1
  let v := z - twoPuncturedDiskLeftCenter α
  have hv : v ≠ 0 := by
    intro hz
    exact (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR t).1.2.2.1
      (sub_eq_zero.mp hz)
  intro hd
  have hval : ‖v‖⁻¹ • v = -Complex.I := by
    have h := congrArg (fun d : Circle => (d : ℂ)) hd
    change ‖v‖⁻¹ • v = -Complex.I at h
    exact h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hscaled : v = ‖v‖ • (-Complex.I) := by
    calc
      v = ‖v‖ • (‖v‖⁻¹ • v) := by
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = ‖v‖ • (-Complex.I) := congrArg (fun w : ℂ => ‖v‖ • w) hval
  have hvim : v.im < 0 := by
    have hcoord := congrArg Complex.im hscaled
    have hsimp : (‖v‖ • -Complex.I).im = -‖v‖ := by
      change ((‖v‖ : ℂ) * (-Complex.I)).im = -‖v‖
      rw [Complex.mul_im]
      simp
    have hvcoord : v.im = -‖v‖ := hcoord.trans hsimp
    rw [hvcoord]
    exact neg_lt_zero.mpr (norm_pos_iff.mpr hv)
  have hvim' : z.im - α < 0 := by
    simpa [v, twoPuncturedDiskLeftCenter] using hvim
  rw [twoPuncturedDiskOuterOverlapConnector_im hαβ hαR hβR hR t] at hvim'
  have hcut : α < twoPuncturedDiskOuterCutHeight α β := by
    dsimp [twoPuncturedDiskOuterCutHeight]
    linarith
  linarith

/-- The lower outer arc's radial direction about its retained center never
reaches the upward vertical pole. -/
private theorem twoPuncturedDiskOuterLowerArcDirectionPath_ne_I
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath hα hα1 hαβ hαR hβR hR t ≠
      (⟨Complex.I, by
        change Complex.I ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm, Complex.norm_I]⟩ : Circle) := by
  change convexPuncturedUnitDirection
    ((twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1 -
      twoPuncturedDiskLeftCenter α)
    (by
      intro hz
      exact (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).2.2.1
        (sub_eq_zero.mp hz)) ≠ _
  let z := (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1
  let v := z - twoPuncturedDiskLeftCenter α
  have hv : v ≠ 0 := by
    intro hz
    exact (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).2.2.1
      (sub_eq_zero.mp hz)
  intro hd
  have hval : ‖v‖⁻¹ • v = Complex.I := by
    have h := congrArg (fun d : Circle => (d : ℂ)) hd
    change ‖v‖⁻¹ • v = Complex.I at h
    exact h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hscaled : v = ‖v‖ • Complex.I := by
    calc
      v = ‖v‖ • (‖v‖⁻¹ • v) := by
        rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
      _ = ‖v‖ • Complex.I := congrArg (fun w : ℂ => ‖v‖ • w) hval
  have hvre : v.re = 0 := by rw [hscaled]; simp
  have hvim : 0 < v.im := by
    have hcoord := congrArg Complex.im hscaled
    have hsimp : (‖v‖ • Complex.I).im = ‖v‖ := by
      change ((‖v‖ : ℂ) * Complex.I).im = ‖v‖
      rw [Complex.mul_im]
      simp
    have hvcoord : v.im = ‖v‖ := hcoord.trans hsimp
    rw [hvcoord]
    exact norm_pos_iff.mpr hv
  have hzre : z.re = 0 := by
    simpa [v, twoPuncturedDiskLeftCenter] using hvre
  have hzim : α < z.im := by
    simpa [v, twoPuncturedDiskLeftCenter] using hvim
  have hnorm : ‖z‖ = R :=
    twoPuncturedDiskOuterLeftToRightArc_norm hαβ hαR hβR hR t
  have habs : |z.im| = R := by
    have hzrepr : z = (0 : ℝ) + z.im * Complex.I := by
      apply Complex.ext
      · simp [hzre]
      · simp
    rw [hzrepr, Complex.norm_add_mul_I] at hnorm
    simpa [Real.sqrt_sq_eq_abs] using hnorm
  rcases eq_or_eq_neg_of_abs_eq habs with hy | hy
  · have harc := twoPuncturedDiskOuterLeftToRightArc_height_le_cut
      hαβ hαR hβR hR t
    rw [hy] at harc
    have hcut := (twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR).2
    linarith
  · have hαRlo : -R < α := (abs_lt.mp hαR).1
    linarith

private theorem twoPuncturedDiskOuterLowerChordDirectionPath_homotopic_circlePath
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath hα hα1 hαβ hαR hβR hR).Homotopic
      (Circle.path
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
          (twoPuncturedDiskLowerRelativePointOfOverlap
            (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
          (twoPuncturedDiskLowerRelativePointOfOverlap
            (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
    (twoPuncturedDiskLowerRelativePointOfOverlap qR)
  let φ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
    (twoPuncturedDiskLowerRelativePointOfOverlap qL)
  have hend := twoPuncturedDiskOuterLowerRadialMap_endpoints
    hα hα1 hαβ hαR hβR hR
  have hθ : 0 < (θ : ℂ).re := by
    dsimp [θ, qR]
    rw [hend.1]
    exact twoPuncturedDiskOuterLowerRightDirection_re_pos hαβ hαR hβR hR
  have hφ : (φ : ℂ) = -star (θ : ℂ) := by
    dsimp [θ, φ, qR, qL]
    rw [hend.2, hend.1]
    exact twoPuncturedDiskOuterLowerDirections_reflect hαβ hαR hβR hR
  let u : Circle := ⟨-Complex.I, by
    change (-Complex.I) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_I]⟩
  have hu : u * u = -1 := by
    apply Circle.ext
    change (-Complex.I) * (-Complex.I) = (-1 : ℂ)
    simp
  apply circle_paths_homotopic_of_mem_rotatedSlitPlane
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath hα hα1 hαβ hαR hβR hR)
    (Circle.path θ φ) u
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (twoPuncturedDiskOuterLowerChordDirectionPath_ne_negI
        hα hα1 hαβ hαR hβR hR t)
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (circle_path_ne_negI_of_re_pos_reflection hθ hφ t)

private theorem twoPuncturedDiskOuterLowerArcDirectionPath_homotopic_circlePath
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath hα hα1 hαβ hαR hβR hR).Homotopic
      (Circle.path
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
          (twoPuncturedDiskLowerRelativePointOfOverlap
            (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR)))
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
          (twoPuncturedDiskLowerRelativePointOfOverlap
            (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
    (twoPuncturedDiskLowerRelativePointOfOverlap qR)
  let φ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
    (twoPuncturedDiskLowerRelativePointOfOverlap qL)
  have hend := twoPuncturedDiskOuterLowerRadialMap_endpoints
    hα hα1 hαβ hαR hβR hR
  have hθ : 0 < (θ : ℂ).re := by
    dsimp [θ, qR]
    rw [hend.1]
    exact twoPuncturedDiskOuterLowerRightDirection_re_pos hαβ hαR hβR hR
  have hφ : (φ : ℂ) = -star (θ : ℂ) := by
    dsimp [θ, φ, qR, qL]
    rw [hend.2, hend.1]
    exact twoPuncturedDiskOuterLowerDirections_reflect hαβ hαR hβR hR
  let u : Circle := ⟨Complex.I, by
    change Complex.I ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, Complex.norm_I]⟩
  have hu : u * u = -1 := by
    apply Circle.ext
    change Complex.I * Complex.I = (-1 : ℂ)
    simp
  apply circle_paths_homotopic_of_mem_rotatedSlitPlane
    (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath hα hα1 hαβ hαR hβR hR)
    (Circle.path φ θ) u
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (twoPuncturedDiskOuterLowerArcDirectionPath_ne_I
        hα hα1 hαβ hαR hβR hR t)
  · intro t
    exact circle_mul_mem_slitPlane_of_ne_pole u u _ hu
      (circle_path_ne_I_of_re_pos_reflection hθ hφ t)

private theorem twoPuncturedDiskOuterLowerCapLoop_map_eq_directionPieces
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterLowerCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR).map
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ).continuous =
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath hα hα1 hαβ hαR hβR hR).trans
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath hα hα1 hαβ hαR hβR hR) := by
  apply Path.ext
  funext t
  simp [twoPuncturedDiskOuterLowerCapLoop,
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath,
    Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath,
    Path.map_trans]

/-- The actual lower cap also maps to one positive turn after radial
normalization about its retained puncture. -/
theorem twoPuncturedDiskOuterLowerCapLoop_radialMap_homotopic_oneTurn
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    ((twoPuncturedDiskOuterLowerCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR).map
        (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ).continuous).Homotopic
      (circleOneTurnLoop (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
        (twoPuncturedDiskLowerRelativePointOfOverlap
          (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)))) := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let qL := twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
    (twoPuncturedDiskLowerRelativePointOfOverlap qR)
  let φ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ
    (twoPuncturedDiskLowerRelativePointOfOverlap qL)
  have hend := twoPuncturedDiskOuterLowerRadialMap_endpoints
    hα hα1 hαβ hαR hβR hR
  have hθ : 0 < (θ : ℂ).re := by
    dsimp [θ, qR]
    rw [hend.1]
    exact twoPuncturedDiskOuterLowerRightDirection_re_pos hαβ hαR hβR hR
  have hφ : (φ : ℂ) = -star (θ : ℂ) := by
    dsimp [θ, φ, qR, qL]
    rw [hend.2, hend.1]
    exact twoPuncturedDiskOuterLowerDirections_reflect hαβ hαR hβR hR
  have hneq : θ ≠ φ := by
    intro heq
    have hre := congrArg (fun z : Circle => (z : ℂ).re) heq
    rw [hφ] at hre
    have hzero : (θ : ℂ).re = 0 := by
      have hre' : (θ : ℂ).re = -(θ : ℂ).re := by simpa using hre
      linarith
    linarith
  have hchord : (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerChordDirectionPath
      hα hα1 hαβ hαR hβR hR).Homotopic (Circle.path θ φ) := by
    simpa [θ, φ] using
      twoPuncturedDiskOuterLowerChordDirectionPath_homotopic_circlePath
        hα hα1 hαβ hαR hβR hR
  have harc : (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerArcDirectionPath
      hα hα1 hαβ hαR hβR hR).Homotopic (Circle.path φ θ) := by
    simpa [θ, φ] using
      twoPuncturedDiskOuterLowerArcDirectionPath_homotopic_circlePath
        hα hα1 hαβ hαR hβR hR
  have hturn := circlePath_trans_circlePath_homotopic_oneTurn hneq
  change ((twoPuncturedDiskOuterLowerCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR).map
      (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ).continuous).Homotopic
    (circleOneTurnLoop θ)
  rw [twoPuncturedDiskOuterLowerCapLoop_map_eq_directionPieces
    hα hα1 hβ hβ1 hαβ hαR hβR hR]
  exact (hchord.hcomp harc).trans hturn

/-- The literal lower cap is the positive peripheral generator in the lower
relative-side factor. -/
theorem twoPuncturedDiskOuterLowerCapLoop_sideFreeGenerator
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)
      ⟦twoPuncturedDiskOuterLowerCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR⟧ =
        FreeGroup.of () := by
  let qR := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let base := twoPuncturedDiskLowerRelativePointOfOverlap qR
  let H : twoPuncturedDiskLowerRelativePoint α β ≃ₜ
      puncturedBaseAt (twoPuncturedDiskLowerBase α β)
        (twoPuncturedDiskLeftCenter α) := twoPuncturedDiskLowerSideHomeomorph hαβ
  let E := twoPuncturedDiskLowerSideHomotopyEquiv hα hα1 hαβ
  let z := H base
  let θ := Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ base
  let cap := twoPuncturedDiskOuterLowerCapLoop hα hα1 hβ hβ1 hαβ hαR hβR hR
  have hradial := twoPuncturedDiskOuterLowerCapLoop_radialMap_homotopic_oneTurn
    hα hα1 hβ hβ1 hαβ hαR hβR hR
  have hhome : fundamentalGroupHomeomorphEquiv H base ⟦cap⟧ =
      ⟦cap.map H.continuous⟧ := by
    change FundamentalGroup.map (H : C(twoPuncturedDiskLowerRelativePoint α β,
      puncturedBaseAt (twoPuncturedDiskLowerBase α β)
        (twoPuncturedDiskLeftCenter α))) base ⟦cap⟧ = _
    dsimp [cap, base, qR]
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
  have hside : twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ z
      ⟦cap.map H.continuous⟧ = ⟦circleOneTurnLoop θ⟧ := by
    change FundamentalGroup.map E.toFun z ⟦cap.map H.continuous⟧ = _
    dsimp [cap, base, qR]
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    have hpath : (cap.map H.continuous).map E.continuous =
        cap.map (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap hα hα1 hαβ).continuous := by
      apply Path.ext
      funext t
      rfl
    rw [hpath]
    exact Path.Homotopic.Quotient.eq.mpr
      (by simpa [θ, z, base, qR, H, E, Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterLowerRadialMap] using hradial)
  change circleFundamentalGroupFreeEquiv θ
    (twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ z
      (fundamentalGroupHomeomorphEquiv H base ⟦cap⟧)) = FreeGroup.of ()
  rw [hhome, hside]
  exact circleFundamentalGroupFreeEquiv_oneTurn θ

set_option backward.isDefEq.respectTransparency false in
/-- The actual positive outer boundary word, based at the literal right
overlap crossing, is lower generator followed by upper generator.  The two
cap loops cancel their shared overlap chord; multiplication reverses path
traversal in the fundamental group. -/
theorem twoPuncturedDiskOuterBoundaryLoop_freeWord
    {α β R : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β)
    (hβ1 : β < 1) (hαβ : α < β)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    let q := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      ⟦(twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR).cast
        (by
          apply Subtype.ext
          simp [q, twoPuncturedDiskOuterRightOverlapPoint,
            twoPuncturedDiskOverlapHomeomorph])
        (by
          apply Subtype.ext
          simp [q, twoPuncturedDiskOuterRightOverlapPoint,
            twoPuncturedDiskOverlapHomeomorph])⟧ =
      FreeGroup.of true * FreeGroup.of false := by
  dsimp only
  let q := twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR
  let U := twoPuncturedDiskLowerRelativeSide α β
  let V := twoPuncturedDiskUpperRelativeSide α β
  let lowerCap := twoPuncturedDiskOuterLowerCapLoop
    hα hα1 hβ hβ1 hαβ hαR hβR hR
  let upperCap := twoPuncturedDiskOuterUpperCapLoop
    hα hα1 hβ hβ1 hαβ hαR hβR hR
  let lowerInc := twoOpenCoverAmalgamInclusion U
  let upperInc := twoOpenCoverAmalgamInclusion V
  have hbase : q.1 = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [q, twoPuncturedDiskOuterRightOverlapPoint,
        twoPuncturedDiskOverlapHomeomorph]
  have hpointLower :
      lowerInc (twoPuncturedDiskLowerRelativePointOfOverlap q) = q.1 := rfl
  have hpointUpper :
      upperInc (twoPuncturedDiskUpperRelativePointOfOverlap q) = q.1 := rfl
  let lowerDiskCap : Path q.1 q.1 :=
    (lowerCap.map lowerInc.continuous).cast hpointLower.symm hpointLower.symm
  let upperDiskCap : Path q.1 q.1 :=
    (upperCap.map upperInc.continuous).cast hpointUpper.symm hpointUpper.symm
  have hlowerMap :
      twoOpenCoverSideToAmbient U V q true ⟦lowerCap⟧ =
        ⟦lowerCap.map lowerInc.continuous⟧ := by
    change FundamentalGroup.map lowerInc
      (twoOpenCoverAmalgamOverlapLeft U V q) ⟦lowerCap⟧ = _
    rw [FundamentalGroup.map_apply]
    rfl
  have hupperMap :
      twoOpenCoverSideToAmbient U V q false ⟦upperCap⟧ =
        ⟦upperCap.map upperInc.continuous⟧ := by
    change FundamentalGroup.map upperInc
      (twoOpenCoverAmalgamOverlapRight U V q) ⟦upperCap⟧ = _
    rw [FundamentalGroup.map_apply]
    rfl
  have hlowerCapCast :
      (⟦lowerCap.map lowerInc.continuous⟧ :
        FundamentalGroup (twoPuncturedUnitDiskPoint α β) q.1) = ⟦lowerDiskCap⟧ := by
    simp [lowerDiskCap]
  have hupperCapCast :
      (⟦upperCap.map upperInc.continuous⟧ :
        FundamentalGroup (twoPuncturedUnitDiskPoint α β) q.1) = ⟦upperDiskCap⟧ := by
    simp [upperDiskCap]
  have hlowerWord :
      twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
        (twoOpenCoverSideToAmbient U V q true ⟦lowerCap⟧) = FreeGroup.of true := by
    have hside : twoPuncturedDiskRelativeSideFreeEquiv
        hα hα1 hβ hβ1 hαβ q true ⟦lowerCap⟧ = FreeGroup.of () := by
      change twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)
        ⟦twoPuncturedDiskOuterLowerCapLoop
          hα hα1 hβ hβ1 hαβ hαR hβR hR⟧ = FreeGroup.of ()
      exact twoPuncturedDiskOuterLowerCapLoop_sideFreeGenerator
        hα hα1 hβ hβ1 hαβ hαR hβR hR
    have hclass : ⟦lowerCap⟧ =
        (twoPuncturedDiskRelativeSideFreeEquiv
          hα hα1 hβ hβ1 hαβ q true).symm (FreeGroup.of ()) := by
      apply (twoPuncturedDiskRelativeSideFreeEquiv
        hα hα1 hβ hβ1 hαβ q true).injective
      rw [hside]
      simp
    rw [hclass]
    exact twoPuncturedDiskFundamentalGroupFreeEquiv_positiveGenerator
      hα hα1 hβ hβ1 hαβ q true
  have hupperWord :
      twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
        (twoOpenCoverSideToAmbient U V q false ⟦upperCap⟧) = FreeGroup.of false := by
    have hside : twoPuncturedDiskRelativeSideFreeEquiv
        hα hα1 hβ hβ1 hαβ q false ⟦upperCap⟧ = FreeGroup.of () := by
      change twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ
        (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)
        ⟦twoPuncturedDiskOuterUpperCapLoop
          hα hα1 hβ hβ1 hαβ hαR hβR hR⟧ = FreeGroup.of ()
      exact twoPuncturedDiskOuterUpperCapLoop_sideFreeGenerator
        hα hα1 hβ hβ1 hαβ hαR hβR hR
    have hclass : ⟦upperCap⟧ =
        (twoPuncturedDiskRelativeSideFreeEquiv
          hα hα1 hβ hβ1 hαβ q false).symm (FreeGroup.of ()) := by
      apply (twoPuncturedDiskRelativeSideFreeEquiv
        hα hα1 hβ hβ1 hαβ q false).injective
      rw [hside]
      simp
    rw [hclass]
    exact twoPuncturedDiskFundamentalGroupFreeEquiv_positiveGenerator
      hα hα1 hβ hβ1 hαβ q false
  have hleft :
      (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR).1 =
        twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR := by
    apply Subtype.ext
    simp [twoPuncturedDiskOuterLeftOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  have hoverRight :
      (twoOpenCoverAmalgamInclusion (U ∩ V)) q = q.1 := rfl
  have hoverLeft :
      (twoOpenCoverAmalgamInclusion (U ∩ V))
        (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR) =
          (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR).1 := rfl
  let chordRaw := (twoPuncturedDiskOuterOverlapConnector hαβ hαR hβR hR).map
    (twoOpenCoverAmalgamInclusion (U ∩ V)).continuous
  let chord : Path q.1
      (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR).1 :=
    chordRaw.cast hoverRight.symm hoverLeft.symm
  have hcompLower :
      lowerInc.comp (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToLower) =
        twoOpenCoverAmalgamInclusion (U ∩ V) := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hcompUpper :
      upperInc.comp (Internal.TwoPuncturedDiskOuterBoundaryWordHelpers.twoPuncturedDiskOuterOverlapToUpper) =
        twoOpenCoverAmalgamInclusion (U ∩ V) := by
    apply ContinuousMap.ext
    intro z
    rfl
  have hpathLower :
      lowerDiskCap =
        chord.trans ((twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR).cast
          hleft hbase) := by
    apply Path.ext
    funext t
    change lowerInc (lowerCap t) =
      (chord.trans ((twoPuncturedDiskOuterLeftToRightArc
        hαβ hαR hβR hR).cast hleft hbase)) t
    simp only [lowerCap, twoPuncturedDiskOuterLowerCapLoop, Path.trans_apply]
    split_ifs
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  have hpathUpper :
      upperDiskCap =
        ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).cast
          hbase hleft).trans chord.symm := by
    apply Path.ext
    funext t
    change upperInc (upperCap t) =
      (((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).cast
        hbase hleft).trans chord.symm) t
    simp only [upperCap, twoPuncturedDiskOuterUpperCapLoop, Path.trans_apply]
    split_ifs
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl
  have hproduct :
      (twoOpenCoverSideToAmbient U V q true ⟦lowerCap⟧) *
          twoOpenCoverSideToAmbient U V q false ⟦upperCap⟧ =
      ⟦(twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR).cast hbase hbase⟧ := by
    change _ = (⟦(twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR).cast hbase hbase⟧ :
      FundamentalGroup (twoPuncturedUnitDiskPoint α β) q.1)
    rw [hlowerMap, hupperMap, hlowerCapCast, hupperCapCast,
      FundamentalGroup.mul_def]
    rw [hpathUpper, hpathLower]
    change
      Path.Homotopic.Quotient.trans
        (Path.Homotopic.Quotient.mk
          (((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).cast
            hbase hleft).trans chord.symm))
        (Path.Homotopic.Quotient.mk
          (chord.trans ((twoPuncturedDiskOuterLeftToRightArc
            hαβ hαR hβR hR).cast hleft hbase))) =
        Path.Homotopic.Quotient.mk
          ((twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR).cast hbase hbase)
    simp only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_assoc]
    rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk chord))
      (Path.Homotopic.Quotient.mk chord),
      Path.Homotopic.Quotient.symm_trans,
      Path.Homotopic.Quotient.refl_trans]
    have hpaths :
        ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).cast
          hbase hleft).trans
          ((twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR).cast
            hleft hbase) =
          ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).trans
            (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR)).cast
              hbase hbase := by
      symm
      exact Path.cast_trans _ _ hbase hleft hbase
    have houter := congrArg
      (fun p : Path.Homotopic.Quotient
        (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR)
        (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR) =>
          p.cast hbase hbase)
      (twoPuncturedDiskOuterArcs_oneTurn_class hαβ hαR hβR hR)
    rw [← Path.Homotopic.Quotient.mk_trans, hpaths]
    exact houter
  rw [← hproduct]
  rw [map_mul, hlowerWord, hupperWord]

#print axioms twoPuncturedDiskOuterBoundaryLoop_freeWord

#print axioms twoPuncturedDiskOuterLowerCapLoop_radialMap_homotopic_oneTurn
#print axioms twoPuncturedDiskOuterLowerCapLoop_sideFreeGenerator


end

end SystolicGrowth
