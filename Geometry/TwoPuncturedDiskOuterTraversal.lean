module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoPuncturedDiskVanKampen
public import Geometry.CircleOneTurnRebase
public import Geometry.CircleCutArcHeight

@[expose] public section

/-!
# The interior outer circle and its literal overlap connector

This module records the concrete geometric cut data needed to split a
positive outer boundary traversal into the upper and lower side loops.  The
circle lies in the original twice-punctured disk carrier, and the horizontal
connector is a path in its actual open overlap.  The loop-word factorization
is not asserted here.
-/

open Set Metric
open scoped ContinuousMap Topology unitInterval

namespace SystolicGrowth

noncomputable section

/-- The outer circle of radius `R`, as a map into the original punctured disk. -/
def twoPuncturedDiskOuterBoundaryCircle (α β R : ℝ)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    C(Circle, twoPuncturedUnitDiskPoint α β) where
  toFun θ := ⟨(R : ℂ) * (θ : ℂ), by
    have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
    refine ⟨?_, ?_, ?_⟩
    · change dist ((R : ℂ) * (θ : ℂ)) 0 < 1
      rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hRpos, Circle.norm_coe, mul_one]
      exact hR
    · intro hz
      have hn := congrArg norm hz
      have hEq : R = |α| := by
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
          twoPuncturedDiskLeftCenter_norm, abs_of_pos hRpos] using hn
      linarith [hEq]
    · intro hz
      have hn := congrArg norm hz
      have hEq : R = |β| := by
        simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, Circle.norm_coe,
          twoPuncturedDiskRightCenter_norm, abs_of_pos hRpos] using hn
      linarith [hEq]⟩
  continuous_toFun :=
    (continuous_const.mul continuous_subtype_val).subtype_mk _

@[simp]
theorem twoPuncturedDiskOuterBoundaryCircle_val (α β R : ℝ)
    (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) (θ : Circle) :
    (twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR θ).1 =
      (R : ℂ) * (θ : ℂ) := rfl

/-- Height of the horizontal cut strictly between the two punctures. -/
def twoPuncturedDiskOuterCutHeight (α β : ℝ) : ℝ := (α + β) / 2

/-- The positive half-width of the horizontal chord where the outer circle
meets the overlap midline. -/
def twoPuncturedDiskOuterCutHalfWidth (α β R : ℝ) : ℝ :=
  Real.sqrt (R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2)

theorem twoPuncturedDiskOuterCutHeight_mem {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) :
    -R < twoPuncturedDiskOuterCutHeight α β ∧
      twoPuncturedDiskOuterCutHeight α β < R := by
  have hαlo : -R < α := (abs_lt.mp hαR).1
  have hαhi : α < R := (abs_lt.mp hαR).2
  have hβlo : -R < β := (abs_lt.mp hβR).1
  have hβhi : β < R := (abs_lt.mp hβR).2
  constructor <;> dsimp [twoPuncturedDiskOuterCutHeight] <;> linarith

theorem twoPuncturedDiskOuterCutHalfWidth_pos {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) :
    0 < twoPuncturedDiskOuterCutHalfWidth α β R := by
  have hm := twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hRad : 0 < R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
    nlinarith [hm.1, hm.2, hRpos]
  apply Real.sqrt_pos.2
  exact hRad

theorem Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_norm {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (s : ℝ) (hs : s = twoPuncturedDiskOuterCutHalfWidth α β R) :
    ‖(s : ℂ) + (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I‖ = R := by
  have hm := twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hsquare : s ^ 2 = R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
    have hRad : 0 ≤ R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
      nlinarith
    simpa [hs, twoPuncturedDiskOuterCutHalfWidth] using Real.sq_sqrt hRad
  rw [Complex.norm_add_mul_I]
  have hsum : s ^ 2 + twoPuncturedDiskOuterCutHeight α β ^ 2 = R ^ 2 := by
    rw [hsquare]
    ring
  rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos hRpos]

theorem Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_neg_norm {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (s : ℝ) (hs : s = twoPuncturedDiskOuterCutHalfWidth α β R) :
    ‖-(s : ℂ) + (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I‖ = R := by
  have hm := twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hsquare : s ^ 2 = R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
    have hRad : 0 ≤ R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
      nlinarith
    simpa [hs, twoPuncturedDiskOuterCutHalfWidth] using Real.sq_sqrt hRad
  have hneg : -(s : ℂ) = ((-s : ℝ) : ℂ) := by push_cast; rfl
  rw [hneg]
  rw [Complex.norm_add_mul_I]
  have hsum : (-s) ^ 2 + twoPuncturedDiskOuterCutHeight α β ^ 2 = R ^ 2 := by
    rw [neg_sq, hsquare]
    ring
  rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos hRpos]

/-- The right boundary point on the overlap midline, as a point of the actual
twice-punctured disk. -/
def twoPuncturedDiskOuterRightCutPoint {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    twoPuncturedUnitDiskPoint α β := by
  let s := twoPuncturedDiskOuterCutHalfWidth α β R
  let z : ℂ := (s : ℂ) + (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I
  have hs : s = twoPuncturedDiskOuterCutHalfWidth α β R := rfl
  refine ⟨z, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change dist z 0 < 1
    rw [dist_zero_right, show z = (s : ℂ) +
      (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I from rfl,
      Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_norm hαβ hαR hβR s hs]
    exact hR
  · intro hz
    have hn := congrArg norm hz
    have hz' : z = (s : ℂ) +
        (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I := rfl
    rw [hz'] at hn
    have hcenter := twoPuncturedDiskLeftCenter_norm α
    have hnorm := Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_norm hαβ hαR hβR s hs
    rw [hcenter, hnorm] at hn
    linarith
  · intro hz
    have hn := congrArg norm hz
    have hz' : z = (s : ℂ) +
        (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I := rfl
    rw [hz'] at hn
    have hcenter := twoPuncturedDiskRightCenter_norm β
    have hnorm := Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_norm hαβ hαR hβR s hs
    rw [hcenter, hnorm] at hn
    linarith

/-- The left boundary point on the overlap midline, as a point of the actual
twice-punctured disk. -/
def twoPuncturedDiskOuterLeftCutPoint {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    twoPuncturedUnitDiskPoint α β := by
  let s := twoPuncturedDiskOuterCutHalfWidth α β R
  let z : ℂ := -(s : ℂ) + (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I
  have hs : s = twoPuncturedDiskOuterCutHalfWidth α β R := rfl
  refine ⟨z, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · change dist z 0 < 1
    rw [dist_zero_right, show z = -(s : ℂ) +
      (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I from rfl,
      Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_neg_norm hαβ hαR hβR s hs]
    exact hR
  · intro hz
    have hn := congrArg norm hz
    have hz' : z = -(s : ℂ) +
        (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I := rfl
    rw [hz'] at hn
    have hcenter := twoPuncturedDiskLeftCenter_norm α
    have hnorm := Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_neg_norm hαβ hαR hβR s hs
    rw [hcenter, hnorm] at hn
    linarith
  · intro hz
    have hn := congrArg norm hz
    have hz' : z = -(s : ℂ) +
        (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I := rfl
    rw [hz'] at hn
    have hcenter := twoPuncturedDiskRightCenter_norm β
    have hnorm := Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_neg_norm hαβ hαR hβR s hs
    rw [hcenter, hnorm] at hn
    linarith

/-- The right boundary cut point is in the actual open overlap. -/
theorem twoPuncturedDiskOuterRightCutPoint_mem_overlap {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 ∈
      twoPuncturedDiskOverlap α β := by
  let s := twoPuncturedDiskOuterCutHalfWidth α β R
  change (↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I) ∈ _
  have hm := twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR
  have him : (↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I).im =
      twoPuncturedDiskOuterCutHeight α β := by
    simp [twoPuncturedDiskOuterCutHeight]
  unfold twoPuncturedDiskOverlap
  refine ⟨?_, ?_⟩
  · change dist (↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I) 0 < 1
    rw [dist_zero_right, Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_norm hαβ hαR hβR s rfl]
    exact hR
  · change twoPuncturedDiskOverlapLower α β <
      (↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I).im ∧
        (↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I).im <
          twoPuncturedDiskOverlapUpper α β
    rw [him]
    constructor <;> dsimp [twoPuncturedDiskOverlapLower,
      twoPuncturedDiskOverlapUpper, twoPuncturedDiskOuterCutHeight] <;> linarith

/-- The left boundary cut point is in the actual open overlap. -/
theorem twoPuncturedDiskOuterLeftCutPoint_mem_overlap {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 ∈
      twoPuncturedDiskOverlap α β := by
  let s := twoPuncturedDiskOuterCutHalfWidth α β R
  change (-↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I) ∈ _
  have hm := twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR
  have him : (-↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I).im =
      twoPuncturedDiskOuterCutHeight α β := by
    simp [twoPuncturedDiskOuterCutHeight]
  unfold twoPuncturedDiskOverlap
  refine ⟨?_, ?_⟩
  · change dist (-↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I) 0 < 1
    rw [dist_zero_right, Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_neg_norm hαβ hαR hβR s rfl]
    exact hR
  · change twoPuncturedDiskOverlapLower α β <
      (-↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I).im ∧
        (-↑s + ↑(twoPuncturedDiskOuterCutHeight α β) * Complex.I).im <
          twoPuncturedDiskOverlapUpper α β
    rw [him]
    constructor <;> dsimp [twoPuncturedDiskOverlapLower,
      twoPuncturedDiskOverlapUpper, twoPuncturedDiskOuterCutHeight] <;> linarith

def Internal.TwoPuncturedDiskOuterTraversalHelpers.pathIntoSubtype {Y : Type*} [TopologicalSpace Y] {A : Set Y}
    {x y : Y} (p : Path x y) (hmem : ∀ t, p t ∈ A) :
    Path (⟨x, p.source ▸ hmem 0⟩ : {z : Y // z ∈ A})
      (⟨y, p.target ▸ hmem 1⟩ : {z : Y // z ∈ A}) where
  toFun t := ⟨p t, hmem t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- The right cut endpoint represented in the literal open-overlap carrier. -/
def twoPuncturedDiskOuterRightOverlapPoint {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskRelativeOverlap α β} :=
  (twoPuncturedDiskOverlapHomeomorph hαβ).symm
    ⟨(twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1,
      twoPuncturedDiskOuterRightCutPoint_mem_overlap hαβ hαR hβR hR⟩

/-- The left cut endpoint represented in the literal open-overlap carrier. -/
def twoPuncturedDiskOuterLeftOverlapPoint {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    {z : twoPuncturedUnitDiskPoint α β // z ∈ twoPuncturedDiskRelativeOverlap α β} :=
  (twoPuncturedDiskOverlapHomeomorph hαβ).symm
    ⟨(twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1,
      twoPuncturedDiskOuterLeftCutPoint_mem_overlap hαβ hαR hβR hR⟩

/-- The straight horizontal chord between the circle's two overlap crossings,
as a path in the literal overlap of the original punctured disk. -/
def twoPuncturedDiskOuterOverlapConnector {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path (twoPuncturedDiskOuterRightOverlapPoint hαβ hαR hβR hR)
      (twoPuncturedDiskOuterLeftOverlapPoint hαβ hαR hβR hR) := by
  let zR := (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1
  let zL := (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1
  have hRmem : zR ∈ twoPuncturedDiskOverlap α β :=
    twoPuncturedDiskOuterRightCutPoint_mem_overlap hαβ hαR hβR hR
  have hLmem : zL ∈ twoPuncturedDiskOverlap α β :=
    twoPuncturedDiskOuterLeftCutPoint_mem_overlap hαβ hαR hβR hR
  have hseg : ∀ t : unitInterval, Path.segment zR zL t ∈ twoPuncturedDiskOverlap α β := by
    intro t
    have ht : Path.segment zR zL t ∈ Set.range (Path.segment zR zL) := ⟨t, rfl⟩
    rw [Path.range_segment] at ht
    exact (twoPuncturedDiskOverlap_convex α β).segment_subset hRmem hLmem ht
  let chord := Internal.TwoPuncturedDiskOuterTraversalHelpers.pathIntoSubtype (Path.segment zR zL) hseg
  change Path
    ((twoPuncturedDiskOverlapHomeomorph hαβ).symm ⟨zR, hRmem⟩)
    ((twoPuncturedDiskOverlapHomeomorph hαβ).symm ⟨zL, hLmem⟩)
  exact chord.map (twoPuncturedDiskOverlapHomeomorph hαβ).symm.continuous

private theorem twoPuncturedDiskOuterRightCutPoint_norm {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    ‖(twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1‖ = R := by
  change ‖(twoPuncturedDiskOuterCutHalfWidth α β R : ℂ) +
      (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I‖ = R
  exact Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_norm hαβ hαR hβR _ rfl

private theorem twoPuncturedDiskOuterLeftCutPoint_norm {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    ‖(twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1‖ = R := by
  change ‖-(twoPuncturedDiskOuterCutHalfWidth α β R : ℂ) +
      (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I‖ = R
  exact Internal.TwoPuncturedDiskOuterTraversalHelpers.outerCutPoint_neg_norm hαβ hαR hβR _ rfl

/-- Circle directions of the two actual outer-circle cut points. -/
noncomputable def twoPuncturedDiskOuterRightDirection {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) : Circle :=
  Circle.exp ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.arg)

noncomputable def twoPuncturedDiskOuterLeftDirection {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) : Circle :=
  Circle.exp ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1.arg)

theorem Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) (right : Bool) :
    twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
      (if right then twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR
       else twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR) =
    if right then twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR
    else twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR := by
  cases right
  · simp only [Bool.false_eq_true, if_false]
    apply Subtype.ext
    change (R : ℂ) *
      (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR : ℂ) = _
    rw [twoPuncturedDiskOuterLeftDirection, Circle.coe_exp]
    calc
      (R : ℂ) * Complex.exp
          ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1.arg * Complex.I) =
          (‖(twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1‖ : ℂ) *
            Complex.exp
              ((twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1.arg * Complex.I) := by
        rw [twoPuncturedDiskOuterLeftCutPoint_norm hαβ hαR hβR hR]
      _ = (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 :=
        Complex.norm_mul_exp_arg_mul_I _
  · simp only [if_true]
    apply Subtype.ext
    change (R : ℂ) *
      (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR : ℂ) = _
    rw [twoPuncturedDiskOuterRightDirection, Circle.coe_exp]
    calc
      (R : ℂ) * Complex.exp
          ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.arg * Complex.I) =
          (‖(twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1‖ : ℂ) *
            Complex.exp
              ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.arg * Complex.I) := by
        rw [twoPuncturedDiskOuterRightCutPoint_norm hαβ hαR hβR hR]
      _ = (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 :=
        Complex.norm_mul_exp_arg_mul_I _

private theorem twoPuncturedDiskOuterRightCutPoint_arg_bounds {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    |(twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.arg| < Real.pi / 2 := by
  apply Complex.abs_arg_lt_pi_div_two_iff.mpr
  left
  have hre :
      (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.re =
        twoPuncturedDiskOuterCutHalfWidth α β R := by
    simp [twoPuncturedDiskOuterRightCutPoint]
  rw [hre]
  exact twoPuncturedDiskOuterCutHalfWidth_pos hαβ hαR hβR

private theorem twoPuncturedDiskOuterCutPoints_star {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 =
      -(star (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1) := by
  apply Complex.ext <;>
    simp [twoPuncturedDiskOuterLeftCutPoint, twoPuncturedDiskOuterRightCutPoint]

private theorem twoPuncturedDiskOuterDirections_star_relation {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR =
      -(twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR)⁻¹ := by
  let θ := twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR
  let φ := twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR
  let γ := twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
  have hθ : γ θ = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true
  have hφ : γ φ = twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR false
  have hθval : (R : ℂ) * (θ : ℂ) =
      (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 := by
    have := congrArg Subtype.val hθ
    simpa [γ, twoPuncturedDiskOuterBoundaryCircle_val] using this
  have hφval : (R : ℂ) * (φ : ℂ) =
      (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 := by
    have := congrArg Subtype.val hφ
    simpa [γ, twoPuncturedDiskOuterBoundaryCircle_val] using this
  have hmul : (R : ℂ) * (φ : ℂ) = (R : ℂ) * (-(star (θ : ℂ))) := by
    calc
      (R : ℂ) * (φ : ℂ) =
          (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR).1 := hφval
      _ = -(star (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1) :=
        twoPuncturedDiskOuterCutPoints_star hαβ hαR hβR hR
      _ = -(star ((R : ℂ) * (θ : ℂ))) := by rw [hθval]
      _ = (R : ℂ) * (-(star (θ : ℂ))) := by simp
  have hval : (φ : ℂ) = -(star (θ : ℂ)) := mul_left_cancel₀ hRne hmul
  apply Subtype.ext
  simpa only [θ, φ, Circle.coe_neg, Circle.coe_inv_eq_conj,
    ← Complex.star_def] using hval

theorem twoPuncturedDiskOuterRightDirection_re_pos {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    0 < (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR : ℂ).re := by
  have hcoord : R *
      (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR : ℂ).re =
      twoPuncturedDiskOuterCutHalfWidth α β R := by
    have h := congrArg (fun z : twoPuncturedUnitDiskPoint α β => z.1.re)
      (Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true)
    simpa [twoPuncturedDiskOuterBoundaryCircle_val,
      twoPuncturedDiskOuterRightCutPoint] using h
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hspos : 0 < twoPuncturedDiskOuterCutHalfWidth α β R :=
    twoPuncturedDiskOuterCutHalfWidth_pos hαβ hαR hβR
  nlinarith

theorem twoPuncturedDiskOuterRightDirection_im_scaled {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    R * (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR : ℂ).im =
      twoPuncturedDiskOuterCutHeight α β := by
  have h := congrArg (fun z : twoPuncturedUnitDiskPoint α β => z.1.im)
    (Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true)
  simpa [twoPuncturedDiskOuterBoundaryCircle_val, Complex.mul_im,
    twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterCutHeight] using h

theorem twoPuncturedDiskOuterLeftDirection_im_scaled {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    R * (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR : ℂ).im =
      twoPuncturedDiskOuterCutHeight α β := by
  have h := congrArg (fun z : twoPuncturedUnitDiskPoint α β => z.1.im)
    (Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR false)
  simpa [twoPuncturedDiskOuterBoundaryCircle_val, Complex.mul_im,
    twoPuncturedDiskOuterLeftCutPoint, twoPuncturedDiskOuterCutHeight] using h

private theorem twoPuncturedDiskOuterCutHeight_mem_overlap_band {α β : ℝ}
    (hαβ : α < β) :
    twoPuncturedDiskOverlapLower α β < twoPuncturedDiskOuterCutHeight α β ∧
      twoPuncturedDiskOuterCutHeight α β < twoPuncturedDiskOverlapUpper α β := by
  dsimp [twoPuncturedDiskOverlapLower, twoPuncturedDiskOverlapUpper,
    twoPuncturedDiskOuterCutHeight]
  constructor <;> linarith

theorem twoPuncturedDiskOuterLeftDirection_val_eq_neg_star_right {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR : ℂ) =
      -star (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR : ℂ) := by
  have h := congrArg (fun z : Circle => (z : ℂ))
    (twoPuncturedDiskOuterDirections_star_relation hαβ hαR hβR hR)
  simpa only [Circle.coe_neg, Circle.coe_inv_eq_conj, ← Complex.star_def] using h

/-- The positive outer arc from the right cut point to the left cut point,
mapped into the original twice-punctured disk carrier. -/
noncomputable def twoPuncturedDiskOuterRightToLeftArc {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR)
      (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR) := by
  let γ := twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
  have hsrc : γ (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR) =
      twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true
  have htgt : γ (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR) =
      twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR false
  exact (Circle.path (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR)
    (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR)).map γ.continuous |>.cast
      hsrc.symm htgt.symm

/-- The complementary positive outer arc from the left cut point back to the
right cut point, in the same actual carrier. -/
noncomputable def twoPuncturedDiskOuterLeftToRightArc {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path (twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR)
      (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR) := by
  let γ := twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
  have hsrc : γ (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR) =
      twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR false
  have htgt : γ (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR) =
      twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true
  exact (Circle.path (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR)
    (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR)).map γ.continuous |>.cast
      hsrc.symm htgt.symm

/-- The positive one-turn outer boundary loop based at the right overlap cut
point, using the literal radius-`R` circle in the twice-punctured disk. -/
noncomputable def twoPuncturedDiskOuterBoundaryLoop {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    Path (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR)
      (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR) := by
  let γ := twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
  have hbase : γ (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR) =
      twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true
  exact (circleOneTurnLoop (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR)).map
    γ.continuous |>.cast hbase.symm hbase.symm

/-- Cutting the literal positive outer loop at the two overlap crossings gives
the two positive arcs, in their traversal order. -/
theorem twoPuncturedDiskOuterArcs_homotopic_boundaryLoop {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).trans
      (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR)).Homotopic
        (twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR) := by
  let θ := twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR
  let φ := twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR
  let γ := twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
  have hθ : γ θ = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR true
  have hφ : γ φ = twoPuncturedDiskOuterLeftCutPoint hαβ hαR hβR hR :=
    Internal.TwoPuncturedDiskOuterTraversalHelpers.twoPuncturedDiskOuterBoundaryCircle_cutPoint_eq hαβ hαR hβR hR false
  have hneq : θ ≠ φ := by
    intro heq
    have hcut := congrArg γ heq
    rw [hθ, hφ] at hcut
    have hre := congrArg (fun z : twoPuncturedUnitDiskPoint α β => z.1.re) hcut
    have hs := twoPuncturedDiskOuterCutHalfWidth_pos hαβ hαR hβR
    simp [twoPuncturedDiskOuterRightCutPoint, twoPuncturedDiskOuterLeftCutPoint] at hre
    linarith
  have hcircles :
      ((Circle.path θ φ).trans (Circle.path φ θ)).Homotopic
        (circleOneTurnLoop θ) :=
    circlePath_trans_circlePath_homotopic_oneTurn hneq
  have hmap := Path.Homotopic.map hcircles γ
  have hθ' : γ θ = twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := hθ
  have hpath :
      ((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).trans
        (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR)) =
        (((Circle.path θ φ).trans (Circle.path φ θ)).map γ.continuous).cast
        hθ'.symm hθ'.symm := by
    dsimp [twoPuncturedDiskOuterRightToLeftArc, twoPuncturedDiskOuterLeftToRightArc,
      θ, φ, γ]
    rw [Path.map_trans, Path.cast_trans]
  have hloop :
      twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR =
        ((circleOneTurnLoop θ).map γ.continuous).cast hθ'.symm hθ'.symm := by
    apply Path.ext
    funext t
    simp [twoPuncturedDiskOuterBoundaryLoop, θ, γ, Path.cast_coe, Path.map_coe]
  rw [hpath, hloop]
  exact hmap.pathCast hθ'.symm hθ'.symm

/-- The literal product of the two positive outer arcs is the positive outer
boundary class in the actual twice-punctured disk. -/
theorem twoPuncturedDiskOuterArcs_oneTurn_class {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1) :
    (⟦(twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR).trans
        (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR)⟧ :
      FundamentalGroup (twoPuncturedUnitDiskPoint α β)
        (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR)) =
      ⟦twoPuncturedDiskOuterBoundaryLoop hαβ hαR hβR hR⟧ :=
  Path.Homotopic.Quotient.eq.mpr
    (twoPuncturedDiskOuterArcs_homotopic_boundaryLoop hαβ hαR hβR hR)

@[simp]
theorem twoPuncturedDiskOuterRightToLeftArc_apply {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t =
      twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
        (Circle.path (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR)
          (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR) t) := by
  simp [twoPuncturedDiskOuterRightToLeftArc]

@[simp]
theorem twoPuncturedDiskOuterLeftToRightArc_apply {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t =
      twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
        (Circle.path (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR)
          (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR) t) := by
  simp [twoPuncturedDiskOuterLeftToRightArc]

theorem twoPuncturedDiskOuterRightToLeftArc_im {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1.im =
      R * (Circle.path (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR)
        (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR) t : ℂ).im := by
  rw [twoPuncturedDiskOuterRightToLeftArc_apply,
    twoPuncturedDiskOuterBoundaryCircle_val]
  simp

theorem twoPuncturedDiskOuterLeftToRightArc_im {α β R : ℝ}
    (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R) (hR : R < 1)
    (t : unitInterval) :
    (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1.im =
      R * (Circle.path (twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR)
        (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR) t : ℂ).im := by
  rw [twoPuncturedDiskOuterLeftToRightArc_apply,
    twoPuncturedDiskOuterBoundaryCircle_val]
  simp

/-- The positive arc from the right cut point to the left cut point stays in
the actual upper member of the two-open cover. -/
theorem twoPuncturedDiskOuterRightToLeftArc_mem_upperRelativeSide
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) (t : unitInterval) :
    twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t ∈
      twoPuncturedDiskUpperRelativeSide α β := by
  let θ := twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR
  let φ := twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hheight : twoPuncturedDiskOuterCutHeight α β ≤
      R * ((Circle.path θ φ t : Circle) : ℂ).im := by
    rw [← twoPuncturedDiskOuterRightDirection_im_scaled hαβ hαR hβR hR]
    exact mul_le_mul_of_nonneg_left
      (circle_path_im_ge_source_of_re_pos_reflection
        (twoPuncturedDiskOuterRightDirection_re_pos hαβ hαR hβR hR)
        (twoPuncturedDiskOuterLeftDirection_val_eq_neg_star_right
          hαβ hαR hβR hR) t)
      (le_of_lt hRpos)
  have hArcHeight : twoPuncturedDiskOuterCutHeight α β ≤
      (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1.im := by
    rw [twoPuncturedDiskOuterRightToLeftArc_im]
    exact hheight
  have hband := twoPuncturedDiskOuterCutHeight_mem_overlap_band hαβ
  have hcarrier := (twoPuncturedDiskOuterRightToLeftArc
    hαβ hαR hβR hR t).2
  rcases hcarrier with ⟨hball, hleft, hright⟩
  change (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1 ∈
    twoPuncturedDiskUpperSide α β
  change (((twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1 ∈
      Metric.ball (0 : ℂ) 1 ∧
      twoPuncturedDiskOverlapLower α β <
        (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1.im) ∧
    (twoPuncturedDiskOuterRightToLeftArc hαβ hαR hβR hR t).1 ≠
      twoPuncturedDiskRightCenter β)
  exact ⟨⟨hball, lt_of_lt_of_le hband.1 hArcHeight⟩, hright⟩

/-- The complementary positive arc from the left cut point to the right cut
point stays in the actual lower member of the two-open cover. -/
theorem twoPuncturedDiskOuterLeftToRightArc_mem_lowerRelativeSide
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) (t : unitInterval) :
    twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t ∈
      twoPuncturedDiskLowerRelativeSide α β := by
  let θ := twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR
  let φ := twoPuncturedDiskOuterLeftDirection hαβ hαR hβR hR
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hheight : R * ((Circle.path φ θ t : Circle) : ℂ).im ≤
      twoPuncturedDiskOuterCutHeight α β := by
    calc
      R * ((Circle.path φ θ t : Circle) : ℂ).im ≤ R * (θ : ℂ).im :=
        mul_le_mul_of_nonneg_left
          (circle_path_im_le_source_of_re_pos_reflection
            (twoPuncturedDiskOuterRightDirection_re_pos hαβ hαR hβR hR)
            (twoPuncturedDiskOuterLeftDirection_val_eq_neg_star_right
              hαβ hαR hβR hR) t)
          (le_of_lt hRpos)
      _ = twoPuncturedDiskOuterCutHeight α β :=
        twoPuncturedDiskOuterRightDirection_im_scaled hαβ hαR hβR hR
  have hArcHeight :
      (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1.im ≤
        twoPuncturedDiskOuterCutHeight α β := by
    rw [twoPuncturedDiskOuterLeftToRightArc_im]
    exact hheight
  have hband := twoPuncturedDiskOuterCutHeight_mem_overlap_band hαβ
  have hcarrier := (twoPuncturedDiskOuterLeftToRightArc
    hαβ hαR hβR hR t).2
  rcases hcarrier with ⟨hball, hleft, hright⟩
  change (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1 ∈
    twoPuncturedDiskLowerSide α β
  change (((twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1 ∈
      Metric.ball (0 : ℂ) 1 ∧
      (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1.im <
        twoPuncturedDiskOverlapUpper α β) ∧
    (twoPuncturedDiskOuterLeftToRightArc hαβ hαR hβR hR t).1 ≠
      twoPuncturedDiskLeftCenter α)
  exact ⟨⟨hball, lt_of_le_of_lt hArcHeight hband.2⟩, hleft⟩

end

end SystolicGrowth

#print axioms SystolicGrowth.twoPuncturedDiskOuterBoundaryCircle
#print axioms SystolicGrowth.twoPuncturedDiskOuterOverlapConnector
#print axioms SystolicGrowth.twoPuncturedDiskOuterBoundaryLoop
#print axioms SystolicGrowth.twoPuncturedDiskOuterRightDirection_re_pos
#print axioms SystolicGrowth.twoPuncturedDiskOuterRightDirection_im_scaled
#print axioms SystolicGrowth.twoPuncturedDiskOuterLeftDirection_im_scaled
#print axioms SystolicGrowth.twoPuncturedDiskOuterLeftDirection_val_eq_neg_star_right
#print axioms SystolicGrowth.twoPuncturedDiskOuterRightToLeftArc
#print axioms SystolicGrowth.twoPuncturedDiskOuterLeftToRightArc
#print axioms SystolicGrowth.twoPuncturedDiskOuterRightToLeftArc_im
#print axioms SystolicGrowth.twoPuncturedDiskOuterLeftToRightArc_im
#print axioms SystolicGrowth.twoPuncturedDiskOuterRightToLeftArc_mem_upperRelativeSide
#print axioms SystolicGrowth.twoPuncturedDiskOuterLeftToRightArc_mem_lowerRelativeSide
#print axioms SystolicGrowth.twoPuncturedDiskOuterArcs_homotopic_boundaryLoop
#print axioms SystolicGrowth.twoPuncturedDiskOuterArcs_oneTurn_class
