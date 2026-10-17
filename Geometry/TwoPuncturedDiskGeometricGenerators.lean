module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.TwoPuncturedDiskFreePresentation
public import Geometry.TwoPuncturedDiskSideCircle
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# Geometric generators for the twice-punctured disk

The free generators are represented by literal positive small circles in the
actual side domains, based at the actual overlap point by the radial homotopy
track. No loop is defined by pulling a generator back through a group
equivalence.
-/

open Set
open scoped ContinuousMap unitInterval

namespace SystolicGrowth

noncomputable section

/-- The actual radial push preserves normalized circle direction. -/
private theorem convexPuncturedUnitDirection_radialPush {ρ : ℝ} (hρ : 0 < ρ)
    (t : I) {z : ℂ} (hz : z ≠ 0) :
    convexPuncturedUnitDirection (convexPuncturedRadialPush ρ t z)
      (convexPuncturedRadialPush_ne_zero hρ t hz) =
      convexPuncturedUnitDirection z hz := by
  apply Circle.ext
  simp only [convexPuncturedUnitDirection]
  rw [convexPuncturedRadialPush_eq_scale]
  let a : ℝ := (1 - (t : ℝ)) + (t : ℝ) * (ρ / ‖z‖)
  have ha : 0 < a :=
    convexPuncturedRadialPush_scale_pos hρ t hz
  change ‖a • z‖⁻¹ • (a • z) = ‖z‖⁻¹ • z
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  apply congrArg (fun r : ℝ => r • z)
  field_simp [ne_of_gt ha, ne_of_gt (norm_pos_iff.mpr hz)]

/-- The actual radial deformation track from a punctured-base point to the
literal small circle at its normalized direction. -/
def puncturedBaseCircleActualTrack (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B)
    (z : puncturedBaseAt B c) :
    Path z (puncturedBaseCircleInclusion B c ρ hB hρ hcircle
      (puncturedBaseCircleRetraction B c z)) := by
  let Ω := puncturedBaseTranslated B c
  let T := puncturedBaseTranslationHomeomorph B c
  have hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω := by
    intro θ
    change (ρ • (θ : ℂ)) + c ∈ B
    rw [add_comm]
    exact hcircle θ
  let p := ((convexPuncturedDomainCircleDeformationRetraction Ω ρ
      (puncturedBaseTranslated_convex hB c) hρ hΩcircle).toHomotopy.evalAt (T z)).map
    T.symm.continuous
  have hstart : z = T.symm (T z) := (T.symm_apply_apply z).symm
  have hend : puncturedBaseCircleInclusion B c ρ hB hρ hcircle
        (puncturedBaseCircleRetraction B c z) =
      T.symm (convexPuncturedCircleInclusion Ω ρ hρ hΩcircle
        (convexPuncturedCircleRetraction Ω (T z))) := by
    rfl
  exact p.cast hstart hend

/-- The literal included one-turn circle, conjugated by the actual radial
track from the chosen based point. -/
def puncturedBaseCircleBasedPositiveLoop (B : Set ℂ) (c : ℂ) (ρ : ℝ)
    (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B)
    (z : puncturedBaseAt B c) : Path z z := by
  let p := puncturedBaseCircleActualTrack B c ρ hB hρ hcircle z
  exact p.trans (((circleOneTurnLoop (puncturedBaseCircleRetraction B c z)).map
      (puncturedBaseCircleInclusion B c ρ hB hρ hcircle).continuous).trans p.symm)

/-- Radial normalization is constant along its own actual deformation track. -/
private theorem puncturedBaseCircleActualTrack_map_retraction
    (B : Set ℂ) (c : ℂ) (ρ : ℝ) (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B)
    (z : puncturedBaseAt B c) :
    ((puncturedBaseCircleActualTrack B c ρ hB hρ hcircle z).map
      (puncturedBaseCircleRetraction B c).continuous).cast rfl
        (puncturedBaseCircleRetraction_inclusion B c ρ hB hρ hcircle
          (puncturedBaseCircleRetraction B c z)).symm =
        Path.refl (puncturedBaseCircleRetraction B c z) := by
  let Ω := puncturedBaseTranslated B c
  let T := puncturedBaseTranslationHomeomorph B c
  have hΩcircle : ∀ θ : Circle, ρ • (θ : ℂ) ∈ Ω := by
    intro θ
    change (ρ • (θ : ℂ)) + c ∈ B
    rw [add_comm]
    exact hcircle θ
  let H := (convexPuncturedDomainCircleDeformationRetraction Ω ρ
    (puncturedBaseTranslated_convex hB c) hρ hΩcircle).toHomotopy
  apply Path.ext
  funext t
  change puncturedBaseCircleRetraction B c
      (T.symm (H.evalAt (T z) t)) = puncturedBaseCircleRetraction B c z
  simp only [puncturedBaseCircleRetraction, ContinuousMap.comp_apply,
    T, puncturedBaseTranslationHomeomorph]
  change convexPuncturedCircleRetraction Ω
      (T (T.symm (H.evalAt (T z) t))) =
    convexPuncturedCircleRetraction Ω (T z)
  rw [T.apply_symm_apply]
  change convexPuncturedUnitDirection
      (convexPuncturedRadialPush ρ t (T z).1)
        (convexPuncturedRadialPush_ne_zero hρ t (T z).2.2) =
    convexPuncturedUnitDirection (T z).1 (T z).2.2
  exact convexPuncturedUnitDirection_radialPush hρ t (T z).2.2

/-- A loop conjugated by a path whose image is null as a based connector has
the same mapped class as the included loop. The endpoint equality is kept
explicit so the statement applies to genuine subtype-valued circle maps. -/
private theorem mapped_conjugate_pathClass
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} (f : C(X, Y)) (p : Path x y) (γ : Path y y)
    (h : f y = f x) {δ : Path (f x) (f x)}
    (hp : (p.map f.continuous).cast rfl h.symm = Path.refl (f x))
    (hγ : Path.Homotopic.Quotient.mk ((γ.map f.continuous).cast h.symm h.symm) =
      Path.Homotopic.Quotient.mk δ) :
    Path.Homotopic.Quotient.mk ((p.trans (γ.trans p.symm)).map f.continuous) =
      Path.Homotopic.Quotient.mk δ := by
  let p' := p.map f.continuous
  let γ' := γ.map f.continuous
  have hcast : (p'.trans (γ'.trans p'.symm)).cast rfl rfl =
      (p'.cast rfl h.symm).trans
        ((γ'.cast h.symm h.symm).trans (p'.cast rfl h.symm).symm) := by
    rw [Path.cast_trans, Path.cast_trans, Path.cast_symm]
  have hmap : (p.trans (γ.trans p.symm)).map f.continuous =
      p'.trans (γ'.trans p'.symm) := by
    rw [Path.map_trans, Path.map_trans, Path.map_symm]
  rw [hmap]
  calc
    Path.Homotopic.Quotient.mk (p'.trans (γ'.trans p'.symm)) =
        Path.Homotopic.Quotient.mk
          ((p'.trans (γ'.trans p'.symm)).cast rfl rfl) := by simp
    _ = Path.Homotopic.Quotient.mk
          ((p'.cast rfl h.symm).trans
            ((γ'.cast h.symm h.symm).trans (p'.cast rfl h.symm).symm)) :=
      congrArg Path.Homotopic.Quotient.mk hcast
    _ = Path.Homotopic.Quotient.mk δ := by
      rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
        hp, Path.Homotopic.Quotient.mk_refl,
        Path.Homotopic.Quotient.refl_trans, hγ]
      simp only [Path.Homotopic.Quotient.mk_refl, Path.refl_symm,
        Path.Homotopic.Quotient.trans_refl]

/-- The actual based loop consisting of the radial track, one positive turn
on the literal radius-`ρ` circle, and the reversed track maps to the positive
one-turn class on the normalized circle. -/
theorem puncturedBaseCircleFundamentalGroupEquiv_actualPositiveLoop
    (B : Set ℂ) (c : ℂ) (ρ : ℝ) (hB : Convex ℝ B) (hρ : 0 < ρ)
    (hcircle : ∀ θ : Circle, c + ρ • (θ : ℂ) ∈ B)
    (z : puncturedBaseAt B c) :
    puncturedBaseCircleFundamentalGroupEquiv B c ρ hB hρ hcircle z
      ⟦puncturedBaseCircleBasedPositiveLoop B c ρ hB hρ hcircle z⟧ =
        ⟦circleOneTurnLoop (puncturedBaseCircleRetraction B c z)⟧ := by
  let θ := puncturedBaseCircleRetraction B c z
  let p := puncturedBaseCircleActualTrack B c ρ hB hρ hcircle z
  let γ := (circleOneTurnLoop θ).map
    (puncturedBaseCircleInclusion B c ρ hB hρ hcircle).continuous
  let h := puncturedBaseCircleRetraction_inclusion B c ρ hB hρ hcircle θ
  have hp : (p.map (puncturedBaseCircleRetraction B c).continuous).cast rfl h.symm =
      Path.refl θ := by
    exact puncturedBaseCircleActualTrack_map_retraction B c ρ hB hρ hcircle z
  have hγ : Path.Homotopic.Quotient.mk
      ((γ.map (puncturedBaseCircleRetraction B c).continuous).cast h.symm h.symm) =
      Path.Homotopic.Quotient.mk (circleOneTurnLoop θ) := by
    have hturn := puncturedBaseCircleRetraction_oneTurn B c ρ hB hρ hcircle θ
    change FundamentalGroup.mapOfEq (puncturedBaseCircleRetraction B c) h
      (Path.Homotopic.Quotient.mk γ) = _ at hturn
    rw [FundamentalGroup.mapOfEq_apply
      (f := puncturedBaseCircleRetraction B c) (h := h)
      (p := Path.Homotopic.Quotient.mk γ),
      ← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast] at hturn
    exact hturn
  change Path.Homotopic.Quotient.mk
      ((p.trans (γ.trans p.symm)).map (puncturedBaseCircleRetraction B c).continuous) =
    Path.Homotopic.Quotient.mk (circleOneTurnLoop θ)
  exact mapped_conjugate_pathClass (puncturedBaseCircleRetraction B c) p γ h hp hγ

/-- The lower relative side's actual positive small-circle loop, based at the
chosen overlap point by the transported radial deformation track. -/
def twoPuncturedDiskLowerRelativeGeometricPositiveLoop {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    Path (twoPuncturedDiskLowerRelativePointOfOverlap q)
      (twoPuncturedDiskLowerRelativePointOfOverlap q) := by
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  exact (puncturedBaseCircleBasedPositiveLoop
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
      (twoPuncturedDiskLowerBase_convex α β)
      (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
      (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)
      (H (twoPuncturedDiskLowerRelativePointOfOverlap q))).map H.symm.continuous

set_option backward.isDefEq.respectTransparency false in
/-- The actual lower-side based loop maps to the positive generator of its
literal relative-side free group. -/
theorem twoPuncturedDiskLowerRelativeSideFreeEquiv_geometricPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q
      ⟦twoPuncturedDiskLowerRelativeGeometricPositiveLoop hα hα1 hαβ q⟧ =
        FreeGroup.of () := by
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  let z := H (twoPuncturedDiskLowerRelativePointOfOverlap q)
  let L := puncturedBaseCircleBasedPositiveLoop
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) z
  have hhome : fundamentalGroupHomeomorphEquiv H
      (twoPuncturedDiskLowerRelativePointOfOverlap q)
      ⟦twoPuncturedDiskLowerRelativeGeometricPositiveLoop hα hα1 hαβ q⟧ = ⟦L⟧ := by
    change Path.Homotopic.Quotient.mk ((L.map H.symm.continuous).map H.continuous) = _
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    change H (H.symm (L t)) = L t
    exact H.apply_symm_apply _
  change circleFundamentalGroupFreeEquiv
      (twoPuncturedDiskLowerRelativeDirection hαβ q)
      (twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ
        (H (twoPuncturedDiskLowerRelativePointOfOverlap q))
        (fundamentalGroupHomeomorphEquiv H
          (twoPuncturedDiskLowerRelativePointOfOverlap q)
          ⟦twoPuncturedDiskLowerRelativeGeometricPositiveLoop hα hα1 hαβ q⟧)) = _
  rw [hhome]
  have hdir : puncturedBaseCircleRetraction
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      (H (twoPuncturedDiskLowerRelativePointOfOverlap q)) =
        twoPuncturedDiskLowerRelativeDirection hαβ q := by
    apply Circle.ext
    rfl
  have hside : twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ
      (H (twoPuncturedDiskLowerRelativePointOfOverlap q)) ⟦L⟧ =
        ⟦circleOneTurnLoop (twoPuncturedDiskLowerRelativeDirection hαβ q)⟧ := by
    change (puncturedBaseCircleFundamentalGroupEquiv
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
      (twoPuncturedDiskLowerBase_convex α β)
      (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
      (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)
      (H (twoPuncturedDiskLowerRelativePointOfOverlap q)))
      ⟦puncturedBaseCircleBasedPositiveLoop
        (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
        (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
        (twoPuncturedDiskLowerBase_convex α β)
        (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
        (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)
        (H (twoPuncturedDiskLowerRelativePointOfOverlap q))⟧ = _
    rw [puncturedBaseCircleFundamentalGroupEquiv_actualPositiveLoop]
    cases hdir
    rfl
  rw [hside]
  exact circleFundamentalGroupFreeEquiv_oneTurn _

/-- The upper relative side's actual positive small-circle loop, based at the
chosen overlap point by the transported radial deformation track. -/
def twoPuncturedDiskUpperRelativeGeometricPositiveLoop {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    Path (twoPuncturedDiskUpperRelativePointOfOverlap q)
      (twoPuncturedDiskUpperRelativePointOfOverlap q) := by
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  exact (puncturedBaseCircleBasedPositiveLoop
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
      (twoPuncturedDiskUpperBase_convex α β)
      (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
      (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)
      (H (twoPuncturedDiskUpperRelativePointOfOverlap q))).map H.symm.continuous

/-- Rebase the lower geometric loop's endpoints to the literal overlap
inclusion used by the van Kampen side factor. -/
def Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskLowerRelativeGeometricPositiveLoopForAmalgam
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    Path (twoOpenCoverAmalgamOverlapLeft
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q)
      (twoOpenCoverAmalgamOverlapLeft
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q) := by
  have hpoint : twoPuncturedDiskLowerRelativePointOfOverlap q =
      twoOpenCoverAmalgamOverlapLeft
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q := by
    apply Subtype.ext
    rfl
  exact (twoPuncturedDiskLowerRelativeGeometricPositiveLoop hα hα1 hαβ q).cast
    hpoint hpoint

/-- Rebase the upper geometric loop's endpoints to the literal overlap
inclusion used by the van Kampen side factor. -/
def Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskUpperRelativeGeometricPositiveLoopForAmalgam
    {α β : ℝ} (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    Path (twoOpenCoverAmalgamOverlapRight
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q)
      (twoOpenCoverAmalgamOverlapRight
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q) := by
  have hpoint : twoPuncturedDiskUpperRelativePointOfOverlap q =
      twoOpenCoverAmalgamOverlapRight
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q := by
    apply Subtype.ext
    rfl
  exact (twoPuncturedDiskUpperRelativeGeometricPositiveLoop hβ hβ1 hαβ q).cast
    hpoint hpoint

set_option backward.isDefEq.respectTransparency false in
/-- The actual upper-side based loop maps to the positive generator of its
literal relative-side free group. -/
theorem twoPuncturedDiskUpperRelativeSideFreeEquiv_geometricPositiveLoop
    {α β : ℝ} (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q
      ⟦twoPuncturedDiskUpperRelativeGeometricPositiveLoop hβ hβ1 hαβ q⟧ =
        FreeGroup.of () := by
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  let z := H (twoPuncturedDiskUpperRelativePointOfOverlap q)
  let L := puncturedBaseCircleBasedPositiveLoop
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) z
  have hhome : fundamentalGroupHomeomorphEquiv H
      (twoPuncturedDiskUpperRelativePointOfOverlap q)
      ⟦twoPuncturedDiskUpperRelativeGeometricPositiveLoop hβ hβ1 hαβ q⟧ = ⟦L⟧ := by
    change Path.Homotopic.Quotient.mk ((L.map H.symm.continuous).map H.continuous) = _
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    change H (H.symm (L t)) = L t
    exact H.apply_symm_apply _
  change circleFundamentalGroupFreeEquiv
      (twoPuncturedDiskUpperRelativeDirection hαβ q)
      (twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ
        (H (twoPuncturedDiskUpperRelativePointOfOverlap q))
        (fundamentalGroupHomeomorphEquiv H
          (twoPuncturedDiskUpperRelativePointOfOverlap q)
          ⟦twoPuncturedDiskUpperRelativeGeometricPositiveLoop hβ hβ1 hαβ q⟧)) = _
  rw [hhome]
  have hdir : puncturedBaseCircleRetraction
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      (H (twoPuncturedDiskUpperRelativePointOfOverlap q)) =
        twoPuncturedDiskUpperRelativeDirection hαβ q := by
    apply Circle.ext
    rfl
  have hside : twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ
      (H (twoPuncturedDiskUpperRelativePointOfOverlap q)) ⟦L⟧ =
        ⟦circleOneTurnLoop (twoPuncturedDiskUpperRelativeDirection hαβ q)⟧ := by
    change (puncturedBaseCircleFundamentalGroupEquiv
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
      (twoPuncturedDiskUpperBase_convex α β)
      (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
      (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)
      (H (twoPuncturedDiskUpperRelativePointOfOverlap q)))
      ⟦puncturedBaseCircleBasedPositiveLoop
        (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
        (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
        (twoPuncturedDiskUpperBase_convex α β)
        (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
        (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)
        (H (twoPuncturedDiskUpperRelativePointOfOverlap q))⟧ = _
    rw [puncturedBaseCircleFundamentalGroupEquiv_actualPositiveLoop]
    cases hdir
    rfl
  rw [hside]
  exact circleFundamentalGroupFreeEquiv_oneTurn _

/-- The actual lower positive circle, included into the full twice-punctured
disk from the literal lower side, represents the `true` tagged free
generator. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_lowerGeometricPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true
        ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskLowerRelativeGeometricPositiveLoopForAmalgam
          hα hα1 hαβ q⟧) =
      FreeGroup.of true := by
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true :=
    ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskLowerRelativeGeometricPositiveLoopForAmalgam
      hα hα1 hαβ q⟧
  have hside : twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q
      ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskLowerRelativeGeometricPositiveLoopForAmalgam
        hα hα1 hαβ q⟧ = FreeGroup.of () := by
    have hpoint : twoPuncturedDiskLowerRelativePointOfOverlap q =
        twoOpenCoverAmalgamOverlapLeft
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q := by
      apply Subtype.ext
      rfl
    cases hpoint
    exact twoPuncturedDiskLowerRelativeSideFreeEquiv_geometricPositiveLoop
      hα hα1 hαβ q
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γ) = FreeGroup.of true
  rw [twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    hα hα1 hβ hβ1 hαβ q true γ]
  change FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
      (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) true
        (twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q
          ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskLowerRelativeGeometricPositiveLoopForAmalgam
            hα hα1 hαβ q⟧)) = FreeGroup.of true
  rw [hside]
  simp [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv]

/-- The actual upper positive circle, included into the full twice-punctured
disk from the literal upper side, represents the `false` tagged free
generator. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_upperGeometricPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false
        ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskUpperRelativeGeometricPositiveLoopForAmalgam
          hβ hβ1 hαβ q⟧) =
      FreeGroup.of false := by
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false :=
    ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskUpperRelativeGeometricPositiveLoopForAmalgam
      hβ hβ1 hαβ q⟧
  have hside : twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q
      ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskUpperRelativeGeometricPositiveLoopForAmalgam
        hβ hβ1 hαβ q⟧ = FreeGroup.of () := by
    have hpoint : twoPuncturedDiskUpperRelativePointOfOverlap q =
        twoOpenCoverAmalgamOverlapRight
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q := by
      apply Subtype.ext
      rfl
    cases hpoint
    exact twoPuncturedDiskUpperRelativeSideFreeEquiv_geometricPositiveLoop
      hβ hβ1 hαβ q
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γ) = FreeGroup.of false
  rw [twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    hα hα1 hβ hβ1 hαβ q false γ]
  change FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
      (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) false
        (twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q
          ⟦Internal.TwoPuncturedDiskGeometricGeneratorsHelpers.twoPuncturedDiskUpperRelativeGeometricPositiveLoopForAmalgam
            hβ hβ1 hαβ q⟧)) = FreeGroup.of false
  rw [hside]
  simp [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv]

#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_lowerGeometricPositiveLoop
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_upperGeometricPositiveLoop

end

end SystolicGrowth
