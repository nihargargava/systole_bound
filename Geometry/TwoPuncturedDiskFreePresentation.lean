module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.FreeGroupTrivialAmalgam
public import Geometry.TwoPuncturedDiskVanKampen
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

@[expose] public section

/-!
# The fundamental group of the actual twice-punctured disk

The two relative sides are carried to their literal punctured convex domains,
then to their normalized positive circle generators. Their actual based
van-Kampen amalgam over the contractible strip is therefore free on the two
tagged side generators. This module does not identify an outer boundary word.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth

noncomputable section

/-- The lower-side point corresponding to a point in the literal overlap. -/
abbrev twoPuncturedDiskLowerRelativePoint (α β : ℝ) :=
  {z : twoPuncturedUnitDiskPoint α β //
    z ∈ twoPuncturedDiskLowerRelativeSide α β}

/-- The upper-side point corresponding to a point in the literal overlap. -/
abbrev twoPuncturedDiskUpperRelativePoint (α β : ℝ) :=
  {z : twoPuncturedUnitDiskPoint α β //
    z ∈ twoPuncturedDiskUpperRelativeSide α β}

/-- View a point in the overlap as a point in the lower open side. -/
def twoPuncturedDiskLowerRelativePointOfOverlap {α β : ℝ}
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskLowerRelativePoint α β :=
  ⟨q.1, q.2.1⟩

/-- View a point in the overlap as a point in the upper open side. -/
def twoPuncturedDiskUpperRelativePointOfOverlap {α β : ℝ}
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    twoPuncturedDiskUpperRelativePoint α β :=
  ⟨q.1, q.2.2⟩

/-- A homeomorphism induces the canonical isomorphism of based fundamental
groups at the corresponding literal points. -/
noncomputable def fundamentalGroupHomeomorphEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) := by
  let h := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  exact MulEquiv.ofBijective (FundamentalGroup.map (e : C(X, Y)) x)
    (h.fullyFaithfulFunctor.map_bijective (FundamentalGroupoid.mk x)
      (FundamentalGroupoid.mk x))

/-- The normalized positive circle direction of the lower overlap point. -/
def twoPuncturedDiskLowerRelativeDirection {α β : ℝ}
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) : Circle :=
  convexPuncturedUnitDirection
    ((twoPuncturedDiskLowerSideHomeomorph hαβ
      (twoPuncturedDiskLowerRelativePointOfOverlap q)).1 -
        twoPuncturedDiskLeftCenter α) (by
    intro hz
    exact (twoPuncturedDiskLowerSideHomeomorph hαβ
      (twoPuncturedDiskLowerRelativePointOfOverlap q)).2.2 (sub_eq_zero.mp hz))

/-- The normalized positive circle direction of the upper overlap point. -/
def twoPuncturedDiskUpperRelativeDirection {α β : ℝ}
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) : Circle :=
  convexPuncturedUnitDirection
    ((twoPuncturedDiskUpperSideHomeomorph hαβ
      (twoPuncturedDiskUpperRelativePointOfOverlap q)).1 -
        twoPuncturedDiskRightCenter β) (by
    intro hz
    exact (twoPuncturedDiskUpperSideHomeomorph hαβ
      (twoPuncturedDiskUpperRelativePointOfOverlap q)).2.2 (sub_eq_zero.mp hz))

/-- The lower relative-side group, with its literal base point in the overlap,
is the free group on the positive winding about the lower puncture. -/
def twoPuncturedDiskLowerRelativeSideFreeEquiv {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    FundamentalGroup (twoPuncturedDiskLowerRelativePoint α β)
      (twoPuncturedDiskLowerRelativePointOfOverlap q) ≃* FreeGroup Unit :=
  (fundamentalGroupHomeomorphEquiv
    (twoPuncturedDiskLowerSideHomeomorph hαβ)
    (twoPuncturedDiskLowerRelativePointOfOverlap q)).trans
    ((twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ
        (twoPuncturedDiskLowerSideHomeomorph hαβ
          (twoPuncturedDiskLowerRelativePointOfOverlap q))).trans
      (circleFundamentalGroupFreeEquiv
        (twoPuncturedDiskLowerRelativeDirection hαβ q)))

/-- The upper relative-side group, with its literal base point in the overlap,
is the free group on the positive winding about the upper puncture. -/
def twoPuncturedDiskUpperRelativeSideFreeEquiv {α β : ℝ}
    (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    FundamentalGroup (twoPuncturedDiskUpperRelativePoint α β)
      (twoPuncturedDiskUpperRelativePointOfOverlap q) ≃* FreeGroup Unit :=
  (fundamentalGroupHomeomorphEquiv
    (twoPuncturedDiskUpperSideHomeomorph hαβ)
    (twoPuncturedDiskUpperRelativePointOfOverlap q)).trans
    ((twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ
        (twoPuncturedDiskUpperSideHomeomorph hαβ
          (twoPuncturedDiskUpperRelativePointOfOverlap q))).trans
      (circleFundamentalGroupFreeEquiv
        (twoPuncturedDiskUpperRelativeDirection hαβ q)))

/-- The relative-side group is indexed by the corresponding actual side
(`true` is lower, `false` is upper). -/
def twoPuncturedDiskRelativeSideFreeEquiv {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) (b : Bool) :
    twoOpenCoverAmalgamSideGroup
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q b ≃* FreeGroup Unit := by
  exact match b with
    | false => twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q
    | true => twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q

/-- Rename the singleton-tagged disjoint union of the lower/upper generators
to `Bool`, retaining the `true` = lower, `false` = upper convention. -/
def twoPuncturedDiskBoolUnitSigmaEquiv : (Σ _ : Bool, Unit) ≃ Bool where
  toFun x := x.1
  invFun b := ⟨b, ()⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

/-- The actual twice-punctured unit disk has free fundamental group on its
two literal relative-side positive windings. -/
def twoPuncturedDiskFundamentalGroupFreeEquiv {α β : ℝ}
    (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) :
    FundamentalGroup (twoPuncturedUnitDiskPoint α β) q.1 ≃* FreeGroup Bool := by
  letI : Subsingleton (FundamentalGroup
      {z : twoPuncturedUnitDiskPoint α β //
        z ∈ twoPuncturedDiskRelativeOverlap α β} q) :=
    twoPuncturedDiskRelativeOverlap_fundamentalGroup_subsingleton
      hα hα1 hβ hβ1 hαβ q
  let e := twoPuncturedDiskRelativeSideFreeEquiv hα hα1 hβ hβ1 hαβ q
  exact (twoPuncturedDiskFundamentalGroupAmalgamEquiv
      hα hα1 hβ hβ1 hαβ q).symm.trans
    ((freeGroupTrivialAmalgamEquiv
        (twoOpenCoverAmalgamSideMap
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q) e).trans
      (FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv))

/-- The actual disk presentation takes each literal van-Kampen factor map to
the corresponding tagged free factor map. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (b : Bool)
    (γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q b) :
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q b γ) =
    FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
        (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) b
          (twoPuncturedDiskRelativeSideFreeEquiv
            hα hα1 hβ hβ1 hαβ q b γ)) := by
  letI : Subsingleton (FundamentalGroup
      {z : twoPuncturedUnitDiskPoint α β //
        z ∈ twoPuncturedDiskRelativeOverlap α β} q) :=
    twoPuncturedDiskRelativeOverlap_fundamentalGroup_subsingleton
      hα hα1 hβ hβ1 hαβ q
  have hVK := twoPuncturedDiskFundamentalGroupAmalgamEquiv_of
    hα hα1 hβ hβ1 hαβ q b γ
  rw [← hVK]
  simp only [twoPuncturedDiskFundamentalGroupFreeEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  rw [freeGroupTrivialAmalgamEquiv_of]

/-- The generator selected by each composed actual side marking maps to its
tagged generator in the punctured-disk group. Here the side class is defined
as the inverse image of the normalized Circle generator under the side
equivalence; this does not yet identify it with a particular literal small
polar loop in the original disk. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_positiveGenerator
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) (b : Bool) :
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q b
        ((twoPuncturedDiskRelativeSideFreeEquiv
          hα hα1 hβ hβ1 hαβ q b).symm (FreeGroup.of ()))) =
      FreeGroup.of b := by
  simpa [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv] using
    twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
      hα hα1 hβ hβ1 hαβ q b
      ((twoPuncturedDiskRelativeSideFreeEquiv
        hα hα1 hβ hβ1 hαβ q b).symm (FreeGroup.of ()))

#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_positiveGenerator

end

end SystolicGrowth
