module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.PuncturedSideConnectorIndependence
public import Geometry.ConvexSidePositivePolarMembership
public import Geometry.TwoPuncturedDiskGeometricGenerators

@[expose] public section

/-!
# Tagged generators from actual Fermi-side connectors

An arbitrary connector inside either literal coordinate side transports the
actual positive Fermi turn to the corresponding tagged generator of the
twice-punctured disk. The side-to-disk map is the genuine van Kampen factor
map, not an assumed presentation compatibility.
-/

open Set
open scoped ContinuousMap

namespace SystolicGrowth

noncomputable section

/-- The lower Fermi positive turn, based by any actual path in the lower
relative side from its overlap point, is the `true` generator under the
actual whole-disk marking. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_lowerFermiPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hball : Metric.ball (twoPuncturedDiskLeftCenter α) δ ⊆
      twoPuncturedDiskLowerBase α β)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskLeftCenter α).im) a b ha hb ρ θ‖ < δ)
    (φ : Circle)
    (p : Path (twoPuncturedDiskLowerRelativePointOfOverlap q)
      ((twoPuncturedDiskLowerSideHomeomorph hαβ).symm
        ((translatedFermiPositivePolarCoordinateMap
          (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
          m a b ha hb ρ δ hρ hball hq) φ))) :
    let F := translatedFermiPositivePolarCoordinateMap
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      m a b ha hb ρ δ hρ hball hq
    let H := twoPuncturedDiskLowerSideHomeomorph hαβ
    let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true ⟦loop⟧) =
      FreeGroup.of true := by
  let F := translatedFermiPositivePolarCoordinateMap
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    m a b ha hb ρ δ hρ hball hq
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  let x := twoPuncturedDiskLowerRelativePointOfOverlap q
  let z : puncturedBaseAt (twoPuncturedDiskLowerBase α β)
      (twoPuncturedDiskLeftCenter α) := H x
  let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
  let pg := (p.map H.continuous).cast rfl (H.apply_symm_apply (F φ))
  let loopg := pg.trans (((circleOneTurnLoop φ).map F.continuous).trans pg.symm)
  have hmap : fundamentalGroupHomeomorphEquiv H x ⟦loop⟧ = ⟦loopg⟧ := by
    change Path.Homotopic.Quotient.mk (loop.map H.continuous) =
      Path.Homotopic.Quotient.mk loopg
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    simp [loop, loopg, pg, Fside, Path.map_trans, Path.map_symm]
    rfl
  have hgen := translatedFermiPositivePolarCoordinateBasedFreeGenerator_of_connector
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
    ρ δ
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ) hρ
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)
    hball m a b ha hb hq z φ pg
  have hbase : puncturedBaseCircleHomotopyEquiv
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
      (twoPuncturedDiskLowerBase_convex α β)
      (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
      (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) z =
      twoPuncturedDiskLowerRelativeDirection hαβ q := by
    apply Circle.ext
    rfl
  have hside : twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q
      ⟦loop⟧ = FreeGroup.of () := by
    let D := (twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ z).trans
      (circleFundamentalGroupFreeEquiv (twoPuncturedDiskLowerRelativeDirection hαβ q))
    have hgenD : D ⟦loopg⟧ = FreeGroup.of () := by
      cases hbase
      exact hgen
    change ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ = _
    rw [show ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ =
      D ((fundamentalGroupHomeomorphEquiv H x) ⟦loop⟧) from rfl, hmap]
    exact hgenD
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true := ⟦loop⟧
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γ) = FreeGroup.of true
  rw [twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    hα hα1 hβ hβ1 hαβ q true γ]
  change FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
      (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) true
        (twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q ⟦loop⟧)) = _
  rw [hside]
  simp [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv]

/-- The upper Fermi positive turn, based by any actual path in the upper
relative side from its overlap point, is the `false` generator under the
actual whole-disk marking. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_upperFermiPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hball : Metric.ball (twoPuncturedDiskRightCenter β) δ ⊆
      twoPuncturedDiskUpperBase α β)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskRightCenter β).im) a b ha hb ρ θ‖ < δ)
    (φ : Circle)
    (p : Path (twoPuncturedDiskUpperRelativePointOfOverlap q)
      ((twoPuncturedDiskUpperSideHomeomorph hαβ).symm
        ((translatedFermiPositivePolarCoordinateMap
          (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
          m a b ha hb ρ δ hρ hball hq) φ))) :
    let F := translatedFermiPositivePolarCoordinateMap
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      m a b ha hb ρ δ hρ hball hq
    let H := twoPuncturedDiskUpperSideHomeomorph hαβ
    let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false ⟦loop⟧) =
      FreeGroup.of false := by
  let F := translatedFermiPositivePolarCoordinateMap
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    m a b ha hb ρ δ hρ hball hq
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  let x := twoPuncturedDiskUpperRelativePointOfOverlap q
  let z : puncturedBaseAt (twoPuncturedDiskUpperBase α β)
      (twoPuncturedDiskRightCenter β) := H x
  let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
  let pg := (p.map H.continuous).cast rfl (H.apply_symm_apply (F φ))
  let loopg := pg.trans (((circleOneTurnLoop φ).map F.continuous).trans pg.symm)
  have hmap : fundamentalGroupHomeomorphEquiv H x ⟦loop⟧ = ⟦loopg⟧ := by
    change Path.Homotopic.Quotient.mk (loop.map H.continuous) =
      Path.Homotopic.Quotient.mk loopg
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    simp [loop, loopg, pg, Fside, Path.map_trans, Path.map_symm]
    rfl
  have hgen := translatedFermiPositivePolarCoordinateBasedFreeGenerator_of_connector
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
    ρ δ
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ) hρ
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)
    hball m a b ha hb hq z φ pg
  have hbase : puncturedBaseCircleHomotopyEquiv
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
      (twoPuncturedDiskUpperBase_convex α β)
      (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
      (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) z =
      twoPuncturedDiskUpperRelativeDirection hαβ q := by
    apply Circle.ext
    rfl
  have hside : twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q
      ⟦loop⟧ = FreeGroup.of () := by
    let D := (twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ z).trans
      (circleFundamentalGroupFreeEquiv (twoPuncturedDiskUpperRelativeDirection hαβ q))
    have hgenD : D ⟦loopg⟧ = FreeGroup.of () := by
      cases hbase
      exact hgen
    change ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ = _
    rw [show ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ =
      D ((fundamentalGroupHomeomorphEquiv H x) ⟦loop⟧) from rfl, hmap]
    exact hgenD
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false := ⟦loop⟧
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γ) = FreeGroup.of false
  rw [twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    hα hα1 hβ hβ1 hαβ q false γ]
  change FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
      (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) false
        (twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q ⟦loop⟧)) = _
  rw [hside]
  simp [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv]

/-- The lower tagged-generator formula is unchanged by a literal positive
Circle rotation of the Fermi parameter. The connector ends at the rotated
point, and the rotation acts on the one-turn path by the exact path identity. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_lowerRotatedFermiPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hball : Metric.ball (twoPuncturedDiskLeftCenter α) δ ⊆
      twoPuncturedDiskLowerBase α β)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskLeftCenter α).im) a b ha hb ρ θ‖ < δ)
    (u φ : Circle)
    (p : Path (twoPuncturedDiskLowerRelativePointOfOverlap q)
      ((twoPuncturedDiskLowerSideHomeomorph hαβ).symm
        ((translatedFermiPositivePolarCoordinateMap
          (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
          m a b ha hb ρ δ hρ hball hq) (u * φ)))) :
    let F := translatedFermiPositivePolarCoordinateMap
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      m a b ha hb ρ δ hρ hball hq
    let H := twoPuncturedDiskLowerSideHomeomorph hαβ
    let A : C(Circle, Circle) := ⟨fun θ => u * θ,
      continuous_const.mul continuous_id⟩
    let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map
      (Fside.comp A).continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true ⟦loop⟧) =
      FreeGroup.of true := by
  let F := translatedFermiPositivePolarCoordinateMap
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    m a b ha hb ρ δ hρ hball hq
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  let x := twoPuncturedDiskLowerRelativePointOfOverlap q
  let A : C(Circle, Circle) := ⟨fun θ => u * θ,
    continuous_const.mul continuous_id⟩
  let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let Frot : C(Circle, twoPuncturedDiskLowerRelativePoint α β) := Fside.comp A
  let ψ := u * φ
  let loop := p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm)
  let loopψ := p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm)
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true := ⟦loop⟧
  let γψ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true := ⟦loopψ⟧
  have hturn : (circleOneTurnLoop φ).map A.continuous =
      circleOneTurnLoop ψ := by
    simpa [A, ψ] using circleOneTurnLoop_map_mul_left u φ
  have hturnMap : (circleOneTurnLoop φ).map Frot.continuous =
      (circleOneTurnLoop ψ).map Fside.continuous := by
    apply Path.ext
    funext t
    have hturnAt : A (circleOneTurnLoop φ t) = circleOneTurnLoop ψ t := by
      have ht := congrArg (fun r : Path ψ ψ => r t) hturn
      simpa [Path.map_coe] using ht
    change Fside (A (circleOneTurnLoop φ t)) = Fside (circleOneTurnLoop ψ t)
    exact congrArg Fside hturnAt
  have hloop : (⟦loop⟧ : Path.Homotopic.Quotient _ _) = ⟦loopψ⟧ := by
    apply congrArg Path.Homotopic.Quotient.mk
    calc
      loop = p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm) := rfl
      _ = p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm) := by
        exact congrArg (fun r : Path (Fside ψ) (Fside ψ) => p.trans (r.trans p.symm)) hturnMap
      _ = loopψ := rfl
  have hγ : γ = γψ := by
    change (⟦loop⟧ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true) = ⟦loopψ⟧
    exact hloop
  have hcore := twoPuncturedDiskFundamentalGroupFreeEquiv_lowerFermiPositiveLoop
    hα hα1 hβ hβ1 hαβ q m a b ρ δ ha hb hρ hball hq ψ p
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γψ) =
      FreeGroup.of true at hcore
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γ) =
      FreeGroup.of true
  rw [hγ]
  exact hcore

/-- The upper tagged-generator formula is unchanged by a literal positive
Circle rotation of the Fermi parameter. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_upperRotatedFermiPositiveLoop
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hball : Metric.ball (twoPuncturedDiskRightCenter β) δ ⊆
      twoPuncturedDiskUpperBase α β)
    (hq : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskRightCenter β).im) a b ha hb ρ θ‖ < δ)
    (u φ : Circle)
    (p : Path (twoPuncturedDiskUpperRelativePointOfOverlap q)
      ((twoPuncturedDiskUpperSideHomeomorph hαβ).symm
        ((translatedFermiPositivePolarCoordinateMap
          (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
          m a b ha hb ρ δ hρ hball hq) (u * φ)))) :
    let F := translatedFermiPositivePolarCoordinateMap
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      m a b ha hb ρ δ hρ hball hq
    let H := twoPuncturedDiskUpperSideHomeomorph hαβ
    let A : C(Circle, Circle) := ⟨fun θ => u * θ,
      continuous_const.mul continuous_id⟩
    let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map
      (Fside.comp A).continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false ⟦loop⟧) =
      FreeGroup.of false := by
  let F := translatedFermiPositivePolarCoordinateMap
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    m a b ha hb ρ δ hρ hball hq
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  let x := twoPuncturedDiskUpperRelativePointOfOverlap q
  let A : C(Circle, Circle) := ⟨fun θ => u * θ,
    continuous_const.mul continuous_id⟩
  let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let Frot : C(Circle, twoPuncturedDiskUpperRelativePoint α β) := Fside.comp A
  let ψ := u * φ
  let loop := p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm)
  let loopψ := p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm)
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false := ⟦loop⟧
  let γψ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false := ⟦loopψ⟧
  have hturn : (circleOneTurnLoop φ).map A.continuous =
      circleOneTurnLoop ψ := by
    simpa [A, ψ] using circleOneTurnLoop_map_mul_left u φ
  have hturnMap : (circleOneTurnLoop φ).map Frot.continuous =
      (circleOneTurnLoop ψ).map Fside.continuous := by
    apply Path.ext
    funext t
    have hturnAt : A (circleOneTurnLoop φ t) = circleOneTurnLoop ψ t := by
      have ht := congrArg (fun r : Path ψ ψ => r t) hturn
      simpa [Path.map_coe] using ht
    change Fside (A (circleOneTurnLoop φ t)) = Fside (circleOneTurnLoop ψ t)
    exact congrArg Fside hturnAt
  have hloop : (⟦loop⟧ : Path.Homotopic.Quotient _ _) = ⟦loopψ⟧ := by
    apply congrArg Path.Homotopic.Quotient.mk
    calc
      loop = p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm) := rfl
      _ = p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm) := by
        exact congrArg (fun r : Path (Fside ψ) (Fside ψ) => p.trans (r.trans p.symm)) hturnMap
      _ = loopψ := rfl
  have hγ : γ = γψ := by
    change (⟦loop⟧ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false) = ⟦loopψ⟧
    exact hloop
  have hcore := twoPuncturedDiskFundamentalGroupFreeEquiv_upperFermiPositiveLoop
    hα hα1 hβ hβ1 hαβ q m a b ρ δ ha hb hρ hball hq ψ p
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γψ) =
      FreeGroup.of false at hcore
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γ) =
      FreeGroup.of false
  rw [hγ]
  exact hcore

/-- The lower tagged formula when membership of every Fermi point in the
actual convex side is known directly, without a norm-ball certificate. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_lowerFermiPositiveLoop_of_mem
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hmem : ∀ θ : Circle,
      twoPuncturedDiskLeftCenter α + fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskLeftCenter α).im) a b ha hb ρ θ ∈
          twoPuncturedDiskLowerBase α β)
    (φ : Circle)
    (p : Path (twoPuncturedDiskLowerRelativePointOfOverlap q)
      ((twoPuncturedDiskLowerSideHomeomorph hαβ).symm
        ((convexSideFermiPositivePolarCoordinateMap
          (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
          m a b ha hb ρ hρ hmem) φ))) :
    let F := convexSideFermiPositivePolarCoordinateMap
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      m a b ha hb ρ hρ hmem
    let H := twoPuncturedDiskLowerSideHomeomorph hαβ
    let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true ⟦loop⟧) =
      FreeGroup.of true := by
  let F := convexSideFermiPositivePolarCoordinateMap
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    m a b ha hb ρ hρ hmem
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  let x := twoPuncturedDiskLowerRelativePointOfOverlap q
  let z : puncturedBaseAt (twoPuncturedDiskLowerBase α β)
      (twoPuncturedDiskLeftCenter α) := H x
  let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
  let pg := (p.map H.continuous).cast rfl (H.apply_symm_apply (F φ))
  let loopg := pg.trans (((circleOneTurnLoop φ).map F.continuous).trans pg.symm)
  have hmap : fundamentalGroupHomeomorphEquiv H x ⟦loop⟧ = ⟦loopg⟧ := by
    change Path.Homotopic.Quotient.mk (loop.map H.continuous) =
      Path.Homotopic.Quotient.mk loopg
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    simp [loop, loopg, pg, Fside, Path.map_trans, Path.map_symm]
    rfl
  have hgen := convexSideFermiPositivePolarCoordinateBasedFreeGenerator_of_connector
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    (twoPuncturedDiskLowerBase_convex α β)
    (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ) ρ
    (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ) hρ
    (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ)
    m a b ha hb hmem z φ pg
  have hbase : puncturedBaseCircleHomotopyEquiv
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      (twoPuncturedDiskLowerSideCircleRadius hα hα1 hαβ)
      (twoPuncturedDiskLowerBase_convex α β)
      (twoPuncturedDiskLowerSideCircleRadius_pos hα hα1 hαβ)
      (twoPuncturedDiskLowerSideCircleRadius_mem hα hα1 hαβ) z =
      twoPuncturedDiskLowerRelativeDirection hαβ q := by
    apply Circle.ext
    rfl
  have hside : twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q
      ⟦loop⟧ = FreeGroup.of () := by
    let D := (twoPuncturedDiskLowerSideFundamentalGroupEquiv hα hα1 hαβ z).trans
      (circleFundamentalGroupFreeEquiv (twoPuncturedDiskLowerRelativeDirection hαβ q))
    have hgenD : D ⟦loopg⟧ = FreeGroup.of () := by
      cases hbase
      exact hgen
    change ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ = _
    rw [show ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ =
      D ((fundamentalGroupHomeomorphEquiv H x) ⟦loop⟧) from rfl, hmap]
    exact hgenD
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true := ⟦loop⟧
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γ) = FreeGroup.of true
  rw [twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    hα hα1 hβ hβ1 hαβ q true γ]
  change FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
      (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) true
        (twoPuncturedDiskLowerRelativeSideFreeEquiv hα hα1 hαβ q ⟦loop⟧)) = _
  rw [hside]
  simp [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv]

/-- The upper tagged formula with direct actual-side membership data. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_upperFermiPositiveLoop_of_mem
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hmem : ∀ θ : Circle,
      twoPuncturedDiskRightCenter β + fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskRightCenter β).im) a b ha hb ρ θ ∈
          twoPuncturedDiskUpperBase α β)
    (φ : Circle)
    (p : Path (twoPuncturedDiskUpperRelativePointOfOverlap q)
      ((twoPuncturedDiskUpperSideHomeomorph hαβ).symm
        ((convexSideFermiPositivePolarCoordinateMap
          (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
          m a b ha hb ρ hρ hmem) φ))) :
    let F := convexSideFermiPositivePolarCoordinateMap
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      m a b ha hb ρ hρ hmem
    let H := twoPuncturedDiskUpperSideHomeomorph hαβ
    let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false ⟦loop⟧) =
      FreeGroup.of false := by
  let F := convexSideFermiPositivePolarCoordinateMap
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    m a b ha hb ρ hρ hmem
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  let x := twoPuncturedDiskUpperRelativePointOfOverlap q
  let z : puncturedBaseAt (twoPuncturedDiskUpperBase α β)
      (twoPuncturedDiskRightCenter β) := H x
  let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let loop := p.trans (((circleOneTurnLoop φ).map Fside.continuous).trans p.symm)
  let pg := (p.map H.continuous).cast rfl (H.apply_symm_apply (F φ))
  let loopg := pg.trans (((circleOneTurnLoop φ).map F.continuous).trans pg.symm)
  have hmap : fundamentalGroupHomeomorphEquiv H x ⟦loop⟧ = ⟦loopg⟧ := by
    change Path.Homotopic.Quotient.mk (loop.map H.continuous) =
      Path.Homotopic.Quotient.mk loopg
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    simp [loop, loopg, pg, Fside, Path.map_trans, Path.map_symm]
    rfl
  have hgen := convexSideFermiPositivePolarCoordinateBasedFreeGenerator_of_connector
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    (twoPuncturedDiskUpperBase_convex α β)
    (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ) ρ
    (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ) hρ
    (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ)
    m a b ha hb hmem z φ pg
  have hbase : puncturedBaseCircleHomotopyEquiv
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      (twoPuncturedDiskUpperSideCircleRadius hβ hβ1 hαβ)
      (twoPuncturedDiskUpperBase_convex α β)
      (twoPuncturedDiskUpperSideCircleRadius_pos hβ hβ1 hαβ)
      (twoPuncturedDiskUpperSideCircleRadius_mem hβ hβ1 hαβ) z =
      twoPuncturedDiskUpperRelativeDirection hαβ q := by
    apply Circle.ext
    rfl
  have hside : twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q
      ⟦loop⟧ = FreeGroup.of () := by
    let D := (twoPuncturedDiskUpperSideFundamentalGroupEquiv hβ hβ1 hαβ z).trans
      (circleFundamentalGroupFreeEquiv (twoPuncturedDiskUpperRelativeDirection hαβ q))
    have hgenD : D ⟦loopg⟧ = FreeGroup.of () := by
      cases hbase
      exact hgen
    change ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ = _
    rw [show ((fundamentalGroupHomeomorphEquiv H x).trans D) ⟦loop⟧ =
      D ((fundamentalGroupHomeomorphEquiv H x) ⟦loop⟧) from rfl, hmap]
    exact hgenD
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false := ⟦loop⟧
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γ) = FreeGroup.of false
  rw [twoPuncturedDiskFundamentalGroupFreeEquiv_sideMap
    hα hα1 hβ hβ1 hαβ q false γ]
  change FreeGroup.freeGroupCongr twoPuncturedDiskBoolUnitSigmaEquiv
      (freeGroupTrivialAmalgamFactorMap (fun _ : Bool => Unit) false
        (twoPuncturedDiskUpperRelativeSideFreeEquiv hβ hβ1 hαβ q ⟦loop⟧)) = _
  rw [hside]
  simp [freeGroupTrivialAmalgamFactorMap, twoPuncturedDiskBoolUnitSigmaEquiv]

/-- The membership-only lower formula is preserved under a left rotation of
the Fermi parameter, with any actual connector to the rotated endpoint. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_lowerRotatedFermiPositiveLoop_of_mem
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hmem : ∀ θ : Circle,
      twoPuncturedDiskLeftCenter α + fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskLeftCenter α).im) a b ha hb ρ θ ∈
          twoPuncturedDiskLowerBase α β)
    (u φ : Circle)
    (p : Path (twoPuncturedDiskLowerRelativePointOfOverlap q)
      ((twoPuncturedDiskLowerSideHomeomorph hαβ).symm
        ((convexSideFermiPositivePolarCoordinateMap
          (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
          m a b ha hb ρ hρ hmem) (u * φ)))) :
    let F := convexSideFermiPositivePolarCoordinateMap
      (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
      m a b ha hb ρ hρ hmem
    let H := twoPuncturedDiskLowerSideHomeomorph hαβ
    let A : C(Circle, Circle) := ⟨fun θ => u * θ,
      continuous_const.mul continuous_id⟩
    let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map
      (Fside.comp A).continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true ⟦loop⟧) =
      FreeGroup.of true := by
  let F := convexSideFermiPositivePolarCoordinateMap
    (twoPuncturedDiskLowerBase α β) (twoPuncturedDiskLeftCenter α)
    m a b ha hb ρ hρ hmem
  let H := twoPuncturedDiskLowerSideHomeomorph hαβ
  let x := twoPuncturedDiskLowerRelativePointOfOverlap q
  let A : C(Circle, Circle) := ⟨fun θ => u * θ,
    continuous_const.mul continuous_id⟩
  let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let Frot : C(Circle, twoPuncturedDiskLowerRelativePoint α β) := Fside.comp A
  let ψ := u * φ
  let loop := p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm)
  let loopψ := p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm)
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true := ⟦loop⟧
  let γψ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true := ⟦loopψ⟧
  have hturn : (circleOneTurnLoop φ).map A.continuous =
      circleOneTurnLoop ψ := by
    simpa [A, ψ] using circleOneTurnLoop_map_mul_left u φ
  have hturnMap : (circleOneTurnLoop φ).map Frot.continuous =
      (circleOneTurnLoop ψ).map Fside.continuous := by
    apply Path.ext
    funext t
    have hturnAt : A (circleOneTurnLoop φ t) = circleOneTurnLoop ψ t := by
      have ht := congrArg (fun r : Path ψ ψ => r t) hturn
      simpa [Path.map_coe] using ht
    change Fside (A (circleOneTurnLoop φ t)) = Fside (circleOneTurnLoop ψ t)
    exact congrArg Fside hturnAt
  have hloop : (⟦loop⟧ : Path.Homotopic.Quotient _ _) = ⟦loopψ⟧ := by
    apply congrArg Path.Homotopic.Quotient.mk
    calc
      loop = p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm) := rfl
      _ = p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm) := by
        exact congrArg (fun r : Path (Fside ψ) (Fside ψ) => p.trans (r.trans p.symm)) hturnMap
      _ = loopψ := rfl
  have hγ : γ = γψ := by
    change (⟦loop⟧ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q true) = ⟦loopψ⟧
    exact hloop
  have hcore := twoPuncturedDiskFundamentalGroupFreeEquiv_lowerFermiPositiveLoop_of_mem
    hα hα1 hβ hβ1 hαβ q m a b ρ ha hb hρ hmem ψ p
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γψ) =
      FreeGroup.of true at hcore
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q true γ) =
      FreeGroup.of true
  rw [hγ]
  exact hcore

/-- The membership-only upper formula is preserved under a left rotation of
the Fermi parameter. -/
theorem twoPuncturedDiskFundamentalGroupFreeEquiv_upperRotatedFermiPositiveLoop_of_mem
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (q : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β})
    (m a b ρ : ℝ) (ha : 0 < a) (hb : 0 < b) (hρ : 0 < ρ)
    (hmem : ∀ θ : Circle,
      twoPuncturedDiskRightCenter β + fermiPositivePolarCoordinate
        (m + a * (twoPuncturedDiskRightCenter β).im) a b ha hb ρ θ ∈
          twoPuncturedDiskUpperBase α β)
    (u φ : Circle)
    (p : Path (twoPuncturedDiskUpperRelativePointOfOverlap q)
      ((twoPuncturedDiskUpperSideHomeomorph hαβ).symm
        ((convexSideFermiPositivePolarCoordinateMap
          (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
          m a b ha hb ρ hρ hmem) (u * φ)))) :
    let F := convexSideFermiPositivePolarCoordinateMap
      (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
      m a b ha hb ρ hρ hmem
    let H := twoPuncturedDiskUpperSideHomeomorph hαβ
    let A : C(Circle, Circle) := ⟨fun θ => u * θ,
      continuous_const.mul continuous_id⟩
    let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
      ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
    let loop := p.trans (((circleOneTurnLoop φ).map
      (Fside.comp A).continuous).trans p.symm)
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false ⟦loop⟧) =
      FreeGroup.of false := by
  let F := convexSideFermiPositivePolarCoordinateMap
    (twoPuncturedDiskUpperBase α β) (twoPuncturedDiskRightCenter β)
    m a b ha hb ρ hρ hmem
  let H := twoPuncturedDiskUpperSideHomeomorph hαβ
  let x := twoPuncturedDiskUpperRelativePointOfOverlap q
  let A : C(Circle, Circle) := ⟨fun θ => u * θ,
    continuous_const.mul continuous_id⟩
  let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
    ⟨fun θ => H.symm (F θ), H.symm.continuous.comp F.continuous⟩
  let Frot : C(Circle, twoPuncturedDiskUpperRelativePoint α β) := Fside.comp A
  let ψ := u * φ
  let loop := p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm)
  let loopψ := p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm)
  let γ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false := ⟦loop⟧
  let γψ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false := ⟦loopψ⟧
  have hturn : (circleOneTurnLoop φ).map A.continuous =
      circleOneTurnLoop ψ := by
    simpa [A, ψ] using circleOneTurnLoop_map_mul_left u φ
  have hturnMap : (circleOneTurnLoop φ).map Frot.continuous =
      (circleOneTurnLoop ψ).map Fside.continuous := by
    apply Path.ext
    funext t
    have hturnAt : A (circleOneTurnLoop φ t) = circleOneTurnLoop ψ t := by
      have ht := congrArg (fun r : Path ψ ψ => r t) hturn
      simpa [Path.map_coe] using ht
    change Fside (A (circleOneTurnLoop φ t)) = Fside (circleOneTurnLoop ψ t)
    exact congrArg Fside hturnAt
  have hloop : (⟦loop⟧ : Path.Homotopic.Quotient _ _) = ⟦loopψ⟧ := by
    apply congrArg Path.Homotopic.Quotient.mk
    calc
      loop = p.trans (((circleOneTurnLoop φ).map Frot.continuous).trans p.symm) := rfl
      _ = p.trans (((circleOneTurnLoop ψ).map Fside.continuous).trans p.symm) := by
        exact congrArg (fun r : Path (Fside ψ) (Fside ψ) => p.trans (r.trans p.symm)) hturnMap
      _ = loopψ := rfl
  have hγ : γ = γψ := by
    change (⟦loop⟧ : twoOpenCoverAmalgamSideGroup
      (twoPuncturedDiskLowerRelativeSide α β)
      (twoPuncturedDiskUpperRelativeSide α β) q false) = ⟦loopψ⟧
    exact hloop
  have hcore := twoPuncturedDiskFundamentalGroupFreeEquiv_upperFermiPositiveLoop_of_mem
    hα hα1 hβ hβ1 hαβ q m a b ρ ha hb hρ hmem ψ p
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γψ) =
      FreeGroup.of false at hcore
  change twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q
      (twoOpenCoverSideToAmbient
        (twoPuncturedDiskLowerRelativeSide α β)
        (twoPuncturedDiskUpperRelativeSide α β) q false γ) =
      FreeGroup.of false
  rw [hγ]
  exact hcore

#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_lowerFermiPositiveLoop
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_upperFermiPositiveLoop
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_lowerRotatedFermiPositiveLoop
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_upperRotatedFermiPositiveLoop
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_lowerFermiPositiveLoop_of_mem
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_upperFermiPositiveLoop_of_mem
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_lowerRotatedFermiPositiveLoop_of_mem
#print axioms twoPuncturedDiskFundamentalGroupFreeEquiv_upperRotatedFermiPositiveLoop_of_mem

end

end SystolicGrowth
