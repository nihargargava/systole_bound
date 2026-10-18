module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.EmbeddedTwoPunctureDiskVanKampen
public import Geometry.TwoPuncturedDiskOuterBoundaryWord
public import Geometry.SurfaceTwoCenterSideConnectorPaths

@[expose] public section

/-!
# The actual annulus boundary word in the local two-puncture marking

The actual relative annulus boundary is sent to the positive outer circle in
the normalized local disk, with its original unit-coordinate circle and the
radius `1/r` retained.  Its local free marking is therefore the actual outer
boundary word, not a word supplied as an extra hypothesis.
-/

open Set UpperHalfPlane
open scoped ContinuousMap

namespace SystolicGrowth

noncomputable section

variable {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}

private theorem twoPuncturedDiskFundamentalGroupFreeEquiv_cast_eq
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1) (hβ : -1 < β) (hβ1 : β < 1)
    (hαβ : α < β)
    (q₀ q₁ : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β}) (hq : q₀ = q₁)
    (γ : Path q₁.1 q₁.1) :
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q₀
      ⟦γ.cast (congrArg Subtype.val hq) (congrArg Subtype.val hq)⟧ =
    twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ q₁ ⟦γ⟧ := by
  cases hq
  rfl

private theorem twoPuncturedDiskOuterBoundaryCircle_rightDirection_eq
    {α β R : ℝ} (hαβ : α < β) (hαR : |α| < R) (hβR : |β| < R)
    (hR : R < 1) :
    twoPuncturedDiskOuterBoundaryCircle α β R hαR hβR hR
      (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR) =
        twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR := by
  apply Subtype.ext
  change (R : ℂ) *
      (twoPuncturedDiskOuterRightDirection hαβ hαR hβR hR : ℂ) = _
  rw [twoPuncturedDiskOuterRightDirection, Circle.coe_exp]
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg α) hαR
  have hheight := twoPuncturedDiskOuterCutHeight_mem hαβ hαR hβR
  have hrad : 0 ≤ R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
    nlinarith
  have hwidthSq : twoPuncturedDiskOuterCutHalfWidth α β R ^ 2 =
      R ^ 2 - twoPuncturedDiskOuterCutHeight α β ^ 2 := by
    simpa [twoPuncturedDiskOuterCutHalfWidth] using Real.sq_sqrt hrad
  have hnorm : ‖(twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1‖ = R := by
    change ‖(twoPuncturedDiskOuterCutHalfWidth α β R : ℂ) +
      (twoPuncturedDiskOuterCutHeight α β : ℂ) * Complex.I‖ = R
    rw [Complex.norm_add_mul_I]
    have hsum : twoPuncturedDiskOuterCutHalfWidth α β R ^ 2 +
        twoPuncturedDiskOuterCutHeight α β ^ 2 = R ^ 2 := by
      rw [hwidthSq]
      ring
    rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos hRpos]
  calc
    (R : ℂ) * Complex.exp
        ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.arg * Complex.I) =
      (‖(twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1‖ : ℂ) *
        Complex.exp
          ((twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1.arg * Complex.I) := by
      rw [hnorm]
    _ = (twoPuncturedDiskOuterRightCutPoint hαβ hαR hβR hR).1 :=
      Complex.norm_mul_exp_arg_mul_I _

/-- The positive generator of the actual annulus overlap maps, under the
literal local-side inclusion and actual local free marking at the right
crossing, to the lower-then-upper outer boundary word.  In particular the
unit-coordinate annulus circle is not replaced by a radius-`r` circle: the
normalized standard-disk circle has radius exactly `r⁻¹`. -/
theorem embeddedTwoPunctureRelativeBoundaryCircle_localDiskFreeWord
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (a r : ℝ) (ha : max ‖(p : ℂ)‖ ‖(q : ℂ)‖ < a)
    (ha1 : a < 1) (hr1 : 1 < r)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpq : p ≠ q) (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0) :
    let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
      (zero_lt_one.trans hr1) hpq hpre hqre
    let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
      (zero_lt_one.trans hr1)
      (((le_max_left _ _).trans_lt ha).trans ha1)
      (((le_max_right _ _).trans_lt ha).trans ha1)
    let hpR := ((le_max_left _ _).trans_lt ha).trans (ha1.trans hr1)
    let hqR := ((le_max_right _ _).trans_lt ha).trans (ha1.trans hr1)
    let hR := (inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1
    let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
    let boundary := embeddedTwoPunctureRelativeBoundaryCircle
      f hf p q a r ha ha1 hr1 haU hrU
    let overlapBase := boundary θ
    let localBase := twoOpenCoverAmalgamOverlapRight
      (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
      (embeddedTwoPunctureLocalDiskRelativeSide f p q r) overlapBase
    embeddedTwoPunctureRelativeLocalDiskFreeEquiv
      f hf p q r (zero_lt_one.trans hr1) hrU
      hpR hqR
      hpq hpre hqre localBase
      (embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
        f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre) 
      (FundamentalGroup.map
        (twoOpenCoverAmalgamOverlapRight
          (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r)) overlapBase
        ⟦(circleOneTurnLoop θ).map boundary.continuous⟧) =
      FreeGroup.of true * FreeGroup.of false := by
  dsimp only
  let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
    (zero_lt_one.trans hr1) hpq hpre hqre
  let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
    (zero_lt_one.trans hr1)
    (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1)
  let hR := (inv_lt_one₀ (zero_lt_one.trans hr1)).mpr hr1
  let hpR := ((le_max_left _ _).trans_lt ha).trans (ha1.trans hr1)
  let hqR := ((le_max_right _ _).trans_lt ha).trans (ha1.trans hr1)
  let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
  let boundary := embeddedTwoPunctureRelativeBoundaryCircle
    f hf p q a r ha ha1 hr1 haU hrU
  let overlapBase := boundary θ
  let exterior := embeddedTwoPunctureExteriorRelativeSide f p q a haU
  let localDisk := embeddedTwoPunctureLocalDiskRelativeSide f p q r
  let rightMap := twoOpenCoverAmalgamOverlapRight exterior localDisk
  let localBase := rightMap overlapBase
  let sideHomeo := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    f hf p q r (zero_lt_one.trans hr1) hrU hpre hqre
  let sideMap : C(_, _) := ⟨sideHomeo, sideHomeo.continuous⟩
  let outerCircle := twoPuncturedDiskOuterBoundaryCircle
    (embeddedTwoPunctureLowerParameter p q r)
    (embeddedTwoPunctureUpperParameter p q r) r⁻¹
    hnorms.1 hnorms.2 hR
  have hmem : sideHomeo localBase ∈
      twoPuncturedDiskRelativeOverlap
        (embeddedTwoPunctureLowerParameter p q r)
        (embeddedTwoPunctureUpperParameter p q r) := by
    exact embeddedTwoPunctureRelativeBoundaryCircle_right_mem_localOverlap
      f hf p q a r ha ha1 hr1 haU hrU hpq hpre hqre
  have hnormalized : sideMap.comp (rightMap.comp boundary) = outerCircle := by
    exact embeddedTwoPunctureRelativeBoundaryCircle_normalizedLocalSide
      f hf p q a r ha ha1 hr1 haU hrU hpre hqre
  have hpoint : sideHomeo localBase = outerCircle θ := by
    have h := congrArg (fun F : C(Circle, _) => F θ) hnormalized
    simpa [sideMap, rightMap, boundary, localBase, outerCircle] using h
  have hcut := twoPuncturedDiskOuterBoundaryCircle_rightDirection_eq
    hαβ hnorms.1 hnorms.2 hR
  have hbase : sideHomeo localBase =
      twoPuncturedDiskOuterRightCutPoint hαβ hnorms.1 hnorms.2 hR :=
    hpoint.trans hcut
  let bounds := embeddedTwoPunctureParameters_bounds p q r
      (zero_lt_one.trans hr1) hpR hqR
  rcases hbd : bounds with ⟨hα, hα1, hβ, hβ1⟩
  let diskBase : twoPuncturedDiskRelativeOverlap
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r) := ⟨sideHomeo localBase, hmem⟩
  let diskFreeEquiv :=
    twoPuncturedDiskFundamentalGroupFreeEquiv bounds.1 bounds.2.1 bounds.2.2.1
      bounds.2.2.2 hαβ diskBase
  let localFreeEquiv := embeddedTwoPunctureRelativeLocalDiskFreeEquiv
    f hf p q r (zero_lt_one.trans hr1) hrU
    hpR hqR
    hpq hpre hqre localBase hmem
  let loopActual := ((circleOneTurnLoop θ).map boundary.continuous).map
    rightMap.continuous |>.map sideMap.continuous
  let boundaryPath := (circleOneTurnLoop θ).map boundary.continuous
  let rightPath := boundaryPath.map rightMap.continuous
  have hpath : loopActual =
      ((circleOneTurnLoop θ).map outerCircle.continuous).cast hpoint hpoint := by
    apply Path.ext
    funext t
    simp only [loopActual, Path.cast_coe, Path.map_coe]
    have h := congrArg (fun F : C(Circle, _) => F (circleOneTurnLoop θ t)) hnormalized
    simpa [sideMap, rightMap, boundary, outerCircle, ContinuousMap.comp_apply] using h
  have hclass :
      FundamentalGroup.map sideMap localBase
        (FundamentalGroup.map rightMap overlapBase
          ⟦(circleOneTurnLoop θ).map boundary.continuous⟧) = ⟦loopActual⟧ := by
    change FundamentalGroup.map sideMap localBase
      (FundamentalGroup.map rightMap overlapBase
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk boundaryPath))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopActual)
    have hright : FundamentalGroup.map rightMap overlapBase
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk boundaryPath)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rightPath) := by
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    have hside : FundamentalGroup.map sideMap localBase
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk rightPath)) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (rightPath.map sideMap.continuous)) := by
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    rw [hright, hside]
  have hlocal : localFreeEquiv
      (FundamentalGroup.map rightMap overlapBase
        ⟦(circleOneTurnLoop θ).map boundary.continuous⟧) =
      diskFreeEquiv (FundamentalGroup.map sideMap localBase
        (FundamentalGroup.map rightMap overlapBase
          ⟦(circleOneTurnLoop θ).map boundary.continuous⟧)) := by
    calc
      _ = twoPuncturedDiskFundamentalGroupFreeEquiv bounds.1 bounds.2.1
          bounds.2.2.1 bounds.2.2.2
          hαβ ⟨sideHomeo localBase, hmem⟩
          (fundamentalGroupHomeomorphEquiv sideHomeo localBase
            (FundamentalGroup.map rightMap overlapBase
              ⟦(circleOneTurnLoop θ).map boundary.continuous⟧)) := by
        simpa [localFreeEquiv, sideHomeo, bounds] using
          (embeddedTwoPunctureRelativeLocalDiskFreeEquiv_apply
        f hf p q r (zero_lt_one.trans hr1) hrU hpR hqR hpq hpre hqre
        localBase hmem
        (FundamentalGroup.map rightMap overlapBase
          ⟦(circleOneTurnLoop θ).map boundary.continuous⟧))
      _ = diskFreeEquiv (FundamentalGroup.map sideMap localBase
          (FundamentalGroup.map rightMap overlapBase
            ⟦(circleOneTurnLoop θ).map boundary.continuous⟧)) := by
        dsimp [diskFreeEquiv, diskBase, sideMap]
        rfl
  set qOuter := twoPuncturedDiskOuterRightOverlapPoint hαβ hnorms.1 hnorms.2 hR
  have hword := twoPuncturedDiskOuterBoundaryLoop_freeWord
    hα hα1 hβ hβ1
    hαβ hnorms.1 hnorms.2 hR
  have houterVal : qOuter.1 =
      twoPuncturedDiskOuterRightCutPoint hαβ hnorms.1 hnorms.2 hR := by
    simp [qOuter, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph]
  have hq : diskBase = qOuter := by
    apply Subtype.ext
    exact hbase.trans houterVal.symm
  have hwordQ :
      twoPuncturedDiskFundamentalGroupFreeEquiv hα hα1 hβ hβ1 hαβ qOuter
        ⟦(twoPuncturedDiskOuterBoundaryLoop hαβ hnorms.1 hnorms.2 hR).cast
          houterVal houterVal⟧ = FreeGroup.of true * FreeGroup.of false := by
    dsimp only at hword
    simpa [qOuter, twoPuncturedDiskOuterRightOverlapPoint,
      twoPuncturedDiskOverlapHomeomorph] using hword
  have hwordAtBase : diskFreeEquiv ⟦loopActual⟧ =
      FreeGroup.of true * FreeGroup.of false := by
    have houterPath :
        ((circleOneTurnLoop θ).map outerCircle.continuous).cast hpoint hpoint =
          (twoPuncturedDiskOuterBoundaryLoop hαβ hnorms.1 hnorms.2 hR).cast
            hbase hbase := by
      apply Path.ext
      funext t
      simp [θ, outerCircle, twoPuncturedDiskOuterBoundaryLoop, Path.cast_coe]
    have hdoubleCast :
        ((twoPuncturedDiskOuterBoundaryLoop hαβ hnorms.1 hnorms.2 hR).cast
          houterVal houterVal).cast (congrArg Subtype.val hq)
            (congrArg Subtype.val hq) =
          (twoPuncturedDiskOuterBoundaryLoop hαβ hnorms.1 hnorms.2 hR).cast
            hbase hbase := by
      apply Path.ext
      funext t
      simp only [Path.cast_coe]
    have htransport := twoPuncturedDiskFundamentalGroupFreeEquiv_cast_eq
      hα hα1 hβ hβ1 hαβ diskBase qOuter hq
      ((twoPuncturedDiskOuterBoundaryLoop hαβ hnorms.1 hnorms.2 hR).cast
        houterVal houterVal)
    rw [hdoubleCast] at htransport
    rw [hpath, houterPath]
    simpa [diskFreeEquiv, diskBase, bounds] using htransport.trans hwordQ
  rw [hpath] at hwordAtBase
  rw [hlocal, hclass, hpath]
  exact hwordAtBase

#print axioms embeddedTwoPunctureRelativeBoundaryCircle_localDiskFreeWord

end

end SystolicGrowth
