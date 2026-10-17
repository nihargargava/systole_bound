module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterSideConnectorPaths
public import Geometry.SurfaceTwoCenterDiskPolarPaths
public import Geometry.TwoPuncturedDiskSideConnectorGenerators
public import Geometry.TwoPuncturedDiskSideScaling

@[expose] public section

/-!
# Native right polar generator in the local disk

Compare the actual native right polar loop with the tagged upper generator of
the literal local-disk free marking, using any certified upper-side connector.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups Topology unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- In the physical lower/upper ordering, the actual native right positive
polar loop, conjugated from any supplied upper-side connector at an actual
overlap basepoint, is the `false` generator under the local-disk free marking.
The endpoint and upper-side containment are literal; the map uses the
closest-deck phase of the selected right lift. -/
theorem componentTwoCenterNativeRightPolarLoop_localFreeGenerator
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ}
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (r : ℝ) (h1r : 1 < r) (hballr' : Metric.closedBall (0 : ℂ) r ⊆ U)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f)
    (d : TwoCenterPolarSideComparisonData p q m a b ρ ha hb)
    (horder : p.1.im < q.1.im)
    (mid : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hmid : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (lt_trans zero_lt_one h1r) hballr' hpre hqre mid :
        twoPuncturedUnitDiskPoint
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
    (rightPath : Path
      (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
        hpMap hqMap false ρ hρ hρr hsmall 1) mid)
    (hrightPath : ∀ t : I,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r (lt_trans zero_lt_one h1r) hballr' hpre hqre
        (rightPath t) : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) :
    let L := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
      hpMap hqMap false ρ hρ hρr hsmall
    let connector := rightPath.symm
    let loop := connector.trans (((circleOneTurnLoop 1).map L.continuous).trans
      connector.symm)
    embeddedTwoPunctureRelativeLocalDiskFreeEquiv f hf p q r
      (lt_trans zero_lt_one h1r) hballr' (by linarith [h1r, hp])
      (by linarith [h1r, hq]) hpq hpre hqre mid hmid ⟦loop⟧ =
      FreeGroup.of false := by
  let α := embeddedTwoPunctureLowerParameter p q r
  let β := embeddedTwoPunctureUpperParameter p q r
  let K := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r
    (lt_trans zero_lt_one h1r) hballr' hpre hqre
  let L := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
    hpMap hqMap false ρ hρ hρr hsmall
  let η := rightPath.symm
  let loop := η.trans (((circleOneTurnLoop 1).map L.continuous).trans η.symm)
  have hr : 0 < r := zero_lt_one.trans h1r
  have horderR : p.1.im / r < q.1.im / r :=
    (div_lt_div_iff_of_pos_right hr).2 horder
  have hparamL : α = p.1.im / r := by
    simp [α, embeddedTwoPunctureLowerParameter, min_eq_left horderR.le]
  have hparamU : β = q.1.im / r := by
    simp [β, embeddedTwoPunctureUpperParameter, max_eq_right horderR.le]
  have hαscale : r⁻¹ * p.1.im = α := by
    rw [hparamL]
    field_simp [hr.ne']
  have hβscale : r⁻¹ * q.1.im = β := by
    rw [hparamU]
    field_simp [hr.ne']
  have hαβ : α < β := by rw [hparamL, hparamU]; exact horderR
  have ⟨hα, hα1, hβ, hβ1⟩ := embeddedTwoPunctureParameters_bounds
    p q r hr (lt_trans hp h1r) (lt_trans hq h1r)
  have hαβ' : embeddedTwoPunctureLowerParameter p q r <
      embeddedTwoPunctureUpperParameter p q r :=
    embeddedTwoPunctureLowerParameter_lt_upper p q r hr hpq hpre hqre
  let q₀ : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β} := ⟨K mid, hmid⟩
  let B₀ := twoPuncturedDiskUpperBase p.1.im q.1.im
  let B := twoPuncturedDiskUpperBase α β
  let c := twoPuncturedDiskRightCenter β
  let phase := gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2
  let Apre := fermiSLPolarAnglePreimageMap γ
    (orientedFermiDiskPoint (m + a * q.1.im) a b 0)
  let phaseMap : C(Circle, Circle) := ⟨fun θ => phase * θ,
    continuous_const.mul continuous_id⟩
  let A := Apre.comp phaseMap
  let u := A 1
  have hmem : ∀ θ : Circle,
      c + fermiPositivePolarCoordinate (m + (a * r) * c.im)
        (a * r) (b * r) (mul_pos ha hr) (mul_pos hb hr) ρ θ ∈ B := by
    intro θ
    have hv := d.right_norm θ
    have hball : q.1 + fermiPositivePolarCoordinate
        (m + a * q.1.im) a b ha hb ρ θ ∈ Metric.ball q.1 d.δRight := by
      rw [Metric.mem_ball, dist_eq_norm]
      have heq : q.1 + fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ θ - q.1 =
            fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ := by
        abel
      rw [heq]
      exact hv
    have hB := d.right_ball hball
    rw [if_pos horder] at hB
    have hcenter : q.1 = twoPuncturedDiskRightCenter q.1.im := by
      apply Complex.ext <;> simp [twoPuncturedDiskRightCenter, hqre]
    have hne : q.1 + fermiPositivePolarCoordinate
        (m + a * q.1.im) a b ha hb ρ θ ≠
          twoPuncturedDiskRightCenter q.1.im := by
      rw [hcenter]
      intro hz
      have hz' : fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ θ = 0 := by
        have hz0 := hz
        rw [twoPuncturedDiskRightCenter_im, ← hcenter] at hz0
        have hzero : q.1 + fermiPositivePolarCoordinate
            (m + a * q.1.im) a b ha hb ρ θ = q.1 + 0 := by
          simpa only [add_zero] using hz0
        exact add_left_cancel hzero
      exact fermiPositivePolarCoordinate_ne_zero
        (m + a * q.1.im) a b ha hb hρ θ hz'
    have hside : q.1 + fermiPositivePolarCoordinate
        (m + a * q.1.im) a b ha hb ρ θ ∈
          twoPuncturedDiskUpperSide p.1.im q.1.im := ⟨hB, hne⟩
    have hscaled := twoPuncturedDiskUpperSide_inv_smul h1r.le hside
    have hc : c = (r⁻¹ : ℝ) • q.1 := by
      apply Complex.ext
      · simp [c, twoPuncturedDiskRightCenter, hqre]
      · change (twoPuncturedDiskRightCenter β).im = _
        rw [twoPuncturedDiskRightCenter_im, Complex.smul_im]
        simpa only [smul_eq_mul] using hβscale.symm
    have him : m + (a * r) * c.im = m + a * q.1.im := by
      have hcim : c.im = r⁻¹ * q.1.im := by
        change (twoPuncturedDiskRightCenter β).im = _
        rw [twoPuncturedDiskRightCenter_im]
        exact hβscale.symm
      rw [hcim]
      field_simp [hr.ne']
    have hcoord : c + fermiPositivePolarCoordinate
        (m + (a * r) * c.im) (a * r) (b * r)
        (mul_pos ha hr) (mul_pos hb hr) ρ θ =
        (r⁻¹ : ℝ) • (q.1 + fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ θ) := by
      rw [him, fermiPositivePolarCoordinate_scaled (m + a * q.1.im)
        a b r ha hb hr ρ θ]
      rw [smul_add, hc]
    rw [hcoord]
    rcases hscaled with ⟨hbase, _⟩
    simpa [B, hαscale, hβscale] using hbase
  let F := convexSideFermiPositivePolarCoordinateMap B c m (a * r) (b * r)
    (mul_pos ha hr) (mul_pos hb hr) ρ hρ hmem
  let Hside := twoPuncturedDiskUpperSideHomeomorph hαβ
  let Fside : C(Circle, twoPuncturedDiskUpperRelativePoint α β) :=
    ⟨fun θ => Hside.symm (F θ), Hside.symm.continuous.comp F.continuous⟩
  let Arot : C(Circle, Circle) := ⟨fun θ => u * θ,
    continuous_const.mul continuous_id⟩
  have hA : A = Arot := by
    apply ContinuousMap.ext
    intro θ
    dsimp [Arot]
    change fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * q.1.im) a b 0) (phase * θ) =
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * q.1.im) a b 0) (phase * 1)) * θ
    dsimp [fermiSLPolarAnglePreimageMap]
    rw [mul_one]
    rw [← mul_assoc (gluingPolarSLPhase γ
      (orientedFermiDiskPoint (m + a * q.1.im) a b 0))⁻¹ phase θ]
    ac_rfl
  let N := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
    hpMap hqMap false ρ hρ hρr hsmall
  have hBr : B₀ ⊆ Metric.ball (0 : ℂ) r := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
    have hzNorm : ‖z‖ < 1 := by
      change dist z 0 < 1 at hz1
      simpa only [dist_zero_right] using hz1
    change dist z 0 < r
    rw [dist_zero_right]
    exact lt_trans hzNorm h1r
  have hBU : B₀ ⊆ U := by
    intro z hz
    apply hballr'
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
    have hzNorm : ‖z‖ < 1 := by
      change dist z 0 < 1 at hz1
      simpa only [dist_zero_right] using hz1
    exact le_of_lt (lt_trans hzNorm h1r)
  have dRightBall : Metric.ball q.1 d.δRight ⊆ B₀ := by
    intro z hz
    simpa [B₀, if_pos horder] using d.right_ball hz
  have hqB : q.1 ∈ B₀ :=
    dRightBall (Metric.mem_ball.mpr (by simpa using d.δRight_pos))
  have hBother : ∀ z : ℂ, z ∈ B₀ → z ≠ p.1 := by
    intro z hz hEq
    have hzlt := hz.2
    change twoPuncturedDiskOverlapLower p.1.im q.1.im < z.im at hzlt
    rw [hEq] at hzlt
    have hbnd := (twoPuncturedDiskOverlap_bounds horder).1
    change p.1.im < twoPuncturedDiskOverlapLower p.1.im q.1.im at hbnd
    linarith
  have hcoord : ∀ θ : Circle,
      (K (N θ) : twoPuncturedUnitDiskPoint α β).1 = (F (A θ)).1 := by
    intro θ
    have hy : (N θ).1 = P.internalCenterPuncturedAmbientHomeomorph
        i f p q hi hnext hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) := by
      rfl
    have hchart := P.componentTwoCenterRightPolar_relativeLocalDisk_coordinate
      i r hr hballr' f hf p q hpMap hqMap hpre hqre hi hnext B₀ hBr hBU hqB
      hBother γ m a b ha hb hformula hright ρ d.δRight hρ hρr dRightBall
      d.right_norm θ (N θ) hy
    have hc : c = (r⁻¹ : ℝ) • q.1 := by
      apply Complex.ext
      · simp [c, twoPuncturedDiskRightCenter, hqre]
      · change (twoPuncturedDiskRightCenter β).im = _
        rw [twoPuncturedDiskRightCenter_im, Complex.smul_im]
        simpa only [smul_eq_mul] using hβscale.symm
    have him : m + (a * r) * c.im = m + a * q.1.im := by
      have hcim : c.im = r⁻¹ * q.1.im := by
        change (twoPuncturedDiskRightCenter β).im = _
        rw [twoPuncturedDiskRightCenter_im]
        exact hβscale.symm
      rw [hcim]
      field_simp [hr.ne']
    have hchart' : (K (N θ)).1 = (r⁻¹ : ℝ) •
        (q.1 + fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ (A θ)) := by
      simpa [K, A, Apre, phaseMap, fermiSLPolarAnglePreimageMap] using hchart
    calc
      (K (N θ)).1 = (r⁻¹ : ℝ) •
          (q.1 + fermiPositivePolarCoordinate
            (m + a * q.1.im) a b ha hb ρ (A θ)) := hchart'
      _ = c + fermiPositivePolarCoordinate
          (m + (a * r) * c.im) (a * r) (b * r)
            (mul_pos ha hr) (mul_pos hb hr) ρ (A θ) := by
        rw [him, hc, fermiPositivePolarCoordinate_scaled
          (m + a * q.1.im) a b r ha hb hr ρ (A θ), smul_add]
  let coordPath := embeddedTwoPunctureCoordinateSidePath r hr hballr'
    f hf p q hpre hqre rightPath
    (twoPuncturedDiskUpperSide α β) hrightPath
  let rawConnector := (coordPath.map Hside.symm.continuous).symm
  have hrawStart : rawConnector 0 = Hside.symm (coordPath 1) := by
    simp [rawConnector]
  have hrawEnd : rawConnector 1 = Hside.symm (coordPath 0) := by
    simp [rawConnector]
  have hstart : twoPuncturedDiskUpperRelativePointOfOverlap q₀ =
      rawConnector 0 := by
    rw [hrawStart, coordPath.target]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hend : Fside (Arot 1) = rawConnector 1 := by
    have hA1 : Arot 1 = A 1 := by
      exact congrArg (fun G : C(Circle, Circle) => G 1) hA.symm
    rw [hA1]
    dsimp [Fside]
    rw [hrawEnd]
    have hcoordPath : F (A 1) = coordPath 0 := by
      apply Subtype.ext
      simpa [coordPath, embeddedTwoPunctureCoordinateSidePath,
        embeddedTwoPunctureCoordinateSidePath_apply_val, K, N, rightPath.source] using
          (hcoord 1).symm
    exact congrArg Hside.symm hcoordPath
  let connector : Path (twoPuncturedDiskUpperRelativePointOfOverlap q₀)
      (Fside (Arot 1)) := rawConnector.cast
        (hstart.trans rawConnector.source) (hend.trans rawConnector.target)
  let Frot := Fside.comp Arot
  let Kmap : C({z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r},
      twoPuncturedUnitDiskPoint α β) := ⟨K, K.continuous⟩
  let loopSide := connector.trans (((circleOneTurnLoop 1).map Frot.continuous).trans
    connector.symm)
  have hcoordPathVal (t : I) : (coordPath t).1 = (K (rightPath t)).1 := by
    simp [coordPath, embeddedTwoPunctureCoordinateSidePath_apply_val, K]
  have hrawMapVal (t : I) :
      ((twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)) (rawConnector t)).1 =
        (coordPath (σ t)).1 := by
    simp only [twoOpenCoverAmalgamInclusion, rawConnector,
      Hside, twoPuncturedDiskUpperSideHomeomorph]
    change (coordPath.symm t).1 = (coordPath (σ t)).1
    exact congrArg Subtype.val (Path.symm_apply coordPath t)
  have hmap : Kmap.comp N =
      (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)).comp Frot := by
    apply ContinuousMap.ext
    intro θ
    apply Subtype.ext
    simpa [Kmap, Frot, Arot, Fside, Hside, hA,
      twoPuncturedDiskUpperSideHomeomorph,
      twoPuncturedDiskUpperSideToDisk,
      twoOpenCoverAmalgamInclusion] using hcoord θ
  have hconnectorMap : ∀ t : I,
      η.map Kmap.continuous t =
        connector.map (twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskUpperRelativeSide α β)).continuous t := by
    intro t
    apply Subtype.ext
    change (K (rightPath (σ t))).1 =
      ((twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)) (connector t)).1
    change (K (rightPath (σ t))).1 =
      ((twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)) (rawConnector t)).1
    rw [hrawMapVal t, hcoordPathVal (σ t)]
  have hbase : (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β))
        (twoPuncturedDiskUpperRelativePointOfOverlap q₀) = Kmap mid := by
    rfl
  have htarget : (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)) (Frot 1) = Kmap (N 1) := by
    have ht := congrArg (fun M : C(Circle, twoPuncturedUnitDiskPoint α β) => M 1) hmap
    simpa only [ContinuousMap.comp_apply] using ht.symm
  have hconnectorMapPath : (η.map Kmap.continuous).cast hbase htarget =
      connector.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)).continuous := by
    apply Path.ext
    funext t
    exact hconnectorMap t
  have hconnectorMapSymm : (η.symm.map Kmap.continuous).cast htarget hbase =
      connector.symm.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)).continuous := by
    simpa only [← Path.cast_symm, Path.map_symm] using congrArg Path.symm hconnectorMapPath
  have hcenterMap :
      ((((circleOneTurnLoop 1).map N.continuous).map Kmap.continuous).cast
        htarget htarget) =
        (((circleOneTurnLoop 1).map Frot.continuous).map
          (twoOpenCoverAmalgamInclusion
            (twoPuncturedDiskUpperRelativeSide α β)).continuous) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    have ht := congrArg (fun M : C(Circle, twoPuncturedUnitDiskPoint α β) =>
      M (circleOneTurnLoop 1 t)) hmap
    simpa only [Path.cast_coe, Path.map_coe, Function.comp_apply,
      ContinuousMap.comp_apply] using congrArg Subtype.val ht
  have hcastDecomp :
      ((η.map Kmap.continuous).trans
        ((((circleOneTurnLoop 1).map L.continuous).map Kmap.continuous).trans
          (η.symm.map Kmap.continuous))).cast hbase hbase =
        ((η.map Kmap.continuous).cast hbase htarget).trans
          (((((circleOneTurnLoop 1).map L.continuous).map Kmap.continuous).cast
            htarget htarget).trans
            ((η.symm.map Kmap.continuous).cast htarget hbase)) := by
    calc
      _ = ((η.map Kmap.continuous).cast hbase htarget).trans
          (((((circleOneTurnLoop 1).map L.continuous).map Kmap.continuous).trans
            (η.symm.map Kmap.continuous)).cast htarget hbase) := by
          rw [Path.cast_trans]
      _ = _ := by rw [Path.cast_trans]
  have hloopMap : (loop.map Kmap.continuous).cast hbase hbase =
      loopSide.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)).continuous := by
    simp only [loop, loopSide, Path.map_trans]
    rw [hcastDecomp, hconnectorMapPath, hcenterMap, hconnectorMapSymm]
  have hloopMapRaw : loop.map Kmap.continuous =
      loopSide.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β)).continuous := by
    apply Path.ext
    funext t
    have ht := congrArg (fun z : Path
        ((twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskUpperRelativeSide α β))
            (twoPuncturedDiskUpperRelativePointOfOverlap q₀))
        ((twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskUpperRelativeSide α β))
            (twoPuncturedDiskUpperRelativePointOfOverlap q₀)) => z t) hloopMap
    exact ht
  have hgen := twoPuncturedDiskFundamentalGroupFreeEquiv_upperRotatedFermiPositiveLoop_of_mem
    hα hα1 hβ hβ1 hαβ q₀ m (a * r) (b * r) ρ
    (mul_pos ha hr) (mul_pos hb hr) hρ hmem u 1 connector
  have hwhole :
      fundamentalGroupHomeomorphEquiv K mid ⟦loop⟧ =
        twoOpenCoverSideToAmbient
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q₀ false
            ⟦loopSide⟧ := by
    change FundamentalGroup.map Kmap mid
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) = _
    dsimp only [twoOpenCoverSideToAmbient,
      twoPuncturedDiskUpperRelativePointOfOverlap,
      twoOpenCoverAmalgamOverlapRight]
    change FundamentalGroup.map Kmap mid
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) =
      FundamentalGroup.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β))
        (twoOpenCoverAmalgamOverlapRight
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q₀)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopSide))
    have hleft : FundamentalGroup.map Kmap mid
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (loop.map Kmap.continuous)) := by
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    have hright : FundamentalGroup.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskUpperRelativeSide α β))
        (twoOpenCoverAmalgamOverlapRight
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q₀)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopSide)) =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (loopSide.map (twoOpenCoverAmalgamInclusion
              (twoPuncturedDiskUpperRelativeSide α β)).continuous)) := by
      change FundamentalGroup.map (twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskUpperRelativeSide α β))
          (twoPuncturedDiskUpperRelativePointOfOverlap q₀)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopSide)) = _
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    rw [hleft, hright]
    exact congrArg FundamentalGroup.fromPath
      (congrArg Path.Homotopic.Quotient.mk hloopMapRaw)
  have hmark := embeddedTwoPunctureRelativeLocalDiskFreeEquiv_apply
    f hf p q r hr hballr' (lt_trans hp h1r) (lt_trans hq h1r) hpq
    hpre hqre mid hmid (⟦loop⟧ : FundamentalGroup _ mid)
  change embeddedTwoPunctureRelativeLocalDiskFreeEquiv f hf p q r hr hballr'
      (lt_trans hp h1r) (lt_trans hq h1r) hpq hpre hqre mid hmid
      (⟦loop⟧ : FundamentalGroup _ mid) = FreeGroup.of false
  rw [hmark, hwhole]
  exact hgen

#print axioms componentTwoCenterNativeRightPolarLoop_localFreeGenerator
/-! The opposite vertical ordering. When the native right center lies
below the native left center, its positive polar loop lies in the lower
relative side and maps to the `true` generator, with the same closest-deck
phase as the original right-polar coordinate theorem. -/

theorem componentTwoCenterNativeRightPolarLoop_localFreeGenerator_lower
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ}
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (r : ℝ) (h1r : 1 < r) (hballr' : Metric.closedBall (0 : ℂ) r ⊆ U)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f)
    (d : TwoCenterPolarSideComparisonData p q m a b ρ ha hb)
    (horder : q.1.im < p.1.im)
    (mid : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hmid : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (lt_trans zero_lt_one h1r) hballr' hpre hqre mid :
        twoPuncturedUnitDiskPoint
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
    (rightPath : Path
      (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
        hpMap hqMap false ρ hρ hρr hsmall 1) mid)
    (hrightPath : ∀ t : I,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r (lt_trans zero_lt_one h1r) hballr' hpre hqre
        (rightPath t) : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) :
    let L := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
      hpMap hqMap false ρ hρ hρr hsmall
    let connector := rightPath.symm
    let loop := connector.trans (((circleOneTurnLoop 1).map L.continuous).trans
      connector.symm)
    embeddedTwoPunctureRelativeLocalDiskFreeEquiv f hf p q r
      (lt_trans zero_lt_one h1r) hballr' (by linarith [h1r, hp])
      (by linarith [h1r, hq]) hpq hpre hqre mid hmid ⟦loop⟧ =
      FreeGroup.of true := by
  let α := embeddedTwoPunctureLowerParameter p q r
  let β := embeddedTwoPunctureUpperParameter p q r
  let K := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r
    (lt_trans zero_lt_one h1r) hballr' hpre hqre
  let L := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
    hpMap hqMap false ρ hρ hρr hsmall
  let η := rightPath.symm
  let loop := η.trans (((circleOneTurnLoop 1).map L.continuous).trans η.symm)
  have hr : 0 < r := zero_lt_one.trans h1r
  have horderR : q.1.im / r < p.1.im / r :=
    (div_lt_div_iff_of_pos_right hr).2 horder
  have hparamL : α = q.1.im / r := by
    simp [α, embeddedTwoPunctureLowerParameter, min_eq_right horderR.le]
  have hparamU : β = p.1.im / r := by
    simp [β, embeddedTwoPunctureUpperParameter, max_eq_left horderR.le]
  have hαscale : r⁻¹ * q.1.im = α := by
    rw [hparamL]
    field_simp [hr.ne']
  have hβscale : r⁻¹ * p.1.im = β := by
    rw [hparamU]
    field_simp [hr.ne']
  have hαβ : α < β := by rw [hparamL, hparamU]; exact horderR
  have ⟨hα, hα1, hβ, hβ1⟩ := embeddedTwoPunctureParameters_bounds
    p q r hr (lt_trans hp h1r) (lt_trans hq h1r)
  have hαβ' : embeddedTwoPunctureLowerParameter p q r <
      embeddedTwoPunctureUpperParameter p q r :=
    embeddedTwoPunctureLowerParameter_lt_upper p q r hr hpq hpre hqre
  let q₀ : {z : twoPuncturedUnitDiskPoint α β //
      z ∈ twoPuncturedDiskRelativeOverlap α β} := ⟨K mid, hmid⟩
  let B₀ := twoPuncturedDiskLowerBase q.1.im p.1.im
  let B := twoPuncturedDiskLowerBase α β
  let c := twoPuncturedDiskLeftCenter α
  let phase := gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2
  let Apre := fermiSLPolarAnglePreimageMap γ
    (orientedFermiDiskPoint (m + a * q.1.im) a b 0)
  let phaseMap : C(Circle, Circle) := ⟨fun θ => phase * θ,
    continuous_const.mul continuous_id⟩
  let A := Apre.comp phaseMap
  let u := A 1
  have horderNot : ¬ p.1.im < q.1.im := not_lt_of_gt horder
  have hmem : ∀ θ : Circle,
      c + fermiPositivePolarCoordinate (m + (a * r) * c.im)
        (a * r) (b * r) (mul_pos ha hr) (mul_pos hb hr) ρ θ ∈ B := by
    intro θ
    have hv := d.right_norm θ
    have hball : q.1 + fermiPositivePolarCoordinate
        (m + a * q.1.im) a b ha hb ρ θ ∈ Metric.ball q.1 d.δRight := by
      rw [Metric.mem_ball, dist_eq_norm]
      have heq : q.1 + fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ θ - q.1 =
            fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ := by
        abel
      rw [heq]
      exact hv
    have hB := d.right_ball hball
    rw [if_neg horderNot] at hB
    have hcenter : q.1 = twoPuncturedDiskLeftCenter q.1.im := by
      apply Complex.ext <;> simp [twoPuncturedDiskLeftCenter, hqre]
    have hne : q.1 + fermiPositivePolarCoordinate
        (m + a * q.1.im) a b ha hb ρ θ ≠
          twoPuncturedDiskLeftCenter q.1.im := by
      rw [hcenter]
      intro hz
      have hz' : fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ θ = 0 := by
        have hz0 := hz
        rw [twoPuncturedDiskLeftCenter_im, ← hcenter] at hz0
        have hzero : q.1 + fermiPositivePolarCoordinate
            (m + a * q.1.im) a b ha hb ρ θ = q.1 + 0 := by
          simpa only [add_zero] using hz0
        exact add_left_cancel hzero
      exact fermiPositivePolarCoordinate_ne_zero
        (m + a * q.1.im) a b ha hb hρ θ hz'
    have hside : q.1 + fermiPositivePolarCoordinate
        (m + a * q.1.im) a b ha hb ρ θ ∈
          twoPuncturedDiskLowerSide q.1.im p.1.im := ⟨hB, hne⟩
    have hscaled := twoPuncturedDiskLowerSide_inv_smul h1r.le hside
    have hc : c = (r⁻¹ : ℝ) • q.1 := by
      apply Complex.ext
      · simp [c, twoPuncturedDiskLeftCenter, hqre]
      · change (twoPuncturedDiskLeftCenter α).im = _
        rw [twoPuncturedDiskLeftCenter_im, Complex.smul_im]
        simpa only [smul_eq_mul] using hαscale.symm
    have him : m + (a * r) * c.im = m + a * q.1.im := by
      have hcim : c.im = r⁻¹ * q.1.im := by
        change (twoPuncturedDiskLeftCenter α).im = _
        rw [twoPuncturedDiskLeftCenter_im]
        exact hαscale.symm
      rw [hcim]
      field_simp [hr.ne']
    have hcoord : c + fermiPositivePolarCoordinate
        (m + (a * r) * c.im) (a * r) (b * r)
        (mul_pos ha hr) (mul_pos hb hr) ρ θ =
        (r⁻¹ : ℝ) • (q.1 + fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ θ) := by
      rw [him, fermiPositivePolarCoordinate_scaled (m + a * q.1.im)
        a b r ha hb hr ρ θ]
      rw [smul_add, hc]
    rw [hcoord]
    rcases hscaled with ⟨hbase, _⟩
    simpa [B, hαscale, hβscale] using hbase
  let F := convexSideFermiPositivePolarCoordinateMap B c m (a * r) (b * r)
    (mul_pos ha hr) (mul_pos hb hr) ρ hρ hmem
  let Hside := twoPuncturedDiskLowerSideHomeomorph hαβ
  let Fside : C(Circle, twoPuncturedDiskLowerRelativePoint α β) :=
    ⟨fun θ => Hside.symm (F θ), Hside.symm.continuous.comp F.continuous⟩
  let Arot : C(Circle, Circle) := ⟨fun θ => u * θ,
    continuous_const.mul continuous_id⟩
  have hA : A = Arot := by
    apply ContinuousMap.ext
    intro θ
    dsimp [Arot]
    change fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * q.1.im) a b 0) (phase * θ) =
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * q.1.im) a b 0) (phase * 1)) * θ
    dsimp [fermiSLPolarAnglePreimageMap]
    rw [mul_one]
    rw [← mul_assoc (gluingPolarSLPhase γ
      (orientedFermiDiskPoint (m + a * q.1.im) a b 0))⁻¹ phase θ]
    ac_rfl
  let N := P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
    hpMap hqMap false ρ hρ hρr hsmall
  have hBr : B₀ ⊆ Metric.ball (0 : ℂ) r := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
    have hzNorm : ‖z‖ < 1 := by
      change dist z 0 < 1 at hz1
      simpa only [dist_zero_right] using hz1
    change dist z 0 < r
    rw [dist_zero_right]
    exact lt_trans hzNorm h1r
  have hBU : B₀ ⊆ U := by
    intro z hz
    apply hballr'
    rw [Metric.mem_closedBall, dist_zero_right]
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hz.1
    have hzNorm : ‖z‖ < 1 := by
      change dist z 0 < 1 at hz1
      simpa only [dist_zero_right] using hz1
    exact le_of_lt (lt_trans hzNorm h1r)
  have dRightBall : Metric.ball q.1 d.δRight ⊆ B₀ := by
    intro z hz
    simpa [B₀, if_neg horderNot] using d.right_ball hz
  have hqB : q.1 ∈ B₀ :=
    dRightBall (Metric.mem_ball.mpr (by simpa using d.δRight_pos))
  have hBother : ∀ z : ℂ, z ∈ B₀ → z ≠ p.1 := by
    intro z hz hEq
    have hzlt := hz.2
    change z.im < twoPuncturedDiskOverlapUpper q.1.im p.1.im at hzlt
    rw [hEq] at hzlt
    have hbnd := (twoPuncturedDiskOverlap_bounds horder).2.2
    change twoPuncturedDiskOverlapUpper q.1.im p.1.im < p.1.im at hbnd
    linarith
  have hcoord : ∀ θ : Circle,
      (K (N θ) : twoPuncturedUnitDiskPoint α β).1 = (F (A θ)).1 := by
    intro θ
    have hy : (N θ).1 = P.internalCenterPuncturedAmbientHomeomorph
        i f p q hi hnext hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) := by
      rfl
    have hchart := P.componentTwoCenterRightPolar_relativeLocalDisk_coordinate
      i r hr hballr' f hf p q hpMap hqMap hpre hqre hi hnext B₀ hBr hBU hqB
      hBother γ m a b ha hb hformula hright ρ d.δRight hρ hρr dRightBall
      d.right_norm θ (N θ) hy
    have hc : c = (r⁻¹ : ℝ) • q.1 := by
      apply Complex.ext
      · simp [c, twoPuncturedDiskLeftCenter, hqre]
      · change (twoPuncturedDiskLeftCenter α).im = _
        rw [twoPuncturedDiskLeftCenter_im, Complex.smul_im]
        simpa only [smul_eq_mul] using hαscale.symm
    have him : m + (a * r) * c.im = m + a * q.1.im := by
      have hcim : c.im = r⁻¹ * q.1.im := by
        change (twoPuncturedDiskLeftCenter α).im = _
        rw [twoPuncturedDiskLeftCenter_im]
        exact hαscale.symm
      rw [hcim]
      field_simp [hr.ne']
    have hchart' : (K (N θ)).1 = (r⁻¹ : ℝ) •
        (q.1 + fermiPositivePolarCoordinate
          (m + a * q.1.im) a b ha hb ρ (A θ)) := by
      simpa [K, A, Apre, phaseMap, fermiSLPolarAnglePreimageMap] using hchart
    calc
      (K (N θ)).1 = (r⁻¹ : ℝ) •
          (q.1 + fermiPositivePolarCoordinate
            (m + a * q.1.im) a b ha hb ρ (A θ)) := hchart'
      _ = c + fermiPositivePolarCoordinate
          (m + (a * r) * c.im) (a * r) (b * r)
            (mul_pos ha hr) (mul_pos hb hr) ρ (A θ) := by
        rw [him, hc, fermiPositivePolarCoordinate_scaled
          (m + a * q.1.im) a b r ha hb hr ρ (A θ), smul_add]
  let coordPath := embeddedTwoPunctureCoordinateSidePath r hr hballr'
    f hf p q hpre hqre rightPath
    (twoPuncturedDiskLowerSide α β) hrightPath
  let rawConnector := (coordPath.map Hside.symm.continuous).symm
  have hrawStart : rawConnector 0 = Hside.symm (coordPath 1) := by
    simp [rawConnector]
  have hrawEnd : rawConnector 1 = Hside.symm (coordPath 0) := by
    simp [rawConnector]
  have hstart : twoPuncturedDiskLowerRelativePointOfOverlap q₀ =
      rawConnector 0 := by
    rw [hrawStart, coordPath.target]
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hend : Fside (Arot 1) = rawConnector 1 := by
    have hA1 : Arot 1 = A 1 := by
      exact congrArg (fun G : C(Circle, Circle) => G 1) hA.symm
    rw [hA1]
    dsimp [Fside]
    rw [hrawEnd]
    have hcoordPath : F (A 1) = coordPath 0 := by
      apply Subtype.ext
      simpa [coordPath, embeddedTwoPunctureCoordinateSidePath,
        embeddedTwoPunctureCoordinateSidePath_apply_val, K, N, rightPath.source] using
          (hcoord 1).symm
    exact congrArg Hside.symm hcoordPath
  let connector : Path (twoPuncturedDiskLowerRelativePointOfOverlap q₀)
      (Fside (Arot 1)) := rawConnector.cast
        (hstart.trans rawConnector.source) (hend.trans rawConnector.target)
  let Frot := Fside.comp Arot
  let Kmap : C({z : embeddedTwoPunctureAmbientPoint f p q //
      z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r},
      twoPuncturedUnitDiskPoint α β) := ⟨K, K.continuous⟩
  let loopSide := connector.trans (((circleOneTurnLoop 1).map Frot.continuous).trans
    connector.symm)
  have hcoordPathVal (t : I) : (coordPath t).1 = (K (rightPath t)).1 := by
    simp [coordPath, embeddedTwoPunctureCoordinateSidePath_apply_val, K]
  have hrawMapVal (t : I) :
      ((twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)) (rawConnector t)).1 =
        (coordPath (σ t)).1 := by
    simp only [twoOpenCoverAmalgamInclusion, rawConnector,
      Hside, twoPuncturedDiskLowerSideHomeomorph]
    change (coordPath.symm t).1 = (coordPath (σ t)).1
    exact congrArg Subtype.val (Path.symm_apply coordPath t)
  have hmap : Kmap.comp N =
      (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)).comp Frot := by
    apply ContinuousMap.ext
    intro θ
    apply Subtype.ext
    simpa [Kmap, Frot, Arot, Fside, Hside, hA,
      twoPuncturedDiskLowerSideHomeomorph,
      twoPuncturedDiskLowerSideToDisk,
      twoOpenCoverAmalgamInclusion] using hcoord θ
  have hconnectorMap : ∀ t : I,
      η.map Kmap.continuous t =
        connector.map (twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskLowerRelativeSide α β)).continuous t := by
    intro t
    apply Subtype.ext
    change (K (rightPath (σ t))).1 =
      ((twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)) (connector t)).1
    change (K (rightPath (σ t))).1 =
      ((twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)) (rawConnector t)).1
    rw [hrawMapVal t, hcoordPathVal (σ t)]
  have hbase : (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β))
        (twoPuncturedDiskLowerRelativePointOfOverlap q₀) = Kmap mid := by
    rfl
  have htarget : (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)) (Frot 1) = Kmap (N 1) := by
    have ht := congrArg (fun M : C(Circle, twoPuncturedUnitDiskPoint α β) => M 1) hmap
    simpa only [ContinuousMap.comp_apply] using ht.symm
  have hconnectorMapPath : (η.map Kmap.continuous).cast hbase htarget =
      connector.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)).continuous := by
    apply Path.ext
    funext t
    exact hconnectorMap t
  have hconnectorMapSymm : (η.symm.map Kmap.continuous).cast htarget hbase =
      connector.symm.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)).continuous := by
    simpa only [← Path.cast_symm, Path.map_symm] using congrArg Path.symm hconnectorMapPath
  have hcenterMap :
      ((((circleOneTurnLoop 1).map N.continuous).map Kmap.continuous).cast
        htarget htarget) =
        (((circleOneTurnLoop 1).map Frot.continuous).map
          (twoOpenCoverAmalgamInclusion
            (twoPuncturedDiskLowerRelativeSide α β)).continuous) := by
    apply Path.ext
    funext t
    apply Subtype.ext
    have ht := congrArg (fun M : C(Circle, twoPuncturedUnitDiskPoint α β) =>
      M (circleOneTurnLoop 1 t)) hmap
    simpa only [Path.cast_coe, Path.map_coe, Function.comp_apply,
      ContinuousMap.comp_apply] using congrArg Subtype.val ht
  have hcastDecomp :
      ((η.map Kmap.continuous).trans
        ((((circleOneTurnLoop 1).map L.continuous).map Kmap.continuous).trans
          (η.symm.map Kmap.continuous))).cast hbase hbase =
        ((η.map Kmap.continuous).cast hbase htarget).trans
          (((((circleOneTurnLoop 1).map L.continuous).map Kmap.continuous).cast
            htarget htarget).trans
            ((η.symm.map Kmap.continuous).cast htarget hbase)) := by
    calc
      _ = ((η.map Kmap.continuous).cast hbase htarget).trans
          (((((circleOneTurnLoop 1).map L.continuous).map Kmap.continuous).trans
            (η.symm.map Kmap.continuous)).cast htarget hbase) := by
          rw [Path.cast_trans]
      _ = _ := by rw [Path.cast_trans]
  have hloopMap : (loop.map Kmap.continuous).cast hbase hbase =
      loopSide.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)).continuous := by
    simp only [loop, loopSide, Path.map_trans]
    rw [hcastDecomp, hconnectorMapPath, hcenterMap, hconnectorMapSymm]
  have hloopMapRaw : loop.map Kmap.continuous =
      loopSide.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β)).continuous := by
    apply Path.ext
    funext t
    have ht := congrArg (fun z : Path
        ((twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskLowerRelativeSide α β))
            (twoPuncturedDiskLowerRelativePointOfOverlap q₀))
        ((twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskLowerRelativeSide α β))
            (twoPuncturedDiskLowerRelativePointOfOverlap q₀)) => z t) hloopMap
    exact ht
  have hgen := twoPuncturedDiskFundamentalGroupFreeEquiv_lowerRotatedFermiPositiveLoop_of_mem
    hα hα1 hβ hβ1 hαβ q₀ m (a * r) (b * r) ρ
    (mul_pos ha hr) (mul_pos hb hr) hρ hmem u 1 connector
  have hwhole :
      fundamentalGroupHomeomorphEquiv K mid ⟦loop⟧ =
        twoOpenCoverSideToAmbient
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q₀ true
            ⟦loopSide⟧ := by
    change FundamentalGroup.map Kmap mid
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) = _
    dsimp only [twoOpenCoverSideToAmbient,
      twoPuncturedDiskLowerRelativePointOfOverlap,
      twoOpenCoverAmalgamOverlapLeft]
    change FundamentalGroup.map Kmap mid
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) =
      FundamentalGroup.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β))
        (twoOpenCoverAmalgamOverlapLeft
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q₀)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopSide))
    have hleft : FundamentalGroup.map Kmap mid
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loop)) =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (loop.map Kmap.continuous)) := by
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    have hright : FundamentalGroup.map (twoOpenCoverAmalgamInclusion
        (twoPuncturedDiskLowerRelativeSide α β))
        (twoOpenCoverAmalgamOverlapLeft
          (twoPuncturedDiskLowerRelativeSide α β)
          (twoPuncturedDiskUpperRelativeSide α β) q₀)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopSide)) =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (loopSide.map (twoOpenCoverAmalgamInclusion
              (twoPuncturedDiskLowerRelativeSide α β)).continuous)) := by
      change FundamentalGroup.map (twoOpenCoverAmalgamInclusion
          (twoPuncturedDiskLowerRelativeSide α β))
          (twoPuncturedDiskLowerRelativePointOfOverlap q₀)
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk loopSide)) = _
      rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    rw [hleft, hright]
    exact congrArg FundamentalGroup.fromPath
      (congrArg Path.Homotopic.Quotient.mk hloopMapRaw)
  have hmark := embeddedTwoPunctureRelativeLocalDiskFreeEquiv_apply
    f hf p q r hr hballr' (lt_trans hp h1r) (lt_trans hq h1r) hpq
    hpre hqre mid hmid (⟦loop⟧ : FundamentalGroup _ mid)
  change embeddedTwoPunctureRelativeLocalDiskFreeEquiv f hf p q r hr hballr'
      (lt_trans hp h1r) (lt_trans hq h1r) hpq hpre hqre mid hmid
      (⟦loop⟧ : FundamentalGroup _ mid) = FreeGroup.of true
  rw [hmark, hwhole]
  exact hgen


#print axioms componentTwoCenterNativeRightPolarLoop_localFreeGenerator_lower

end

end ExerciseGluingPreparation
end SystolicGrowth
