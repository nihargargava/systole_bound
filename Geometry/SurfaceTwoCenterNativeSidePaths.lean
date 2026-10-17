module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterSideConnectorPaths
public import Geometry.SurfaceTwoCenterAnnulusConnectorPaths
public import Geometry.SurfaceTwoCenterPolarCutTransport

@[expose] public section

/-!
# Native connector halves in actual local coordinate sides

The native radius-angle connector's two literal half-paths are transported
into the relative local disk of any larger chart radius. Their shared point
is the actual center-segment midpoint, and the chart coordinates place the
halves in the appropriate lower and upper sides.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups Topology unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)} {U : Set ℂ}

/-- The checked unit-radius half witnesses give actual paths in the relative
local disk of any larger chart radius. The path endpoints are the existing
small positive-polar maps, and inclusion into the native carrier recovers the
two literal native half-paths pointwise. The actual midpoint remains in the
relative overlap after its positive radius normalization. -/
theorem exists_componentTwoCenterNativeSidePaths
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (f : C(U, (X i).Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (hsegment : ∀ t : I,
      P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f)
    (r : ℝ) (h1r : 1 < r)
    (hballr : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      ∃ hsmall : (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f),
      (∀ t : I,
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      Nonempty (TwoCenterPolarSideComparisonData p q m a b ρ ha hb) ∧
      ∃ mid : {w : embeddedTwoPunctureAmbientPoint f p q //
          w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r},
        mid.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
          hpMap hqMap
          (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
            componentTwoCenterSmallConnectorMidpointTime) ∧
        embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre mid ∈
            twoPuncturedDiskRelativeOverlap
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r) ∧
        ((p.1.im < q.1.im ∧
          ∃ leftPath : Path
              (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                hpMap hqMap true ρ hρ hρr hsmall 1) mid,
          ∃ rightPath : Path mid
              (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                hpMap hqMap false ρ hρ hρr hsmall 1),
            (∀ t : I,
              P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap
                (twoOpenCoverAmalgamInclusion
                  (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
                  (leftPath t)) =
                P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
            (∀ t : I,
              P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap
                (twoOpenCoverAmalgamInclusion
                  (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
                  (rightPath t)) =
                P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
            (∀ t : I,
              (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
                f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre
                  (leftPath t) : ℂ) ∈
                twoPuncturedDiskLowerSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)) ∧
            (∀ t : I,
              (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
                f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre
                  (rightPath t) : ℂ) ∈
                twoPuncturedDiskUpperSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r))) ∨
         (q.1.im < p.1.im ∧
          ∃ leftPath : Path
              (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                hpMap hqMap true ρ hρ hρr hsmall 1) mid,
          ∃ rightPath : Path mid
              (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                hpMap hqMap false ρ hρ hρr hsmall 1),
            (∀ t : I,
              P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap
                (twoOpenCoverAmalgamInclusion
                  (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
                  (leftPath t)) =
                P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
            (∀ t : I,
              P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap
                (twoOpenCoverAmalgamInclusion
                  (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
                  (rightPath t)) =
                P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
            (∀ t : I,
              (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
                f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre
                  (leftPath t) : ℂ) ∈
                twoPuncturedDiskUpperSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)) ∧
            (∀ t : I,
              (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
                f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre
                  (rightPath t) : ℂ) ∈
                twoPuncturedDiskLowerSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)))) := by
  have hball1 : Metric.closedBall (0 : ℂ) 1 ⊆ U := by
    intro z hz
    apply hballr
    apply Metric.mem_closedBall.mpr
    have hz' := Metric.mem_closedBall.mp hz
    simpa only [dist_zero_right] using le_trans hz' (le_of_lt h1r)
  obtain ⟨ρ, hρ, hρr, hcircles, hcandidate, hcomparison, horder⟩ :=
    P.exists_componentTwoCenterSmallConnector_halves_mem_relativeSides_with_comparisonData i hU hball1
      f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext γ m a b ha hb
      hformula hleft hright hsegment hchartSegment
  have hsmall : ∀ (b : Bool) (θ : Circle),
      (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
        embeddedCoordinatePunctureDisk f := hcircles
  obtain ⟨ymid, hymid, hcoordmid⟩ :=
    P.exists_componentTwoCenterConnectorMidpoint_mem_relativeOverlap i hball1 f hf
      p q hpMap hqMap hpre hqre hpq hi hnext hchartSegment ρ hρ hρr
  let mid := embeddedTwoPunctureRelativeLocalDiskInclusion
    f p q 1 r (le_of_lt h1r) ymid
  have hmidval : mid.1 = P.internalCenterPuncturedAmbientHomeomorph
      i f p q hi hnext hpMap hqMap
      (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime) := by
    simpa [mid, embeddedTwoPunctureRelativeLocalDiskInclusion,
      P.internalCenterPuncturedAmbientHomeomorph_apply_val,
      P.componentTwoCenterSmallConnector_midpoint_value] using hymid
  have hcoordmidR :
      embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre mid ∈
        twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
    dsimp [mid]
    let E1 := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q 1 one_pos hball1 hpre hqre
    let Er := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre
    have hcoord : (Er (embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) ymid) : ℂ) =
        (r⁻¹ : ℝ) • (E1 ymid : ℂ) :=
      embeddedTwoPunctureRelativeLocalDiskInclusion_unitCoordinate
        f hf p q r (lt_trans zero_lt_one h1r) (le_of_lt h1r)
        hball1 hballr hpre hqre ymid
    have hparamsL := embeddedTwoPunctureLowerParameter_scaled p q r
      (lt_trans zero_lt_one h1r)
    have hparamsU := embeddedTwoPunctureUpperParameter_scaled p q r
      (lt_trans zero_lt_one h1r)
    have hcoordLower : (E1 ymid : ℂ) ∈ twoPuncturedDiskLowerSide
        (embeddedTwoPunctureLowerParameter p q 1)
        (embeddedTwoPunctureUpperParameter p q 1) := by
      change E1 ymid ∈ twoPuncturedDiskRelativeOverlap
        (embeddedTwoPunctureLowerParameter p q 1)
        (embeddedTwoPunctureUpperParameter p q 1) at hcoordmid
      exact hcoordmid.1
    have hcoordUpper : (E1 ymid : ℂ) ∈ twoPuncturedDiskUpperSide
        (embeddedTwoPunctureLowerParameter p q 1)
        (embeddedTwoPunctureUpperParameter p q 1) := by
      change E1 ymid ∈ twoPuncturedDiskRelativeOverlap
        (embeddedTwoPunctureLowerParameter p q 1)
        (embeddedTwoPunctureUpperParameter p q 1) at hcoordmid
      exact hcoordmid.2
    refine ⟨?_, ?_⟩
    · change ((Er (embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) ymid) : ℂ) ∈
          twoPuncturedDiskLowerSide (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r))
      rw [hcoord, hparamsL, hparamsU]
      exact twoPuncturedDiskLowerSide_inv_smul (le_of_lt h1r) hcoordLower
    · change ((Er (embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) ymid) : ℂ) ∈
          twoPuncturedDiskUpperSide (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r))
      rw [hcoord, hparamsL, hparamsU]
      exact twoPuncturedDiskUpperSide_inv_smul (le_of_lt h1r) hcoordUpper
  refine ⟨ρ, hρ, hρr, hsmall, hcandidate, hcomparison, mid, hmidval,
    hcoordmidR, ?_⟩
  rcases horder with horder | horder
  · rcases horder with ⟨hpqOrder, hleftWitness, hrightWitness⟩
    let ηL := P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr
    let ηR := P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr
    let H := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hpMap hqMap
    let J := P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap
      ∘ twoOpenCoverAmalgamInclusion
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
    let coord := fun y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} =>
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre y : ℂ)
    let SL := twoPuncturedDiskLowerSide
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r)
    let SU := twoPuncturedDiskUpperSide
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r)
    have hmemL : ∀ t : I, H (ηL t) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      intro t
      obtain ⟨y, hy, _⟩ := hleftWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hval : yR.1 = H (ηL t) := by
        change y.1 = H (ηL t)
        exact hy
      rw [← hval]
      exact yR.2
    have hmemR : ∀ t : I, H (ηR t) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      intro t
      obtain ⟨y, hy, _⟩ := hrightWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hval : yR.1 = H (ηR t) := by
        change y.1 = H (ηR t)
        exact hy
      rw [← hval]
      exact yR.2
    have hmemL0 : H (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.source ηL]
      exact hmemL 0
    have hmemL1 : H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.target ηL]
      exact hmemL 1
    have hmemR0 : H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.source ηR]
      exact hmemR 0
    have hmemR1 : H (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.target ηR]
      exact hmemR 1
    let lSource : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1), hmemL0⟩
    let lTarget : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime), hmemL1⟩
    let rSource : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime), hmemR0⟩
    let rTarget : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1), hmemR1⟩
    let rawL : Path lSource lTarget := P.componentTwoCenterRelativeLocalDiskPath i f p q r
      hi hnext hpMap hqMap ηL hmemL
    let rawR : Path rSource rTarget := P.componentTwoCenterRelativeLocalDiskPath i f p q r
      hi hnext hpMap hqMap ηR hmemR
    have hstartL :
        P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap true ρ hρ hρr hsmall 1 = lSource := by
      apply Subtype.ext
      apply Subtype.ext
      change (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1).1 =
        (H (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)).1
      exact (P.internalCenterPuncturedAmbientHomeomorph_apply_val i f p q
        hi hnext hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)).symm
    have hstartR :
        P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap false ρ hρ hρr hsmall 1 = rTarget := by
      apply Subtype.ext
      apply Subtype.ext
      change (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1).1 =
        (H (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1)).1
      exact (P.internalCenterPuncturedAmbientHomeomorph_apply_val i f p q
        hi hnext hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1)).symm
    have hmidL : mid = lTarget := by
      apply Subtype.ext
      simpa [mid, lTarget, embeddedTwoPunctureRelativeLocalDiskInclusion] using hymid
    have hmidR : mid = rSource := by
      apply Subtype.ext
      simpa [mid, rSource, embeddedTwoPunctureRelativeLocalDiskInclusion] using hymid
    let leftPath := rawL.cast hstartL hmidL
    let rightPath := rawR.cast hmidR hstartR
    have hcoordL : ∀ t : I, coord (leftPath t) ∈ SL := by
      intro t
      obtain ⟨y, hy, hside⟩ := hleftWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hside' : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball1 hpre hqre y : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q 1)
            (embeddedTwoPunctureUpperParameter p q 1) := by
        simpa [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
          min_eq_left hpqOrder.le, max_eq_right hpqOrder.le] using hside
      have hsc := embeddedTwoPunctureRelativeLocalDiskInclusion_mem_lowerSide
        f hf p q r (lt_trans zero_lt_one h1r) (le_of_lt h1r)
        hball1 hballr hpre hqre y hside'
      have hval : leftPath t = yR := by
        apply Subtype.ext
        change H (ηL t) = y.1
        exact hy.symm
      rw [hval]
      exact hsc
    have hcoordR : ∀ t : I, coord (rightPath t) ∈ SU := by
      intro t
      obtain ⟨y, hy, hside⟩ := hrightWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hside' : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball1 hpre hqre y : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q 1)
            (embeddedTwoPunctureUpperParameter p q 1) := by
        simpa [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
          min_eq_left hpqOrder.le, max_eq_right hpqOrder.le] using hside
      have hsc := embeddedTwoPunctureRelativeLocalDiskInclusion_mem_upperSide
        f hf p q r (lt_trans zero_lt_one h1r) (le_of_lt h1r)
        hball1 hballr hpre hqre y hside'
      have hval : rightPath t = yR := by
        apply Subtype.ext
        change H (ηR t) = y.1
        exact hy.symm
      rw [hval]
      exact hsc
    refine Or.inl ⟨hpqOrder, leftPath, rightPath, ?_, ?_, hcoordL, hcoordR⟩
    · intro t
      have hpath := congrArg (fun η : Path _ _ => η t)
        (P.componentTwoCenterRelativeLocalDiskPath_native i f p q r hi hnext
          hpMap hqMap ηL hmemL)
      exact hpath
    · intro t
      have hpath := congrArg (fun η : Path _ _ => η t)
        (P.componentTwoCenterRelativeLocalDiskPath_native i f p q r hi hnext
          hpMap hqMap ηR hmemR)
      exact hpath
  · rcases horder with ⟨hqpOrder, hleftWitness, hrightWitness⟩
    let ηL := P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr
    let ηR := P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr
    let H := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hpMap hqMap
    let coord := fun y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} =>
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r (lt_trans zero_lt_one h1r) hballr hpre hqre y : ℂ)
    let SL := twoPuncturedDiskUpperSide
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r)
    let SU := twoPuncturedDiskLowerSide
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r)
    have hmemL : ∀ t : I, H (ηL t) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      intro t
      obtain ⟨y, hy, _⟩ := hleftWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hval : yR.1 = H (ηL t) := by
        change y.1 = H (ηL t)
        exact hy
      rw [← hval]
      exact yR.2
    have hmemR : ∀ t : I, H (ηR t) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      intro t
      obtain ⟨y, hy, _⟩ := hrightWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hval : yR.1 = H (ηR t) := by
        change y.1 = H (ηR t)
        exact hy
      rw [← hval]
      exact yR.2
    have hmemL0 : H (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.source ηL]
      exact hmemL 0
    have hmemL1 : H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.target ηL]
      exact hmemL 1
    have hmemR0 : H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.source ηR]
      exact hmemR 0
    have hmemR1 : H (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
      rw [← Path.target ηR]
      exact hmemR 1
    let lSource : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1), hmemL0⟩
    let lTarget : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime), hmemL1⟩
    let rSource : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime), hmemR0⟩
    let rTarget : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} :=
      ⟨H (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1), hmemR1⟩
    let rawL : Path lSource lTarget := P.componentTwoCenterRelativeLocalDiskPath i f p q r
      hi hnext hpMap hqMap ηL hmemL
    let rawR : Path rSource rTarget := P.componentTwoCenterRelativeLocalDiskPath i f p q r
      hi hnext hpMap hqMap ηR hmemR
    have hstartL :
        P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap true ρ hρ hρr hsmall 1 = lSource := by
      apply Subtype.ext
      apply Subtype.ext
      change (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1).1 =
        (H (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)).1
      exact (P.internalCenterPuncturedAmbientHomeomorph_apply_val i f p q
        hi hnext hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)).symm
    have hstartR :
        P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap false ρ hρ hρr hsmall 1 = rTarget := by
      apply Subtype.ext
      apply Subtype.ext
      change (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1).1 =
        (H (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1)).1
      exact (P.internalCenterPuncturedAmbientHomeomorph_apply_val i f p q
        hi hnext hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1)).symm
    have hmidL : mid = lTarget := by
      apply Subtype.ext
      simpa [mid, lTarget, embeddedTwoPunctureRelativeLocalDiskInclusion] using hymid
    have hmidR : mid = rSource := by
      apply Subtype.ext
      simpa [mid, rSource, embeddedTwoPunctureRelativeLocalDiskInclusion] using hymid
    let leftPath := rawL.cast hstartL hmidL
    let rightPath := rawR.cast hmidR hstartR
    have hcoordL : ∀ t : I, coord (leftPath t) ∈ SL := by
      intro t
      obtain ⟨y, hy, hside⟩ := hleftWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hside' : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball1 hpre hqre y : ℂ) ∈
          twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q 1)
            (embeddedTwoPunctureUpperParameter p q 1) := by
        simpa [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
          min_eq_right hqpOrder.le, max_eq_left hqpOrder.le] using hside
      have hsc := embeddedTwoPunctureRelativeLocalDiskInclusion_mem_upperSide
        f hf p q r (lt_trans zero_lt_one h1r) (le_of_lt h1r)
        hball1 hballr hpre hqre y hside'
      have hval : leftPath t = yR := by
        apply Subtype.ext
        change H (ηL t) = y.1
        exact hy.symm
      rw [hval]
      exact hsc
    have hcoordR : ∀ t : I, coord (rightPath t) ∈ SU := by
      intro t
      obtain ⟨y, hy, hside⟩ := hrightWitness t
      let yR := embeddedTwoPunctureRelativeLocalDiskInclusion
        f p q 1 r (le_of_lt h1r) y
      have hside' : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball1 hpre hqre y : ℂ) ∈
          twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q 1)
            (embeddedTwoPunctureUpperParameter p q 1) := by
        simpa [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
          min_eq_right hqpOrder.le, max_eq_left hqpOrder.le] using hside
      have hsc := embeddedTwoPunctureRelativeLocalDiskInclusion_mem_lowerSide
        f hf p q r (lt_trans zero_lt_one h1r) (le_of_lt h1r)
        hball1 hballr hpre hqre y hside'
      have hval : rightPath t = yR := by
        apply Subtype.ext
        change H (ηR t) = y.1
        exact hy.symm
      rw [hval]
      exact hsc
    refine Or.inr ⟨hqpOrder, leftPath, rightPath, ?_, ?_, hcoordL, hcoordR⟩
    · intro t
      have hpath := congrArg (fun η : Path _ _ => η t)
        (P.componentTwoCenterRelativeLocalDiskPath_native i f p q r hi hnext
          hpMap hqMap ηL hmemL)
      exact hpath
    · intro t
      have hpath := congrArg (fun η : Path _ _ => η t)
        (P.componentTwoCenterRelativeLocalDiskPath_native i f p q r hi hnext
          hpMap hqMap ηR hmemR)
      exact hpath

private theorem nativeSidePath_mem_trans {Y : Type*} [TopologicalSpace Y]
    {x y z : Y} (p : Path x y) (q : Path y z) {Z : Type*}
    (F : Y → Z) (S : Set Z)
    (hp : ∀ t : I, F (p t) ∈ S) (hq : ∀ t : I, F (q t) ∈ S) :
    ∀ t : I, F ((p.trans q) t) ∈ S := by
  intro t
  have ht : (p.trans q) t ∈ Set.range (p.trans q) := ⟨t, rfl⟩
  rw [Path.trans_range] at ht
  rcases ht with ht | ht
  · obtain ⟨s, hs⟩ := ht
    rw [← hs]
    exact hp s
  · obtain ⟨s, hs⟩ := ht
    rw [← hs]
    exact hq s

private theorem nativeSidePath_mem_symm {Y : Type*} [TopologicalSpace Y]
    {x y : Y} (p : Path x y) {Z : Type*} (F : Y → Z) (S : Set Z)
    (hp : ∀ t : I, F (p t) ∈ S) : ∀ t : I, F (p.symm t) ∈ S := by
  intro t
  have ht : p.symm t ∈ Set.range p := by
    rw [← Path.symm_range p]
    exact ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := ht
  rw [← hs]
  exact hp s

/-- Rebase the actual native small-polar half paths at the right crossing of
the actual exterior/local annulus.  The selected radius, Fermi comparison data,
and chart are shared with the half-path constructor.  The two based paths keep
their physical lower/upper assignment in both chart orderings, and after
literal inclusion into the original punctured component their joined path is
homotopic to the original small cut connector. -/
theorem exists_componentTwoCenterAnnulusBasedNativeSidePaths
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (f : C(U, (X i).Carrier))
    (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m fermiA fermiB : ℝ)
    (hfermiA : 0 < fermiA) (hfermiB : 0 < fermiB)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m fermiA fermiB z.1))
    (hleft : γ • orientedFermiDiskPoint m fermiA fermiB p.1 = (P.centers i).1)
    (hright : γ • orientedFermiDiskPoint m fermiA fermiB q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (hsegment : ∀ t : I,
      P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f)
    (a : ℝ) (ha : max ‖p.1‖ ‖q.1‖ < a) (ha1 : a < 1)
    (haU : Metric.closedBall (0 : ℂ) a ⊆ U)
    (r : ℝ) (h1r : 1 < r) (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s) :
    let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
      (zero_lt_one.trans h1r) hpq hpre hqre
    let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
      (zero_lt_one.trans h1r)
      (((le_max_left _ _).trans_lt ha).trans ha1)
      (((le_max_right _ _).trans_lt ha).trans ha1)
    let hR := (inv_lt_one₀ (zero_lt_one.trans h1r)).mpr h1r
    let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
    let qR := twoOpenCoverAmalgamOverlapRight
      (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
      (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
      (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 h1r haU hrU θ)
    let LocalPoint := {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}
    let coord := fun y : LocalPoint =>
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r (zero_lt_one.trans h1r) hrU hpre hqre y : ℂ)
    let F : C(LocalPoint, P.CenterPuncturedChainComponent i) :=
      (P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap).comp
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r))
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g),
      ∃ hsmall : ∀ (b : Bool) (φ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr φ).val ∈
          embeddedCoordinatePunctureDisk f,
      (∀ t : I,
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      Nonempty (TwoCenterPolarSideComparisonData p q m fermiA fermiB ρ hfermiA hfermiB) ∧
      ∃ mid : LocalPoint,
        mid.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
          hpMap hqMap
          (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
            componentTwoCenterSmallConnectorMidpointTime) ∧
        embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q r (zero_lt_one.trans h1r) hrU hpre hqre mid ∈
          twoPuncturedDiskRelativeOverlap
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) ∧
        ∃ leftHalf : Path
            (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
              hpMap hqMap true ρ hρ hρr
              hsmall 1) mid,
        ∃ rightHalf : Path mid
            (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
              hpMap hqMap false ρ hρ hρr
              hsmall 1),
          (∀ t : I, F (leftHalf t) =
            P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
          (∀ t : I, F (rightHalf t) =
            P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
          ((p.1.im < q.1.im ∧
            (∀ t : I, coord (leftHalf t) ∈ twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) ∧
            (∀ t : I, coord (rightHalf t) ∈ twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) ∧
            ∃ η : Path mid qR,
              (∀ t : I, coord (η t) ∈ twoPuncturedDiskLowerSide
                (embeddedTwoPunctureLowerParameter p q r)
                (embeddedTwoPunctureUpperParameter p q r)) ∧
              (∀ t : I, coord (η t) ∈ twoPuncturedDiskUpperSide
                (embeddedTwoPunctureLowerParameter p q r)
                (embeddedTwoPunctureUpperParameter p q r)) ∧
              (∀ t : I, coord ((leftHalf.trans η) t) ∈
                twoPuncturedDiskLowerSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)) ∧
              (∀ t : I, coord ((rightHalf.symm.trans η) t) ∈
                twoPuncturedDiskUpperSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)) ∧
              ∃ hL : P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1 =
                F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                  hpMap hqMap true ρ hρ hρr hsmall 1),
              ∃ hR : P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1 =
                F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                  hpMap hqMap false ρ hρ hρr hsmall 1),
                ((((leftHalf.trans η).trans (rightHalf.symm.trans η).symm).map
                  F.continuous).cast hL hR).Homotopic
                  (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr)) ∨
           (q.1.im < p.1.im ∧
            (∀ t : I, coord (leftHalf t) ∈ twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) ∧
            (∀ t : I, coord (rightHalf t) ∈ twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q r)
              (embeddedTwoPunctureUpperParameter p q r)) ∧
            ∃ η : Path mid qR,
              (∀ t : I, coord (η t) ∈ twoPuncturedDiskLowerSide
                (embeddedTwoPunctureLowerParameter p q r)
                (embeddedTwoPunctureUpperParameter p q r)) ∧
              (∀ t : I, coord (η t) ∈ twoPuncturedDiskUpperSide
                (embeddedTwoPunctureLowerParameter p q r)
                (embeddedTwoPunctureUpperParameter p q r)) ∧
              (∀ t : I, coord ((leftHalf.trans η) t) ∈
                twoPuncturedDiskUpperSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)) ∧
              (∀ t : I, coord ((rightHalf.symm.trans η) t) ∈
                twoPuncturedDiskLowerSide
                  (embeddedTwoPunctureLowerParameter p q r)
                  (embeddedTwoPunctureUpperParameter p q r)) ∧
              ∃ hL : P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1 =
                F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                  hpMap hqMap true ρ hρ hρr hsmall 1),
      ∃ hR : P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1 =
                F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
                  hpMap hqMap false ρ hρ hρr hsmall 1),
                ((((leftHalf.trans η).trans (rightHalf.symm.trans η).symm).map
                  F.continuous).cast hL hR).Homotopic
                  (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr))) := by
  dsimp only
  let hαβ := embeddedTwoPunctureLowerParameter_lt_upper p q r
    (zero_lt_one.trans h1r) hpq hpre hqre
  let hnorms := embeddedTwoPunctureParameters_abs_lt_inv p q
    (zero_lt_one.trans h1r)
    (((le_max_left _ _).trans_lt ha).trans ha1)
    (((le_max_right _ _).trans_lt ha).trans ha1)
  let hR := (inv_lt_one₀ (zero_lt_one.trans h1r)).mpr h1r
  let θ := twoPuncturedDiskOuterRightDirection hαβ hnorms.1 hnorms.2 hR
  let qR := twoOpenCoverAmalgamOverlapRight
    (embeddedTwoPunctureExteriorRelativeSide f p q a haU)
    (embeddedTwoPunctureLocalDiskRelativeSide f p q r)
    (embeddedTwoPunctureRelativeBoundaryCircle f hf p q a r ha ha1 h1r haU hrU θ)
  let LocalPoint := {w : embeddedTwoPunctureAmbientPoint f p q //
    w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}
  let coord := fun y : LocalPoint =>
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (zero_lt_one.trans h1r) hrU hpre hqre y : ℂ)
  let F : C(LocalPoint, P.CenterPuncturedChainComponent i) :=
    (P.twoCenterAmbientToNativeComponent i f p q hpMap hqMap).comp
      (twoOpenCoverAmalgamInclusion
        (embeddedTwoPunctureLocalDiskRelativeSide f p q r))
  obtain ⟨ρ, hρ, hρr, hsmall, hcandidate, hcomparison, mid,
    hmidval, hmidcoord, horder⟩ :=
    P.exists_componentTwoCenterNativeSidePaths i hU f hf p q hpMap hqMap
      hpre hqre hp hq hpq hi hnext γ m fermiA fermiB hfermiA hfermiB
      hformula hleft hright hsegment r h1r hrU hchartSegment
  have hmidcoord' : embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r (zero_lt_one.trans h1r) hrU hpre hqre mid ∈
      twoPuncturedDiskRelativeOverlap
      (embeddedTwoPunctureLowerParameter p q r)
      (embeddedTwoPunctureUpperParameter p q r) := by
    simpa [coord] using hmidcoord
  obtain ⟨η, hηLower, hηUpper⟩ :=
    exists_embeddedTwoPunctureAnnulusLocalConnector f hf p q a r
      ha ha1 h1r haU hrU hpq hpre hqre mid hmidcoord'
  refine ⟨ρ, hρ, hρr, hsmall, hcandidate, hcomparison, mid,
    hmidval, hmidcoord', ?_⟩
  rcases horder with horder | horder
  · rcases horder with ⟨hvertical, leftHalf, rightHalf,
      hnativeLeft, hnativeRight, hleftSide, hrightSide⟩
    let leftBasePath := leftHalf.trans η
    let rightBasePath := rightHalf.symm.trans η
    have hleftBaseSide : ∀ t : I, coord (leftBasePath t) ∈
        twoPuncturedDiskLowerSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
      exact nativeSidePath_mem_trans leftHalf η coord
        (twoPuncturedDiskLowerSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) hleftSide hηLower
    have hrightBaseSide : ∀ t : I, coord (rightBasePath t) ∈
        twoPuncturedDiskUpperSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
      exact nativeSidePath_mem_trans rightHalf.symm η coord
        (twoPuncturedDiskUpperSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
        (nativeSidePath_mem_symm rightHalf coord
          (twoPuncturedDiskUpperSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) hrightSide)
        hηUpper
    have hpair := embeddedTwoPunctureAnnulusConnectorPair f hf p q r
      (zero_lt_one.trans h1r) hrU hpre hqre leftHalf rightHalf η
      (Or.inl ⟨hleftSide, hrightSide⟩) hηLower hηUpper
    have hlocalCut : (leftBasePath.trans rightBasePath.symm).Homotopic
        (leftHalf.trans rightHalf) := by
      simpa [leftBasePath, rightBasePath,
        embeddedTwoPunctureAnnulusLeftConnector,
        embeddedTwoPunctureAnnulusRightConnector, Path.trans_symm] using hpair.2
    have hleftEnd : P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1 =
        F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap true ρ hρ hρr hsmall 1) := by
      have h := hnativeLeft 0
      simpa [F, Path.source] using h.symm
    have hrightEnd : P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1 =
        F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap false ρ hρ hρr hsmall 1) := by
      have h := hnativeRight 1
      simpa [F, Path.target] using h.symm
    have hmapHalves :
        ((leftHalf.trans rightHalf).map F.continuous).cast hleftEnd hrightEnd =
          (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr).trans
            (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr) := by
      apply Path.ext
      funext t
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
        Path.trans_apply]
      split_ifs with ht
      · simpa [F] using hnativeLeft
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨t.2.1, ht⟩⟩
      · simpa [F] using hnativeRight
          ⟨2 * (t : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩
    have hnativeCut :
        (((leftBasePath.trans rightBasePath.symm).map F.continuous).cast
          hleftEnd hrightEnd).Homotopic
          (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
      have hmapCut := (hlocalCut.map F).pathCast hleftEnd hrightEnd
      rw [hmapHalves] at hmapCut
      exact hmapCut.trans
        (P.componentTwoCenterSmallConnector_halves_homotopic_candidate
          i ρ hρ hρr)
    refine ⟨leftHalf, rightHalf, hnativeLeft, hnativeRight,
      Or.inl ⟨hvertical, hleftSide, hrightSide, η, hηLower, hηUpper,
        ?_, ?_, hleftEnd, hrightEnd, ?_⟩⟩
    · simpa [leftBasePath] using hleftBaseSide
    · simpa [rightBasePath] using hrightBaseSide
    · simpa [leftBasePath, rightBasePath] using hnativeCut
  · rcases horder with ⟨hvertical, leftHalf, rightHalf,
      hnativeLeft, hnativeRight, hleftSide, hrightSide⟩
    let leftBasePath := leftHalf.trans η
    let rightBasePath := rightHalf.symm.trans η
    have hleftBaseSide : ∀ t : I, coord (leftBasePath t) ∈
        twoPuncturedDiskUpperSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
      exact nativeSidePath_mem_trans leftHalf η coord
        (twoPuncturedDiskUpperSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r)) hleftSide hηUpper
    have hrightBaseSide : ∀ t : I, coord (rightBasePath t) ∈
        twoPuncturedDiskLowerSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
      exact nativeSidePath_mem_trans rightHalf.symm η coord
        (twoPuncturedDiskLowerSide
          (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
        (nativeSidePath_mem_symm rightHalf coord
          (twoPuncturedDiskLowerSide
            (embeddedTwoPunctureLowerParameter p q r)
            (embeddedTwoPunctureUpperParameter p q r)) hrightSide)
        hηLower
    have hpair := embeddedTwoPunctureAnnulusConnectorPair f hf p q r
      (zero_lt_one.trans h1r) hrU hpre hqre leftHalf rightHalf η
      (Or.inr ⟨hleftSide, hrightSide⟩) hηLower hηUpper
    have hlocalCut : (leftBasePath.trans rightBasePath.symm).Homotopic
        (leftHalf.trans rightHalf) := by
      simpa [leftBasePath, rightBasePath,
        embeddedTwoPunctureAnnulusLeftConnector,
        embeddedTwoPunctureAnnulusRightConnector, Path.trans_symm] using hpair.2
    have hleftEnd : P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1 =
        F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap true ρ hρ hρr hsmall 1) := by
      have h := hnativeLeft 0
      simpa [F, Path.source] using h.symm
    have hrightEnd : P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1 =
        F (P.twoCenterSmallPolarRelativeLocalDiskMap i f p q r h1r
          hpMap hqMap false ρ hρ hρr hsmall 1) := by
      have h := hnativeRight 1
      simpa [F, Path.target] using h.symm
    have hmapHalves :
        ((leftHalf.trans rightHalf).map F.continuous).cast hleftEnd hrightEnd =
          (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr).trans
            (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr) := by
      apply Path.ext
      funext t
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
        Path.trans_apply]
      split_ifs with ht
      · simpa [F] using hnativeLeft
          ⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨t.2.1, ht⟩⟩
      · simpa [F] using hnativeRight
          ⟨2 * (t : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, t.2.2⟩⟩
    have hnativeCut :
        (((leftBasePath.trans rightBasePath.symm).map F.continuous).cast
          hleftEnd hrightEnd).Homotopic
          (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
      have hmapCut := (hlocalCut.map F).pathCast hleftEnd hrightEnd
      rw [hmapHalves] at hmapCut
      exact hmapCut.trans
        (P.componentTwoCenterSmallConnector_halves_homotopic_candidate
          i ρ hρ hρr)
    refine ⟨leftHalf, rightHalf, hnativeLeft, hnativeRight,
      Or.inr ⟨hvertical, hleftSide, hrightSide, η, hηLower, hηUpper,
        ?_, ?_, hleftEnd, hrightEnd, ?_⟩⟩
    · simpa [leftBasePath] using hleftBaseSide
    · simpa [rightBasePath] using hrightBaseSide
    · simpa [leftBasePath, rightBasePath] using hnativeCut

/-- Basepoint transport commutes with literal inclusion of a loop. The
right-hand side is the included loop conjugated by the original local path;
this is the exact path-class equation used for the small left polar turn. -/
theorem fundamentalGroupMulEquivOfPath_map_conjugate_loop
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (F : C(Y, Z)) {x z : Y} (p : Path x z) (γ : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map F.continuous)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.map F.continuous))) =
    FundamentalGroup.map F z
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p.symm.trans (γ.trans p)))) := by
  change FundamentalGroup.fundamentalGroupMulEquivOfPath
      (p.map F.continuous) ⟦γ.map F.continuous⟧ = _
  rw [fundamentalGroupMulEquivOfPath_apply_generic, FundamentalGroup.map_apply]
  apply congrArg FundamentalGroup.fromPath
  rw [← Path.Homotopic.Quotient.mk_map]
  simp only [Path.map_trans, Path.map_symm]
  rfl

/-- The same literal-inclusion transport identity when the mapped path's
initial point is identified with the chosen native basepoint by an explicit
endpoint equality. The cast is kept on the native loop, rather than silently
identifying distinct subtype carriers. -/
theorem fundamentalGroupMulEquivOfPath_map_conjugate_loop_cast
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (F : C(Y, Z)) {x z : Y} {a : Z} (hx : a = F x)
    (p : Path x z) (γ : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath
        ((p.map F.continuous).cast hx rfl)
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((γ.map F.continuous).cast hx hx))) =
    FundamentalGroup.map F z
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (p.symm.trans (γ.trans p)))) := by
  cases hx
  simpa using fundamentalGroupMulEquivOfPath_map_conjugate_loop F p γ

/-- If two paths from a common basepoint to the same endpoint determine the
same connector between their initial points, then the corresponding
conjugates of one literal right loop agree. This is the cut-cancellation
identity used after the annulus half-paths are joined through their overlap
connector. -/
theorem fundamentalGroup_conjugateCut_eq_of_homotopic
    {Y : Type*} [TopologicalSpace Y] {x y z : Y}
    (p : Path x z) (q : Path y z) (c : Path x y) (γ : Path y y)
    (hc : c.Homotopic (p.trans q.symm)) :
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk
        (p.symm.trans (c.trans ((γ.trans c.symm).trans p)))) =
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (q.symm.trans (γ.trans q))) := by
  apply congrArg FundamentalGroup.fromPath
  have hcq : Path.Homotopic.Quotient.mk c =
      (Path.Homotopic.Quotient.mk p).trans
        (Path.Homotopic.Quotient.mk q).symm := by
    simpa only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm] using
      Path.Homotopic.Quotient.eq.mpr hc
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm]
  have hreverse :
      ((Path.Homotopic.Quotient.mk p).trans
        (Path.Homotopic.Quotient.mk q).symm).symm =
      (Path.Homotopic.Quotient.mk q).trans
        (Path.Homotopic.Quotient.mk p).symm := by
    rw [← Path.Homotopic.Quotient.mk_symm,
      ← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_symm,
      Path.trans_symm, Path.symm_symm,
      Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
  rw [hcq]
  rw [hreverse]
  rw [Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk p)
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk q))]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk p))
    (Path.Homotopic.Quotient.mk p)]
  simp only [Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]
  rw [Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk γ)
    (Path.Homotopic.Quotient.trans
      (Path.Homotopic.Quotient.mk q)
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk p)))
    (Path.Homotopic.Quotient.mk p)]
  rw [Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk q)
    (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk p))
    (Path.Homotopic.Quotient.mk p)]
  simp only [Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

#print axioms fundamentalGroupMulEquivOfPath_map_conjugate_loop
#print axioms fundamentalGroupMulEquivOfPath_map_conjugate_loop_cast
#print axioms fundamentalGroup_conjugateCut_eq_of_homotopic

end

end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterNativeSidePaths
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterAnnulusBasedNativeSidePaths
