module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterCutSidePaths
public import Geometry.TwoPuncturedDiskSideScaling

@[expose] public section

/-!
# Actual connector paths in local disk coordinates

Restrict native paths to the actual relative local disk, without replacing
their parametrization. The common split point of the small connector lies
in the genuine overlap of the lower and upper coordinate sides.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups Topology unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)} {U : Set ℂ}

/-- Positive chart normalization preserves the actual sorted lower height. -/
theorem embeddedTwoPunctureLowerParameter_scaled (p q : U) (r : ℝ) (hr : 0 < r) :
    embeddedTwoPunctureLowerParameter p q r =
      r⁻¹ * embeddedTwoPunctureLowerParameter p q 1 := by
  simp only [embeddedTwoPunctureLowerParameter, div_eq_mul_inv, inv_one, mul_one]
  rw [← min_mul_of_nonneg _ _ (inv_nonneg.mpr hr.le), mul_comm]

/-- Positive chart normalization preserves the actual sorted upper height. -/
theorem embeddedTwoPunctureUpperParameter_scaled (p q : U) (r : ℝ) (hr : 0 < r) :
    embeddedTwoPunctureUpperParameter p q r =
      r⁻¹ * embeddedTwoPunctureUpperParameter p q 1 := by
  simp only [embeddedTwoPunctureUpperParameter, div_eq_mul_inv, inv_one, mul_one]
  rw [← max_mul_of_nonneg _ _ (inv_nonneg.mpr hr.le), mul_comm]

/-- The literal inclusion between two nested relative chart disks. -/
def embeddedTwoPunctureRelativeLocalDiskInclusion
    {k : ℕ} {Y : ClosedHyperbolicSurface k}
    (f : C(U, Y.Carrier)) (p q : U) (a r : ℝ) (har : a ≤ r) :
    C({w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q a},
      {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}) := by
  have hmem : ∀ y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q a},
      y.1 ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r := by
    intro y
    obtain ⟨⟨z, hz, hzy⟩, hambient⟩ := y.2
    exact ⟨⟨z, lt_of_lt_of_le hz har, hzy⟩, hambient⟩
  exact ⟨fun y => ⟨y.1, hmem y⟩, continuous_subtype_val.subtype_mk hmem⟩

/-- Normalizing the actual larger local disk scales the original unit-disk
coordinate by precisely `1/r`. The underlying surface point is unchanged. -/
theorem embeddedTwoPunctureRelativeLocalDiskInclusion_unitCoordinate
    {k : ℕ} {Y : ClosedHyperbolicSurface k}
    (f : C(U, Y.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → Y.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r) (h1r : 1 ≤ r)
    (hball1 : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hballr : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1}) :
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r hr hballr hpre hqre
      (embeddedTwoPunctureRelativeLocalDiskInclusion f p q 1 r h1r y) : ℂ) =
      (r⁻¹ : ℝ) • (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hball1 hpre hqre y : ℂ) := by
  obtain ⟨z, hz, hzy⟩ := y.2.1
  have hcoord1 := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q 1 one_pos hball1 hpre hqre y.1 y.2 z hz hzy
  let yr := embeddedTwoPunctureRelativeLocalDiskInclusion f p q 1 r h1r y
  have hcoordr := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q r hr hballr hpre hqre yr.1 yr.2 z (lt_of_lt_of_le hz h1r) hzy
  simp only [inv_one, one_smul] at hcoord1
  rw [hcoord1]
  exact hcoordr

/-- A proved lower-side point in the actual unit chart remains on the lower
side under the literal inclusion into the larger local cover member. -/
theorem embeddedTwoPunctureRelativeLocalDiskInclusion_mem_lowerSide
    {k : ℕ} {Y : ClosedHyperbolicSurface k}
    (f : C(U, Y.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → Y.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r) (h1r : 1 ≤ r)
    (hball1 : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hballr : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1})
    (hy : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q 1 one_pos hball1 hpre hqre y : ℂ) ∈
        twoPuncturedDiskLowerSide (embeddedTwoPunctureLowerParameter p q 1)
          (embeddedTwoPunctureUpperParameter p q 1)) :
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r hr hballr hpre hqre
      (embeddedTwoPunctureRelativeLocalDiskInclusion f p q 1 r h1r y) : ℂ) ∈
        twoPuncturedDiskLowerSide (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
  rw [embeddedTwoPunctureRelativeLocalDiskInclusion_unitCoordinate f hf p q r hr h1r
    hball1 hballr hpre hqre y, embeddedTwoPunctureLowerParameter_scaled p q r hr,
    embeddedTwoPunctureUpperParameter_scaled p q r hr]
  exact twoPuncturedDiskLowerSide_inv_smul h1r hy

/-- The corresponding literal larger-disk inclusion preserves upper-side
membership as well; it does not reverse the two punctures. -/
theorem embeddedTwoPunctureRelativeLocalDiskInclusion_mem_upperSide
    {k : ℕ} {Y : ClosedHyperbolicSurface k}
    (f : C(U, Y.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → Y.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r) (h1r : 1 ≤ r)
    (hball1 : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (hballr : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1})
    (hy : (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q 1 one_pos hball1 hpre hqre y : ℂ) ∈
        twoPuncturedDiskUpperSide (embeddedTwoPunctureLowerParameter p q 1)
          (embeddedTwoPunctureUpperParameter p q 1)) :
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph f hf p q r hr hballr hpre hqre
      (embeddedTwoPunctureRelativeLocalDiskInclusion f p q 1 r h1r y) : ℂ) ∈
        twoPuncturedDiskUpperSide (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r) := by
  rw [embeddedTwoPunctureRelativeLocalDiskInclusion_unitCoordinate f hf p q r hr h1r
    hball1 hballr hpre hqre y, embeddedTwoPunctureLowerParameter_scaled p q r hr,
    embeddedTwoPunctureUpperParameter_scaled p q r hr]
  exact twoPuncturedDiskUpperSide_inv_smul h1r hy

/-- Restrict the literal coordinate path to a proved side. In particular,
the lower and upper specializations have the `puncturedBaseAt` types used
by the connector-independent positive-generator theorem. -/
def embeddedTwoPunctureCoordinateSidePath
    {k : ℕ} {Y : ClosedHyperbolicSurface k}
    (r : ℝ) (hr : 0 < r) (hballU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (f : C(U, Y.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → Y.Carrier))
    (p q : U) (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    {x y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (η : Path x y) (S : Set ℂ)
    (hη : ∀ t : I,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hballU hpre hqre (η t) : ℂ) ∈ S) :
    Path
      (⟨(embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hballU hpre hqre x : ℂ),
        by simpa only [η.source] using hη 0⟩ : ↥S)
      ⟨(embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hballU hpre hqre y : ℂ),
        by simpa only [η.target] using hη 1⟩ where
  toFun t := ⟨(embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    f hf p q r hr hballU hpre hqre (η t) : ℂ), hη t⟩
  continuous_toFun := (continuous_subtype_val.comp
    ((embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hballU hpre hqre).continuous.comp η.continuous)).subtype_mk hη
  source' := Subtype.ext (congrArg
    (fun z => (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hballU hpre hqre z : ℂ)) η.source)
  target' := Subtype.ext (congrArg
    (fun z => (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hballU hpre hqre z : ℂ)) η.target)

@[simp]
theorem embeddedTwoPunctureCoordinateSidePath_apply_val
    {k : ℕ} {Y : ClosedHyperbolicSurface k}
    (r : ℝ) (hr : 0 < r) (hballU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (f : C(U, Y.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → Y.Carrier))
    (p q : U) (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    {x y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r}}
    (η : Path x y) (S : Set ℂ)
    (hη : ∀ t : I,
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hballU hpre hqre (η t) : ℂ) ∈ S) (t : I) :
    (embeddedTwoPunctureCoordinateSidePath r hr hballU f hf p q hpre hqre η S hη t : ℂ) =
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q r hr hballU hpre hqre (η t) : ℂ) := rfl

/-- A contained native path, in the literal relative local-disk carrier.
The endpoints and every intermediate point retain their original values. -/
def componentTwoCenterRelativeLocalDiskPath
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    {x y : P.CenterPuncturedChainComponent i} (η : Path x y)
    (hη : ∀ t : I,
      P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq (η t) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r) :
    Path
      (⟨P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq x,
        by simpa only [η.source] using hη 0⟩ :
        {z : embeddedTwoPunctureAmbientPoint f p q //
          z ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
      ⟨P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq y,
        by simpa only [η.target] using hη 1⟩ where
  toFun t := ⟨P.internalCenterPuncturedAmbientHomeomorph
    i f p q hi hnext hp hq (η t), hη t⟩
  continuous_toFun :=
    ((P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq).continuous.comp
      η.continuous).subtype_mk hη
  source' := Subtype.ext (congrArg
    (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq) η.source)
  target' := Subtype.ext (congrArg
    (P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq) η.target)

/-- Inclusion recovers the exact native path, not only its homotopy class. -/
theorem componentTwoCenterRelativeLocalDiskPath_native
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (f : C(U, (X i).Carrier)) (p q : U) (r : ℝ)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    {x y : P.CenterPuncturedChainComponent i} (η : Path x y)
    (hη : ∀ t : I,
      P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq (η t) ∈
        embeddedTwoPunctureLocalDiskRelativeSide f p q r) :
    ((P.componentTwoCenterRelativeLocalDiskPath i f p q r hi hnext hp hq η hη).map
      (((P.twoCenterAmbientToNativeComponent i f p q hp hq).comp
        (twoOpenCoverAmalgamInclusion
          (embeddedTwoPunctureLocalDiskRelativeSide f p q r))).continuous)) = η := by
  apply Path.ext
  funext t
  apply Subtype.ext
  rfl

/-- The coordinate of an actual left polar point is its explicit translated
Fermi coordinate at the original SL polar phase. This applies to either side
ordering; the side is supplied by its actual chart domain. -/
theorem componentTwoCenterLeftPolar_relativeLocalDisk_coordinate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (r : ℝ) (hr : 0 < r) (hballU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (B : Set ℂ) (hBr : B ⊆ Metric.ball (0 : ℂ) r)
    (hBU : B ⊆ U) (hpB : p.1 ∈ B)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ q.1)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball p.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle)
    (y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hy : y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
      hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ)) :
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hballU hpre hqre y : ℂ) =
      (r⁻¹ : ℝ) • (p.1 + fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ
        (fermiSLPolarAnglePreimageMap γ
          (orientedFermiDiskPoint (m + a * p.1.im) a b 0) θ)) := by
  let φ := fermiSLPolarAnglePreimageMap γ
    (orientedFermiDiskPoint (m + a * p.1.im) a b 0) θ
  let F := translatedFermiPositivePolarCoordinateMap B p.1 m a b ha hb ρ δ
    hρ hball hqball
  let z : U := ⟨(F φ).1, hBU (F φ).2.1⟩
  have hznorm : ‖z.1‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hBr (F φ).2.1
  have hsys : 2 * ρ < (X i).systole := by
    nlinarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  have himage : f z = y.1.1 := by
    have hchart : f z =
        ((translatedFermiSideOriginalPolarMap B p.1 q.1 hBU hpB q.2 hBother
          f hf γ m a b ha hb hformula hpre ρ δ hρ hsys hball hqball θ).1 :
            (X i).Carrier) := rfl
    calc
      f z = (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ).1 :=
        hchart.trans (P.translatedFermiSideOriginalPolarMap_left_twoCenterPolarBoundaryMap
          i f B p q hBU hpB q.2 hBother hf γ m a b ha hb hformula hpre
          ρ δ hρ hρr hball hqball hleft θ)
      _ = y.1.1 := by simp only [hy,
        P.internalCenterPuncturedAmbientHomeomorph_apply_val]
  have hcoord := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q r hr hballU hpre hqre y.1 y.2 z hznorm himage
  exact hcoord

/-- The right polar coordinate retains the exact closest-deck phase as well
as the SL phase of the actual Fermi chart. No sign choice is introduced. -/
theorem componentTwoCenterRightPolar_relativeLocalDisk_coordinate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (r : ℝ) (hr : 0 < r) (hballU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (B : Set ℂ) (hBr : B ⊆ Metric.ball (0 : ℂ) r)
    (hBU : B ⊆ U) (hqB : q.1 ∈ B)
    (hBother : ∀ z : ℂ, z ∈ B → z ≠ p.1)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball q.1 δ ⊆ B)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle)
    (y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hy : y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
      hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ)) :
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hballU hpre hqre y : ℂ) =
      (r⁻¹ : ℝ) • (q.1 + fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ
        (fermiSLPolarAnglePreimageMap γ
          (orientedFermiDiskPoint (m + a * q.1.im) a b 0)
          (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * θ))) := by
  let φ := fermiSLPolarAnglePreimageMap γ
    (orientedFermiDiskPoint (m + a * q.1.im) a b 0)
    (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * θ)
  let F := translatedFermiPositivePolarCoordinateMap B q.1 m a b ha hb ρ δ
    hρ hball hqball
  let z : U := ⟨(F φ).1, hBU (F φ).2.1⟩
  have hznorm : ‖z.1‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hBr (F φ).2.1
  have hsys : 2 * ρ < (X i).systole := by
    nlinarith [P.twice_outer_lt_systole i, P.radius_lt_embeddedRadius]
  have himage : f z = y.1.1 := by
    have hchart : f z =
        ((translatedFermiSideOriginalPolarMap B q.1 p.1 hBU hqB p.2 hBother
          f hf γ m a b ha hb hformula hqre ρ δ hρ hsys hball hqball
          (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * θ)).1 :
            (X i).Carrier) := rfl
    calc
      f z = (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ).1 :=
        hchart.trans (P.translatedFermiSideOriginalPolarMap_right_twoCenterPolarBoundaryMap
          i f B p q hBU hqB p.2 hBother hf γ m a b ha hb hformula hqre
          ρ δ hρ hρr hball hqball hright θ)
      _ = y.1.1 := by simp only [hy,
        P.internalCenterPuncturedAmbientHomeomorph_apply_val]
  have hcoord := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q r hr hballU hpre hqre y.1 y.2 z hznorm himage
  exact hcoord

/-- The actual center-segment midpoint is an overlap basepoint of the two
coordinate sides, in either ordering of the original chart centers. -/
theorem exists_componentTwoCenterConnectorMidpoint_mem_relativeOverlap
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U)
    (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hpMap hqMap
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
          componentTwoCenterSmallConnectorMidpointTime) ∧
      embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hball hpre hqre y ∈
          twoPuncturedDiskRelativeOverlap (embeddedTwoPunctureLowerParameter p q 1)
            (embeddedTwoPunctureUpperParameter p q 1) := by
  let s : I := ⟨1 / 2, by constructor <;> norm_num⟩
  obtain ⟨y, hy, hcoord⟩ := P.componentTwoCenterGeodPoint_relativeLocalDiskUnit_coordinate
    i hball f hf p q hpMap hqMap hpre hqre hi hnext hchartSegment s
    (by norm_num [s]) (by norm_num [s])
  have himne : p.1.im ≠ q.1.im := by
    intro h
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact h
  have hyval : y.1.1 = P.componentCenterGeodPoint i s := congrArg Subtype.val hy
  have hnative : y.1 = P.internalCenterPuncturedAmbientHomeomorph
      i f p q hi hnext hpMap hqMap
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
          componentTwoCenterSmallConnectorMidpointTime) := by
    apply Subtype.ext
    simpa only [P.internalCenterPuncturedAmbientHomeomorph_apply_val,
      P.componentTwoCenterSmallConnector_midpoint_value] using hyval
  let E := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
    f hf p q 1 one_pos hball hpre hqre
  have him : (E y).1.im = (p.1.im + q.1.im) / 2 := by
    rw [hcoord]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    dsimp [s]
    ring
  have hballcoord : (E y).1 ∈ Metric.ball (0 : ℂ) 1 := (E y).2.1
  have hlowne : (E y).1 ≠ twoPuncturedDiskLeftCenter
      (embeddedTwoPunctureLowerParameter p q 1) := (E y).2.2.1
  have huppne : (E y).1 ≠ twoPuncturedDiskRightCenter
      (embeddedTwoPunctureUpperParameter p q 1) := (E y).2.2.2
  refine ⟨y, hnative, ⟨⟨⟨hballcoord, ?_⟩, hlowne⟩, ⟨⟨hballcoord, ?_⟩, huppne⟩⟩⟩
  · change (E y).1.im < twoPuncturedDiskOverlapUpper
      (embeddedTwoPunctureLowerParameter p q 1) (embeddedTwoPunctureUpperParameter p q 1)
    rw [him]
    rcases lt_or_gt_of_ne himne with horder | horder <;>
      simp only [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
        div_one, min_eq_left horder.le, max_eq_right horder.le,
        min_eq_right horder.le, max_eq_left horder.le, twoPuncturedDiskOverlapUpper] <;>
      linarith
  · change twoPuncturedDiskOverlapLower
      (embeddedTwoPunctureLowerParameter p q 1) (embeddedTwoPunctureUpperParameter p q 1) <
        (E y).1.im
    rw [him]
    rcases lt_or_gt_of_ne himne with horder | horder <;>
      simp only [embeddedTwoPunctureLowerParameter, embeddedTwoPunctureUpperParameter,
        div_one, min_eq_left horder.le, max_eq_right horder.le,
        min_eq_right horder.le, max_eq_left horder.le, twoPuncturedDiskOverlapLower] <;>
      linarith

end
end ExerciseGluingPreparation
end SystolicGrowth

namespace SystolicGrowth

/-- The translated Fermi coordinate at the positively scaled center is the
literal normalization of the original translated coordinate. -/
theorem fermiPositivePolarCoordinate_normalized_center
    (c : ℂ) (m a b r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (ρ : ℝ) (θ : Circle) :
    (r⁻¹ : ℝ) • c + fermiPositivePolarCoordinate
      (m + (a * r) * ((r⁻¹ : ℝ) • c).im) (a * r) (b * r)
      (mul_pos ha hr) (mul_pos hb hr) ρ θ =
      (r⁻¹ : ℝ) • (c + fermiPositivePolarCoordinate
        (m + a * c.im) a b ha hb ρ θ) := by
  have hshift : m + (a * r) * ((r⁻¹ : ℝ) • c).im = m + a * c.im := by
    rw [Complex.smul_im]
    simp only [smul_eq_mul]
    field_simp
  rw [hshift, fermiPositivePolarCoordinate_scaled (m + a * c.im) a b r ha hb hr,
    smul_add]

/-- Evaluate the actual local free marking through its literal coordinate
homeomorphism. This exposes the map without eliminating a bounds proof in
the consumer's dependent basepoint type. -/
theorem embeddedTwoPunctureRelativeLocalDiskFreeEquiv_apply
    {k : ℕ} {Y : ClosedHyperbolicSurface k} {U : Set ℂ}
    (f : C(U, Y.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → Y.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hp : ‖(p : ℂ)‖ < r) (hq : ‖(q : ℂ)‖ < r) (hpq : p ≠ q)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (z : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r})
    (hz : embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre z ∈
        twoPuncturedDiskRelativeOverlap (embeddedTwoPunctureLowerParameter p q r)
          (embeddedTwoPunctureUpperParameter p q r))
    (ξ : FundamentalGroup {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r} z) :
    let H := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre
    let hb := embeddedTwoPunctureParameters_bounds p q r hr hp hq
    embeddedTwoPunctureRelativeLocalDiskFreeEquiv
      f hf p q r hr hrU hp hq hpq hpre hqre z hz ξ =
      twoPuncturedDiskFundamentalGroupFreeEquiv hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
        (embeddedTwoPunctureLowerParameter_lt_upper p q r hr hpq hpre hqre)
        ⟨H z, hz⟩ (fundamentalGroupHomeomorphEquiv H z ξ) := by
  dsimp only
  unfold embeddedTwoPunctureRelativeLocalDiskFreeEquiv
  rcases embeddedTwoPunctureParameters_bounds p q r hr hp hq with
    ⟨hα, hα1, hβ, hβ1⟩
  rfl

end SystolicGrowth

#print axioms SystolicGrowth.embeddedTwoPunctureRelativeLocalDiskFreeEquiv_apply
#print axioms SystolicGrowth.fermiPositivePolarCoordinate_normalized_center
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRelativeLocalDiskPath_native
#print axioms SystolicGrowth.ExerciseGluingPreparation.embeddedTwoPunctureRelativeLocalDiskInclusion_unitCoordinate
#print axioms SystolicGrowth.ExerciseGluingPreparation.embeddedTwoPunctureRelativeLocalDiskInclusion_mem_lowerSide
#print axioms SystolicGrowth.ExerciseGluingPreparation.embeddedTwoPunctureRelativeLocalDiskInclusion_mem_upperSide
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftPolar_relativeLocalDisk_coordinate
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightPolar_relativeLocalDisk_coordinate
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterConnectorMidpoint_mem_relativeOverlap
