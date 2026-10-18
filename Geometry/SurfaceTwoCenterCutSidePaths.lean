module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterSmallDiskConnector
public import Geometry.SurfaceTwoCenterChartPolarIdentity
public import Geometry.SurfaceTwoCenterConvexSidePolarComparison
public import Geometry.SurfaceTwoCenterDiskPolarPaths
public import Geometry.SurfaceTwoCenterPuncturedComponentCover

@[expose] public section

/-!
# Split the actual small connector at the center midpoint

The radius-angle connector uses equal-radius truncations at the two ends of
the minimizing center segment. Its cut-arc midpoint is therefore the actual
midpoint of that segment. This module begins by exposing that exact split;
the coordinate-side containment lemmas follow from the actual chart data.
-/

open Set Metric UpperHalfPlane
open scoped ContinuousMap MatrixGroups Topology unitInterval

namespace SystolicGrowth
namespace ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The parameter where the right half of the outer concatenation enters the
middle of the cut arc. The candidate is `A.trans (core.trans B)`, so this is
the corresponding global parameter `5/8`. -/
def componentTwoCenterSmallConnectorMidpointTime : I :=
  ⟨5 / 8, by constructor <;> norm_num⟩

/-- The literal first half of the candidate, ending at the midpoint of the
actual minimizing center segment. -/
def componentTwoCenterSmallConnectorLeftHalf
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.twoCenterPolarBoundaryMap i true ρ hρ hρr 1)
      (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime) :=
  ((P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr).subpath 0
    componentTwoCenterSmallConnectorMidpointTime).cast (Path.source _).symm rfl

/-- The literal second half of the candidate, starting at the midpoint of the
actual minimizing center segment. -/
def componentTwoCenterSmallConnectorRightHalf
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    Path (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
        componentTwoCenterSmallConnectorMidpointTime)
      (P.twoCenterPolarBoundaryMap i false ρ hρ hρr 1) :=
  ((P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr).subpath
    componentTwoCenterSmallConnectorMidpointTime 1).cast rfl (Path.target _).symm

/-- Concatenating the two literal subpaths recovers the candidate up to the
standard path reparameterization, without changing either endpoint. -/
theorem componentTwoCenterSmallConnector_halves_homotopic_candidate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    ((P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr).trans
      (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr)).Homotopic
      (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr) := by
  let γ := P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
  let s := componentTwoCenterSmallConnectorMidpointTime
  have hsplit : ((γ.subpath 0 s).trans (γ.subpath s 1)).Homotopic
      (γ.subpath 0 1) := ⟨Path.Homotopy.subpathTransSubpath γ 0 s 1⟩
  have hfull : (γ.subpath 0 1).cast (Path.source _).symm
      (Path.target _).symm = γ := by
    ext t
    simp only [Path.cast_coe, Path.subpath_zero_one]
  have hparts : ((γ.subpath 0 s).trans (γ.subpath s 1)).cast
      (Path.source _).symm (Path.target _).symm =
      (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr).trans
        (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr) := by
    ext t
    rfl
  have hcast := hsplit.pathCast (Path.source _).symm (Path.target _).symm
  simpa only [hparts, hfull] using hcast

/-- The split point is precisely the full geodesic's parameter-`1/2`
midpoint, not merely a point between the two truncation endpoints. -/
theorem componentTwoCenterSmallConnector_midpoint_value
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
      componentTwoCenterSmallConnectorMidpointTime).val =
      P.componentCenterGeodPoint i ⟨1 / 2, by constructor <;> norm_num⟩ := by
  have hDpos : 0 < dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2) := by
    have hR : 0 < gluingEmbeddedRadius C g + gluingRadius C g := by
      have := P.radius_lt_embeddedRadius
      linarith [P.radius_pos]
    exact lt_of_lt_of_le hR (P.carrier_centers_outer_add_inner_le_dist i)
  have hcut : (P.componentTwoCenterCutCoordinate i
      ⟨1 / 2, by constructor <;> norm_num⟩ : ℝ) = 1 / 2 := by
    simp only [componentTwoCenterCutCoordinate]
    field_simp [ne_of_gt hDpos]
    ring
  change (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
    ⟨5 / 8, by norm_num⟩).val = _
  simp only [componentTwoCenterSmallDiskConnectorCandidate, Path.trans_apply]
  norm_num at *
  change P.componentCenterGeodPoint i
    (P.componentTwoCenterCutCoordinate i ⟨1 / 2, by constructor <;> norm_num⟩) = _
  have hcutI : P.componentTwoCenterCutCoordinate i
      ⟨1 / 2, by constructor <;> norm_num⟩ =
        ⟨1 / 2, by constructor <;> norm_num⟩ := Subtype.ext hcut
  rw [hcutI]

/-- The deleted-radius truncation maps the open cut interval strictly inside
the full center segment and preserves its midpoint. -/
theorem componentTwoCenterCutCoordinate_half_bounds
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (t : I) :
    0 < (P.componentTwoCenterCutCoordinate i t : ℝ) ∧
      (P.componentTwoCenterCutCoordinate i t : ℝ) < 1 ∧
      ((t : ℝ) ≤ 1 / 2 →
        (P.componentTwoCenterCutCoordinate i t : ℝ) ≤ 1 / 2) ∧
      (1 / 2 ≤ (t : ℝ) →
        1 / 2 ≤ (P.componentTwoCenterCutCoordinate i t : ℝ)) := by
  let D := dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
    (Quotient.mk'' (P.centers i).2)
  have hD : gluingEmbeddedRadius C g + gluingRadius C g ≤ D :=
    P.carrier_centers_outer_add_inner_le_dist i
  have hgap : 0 < D - 2 * gluingRadius C g := by
    have := P.radius_lt_embeddedRadius
    dsimp [D] at hD ⊢
    nlinarith
  have hDpos : 0 < D := by
    nlinarith [hgap, P.radius_pos]
  change
    0 < (gluingRadius C g + (t : ℝ) * (D - 2 * gluingRadius C g)) / D ∧
      (gluingRadius C g + (t : ℝ) * (D - 2 * gluingRadius C g)) / D < 1 ∧
      ((t : ℝ) ≤ 1 / 2 →
        (gluingRadius C g + (t : ℝ) * (D - 2 * gluingRadius C g)) / D ≤ 1 / 2) ∧
      (1 / 2 ≤ (t : ℝ) →
        1 / 2 ≤ (gluingRadius C g + (t : ℝ) * (D - 2 * gluingRadius C g)) / D)
  constructor
  · apply div_pos
    · nlinarith [t.2.1, P.radius_pos, hgap]
    · exact hDpos
  constructor
  · rw [div_lt_one hDpos]
    have hmul := mul_nonneg (sub_nonneg.mpr t.2.2) hgap.le
    have hdiff : D - (gluingRadius C g + (t : ℝ) *
        (D - 2 * gluingRadius C g)) = gluingRadius C g +
        (1 - (t : ℝ)) * (D - 2 * gluingRadius C g) := by ring
    apply sub_pos.mp
    rw [hdiff]
    exact add_pos_of_pos_of_nonneg P.radius_pos hmul
  constructor
  · intro ht
    rw [div_le_iff₀ hDpos]
    have hmul := mul_le_mul_of_nonneg_right ht hgap.le
    nlinarith
  · intro ht
    rw [le_div_iff₀ hDpos]
    have hmul := mul_le_mul_of_nonneg_right ht hgap.le
    nlinarith

/-- The first half of the actual coordinate center segment belongs to the
lower member of the twice-punctured-disk cover, away from its puncture. -/
theorem twoPuncturedDiskVerticalCenterSegment_mem_lowerSide
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (t : I) (ht0 : 0 < (t : ℝ)) (htmid : (t : ℝ) ≤ 1 / 2) :
    (((1 - (t : ℝ)) * α + (t : ℝ) * β : ℝ) : ℂ) * Complex.I ∈
      twoPuncturedDiskLowerSide α β := by
  let y := (1 - (t : ℝ)) * α + (t : ℝ) * β
  have hylo : -1 < y := by dsimp [y]; nlinarith [t.2.1, t.2.2]
  have hyhi : y < 1 := by dsimp [y]; nlinarith [t.2.1, t.2.2]
  have hymid : y ≤ (α + β) / 2 := by
    dsimp [y]
    have hcoef : 0 ≤ 1 - 2 * (t : ℝ) := by linarith
    have hgap : 0 ≤ β - α := (sub_nonneg.mpr hαβ.le)
    nlinarith [mul_nonneg hcoef hgap]
  have hnorm : ‖(y : ℂ) * Complex.I‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact abs_lt.mpr ⟨hylo, hyhi⟩
  have hball : (y : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hnorm
  have hheight : ((y : ℂ) * Complex.I).im <
      twoPuncturedDiskOverlapUpper α β := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp only [zero_mul, mul_one, add_zero]
    exact lt_of_le_of_lt hymid (by
      have hb := twoPuncturedDiskOverlap_bounds hαβ
      dsimp [twoPuncturedDiskOverlapUpper]
      linarith)
  have hleft : (y : ℂ) * Complex.I ≠ twoPuncturedDiskLeftCenter α := by
    intro heq
    have him := congrArg Complex.im heq
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, twoPuncturedDiskLeftCenter_im] at him
    simp only [zero_mul, mul_one, add_zero] at him
    dsimp [y] at him
    nlinarith [mul_pos ht0 (sub_pos.mpr hαβ)]
  change ((y : ℂ) * Complex.I ∈ twoPuncturedDiskLowerBase α β) ∧
    (y : ℂ) * Complex.I ≠ twoPuncturedDiskLeftCenter α
  exact ⟨⟨hball, hheight⟩, hleft⟩

/-- The second half of the actual coordinate center segment belongs to the
upper member, away from its puncture. -/
theorem twoPuncturedDiskVerticalCenterSegment_mem_upperSide
    {α β : ℝ} (hα : -1 < α) (hα1 : α < 1)
    (hβ : -1 < β) (hβ1 : β < 1) (hαβ : α < β)
    (t : I) (htmid : 1 / 2 ≤ (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    (((1 - (t : ℝ)) * α + (t : ℝ) * β : ℝ) : ℂ) * Complex.I ∈
      twoPuncturedDiskUpperSide α β := by
  let y := (1 - (t : ℝ)) * α + (t : ℝ) * β
  have hylo : -1 < y := by dsimp [y]; nlinarith [t.2.1, t.2.2]
  have hyhi : y < 1 := by dsimp [y]; nlinarith [t.2.1, t.2.2]
  have hymid : (α + β) / 2 ≤ y := by
    dsimp [y]
    have hcoef : 0 ≤ 2 * (t : ℝ) - 1 := by linarith
    have hgap : 0 ≤ β - α := (sub_nonneg.mpr hαβ.le)
    nlinarith [mul_nonneg hcoef hgap]
  have hnorm : ‖(y : ℂ) * Complex.I‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
    exact abs_lt.mpr ⟨hylo, hyhi⟩
  have hball : (y : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hnorm
  have hheight : twoPuncturedDiskOverlapLower α β <
      ((y : ℂ) * Complex.I).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simp only [zero_mul, mul_one, add_zero]
    have hlowmid : twoPuncturedDiskOverlapLower α β < (α + β) / 2 := by
      dsimp [twoPuncturedDiskOverlapLower]
      linarith [hαβ]
    exact lt_of_lt_of_le hlowmid hymid
  have hright : (y : ℂ) * Complex.I ≠ twoPuncturedDiskRightCenter β := by
    intro heq
    have him := congrArg Complex.im heq
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, twoPuncturedDiskRightCenter_im] at him
    simp only [zero_mul, mul_one, add_zero] at him
    dsimp [y] at him
    nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hαβ)]
  change ((y : ℂ) * Complex.I ∈ twoPuncturedDiskUpperBase α β) ∧
    (y : ℂ) * Complex.I ≠ twoPuncturedDiskRightCenter β
  exact ⟨⟨hball, hheight⟩, hright⟩

/-- In the actual ellipse chart, the affine imaginary-axis segment between
the two original chart centers maps to the literal minimizing geodesic. This
is the coordinate bridge needed before applying the standard lower/upper
side inequalities to the cut core. -/
theorem componentTwoCenterAxisChart_affineSegment
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (e : ℂ ≃ₜ ℍ)
    (hproj : ∀ z : U, f z = (X i).orbitProjection (e z.1))
    (m a b : ℝ) (ha : 0 < a)
    (hcoord : ∀ z : ℂ, e z = P.componentTwoCenterGeodesicCoordinateHomeomorph i
      (m + a * z.im, b * z.re))
    (p q : U) (hpRe : p.1.re = 0) (hqRe : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1)
    (hpLift : e p.1 = (P.centers i).1)
    (hqLift : e q.1 = P.componentCenterClosestDeck i • (P.centers i).2)
    (t : I) :
    ∃ z : U,
      z.1 = (((1 - (t : ℝ)) * p.1.im + (t : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i t := by
  let H := P.componentTwoCenterGeodesicCoordinateHomeomorph i
  let l := Real.log (P.componentTwoCenterGeodesicVerticalizer i • (P.centers i).1).im
  let r := Real.log (P.componentTwoCenterGeodesicVerticalizer i •
    (P.componentCenterClosestDeck i • (P.centers i).2)).im
  have hleft : H (l, 0) = (P.centers i).1 := by
    calc
      H (l, 0) = H (H.symm (P.centers i).1) := by
        rw [P.componentTwoCenterGeodesicCoordinateHomeomorph_left_center]
      _ = (P.centers i).1 := H.apply_symm_apply _
  have hright : H (r, 0) = P.componentCenterClosestDeck i • (P.centers i).2 := by
    calc
      H (r, 0) = H (H.symm (P.componentCenterClosestDeck i • (P.centers i).2)) := by
        rw [P.componentTwoCenterGeodesicCoordinateHomeomorph_right_center]
      _ = P.componentCenterClosestDeck i • (P.centers i).2 := H.apply_symm_apply _
  have hpTuple : (m + a * p.1.im, b * p.1.re) = (l, 0) := by
    apply H.injective
    calc
      H (m + a * p.1.im, b * p.1.re) = e p.1 := (hcoord p.1).symm
      _ = (P.centers i).1 := hpLift
      _ = H (l, 0) := hleft.symm
  have hqTuple : (m + a * q.1.im, b * q.1.re) = (r, 0) := by
    apply H.injective
    calc
      H (m + a * q.1.im, b * q.1.re) = e q.1 := (hcoord q.1).symm
      _ = P.componentCenterClosestDeck i • (P.centers i).2 := hqLift
      _ = H (r, 0) := hright.symm
  have hpim : p.1.im = (l - m) / a := by
    have h := congrArg Prod.fst hpTuple
    dsimp at h
    field_simp [ne_of_gt ha]
    nlinarith
  have hqim : q.1.im = (r - m) / a := by
    have h := congrArg Prod.fst hqTuple
    dsimp at h
    field_simp [ne_of_gt ha]
    nlinarith
  let zt : ℂ := (((1 - (t : ℝ)) * p.1.im + (t : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I
  have hzt_eq : zt = (1 - (t : ℝ)) • (p : ℂ) + (t : ℝ) • (q : ℂ) := by
    apply Complex.ext <;> simp [zt, hpRe, hqRe]
  have hztball : zt ∈ Metric.ball (0 : ℂ) 1 := by
    rw [hzt_eq]
    exact (convex_ball (0 : ℂ) 1)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hp)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hq)
      (sub_nonneg.mpr t.2.2) t.2.1 (by ring)
  have hztle : dist zt 0 ≤ 1 := hztball.le
  have hztmem : zt ∈ U := hball (Metric.mem_closedBall.mpr hztle)
  let z : U := ⟨zt, hztmem⟩
  have hEt : e zt = P.componentLiftedCenterGeodPoint i t := by
    rw [hcoord]
    have hpair : (m + a * zt.im, b * zt.re) = ((1 - (t : ℝ)) * l + (t : ℝ) * r, 0) := by
      apply Prod.ext
      · dsimp [zt]
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero]
        rw [hpim, hqim]
        field_simp [ne_of_gt ha]
        ring
      · dsimp [zt]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self]
    rw [hpair]
    dsimp [l, r]
    exact P.componentTwoCenterGeodesicCoordinateHomeomorph_core i t
  have hproj' : f z = P.componentCenterGeodPoint i t := by
    rw [hproj, hEt]
    rfl
  refine ⟨z, rfl, ?_, hproj'⟩
  simpa only [Metric.mem_ball, dist_zero_right] using hztball

/-- The relative local-disk unit coordinate of an actual chart-image point is
the literal scaled chart coordinate. -/
theorem embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    {g : ℕ} {X : ClosedHyperbolicSurface g} {U : Set ℂ}
    (f : C(U, X.Carrier)) (hf : Topology.IsOpenEmbedding (f : U → X.Carrier))
    (p q : U) (r : ℝ) (hr : 0 < r)
    (hrU : Metric.closedBall (0 : ℂ) r ⊆ U)
    (hpre : (p : ℂ).re = 0) (hqre : (q : ℂ).re = 0)
    (x : embeddedTwoPunctureAmbientPoint f p q)
    (hx : x ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q r)
    (z : U) (hz : ‖(z : ℂ)‖ < r) (himage : f z = x.1) :
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q r hr hrU hpre hqre ⟨x, hx⟩ : ℂ) = (r⁻¹ : ℝ) • (z : ℂ) := by
  have hambient : f z ∈ embeddedTwoPunctureAmbient f p q := by
    rw [himage]
    exact x.2
  have hchart : f z ∈ embeddedTwoPunctureLocalDisk f p q r := by
    change f z ∈ f '' {w : U | ‖(w : ℂ)‖ < r} ∩
      embeddedTwoPunctureAmbient f p q
    exact ⟨⟨z, hz, rfl⟩, hambient⟩
  let w : ↥(embeddedTwoPunctureLocalDisk f p q r) := ⟨f z, hchart⟩
  have hrelative :
      embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r ⟨x, hx⟩ = w := by
    apply Subtype.ext
    exact himage.symm
  have hdomp : z ≠ p := by
    intro heq
    exact x.2.1 (himage.symm.trans (congrArg f heq))
  have hdomq : z ≠ q := by
    intro heq
    exact x.2.2 (himage.symm.trans (congrArg f heq))
  let zd : {w : U // w ∈ embeddedTwoPunctureLocalDiskDomain p q r} :=
    ⟨z, ⟨hz, hdomp, hdomq⟩⟩
  have hpoint := embeddedTwoPunctureLocalDiskCoordinateHomeomorph_chartPoint
    f hf p q r hrU zd
  have hcoordval :
      (embeddedTwoPunctureLocalDiskCoordinateHomeomorph f hf p q r hrU w : ℂ) =
        (z : ℂ) := by
    have hval := congrArg Subtype.val hpoint
    simpa [zd, embeddedTwoPunctureLocalDiskDomainHomeomorph] using hval
  change (embeddedTwoPunctureLocalDiskUnitHomeomorph f hf p q r hr hrU hpre hqre
      (embeddedTwoPunctureLocalDiskRelativeHomeomorph f p q r ⟨x, hx⟩) : ℂ) = _
  rw [hrelative, embeddedTwoPunctureLocalDiskUnitHomeomorph_apply, hcoordval]

/-- A literal chart point in the unit disk gives its actual ambient punctured
point in the relative local-disk carrier, with the same normalized coordinate.
This is the pointwise bridge used for polar arcs. -/
private theorem internalPolarChartPoint_mem_relativeLocalDisk
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hp : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hq : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (native : P.CenterPuncturedChainComponent i)
    (z : U) (hz : ‖z.1‖ < 1) (himage : f z = native.1)
    (S : Set ℂ) (hS : z.1 ∈ S) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq native ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈ S := by
  let x := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hp hq native
  have himage' : f z = x.1 := by
    simpa [x, P.internalCenterPuncturedAmbientHomeomorph_apply_val] using himage
  have hlocal : x.1 ∈ embeddedTwoPunctureLocalDisk f p q 1 := by
    change x.1 ∈ f '' {w : U | ‖w.1‖ < 1} ∩ embeddedTwoPunctureAmbient f p q
    exact ⟨⟨z, hz, himage'⟩, x.2⟩
  have hrelative : x ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1 := hlocal
  let y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1} := ⟨x, hrelative⟩
  have hcoord := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q 1 one_pos hball hpre hqre x hrelative z hz himage'
  refine ⟨y, rfl, ?_⟩
  rw [hcoord]
  simpa using hS

/-- The actual left positive polar point lies in the relative lower-side
local-disk carrier when the first chart puncture is the lower one. -/
theorem componentTwoCenterLeftPolarPoint_mem_lowerSide
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hBU : twoPuncturedDiskLowerBase p.1.im q.1.im ⊆ U)
    (hpB : p.1 ∈ twoPuncturedDiskLowerBase p.1.im q.1.im)
    (hqU : q.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ twoPuncturedDiskLowerBase p.1.im q.1.im → z ≠ q.1)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball p.1 δ ⊆ twoPuncturedDiskLowerBase p.1.im q.1.im)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ) ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
        twoPuncturedDiskLowerSide p.1.im q.1.im := by
  let c := twoPuncturedDiskLeftCenter p.1.im
  have hc : p.1 = c := by
    apply Complex.ext
    · simpa [c, twoPuncturedDiskLeftCenter] using hpre
    · simp [c, twoPuncturedDiskLeftCenter]
  let u := fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ
    (fermiSLPolarAnglePreimageMap γ
      (orientedFermiDiskPoint (m + a * p.1.im) a b 0) θ)
  have hdist : dist (p.1 + u) p.1 < δ := by
    rw [dist_eq_norm]
    have hsub : p.1 + u - p.1 = u := by abel
    rw [hsub]
    exact hqball _
  have hzbase : p.1 + u ∈ twoPuncturedDiskLowerBase p.1.im q.1.im :=
    hball hdist
  have hzball : p.1 + u ∈ Metric.ball (0 : ℂ) 1 := hzbase.1
  have hznorm : ‖p.1 + u‖ < 1 := by
    change dist (p.1 + u) 0 < 1 at hzball
    simpa only [dist_zero_right] using hzball
  have hc' : twoPuncturedDiskLeftCenter p.1.im = p.1 := by
    simpa [c] using hc.symm
  have hzne : p.1 + u ≠ twoPuncturedDiskLeftCenter p.1.im := by
    rw [hc']
    intro heq
    have hu : u = 0 := by
      have hcancel : p.1 + u = p.1 + 0 := by simpa using heq
      exact add_left_cancel hcancel
    exact fermiPositivePolarCoordinate_ne_zero (m + a * p.1.im) a b ha hb hρ
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * p.1.im) a b 0) θ) hu
  have hzside : p.1 + u ∈ twoPuncturedDiskLowerSide p.1.im q.1.im :=
    ⟨hzbase, hzne⟩
  let z : U := ⟨p.1 + u, hBU hzbase⟩
  have hsys : 2 * ρ < (X i).systole := by
    have houter : 2 * gluingEmbeddedRadius C g < (X i).systole := by
      linarith [P.twice_outer_lt_systole i]
    nlinarith [lt_of_le_of_lt hρr P.radius_lt_embeddedRadius]
  have himage : f z = (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ).val := by
    have hchart : f z =
        ((translatedFermiSideOriginalPolarMap
          (twoPuncturedDiskLowerBase p.1.im q.1.im) p.1 q.1
          hBU hpB hqU hBother f hf γ m a b ha hb hformula hpre ρ δ hρ
          hsys hball hqball θ).1 :
            (X i).Carrier) := by
      rfl
    exact hchart.trans
      (P.translatedFermiSideOriginalPolarMap_left_twoCenterPolarBoundaryMap
        i f (twoPuncturedDiskLowerBase p.1.im q.1.im) p q
        hBU hpB hqU hBother hf γ m a b ha hb hformula hpre ρ δ hρ hρr
        hball hqball hleft θ)
  exact P.internalPolarChartPoint_mem_relativeLocalDisk i hballU f hf p q
    hpMap hqMap hpre hqre hi hnext (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ)
    z hznorm himage (twoPuncturedDiskLowerSide p.1.im q.1.im) hzside

/-- The same actual left polar point lies in the relative upper-side carrier
when the first chart puncture is the upper one. -/
theorem componentTwoCenterLeftPolarPoint_mem_upperSide
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hleft : γ • orientedFermiDiskPoint m a b p.1 = (P.centers i).1)
    (hBU : twoPuncturedDiskUpperBase q.1.im p.1.im ⊆ U)
    (hpB : p.1 ∈ twoPuncturedDiskUpperBase q.1.im p.1.im)
    (hqU : q.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ twoPuncturedDiskUpperBase q.1.im p.1.im → z ≠ q.1)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball p.1 δ ⊆ twoPuncturedDiskUpperBase q.1.im p.1.im)
    (hqball : ∀ θ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δ)
    (θ : Circle) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ) ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
        twoPuncturedDiskUpperSide q.1.im p.1.im := by
  let c := twoPuncturedDiskRightCenter p.1.im
  have hc : p.1 = c := by
    apply Complex.ext
    · simpa [c, twoPuncturedDiskRightCenter] using hpre
    · simp [c, twoPuncturedDiskRightCenter]
  let u := fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ
    (fermiSLPolarAnglePreimageMap γ
      (orientedFermiDiskPoint (m + a * p.1.im) a b 0) θ)
  have hdist : dist (p.1 + u) p.1 < δ := by
    rw [dist_eq_norm]
    have hsub : p.1 + u - p.1 = u := by abel
    rw [hsub]
    exact hqball _
  have hzbase : p.1 + u ∈ twoPuncturedDiskUpperBase q.1.im p.1.im :=
    hball hdist
  have hzball : p.1 + u ∈ Metric.ball (0 : ℂ) 1 := hzbase.1
  have hznorm : ‖p.1 + u‖ < 1 := by
    change dist (p.1 + u) 0 < 1 at hzball
    simpa only [dist_zero_right] using hzball
  have hc' : twoPuncturedDiskRightCenter p.1.im = p.1 := by
    simpa [c] using hc.symm
  have hzne : p.1 + u ≠ twoPuncturedDiskRightCenter p.1.im := by
    rw [hc']
    intro heq
    have hu : u = 0 := by
      have hcancel : p.1 + u = p.1 + 0 := by simpa using heq
      exact add_left_cancel hcancel
    exact fermiPositivePolarCoordinate_ne_zero (m + a * p.1.im) a b ha hb hρ
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * p.1.im) a b 0) θ) hu
  have hzside : p.1 + u ∈ twoPuncturedDiskUpperSide q.1.im p.1.im :=
    ⟨hzbase, hzne⟩
  let z : U := ⟨p.1 + u, hBU hzbase⟩
  have hsys : 2 * ρ < (X i).systole := by
    have houter : 2 * gluingEmbeddedRadius C g < (X i).systole := by
      linarith [P.twice_outer_lt_systole i]
    nlinarith [lt_of_le_of_lt hρr P.radius_lt_embeddedRadius]
  have himage : f z = (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ).val := by
    have hchart : f z =
        ((translatedFermiSideOriginalPolarMap
          (twoPuncturedDiskUpperBase q.1.im p.1.im) p.1 q.1
          hBU hpB hqU hBother f hf γ m a b ha hb hformula hpre ρ δ hρ
          hsys hball hqball θ).1 : (X i).Carrier) := by
      rfl
    exact hchart.trans
      (P.translatedFermiSideOriginalPolarMap_left_twoCenterPolarBoundaryMap
        i f (twoPuncturedDiskUpperBase q.1.im p.1.im) p q
        hBU hpB hqU hBother hf γ m a b ha hb hformula hpre ρ δ hρ hρr
        hball hqball hleft θ)
  exact P.internalPolarChartPoint_mem_relativeLocalDisk i hballU f hf p q
    hpMap hqMap hpre hqre hi hnext (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ)
    z hznorm himage (twoPuncturedDiskUpperSide q.1.im p.1.im) hzside

/-- The actual right positive polar point lies in the relative upper-side
carrier when the second chart puncture is the upper one. -/
theorem componentTwoCenterRightPolarPoint_mem_upperSide
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (hBU : twoPuncturedDiskUpperBase p.1.im q.1.im ⊆ U)
    (hqB : q.1 ∈ twoPuncturedDiskUpperBase p.1.im q.1.im)
    (hpU : p.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ twoPuncturedDiskUpperBase p.1.im q.1.im → z ≠ p.1)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball q.1 δ ⊆ twoPuncturedDiskUpperBase p.1.im q.1.im)
    (hqball : ∀ φ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ φ‖ < δ)
    (θ : Circle) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
        twoPuncturedDiskUpperSide p.1.im q.1.im := by
  let c := twoPuncturedDiskRightCenter q.1.im
  have hc : q.1 = c := by
    apply Complex.ext
    · simpa [c, twoPuncturedDiskRightCenter] using hqre
    · simp [c, twoPuncturedDiskRightCenter]
  let φ := gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * θ
  let u := fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ
    (fermiSLPolarAnglePreimageMap γ
      (orientedFermiDiskPoint (m + a * q.1.im) a b 0) φ)
  have hdist : dist (q.1 + u) q.1 < δ := by
    rw [dist_eq_norm]
    have hsub : q.1 + u - q.1 = u := by abel
    rw [hsub]
    exact hqball _
  have hzbase : q.1 + u ∈ twoPuncturedDiskUpperBase p.1.im q.1.im :=
    hball hdist
  have hzball : q.1 + u ∈ Metric.ball (0 : ℂ) 1 := hzbase.1
  have hznorm : ‖q.1 + u‖ < 1 := by
    change dist (q.1 + u) 0 < 1 at hzball
    simpa only [dist_zero_right] using hzball
  have hc' : twoPuncturedDiskRightCenter q.1.im = q.1 := by
    simpa [c] using hc.symm
  have hzne : q.1 + u ≠ twoPuncturedDiskRightCenter q.1.im := by
    rw [hc']
    intro heq
    have hu : u = 0 := by
      have hcancel : q.1 + u = q.1 + 0 := by simpa using heq
      exact add_left_cancel hcancel
    exact fermiPositivePolarCoordinate_ne_zero (m + a * q.1.im) a b ha hb hρ
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * q.1.im) a b 0) φ) hu
  have hzside : q.1 + u ∈ twoPuncturedDiskUpperSide p.1.im q.1.im :=
    ⟨hzbase, hzne⟩
  let z : U := ⟨q.1 + u, hBU hzbase⟩
  have hsys : 2 * ρ < (X i).systole := by
    have houter : 2 * gluingEmbeddedRadius C g < (X i).systole := by
      linarith [P.twice_outer_lt_systole i]
    nlinarith [lt_of_le_of_lt hρr P.radius_lt_embeddedRadius]
  have himage : f z = (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ).val := by
    have hchart : f z =
        ((translatedFermiSideOriginalPolarMap
          (twoPuncturedDiskUpperBase p.1.im q.1.im) q.1 p.1
          hBU hqB hpU hBother f hf γ m a b ha hb hformula hqre ρ δ hρ
          hsys hball hqball φ).1 : (X i).Carrier) := by
      rfl
    exact hchart.trans
      (P.translatedFermiSideOriginalPolarMap_right_twoCenterPolarBoundaryMap
        i f (twoPuncturedDiskUpperBase p.1.im q.1.im) p q
        hBU hqB hpU hBother hf γ m a b ha hb hformula hqre ρ δ hρ hρr
        hball hqball hright θ)
  exact P.internalPolarChartPoint_mem_relativeLocalDisk i hballU f hf p q
    hpMap hqMap hpre hqre hi hnext (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ)
    z hznorm himage (twoPuncturedDiskUpperSide p.1.im q.1.im) hzside

/-- The actual right positive polar point lies in the relative lower-side
carrier when the second chart puncture is the lower one. -/
theorem componentTwoCenterRightPolarPoint_mem_lowerSide
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (γ : SL(2, ℝ)) (m a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hformula : ∀ z : U,
      f z = (X i).orbitProjection (γ • orientedFermiDiskPoint m a b z.1))
    (hright : γ • orientedFermiDiskPoint m a b q.1 =
      P.componentCenterClosestDeck i • (P.centers i).2)
    (hBU : twoPuncturedDiskLowerBase q.1.im p.1.im ⊆ U)
    (hqB : q.1 ∈ twoPuncturedDiskLowerBase q.1.im p.1.im)
    (hpU : p.1 ∈ U)
    (hBother : ∀ z : ℂ, z ∈ twoPuncturedDiskLowerBase q.1.im p.1.im → z ≠ p.1)
    (ρ δ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g)
    (hball : Metric.ball q.1 δ ⊆ twoPuncturedDiskLowerBase q.1.im p.1.im)
    (hqball : ∀ φ : Circle,
      ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ φ‖ < δ)
    (θ : Circle) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
        twoPuncturedDiskLowerSide q.1.im p.1.im := by
  let c := twoPuncturedDiskLeftCenter q.1.im
  have hc : q.1 = c := by
    apply Complex.ext
    · simpa [c, twoPuncturedDiskLeftCenter] using hqre
    · simp [c, twoPuncturedDiskLeftCenter]
  let φ := gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 * θ
  let u := fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ
    (fermiSLPolarAnglePreimageMap γ
      (orientedFermiDiskPoint (m + a * q.1.im) a b 0) φ)
  have hdist : dist (q.1 + u) q.1 < δ := by
    rw [dist_eq_norm]
    have hsub : q.1 + u - q.1 = u := by abel
    rw [hsub]
    exact hqball _
  have hzbase : q.1 + u ∈ twoPuncturedDiskLowerBase q.1.im p.1.im :=
    hball hdist
  have hzball : q.1 + u ∈ Metric.ball (0 : ℂ) 1 := hzbase.1
  have hznorm : ‖q.1 + u‖ < 1 := by
    change dist (q.1 + u) 0 < 1 at hzball
    simpa only [dist_zero_right] using hzball
  have hc' : twoPuncturedDiskLeftCenter q.1.im = q.1 := by
    simpa [c] using hc.symm
  have hzne : q.1 + u ≠ twoPuncturedDiskLeftCenter q.1.im := by
    rw [hc']
    intro heq
    have hu : u = 0 := by
      have hcancel : q.1 + u = q.1 + 0 := by simpa using heq
      exact add_left_cancel hcancel
    exact fermiPositivePolarCoordinate_ne_zero (m + a * q.1.im) a b ha hb hρ
      (fermiSLPolarAnglePreimageMap γ
        (orientedFermiDiskPoint (m + a * q.1.im) a b 0) φ) hu
  have hzside : q.1 + u ∈ twoPuncturedDiskLowerSide q.1.im p.1.im :=
    ⟨hzbase, hzne⟩
  let z : U := ⟨q.1 + u, hBU hzbase⟩
  have hsys : 2 * ρ < (X i).systole := by
    have houter : 2 * gluingEmbeddedRadius C g < (X i).systole := by
      linarith [P.twice_outer_lt_systole i]
    nlinarith [lt_of_le_of_lt hρr P.radius_lt_embeddedRadius]
  have himage : f z = (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ).val := by
    have hchart : f z =
        ((translatedFermiSideOriginalPolarMap
          (twoPuncturedDiskLowerBase q.1.im p.1.im) q.1 p.1
          hBU hqB hpU hBother f hf γ m a b ha hb hformula hqre ρ δ hρ
          hsys hball hqball φ).1 : (X i).Carrier) := by
      rfl
    exact hchart.trans
      (P.translatedFermiSideOriginalPolarMap_right_twoCenterPolarBoundaryMap
        i f (twoPuncturedDiskLowerBase q.1.im p.1.im) p q
        hBU hqB hpU hBother hf γ m a b ha hb hformula hqre ρ δ hρ hρr
        hball hqball hright θ)
  exact P.internalPolarChartPoint_mem_relativeLocalDisk i hballU f hf p q
    hpMap hqMap hpre hqre hi hnext (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ)
    z hznorm himage (twoPuncturedDiskLowerSide q.1.im p.1.im) hzside

/-- Comparison balls and Fermi-coordinate bounds for the same selected native
polar radius. The two possible chart-center orderings remain explicit. -/
structure TwoCenterPolarSideComparisonData {U : Set ℂ} (p q : U) (m a b ρ : ℝ)
    (ha : 0 < a) (hb : 0 < b) where
  δLeft : ℝ
  δRight : ℝ
  δLeft_pos : 0 < δLeft
  δRight_pos : 0 < δRight
  left_ball : Metric.ball p.1 δLeft ⊆
    if p.1.im < q.1.im then twoPuncturedDiskLowerBase p.1.im q.1.im
    else twoPuncturedDiskUpperBase q.1.im p.1.im
  right_ball : Metric.ball q.1 δRight ⊆
    if p.1.im < q.1.im then twoPuncturedDiskUpperBase p.1.im q.1.im
    else twoPuncturedDiskLowerBase q.1.im p.1.im
  left_norm : ∀ θ : Circle,
    ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δLeft
  right_norm : ∀ θ : Circle,
    ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δRight

/-- Select the same actual circles while retaining their Fermi comparison
certificates. These certificates fix the lift and phase at the selected
radius when the physical polar loops are identified with local generators. -/
theorem exists_componentTwoCenterPolarArcs_mem_relativeSides_with_comparisonData
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
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
      P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ t : I,
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      Nonempty (TwoCenterPolarSideComparisonData p q m a b ρ ha hb) ∧
      ((p.1.im < q.1.im ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide p.1.im q.1.im) ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide p.1.im q.1.im)) ∨
       (q.1.im < p.1.im ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide q.1.im p.1.im) ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide q.1.im p.1.im))) := by
  have hunit : Metric.ball (0 : ℂ) 1 ⊆ U := by
    intro z hz
    exact hballU (Metric.mem_closedBall.mpr hz.le)
  have hpAbs : |p.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hp
  have hqAbs : |q.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hq
  have hpBounds := abs_lt.mp hpAbs
  have hqBounds := abs_lt.mp hqAbs
  have himne : p.1.im ≠ q.1.im := by
    intro h
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact h
  have hleftD : (Quotient.mk'' (P.centers i).1 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f := by
    rw [← hpMap, embeddedCoordinatePunctureDisk]
    exact ⟨p, hp, rfl⟩
  have hrightD : (Quotient.mk'' (P.centers i).2 : (X i).Carrier) ∈
      embeddedCoordinatePunctureDisk f := by
    rw [← hqMap, embeddedCoordinatePunctureDisk]
    exact ⟨q, hq, rfl⟩
  have hD := embeddedCoordinatePunctureDisk_isOpen_of_isOpenEmbedding hU hballU f hf
  rcases lt_or_gt_of_ne himne with hpqOrder | hqpOrder
  · have hlower := twoPuncturedDiskLowerSide_uniformSurfaceComparison
      hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2 hpqOrder hunit f hf
      γ m a b ha hb hformula
    have hupper := twoPuncturedDiskUpperSide_uniformSurfaceComparison
      hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2 hpqOrder hunit f hf
      γ m a b ha hb hformula
    obtain ⟨εL, δL, hεL, hδL, hballL, hspecL⟩ := hlower
    obtain ⟨εU, δU, hεU, hδU, hballU', hspecU⟩ := hupper
    let ε := min εL εU
    have hε : 0 < ε := lt_min hεL hεU
    obtain ⟨ρ, hρ, hρr, hρlt, hmem⟩ :=
      P.exists_small_twoCenterPolarRadius_mem_of_isOpen_lt i hD hleftD hrightD ε hε
    have hρL : ρ ≤ εL := le_of_lt (lt_of_lt_of_le hρlt (min_le_left _ _))
    have hρU : ρ ≤ εU := le_of_lt (lt_of_lt_of_le hρlt (min_le_right _ _))
    obtain ⟨hqL, _, _⟩ := hspecL ρ hρ hρL
    obtain ⟨hqU', _, _⟩ := hspecU ρ hρ hρU
    have hcircles : ∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f := by
      intro b θ
      have h := hmem b θ ρ hρ le_rfl
      have heq : (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val =
          (P.twoCenterPolarPoint i b θ ρ hρ hρr).val := rfl
      rw [heq]
      exact h
    have hcandidate := P.componentTwoCenterSmallDiskConnectorCandidate_mem
      i ρ hρ hρr hsegment hcircles
    have hpLeft : p.1 = twoPuncturedDiskLeftCenter p.1.im := by
      apply Complex.ext
      · simpa [twoPuncturedDiskLeftCenter] using hpre
      · simp [twoPuncturedDiskLeftCenter]
    have hqRight : q.1 = twoPuncturedDiskRightCenter q.1.im := by
      apply Complex.ext
      · simpa [twoPuncturedDiskRightCenter] using hqre
      · simp [twoPuncturedDiskRightCenter]
    have hLowerU : twoPuncturedDiskLowerBase p.1.im q.1.im ⊆ U := by
      intro z hz
      exact hunit hz.1
    have hUpperU : twoPuncturedDiskUpperBase p.1.im q.1.im ⊆ U := by
      intro z hz
      exact hunit hz.1
    have hballLeft : Metric.ball p.1 δL ⊆
        twoPuncturedDiskLowerBase p.1.im q.1.im := by
      have hballEq : Metric.ball p.1 δL =
          Metric.ball (twoPuncturedDiskLeftCenter p.1.im) δL :=
        congrArg (fun z : ℂ => Metric.ball z δL) hpLeft
      rw [hballEq]
      exact hballL
    have hballRight : Metric.ball q.1 δU ⊆
        twoPuncturedDiskUpperBase p.1.im q.1.im := by
      have hballEq : Metric.ball q.1 δU =
          Metric.ball (twoPuncturedDiskRightCenter q.1.im) δU :=
        congrArg (fun z : ℂ => Metric.ball z δU) hqRight
      rw [hballEq]
      exact hballU'
    have hqFermiLeft : ∀ θ : Circle,
        ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δL := by
      intro θ
      simpa [twoPuncturedDiskLeftCenter] using hqL θ
    have hqFermiRight : ∀ θ : Circle,
        ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δU := by
      intro θ
      simpa [twoPuncturedDiskRightCenter] using hqU' θ
    have hpB : p.1 ∈ twoPuncturedDiskLowerBase p.1.im q.1.im := by
      simpa only [← hpLeft] using
        (twoPuncturedDiskLeftCenter_mem_lowerBase hpBounds.1 hpBounds.2 hpqOrder)
    have hqB : q.1 ∈ twoPuncturedDiskUpperBase p.1.im q.1.im := by
      simpa only [← hqRight] using
        (twoPuncturedDiskRightCenter_mem_upperBase hqBounds.1 hqBounds.2 hpqOrder)
    have hleftOther : ∀ z : ℂ,
        z ∈ twoPuncturedDiskLowerBase p.1.im q.1.im → z ≠ q.1 := by
      intro z hz heq
      have hcenter : z = twoPuncturedDiskRightCenter q.1.im := heq.trans hqRight
      exact twoPuncturedDiskRightCenter_not_lowerBase hpqOrder (by
        rw [← hcenter]
        exact hz)
    have hrightOther : ∀ z : ℂ,
        z ∈ twoPuncturedDiskUpperBase p.1.im q.1.im → z ≠ p.1 := by
      intro z hz heq
      have hcenter : z = twoPuncturedDiskLeftCenter p.1.im := heq.trans hpLeft
      exact twoPuncturedDiskLeftCenter_not_upperBase hpqOrder (by
        rw [← hcenter]
        exact hz)
    have hcomparison : Nonempty (TwoCenterPolarSideComparisonData p q m a b ρ ha hb) :=
      ⟨⟨δL, δU, hδL, hδU,
        by simpa only [if_pos hpqOrder] using hballLeft,
        by simpa only [if_pos hpqOrder] using hballRight,
        hqFermiLeft, hqFermiRight⟩⟩
    refine ⟨ρ, hρ, hρr, hcircles, hcandidate, hcomparison,
      Or.inl ⟨hpqOrder, ?_, ?_⟩⟩
    · intro θ
      exact P.componentTwoCenterLeftPolarPoint_mem_lowerSide i hballU f hf p q
        hpMap hqMap hpre hqre hi hnext γ m a b ha hb hformula hleft
        hLowerU hpB q.2 hleftOther ρ δL hρ hρr hballLeft hqFermiLeft θ
    · intro θ
      exact P.componentTwoCenterRightPolarPoint_mem_upperSide i hballU f hf p q
        hpMap hqMap hpre hqre hi hnext γ m a b ha hb hformula hright
        hUpperU hqB p.2 hrightOther ρ δU hρ hρr hballRight hqFermiRight θ
  · have hlower := twoPuncturedDiskLowerSide_uniformSurfaceComparison
      hqBounds.1 hqBounds.2 hpBounds.1 hpBounds.2 hqpOrder hunit f hf
      γ m a b ha hb hformula
    have hupper := twoPuncturedDiskUpperSide_uniformSurfaceComparison
      hqBounds.1 hqBounds.2 hpBounds.1 hpBounds.2 hqpOrder hunit f hf
      γ m a b ha hb hformula
    obtain ⟨εL, δL, hεL, hδL, hballL, hspecL⟩ := hlower
    obtain ⟨εU, δU, hεU, hδU, hballU', hspecU⟩ := hupper
    let ε := min εL εU
    have hε : 0 < ε := lt_min hεL hεU
    obtain ⟨ρ, hρ, hρr, hρlt, hmem⟩ :=
      P.exists_small_twoCenterPolarRadius_mem_of_isOpen_lt i hD hleftD hrightD ε hε
    have hρL : ρ ≤ εL := le_of_lt (lt_of_lt_of_le hρlt (min_le_left _ _))
    have hρU : ρ ≤ εU := le_of_lt (lt_of_lt_of_le hρlt (min_le_right _ _))
    obtain ⟨hqL, _, _⟩ := hspecL ρ hρ hρL
    obtain ⟨hqU', _, _⟩ := hspecU ρ hρ hρU
    have hcircles : ∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f := by
      intro b θ
      have h := hmem b θ ρ hρ le_rfl
      have heq : (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val =
          (P.twoCenterPolarPoint i b θ ρ hρ hρr).val := rfl
      rw [heq]
      exact h
    have hcandidate := P.componentTwoCenterSmallDiskConnectorCandidate_mem
      i ρ hρ hρr hsegment hcircles
    have hqLeft : q.1 = twoPuncturedDiskLeftCenter q.1.im := by
      apply Complex.ext
      · simpa [twoPuncturedDiskLeftCenter] using hqre
      · simp [twoPuncturedDiskLeftCenter]
    have hpRight : p.1 = twoPuncturedDiskRightCenter p.1.im := by
      apply Complex.ext
      · simpa [twoPuncturedDiskRightCenter] using hpre
      · simp [twoPuncturedDiskRightCenter]
    have hLowerU : twoPuncturedDiskLowerBase q.1.im p.1.im ⊆ U := by
      intro z hz
      exact hunit hz.1
    have hUpperU : twoPuncturedDiskUpperBase q.1.im p.1.im ⊆ U := by
      intro z hz
      exact hunit hz.1
    have hballRight : Metric.ball p.1 δU ⊆
        twoPuncturedDiskUpperBase q.1.im p.1.im := by
      have hballEq : Metric.ball p.1 δU =
          Metric.ball (twoPuncturedDiskRightCenter p.1.im) δU :=
        congrArg (fun z : ℂ => Metric.ball z δU) hpRight
      rw [hballEq]
      exact hballU'
    have hballLeft : Metric.ball q.1 δL ⊆
        twoPuncturedDiskLowerBase q.1.im p.1.im := by
      have hballEq : Metric.ball q.1 δL =
          Metric.ball (twoPuncturedDiskLeftCenter q.1.im) δL :=
        congrArg (fun z : ℂ => Metric.ball z δL) hqLeft
      rw [hballEq]
      exact hballL
    have hqFermiRight : ∀ θ : Circle,
        ‖fermiPositivePolarCoordinate (m + a * p.1.im) a b ha hb ρ θ‖ < δU := by
      intro θ
      simpa [twoPuncturedDiskRightCenter] using hqU' θ
    have hqFermiLeft : ∀ θ : Circle,
        ‖fermiPositivePolarCoordinate (m + a * q.1.im) a b ha hb ρ θ‖ < δL := by
      intro θ
      simpa [twoPuncturedDiskLeftCenter] using hqL θ
    have hpB : p.1 ∈ twoPuncturedDiskUpperBase q.1.im p.1.im := by
      simpa only [← hpRight] using
        (twoPuncturedDiskRightCenter_mem_upperBase hpBounds.1 hpBounds.2 hqpOrder)
    have hqB : q.1 ∈ twoPuncturedDiskLowerBase q.1.im p.1.im := by
      simpa only [← hqLeft] using
        (twoPuncturedDiskLeftCenter_mem_lowerBase hqBounds.1 hqBounds.2 hqpOrder)
    have hleftOther : ∀ z : ℂ,
        z ∈ twoPuncturedDiskUpperBase q.1.im p.1.im → z ≠ q.1 := by
      intro z hz heq
      have hcenter : z = twoPuncturedDiskLeftCenter q.1.im := heq.trans hqLeft
      exact twoPuncturedDiskLeftCenter_not_upperBase hqpOrder (by
        rw [← hcenter]
        exact hz)
    have hrightOther : ∀ z : ℂ,
        z ∈ twoPuncturedDiskLowerBase q.1.im p.1.im → z ≠ p.1 := by
      intro z hz heq
      have hcenter : z = twoPuncturedDiskRightCenter p.1.im := heq.trans hpRight
      exact twoPuncturedDiskRightCenter_not_lowerBase hqpOrder (by
        rw [← hcenter]
        exact hz)
    have hnot : ¬ p.1.im < q.1.im := not_lt_of_ge hqpOrder.le
    have hcomparison : Nonempty (TwoCenterPolarSideComparisonData p q m a b ρ ha hb) :=
      ⟨⟨δU, δL, hδU, hδL,
        by simpa only [if_neg hnot] using hballRight,
        by simpa only [if_neg hnot] using hballLeft,
        hqFermiRight, hqFermiLeft⟩⟩
    refine ⟨ρ, hρ, hρr, hcircles, hcandidate, hcomparison,
      Or.inr ⟨hqpOrder, ?_, ?_⟩⟩
    · intro θ
      exact P.componentTwoCenterLeftPolarPoint_mem_upperSide i hballU f hf p q
        hpMap hqMap hpre hqre hi hnext γ m a b ha hb hformula hleft
        hUpperU hpB q.2 hleftOther ρ δU hρ hρr hballRight hqFermiRight θ
    · intro θ
      exact P.componentTwoCenterRightPolarPoint_mem_lowerSide i hballU f hf p q
        hpMap hqMap hpre hqre hi hnext γ m a b ha hb hformula hright
        hLowerU hqB p.2 hrightOther ρ δL hρ hρr hballLeft hqFermiLeft θ

/-- The original side-containment contract, projected from the
certificate-retaining selector without changing its radius or endpoints. -/
theorem exists_componentTwoCenterPolarArcs_mem_relativeSides
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
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
      P.componentCenterGeodPoint i t ∈ embeddedCoordinatePunctureDisk f) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ t : I,
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      ((p.1.im < q.1.im ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide p.1.im q.1.im) ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide p.1.im q.1.im)) ∨
       (q.1.im < p.1.im ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i true ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide q.1.im p.1.im) ∧
        (∀ θ : Circle,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap (P.twoCenterPolarBoundaryMap i false ρ hρ hρr θ) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide q.1.im p.1.im))) := by
  obtain ⟨ρ, hρ, hρr, hcircles, hcandidate, _hcomparison, horder⟩ :=
    P.exists_componentTwoCenterPolarArcs_mem_relativeSides_with_comparisonData
      i hU hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext
      γ m a b ha hb hformula hleft hright hsegment
  exact ⟨ρ, hρ, hρr, hcircles, hcandidate, horder⟩

/-- The native cut point, viewed in the actual relative local-disk carrier,
has the coordinate given by the affine axis segment between the two chart
punctures. -/
theorem componentTwoCenterCutPoint_relativeLocalDiskUnit_coordinate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (t : I) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.componentPunctureInclusion i (P.componentTwoCenterCutArc i t)) ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hball hpre hqre y : ℂ) =
        (((1 - ((P.componentTwoCenterCutCoordinate i t : I) : ℝ)) * p.1.im +
          ((P.componentTwoCenterCutCoordinate i t : I) : ℝ) * q.1.im : ℝ) : ℂ) *
            Complex.I := by
  let s := P.componentTwoCenterCutCoordinate i t
  obtain ⟨z, hzval, hznorm, hfz⟩ := hchartSegment s
  let native := P.componentPunctureInclusion i (P.componentTwoCenterCutArc i t)
  let ambient := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
    hpMap hqMap native
  have hambientVal : ambient.1 = P.componentCenterGeodPoint i s := by
    change P.componentTwoCenterCutPoint i t = P.componentCenterGeodPoint i s
    rfl
  have himage : f z = ambient.1 := hfz.trans hambientVal.symm
  have hlocal : ambient.1 ∈ embeddedTwoPunctureLocalDisk f p q 1 := by
    change ambient.1 ∈ f '' {w : U | ‖w.1‖ < 1} ∩
      embeddedTwoPunctureAmbient f p q
    exact ⟨⟨z, hznorm, himage⟩, ambient.2⟩
  have hrelative : ambient ∈
      embeddedTwoPunctureLocalDiskRelativeSide f p q 1 := hlocal
  let y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1} := ⟨ambient, hrelative⟩
  have hcoordinate := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q 1 one_pos hball hpre hqre ambient hrelative z hznorm himage
  refine ⟨y, rfl, ?_⟩
  simpa [y, hzval] using hcoordinate

/-- The two actual quotient centers are distinct, with positive distance,
from the existing outer-plus-inner radius separation estimate. -/
private theorem componentTwoCenterCarrierDistance_pos
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    0 < dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2) := by
  have hR : 0 < gluingEmbeddedRadius C g + gluingRadius C g := by
    have := P.radius_lt_embeddedRadius
    linarith [P.radius_pos]
  exact lt_of_lt_of_le hR (P.carrier_centers_outer_add_inner_le_dist i)

/-- The same coordinate bridge for an arbitrary interior point of the
minimizing geodesic. It packages actual center-punctured membership, so it is
also available for the two radial connector tracks. -/
theorem componentTwoCenterGeodPoint_relativeLocalDiskUnit_coordinate
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (s : I) (hs0 : 0 < (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap ⟨P.componentCenterGeodPoint i s, by
          rw [P.componentCenterPuncturedSet_eq i]
          simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
            if_pos hi, if_pos hnext, not_or]
          constructor
          · intro heq
            have hformula : dist (P.componentCenterGeodPoint i s)
                (Quotient.mk'' (P.centers i).1 : (X i).Carrier) =
                  (s : ℝ) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                    (Quotient.mk'' (P.centers i).2) := by
              rw [← P.componentCenterGeodPoint_zero i, P.componentCenterGeodPoint_dist]
              simp [abs_of_nonneg s.2.1]
            rw [heq, dist_self] at hformula
            nlinarith [componentTwoCenterCarrierDistance_pos P i, hs0]
          · intro heq
            have hformula : dist (P.componentCenterGeodPoint i s)
                (Quotient.mk'' (P.centers i).2 : (X i).Carrier) =
                  (1 - (s : ℝ)) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                    (Quotient.mk'' (P.centers i).2) := by
              rw [← P.componentCenterGeodPoint_one i, P.componentCenterGeodPoint_dist]
              simp [abs_of_nonpos (sub_nonpos.mpr s.2.2)]
            rw [heq, dist_self] at hformula
            nlinarith [componentTwoCenterCarrierDistance_pos P i, hs1]⟩ ∧
      (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
        f hf p q 1 one_pos hball hpre hqre y : ℂ) =
        (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I := by
  obtain ⟨z, hzval, hznorm, hfz⟩ := hchartSegment s
  let native : P.CenterPuncturedChainComponent i :=
    ⟨P.componentCenterGeodPoint i s, by
      rw [P.componentCenterPuncturedSet_eq i]
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
        if_pos hi, if_pos hnext, not_or]
      constructor
      · intro heq
        have hformula : dist (P.componentCenterGeodPoint i s)
            (Quotient.mk'' (P.centers i).1 : (X i).Carrier) =
              (s : ℝ) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                (Quotient.mk'' (P.centers i).2) := by
          rw [← P.componentCenterGeodPoint_zero i, P.componentCenterGeodPoint_dist]
          simp [abs_of_nonneg s.2.1]
        rw [heq, dist_self] at hformula
        nlinarith [componentTwoCenterCarrierDistance_pos P i, hs0]
      · intro heq
        have hformula : dist (P.componentCenterGeodPoint i s)
            (Quotient.mk'' (P.centers i).2 : (X i).Carrier) =
              (1 - (s : ℝ)) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                (Quotient.mk'' (P.centers i).2) := by
          rw [← P.componentCenterGeodPoint_one i, P.componentCenterGeodPoint_dist]
          simp [abs_of_nonpos (sub_nonpos.mpr s.2.2)]
        rw [heq, dist_self] at hformula
        nlinarith [componentTwoCenterCarrierDistance_pos P i, hs1]⟩
  let ambient := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
    hpMap hqMap native
  have hambientVal : ambient.1 = P.componentCenterGeodPoint i s := rfl
  have himage : f z = ambient.1 := hfz.trans hambientVal.symm
  have hlocal : ambient.1 ∈ embeddedTwoPunctureLocalDisk f p q 1 := by
    change ambient.1 ∈ f '' {w : U | ‖w.1‖ < 1} ∩
      embeddedTwoPunctureAmbient f p q
    exact ⟨⟨z, hznorm, himage⟩, ambient.2⟩
  have hrelative : ambient ∈
      embeddedTwoPunctureLocalDiskRelativeSide f p q 1 := hlocal
  let y : {w : embeddedTwoPunctureAmbientPoint f p q //
      w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1} := ⟨ambient, hrelative⟩
  have hcoordinate := embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph_chartImage
    f hf p q 1 one_pos hball hpre hqre ambient hrelative z hznorm himage
  refine ⟨y, rfl, ?_⟩
  simpa [y, hzval] using hcoordinate

/-- An actual interior point on the first half of the minimizing segment lies
in the side containing the first chart puncture. -/
theorem componentTwoCenterGeodPoint_firstHalf_mem_side
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (s : I) (hs0 : 0 < (s : ℝ)) (hs : (s : ℝ) ≤ 1 / 2) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap ⟨P.componentCenterGeodPoint i s, by
          rw [P.componentCenterPuncturedSet_eq i]
          simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
            if_pos hi, if_pos hnext, not_or]
          constructor
          · intro heq
            have hformula : dist (P.componentCenterGeodPoint i s)
                (Quotient.mk'' (P.centers i).1 : (X i).Carrier) =
                  (s : ℝ) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                    (Quotient.mk'' (P.centers i).2) := by
              rw [← P.componentCenterGeodPoint_zero i, P.componentCenterGeodPoint_dist]
              simp [abs_of_nonneg s.2.1]
            rw [heq, dist_self] at hformula
            nlinarith [componentTwoCenterCarrierDistance_pos P i, hs0]
          · intro heq
            have hformula : dist (P.componentCenterGeodPoint i s)
                (Quotient.mk'' (P.centers i).2 : (X i).Carrier) =
                  (1 - (s : ℝ)) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                    (Quotient.mk'' (P.centers i).2) := by
              rw [← P.componentCenterGeodPoint_one i, P.componentCenterGeodPoint_dist]
              simp [abs_of_nonpos (sub_nonpos.mpr s.2.2)]
            rw [heq, dist_self] at hformula
            nlinarith [componentTwoCenterCarrierDistance_pos P i, s.2.2]⟩ ∧
      ((p.1.im < q.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1)) ∨
       (q.1.im < p.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1))) := by
  have hslt : (s : ℝ) < 1 := lt_of_le_of_lt hs (by norm_num)
  obtain ⟨y, hy, hcoord⟩ := P.componentTwoCenterGeodPoint_relativeLocalDiskUnit_coordinate
    i hball f hf p q hpMap hqMap hpre hqre hi hnext hchartSegment s hs0 hslt
  have himne : p.1.im ≠ q.1.im := by
    intro h
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact h
  have hpabs : |p.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hp
  have hqabs : |q.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hq
  rcases lt_or_gt_of_ne himne with hpLower | hqLower
  · have hpBounds := abs_lt.mp hpabs
    have hqBounds := abs_lt.mp hqabs
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_lowerSide
      hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2 hpLower s hs0 hs
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_left hpLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_right hpLower.le]
    refine ⟨y, hy, Or.inl ⟨hpLower, ?_⟩⟩
    rw [hcoord, hparamsL, hparamsU]
    exact hside
  · have hqBounds := abs_lt.mp hqabs
    have hpBounds := abs_lt.mp hpabs
    let u : I := ⟨1 - (s : ℝ), by constructor <;> linarith [hs0, hslt]⟩
    have humid : 1 / 2 ≤ (u : ℝ) := by dsimp [u]; linarith
    have hu1 : (u : ℝ) < 1 := by dsimp [u]; linarith [hs0]
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_upperSide
      hqBounds.1 hqBounds.2 hpBounds.1 hpBounds.2 hqLower u humid hu1
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_right hqLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_left hqLower.le]
    have hflip : (1 - (u : ℝ)) * q.1.im + (u : ℝ) * p.1.im =
        (1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im := by
      dsimp [u]
      ring
    have hflipC := congrArg (fun y : ℝ => (y : ℂ) * Complex.I) hflip
    refine ⟨y, hy, Or.inr ⟨hqLower, ?_⟩⟩
    rw [hcoord, ← hflipC, hparamsL, hparamsU]
    exact hside

/-- An actual interior point on the second half of the minimizing segment
lies in the side containing the second chart puncture. -/
theorem componentTwoCenterGeodPoint_secondHalf_mem_side
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (s : I) (hs : 1 / 2 ≤ (s : ℝ)) (hs1 : (s : ℝ) < 1) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap ⟨P.componentCenterGeodPoint i s, by
          rw [P.componentCenterPuncturedSet_eq i]
          simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
            if_pos hi, if_pos hnext, not_or]
          constructor
          · intro heq
            have hformula : dist (P.componentCenterGeodPoint i s)
                (Quotient.mk'' (P.centers i).1 : (X i).Carrier) =
                  (s : ℝ) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                    (Quotient.mk'' (P.centers i).2) := by
              rw [← P.componentCenterGeodPoint_zero i, P.componentCenterGeodPoint_dist]
              simp [abs_of_nonneg s.2.1]
            rw [heq, dist_self] at hformula
            nlinarith [componentTwoCenterCarrierDistance_pos P i, s.2.1]
          · intro heq
            have hformula : dist (P.componentCenterGeodPoint i s)
                (Quotient.mk'' (P.centers i).2 : (X i).Carrier) =
                  (1 - (s : ℝ)) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
                    (Quotient.mk'' (P.centers i).2) := by
              rw [← P.componentCenterGeodPoint_one i, P.componentCenterGeodPoint_dist]
              simp [abs_of_nonpos (sub_nonpos.mpr s.2.2)]
            rw [heq, dist_self] at hformula
            nlinarith [componentTwoCenterCarrierDistance_pos P i, hs1]⟩ ∧
      ((p.1.im < q.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1)) ∨
       (q.1.im < p.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1))) := by
  obtain ⟨y, hy, hcoord⟩ := P.componentTwoCenterGeodPoint_relativeLocalDiskUnit_coordinate
    i hball f hf p q hpMap hqMap hpre hqre hi hnext hchartSegment s
    (by linarith [hs]) hs1
  have himne : p.1.im ≠ q.1.im := by
    intro h
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact h
  have hpabs : |p.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hp
  have hqabs : |q.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hq
  rcases lt_or_gt_of_ne himne with hpLower | hqLower
  · have hpBounds := abs_lt.mp hpabs
    have hqBounds := abs_lt.mp hqabs
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_upperSide
      hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2 hpLower s hs hs1
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_left hpLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_right hpLower.le]
    refine ⟨y, hy, Or.inl ⟨hpLower, ?_⟩⟩
    rw [hcoord, hparamsL, hparamsU]
    exact hside
  · have hqBounds := abs_lt.mp hqabs
    have hpBounds := abs_lt.mp hpabs
    let u : I := ⟨1 - (s : ℝ), by constructor <;> linarith [hs1]⟩
    have hu0 : 0 < (u : ℝ) := by dsimp [u]; linarith [hs1]
    have huhalf : (u : ℝ) ≤ 1 / 2 := by dsimp [u]; linarith [hs]
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_lowerSide
      hqBounds.1 hqBounds.2 hpBounds.1 hpBounds.2 hqLower u hu0 huhalf
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_right hqLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_left hqLower.le]
    have hflip : (1 - (u : ℝ)) * q.1.im + (u : ℝ) * p.1.im =
        (1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im := by
      dsimp [u]
      ring
    have hflipC := congrArg (fun y : ℝ => (y : ℂ) * Complex.I) hflip
    refine ⟨y, hy, Or.inr ⟨hqLower, ?_⟩⟩
    rw [hcoord, ← hflipC, hparamsL, hparamsU]
    exact hside

/-- A left cut-direction polar point of radius at most the gluing radius is
the quotient of an actual point on the first half of the minimizing segment.
The parameter bound follows from its exact hyperbolic radius. -/
theorem componentTwoCenterLeftPolarRadius_geodParameter
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    ∃ s : I, 0 < (s : ℝ) ∧ (s : ℝ) ≤ 1 / 2 ∧
      (Quotient.mk'' (gluingPolarPoint (P.centers i).1
        (P.componentTwoCenterCutLeftAngle i) ρ) : (X i).Carrier) =
        P.componentCenterGeodPoint i s := by
  let p := (P.centers i).1
  let q := P.componentCenterClosestDeck i • (P.centers i).2
  let θ := P.componentTwoCenterCutLeftAngle i
  let D := dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
    (Quotient.mk'' (P.centers i).2)
  have hseg := P.componentTwoCenterLeftPolarRadius_mem_centerGeodesic i hρ hρr
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hseg
  obtain ⟨t, ht, hEq⟩ := hseg
  let s : I := ⟨t, ht⟩
  have hD : dist p q = D := by
    have hchoose : (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 =
        dist p q := by
      dsimp [p, q, componentCenterClosestDeck]
      exact Classical.choose_spec
        ((X i).exists_liftOrbitDist_eq_dist (P.centers i).1 (P.centers i).2)
    calc
      dist p q = (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 := hchoose.symm
      _ = D := by dsimp [D]
  have hmul : t * D = ρ := by
    calc
      t * D = t * dist p q := by rw [hD]
      _ = dist p (Vendored.RiemannDynamics.geodInterp p q t) :=
        (Vendored.RiemannDynamics.dist_geodInterp_left p q ht).symm
      _ = dist p (gluingPolarPoint p θ ρ) := by
        exact congrArg (dist p) hEq
      _ = ρ := dist_gluingPolarPoint p θ hρ.le
  have hDpos : 0 < D := componentTwoCenterCarrierDistance_pos P i
  have hDdouble : 2 * gluingRadius C g < D := by
    have hsep := P.carrier_centers_outer_add_inner_le_dist i
    have hrad := P.radius_lt_embeddedRadius
    dsimp [D, gluingEmbeddedRadius] at hsep hrad ⊢
    nlinarith [P.radius_pos, P.depth_pos]
  have htpos : 0 < t := by
    by_contra hn
    have htn : t ≤ 0 := le_of_not_gt hn
    nlinarith [hmul, hρ, hDpos]
  have hthalf : t ≤ 1 / 2 := by
    by_contra hn
    have hgt : 1 / 2 < t := lt_of_not_ge hn
    have hmulgt := mul_lt_mul_of_pos_right hgt hDpos
    have : (1 / 2) * D < ρ := by nlinarith [hmul, hmulgt]
    nlinarith [this, hDdouble, hρr]
  refine ⟨s, ?_, ?_, ?_⟩
  · exact htpos
  · exact hthalf
  · change Quotient.mk'' (gluingPolarPoint p θ ρ) =
      Quotient.mk'' (Vendored.RiemannDynamics.geodInterp p q t)
    exact congrArg Quotient.mk'' hEq.symm

/-- A right cut-direction polar point of radius at most the gluing radius is
the quotient of an actual point on the second half of the minimizing segment.
The closest-deck phase is retained in the lifted calculation and removed only
by the quotient map. -/
theorem componentTwoCenterRightPolarRadius_geodParameter
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    ∃ s : I, 1 / 2 ≤ (s : ℝ) ∧ (s : ℝ) < 1 ∧
      (Quotient.mk'' (gluingPolarPoint (P.centers i).2
        (P.componentTwoCenterCutRightAngle i) ρ) : (X i).Carrier) =
        P.componentCenterGeodPoint i s := by
  let p := (P.centers i).1
  let q := P.componentCenterClosestDeck i • (P.centers i).2
  let δ := P.componentCenterClosestDeck i
  let θ := gluingPolarSLPhase δ (P.centers i).2 *
    P.componentTwoCenterCutRightAngle i
  let w := gluingPolarPoint (P.centers i).2
    (P.componentTwoCenterCutRightAngle i) ρ
  have hseg := P.componentTwoCenterRightPolarRadius_mem_centerGeodesic i hρ hρr
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hseg
  obtain ⟨t, ht, hEq⟩ := hseg
  let s : I := ⟨t, ht⟩
  have hpolar : δ • w = gluingPolarPoint q θ ρ := by
    exact gluingPolarPoint_smul (↑δ) (P.centers i).2
      (P.componentTwoCenterCutRightAngle i) ρ
  have hproj : (Quotient.mk'' (δ • w) : (X i).Carrier) =
      Quotient.mk'' w := by
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨δ, rfl⟩)
  have hquot : (Quotient.mk'' (gluingPolarPoint q θ ρ) : (X i).Carrier) =
      Quotient.mk'' w := by
    rw [← hpolar]
    exact hproj
  have hpoint : (Quotient.mk'' w : (X i).Carrier) =
      P.componentCenterGeodPoint i s := by
    change (Quotient.mk'' w : (X i).Carrier) =
      Quotient.mk'' (Vendored.RiemannDynamics.geodInterp p q t)
    calc
      Quotient.mk'' w = Quotient.mk'' (gluingPolarPoint q θ ρ) := hquot.symm
      _ = Quotient.mk'' (Vendored.RiemannDynamics.geodInterp p q t) :=
        congrArg Quotient.mk'' hEq.symm
  have hρR : ρ < gluingEmbeddedRadius C g :=
    lt_of_le_of_lt hρr P.radius_lt_embeddedRadius
  have hpolarDist : dist (Quotient.mk'' w : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2) = ρ := by
    rw [dist_comm]
    rw [(X i).carrier_dist_mk_center_eq_of_mem_closedBall
      (P.centers i).2 (gluingEmbeddedRadius C g) (P.twice_outer_lt_systole i)]
    · simpa [w] using (dist_gluingPolarPoint (P.centers i).2
        (P.componentTwoCenterCutRightAngle i) hρ.le)
    · change gluingPolarPoint (P.centers i).2
        (P.componentTwoCenterCutRightAngle i) ρ ∈
          Metric.closedBall (P.centers i).2 (gluingEmbeddedRadius C g)
      rw [mem_closedBall, dist_comm,
        dist_gluingPolarPoint (P.centers i).2
          (P.componentTwoCenterCutRightAngle i) hρ.le]
      exact hρR.le
  have hgeodDist : dist (P.componentCenterGeodPoint i s)
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) =
        (1 - (s : ℝ)) * dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
          (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
    rw [← P.componentCenterGeodPoint_one i, P.componentCenterGeodPoint_dist]
    simp [abs_of_nonpos (sub_nonpos.mpr s.2.2)]
  have hparameter : (1 - (s : ℝ)) *
      dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (P.centers i).2 : (X i).Carrier) = ρ := by
    have h := congrArg (fun x : (X i).Carrier =>
      dist x (Quotient.mk'' (P.centers i).2 : (X i).Carrier)) hpoint
    rw [hpolarDist, hgeodDist] at h
    exact h.symm
  have hparameter' : (1 - t) *
      dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (P.centers i).2 : (X i).Carrier) = ρ := by
    simpa [s] using hparameter
  have hDpos : 0 < dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) :=
    componentTwoCenterCarrierDistance_pos P i
  have hDdouble : 2 * gluingRadius C g <
      dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
        (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
    have hsep := P.carrier_centers_outer_add_inner_le_dist i
    have hrad := P.radius_lt_embeddedRadius
    dsimp [gluingEmbeddedRadius] at hsep hrad ⊢
    nlinarith [P.radius_pos, P.depth_pos]
  have htlt : t < 1 := by
    by_contra hn
    have htn : 1 ≤ t := le_of_not_gt hn
    nlinarith [hparameter']
  have hthalf : 1 / 2 ≤ t := by
    by_contra hn
    have hbelow : t < 1 / 2 := lt_of_not_ge hn
    have hfactor : 1 / 2 < 1 - t := by linarith
    have hmul := mul_lt_mul_of_pos_right hfactor hDpos
    nlinarith [hparameter', hDdouble, hρr]
  exact ⟨s, hthalf, htlt, hpoint⟩

/-- Every point of the actual left radial connector track is represented in
the relative local-disk cover member on the side of the left chart puncture.
The equality is for the literal native radius homotopy path. -/
theorem componentTwoCenterLeftRadiusTrack_point_mem_side
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) (τ : I) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap
          ((P.twoCenterPolarRadiusHomotopy i true ρ (gluingRadius C g)
            hρ P.radius_pos hρr le_rfl).evalAt
              (P.componentTwoCenterCutLeftAngle i) τ) ∧
      ((p.1.im < q.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1)) ∨
       (q.1.im < p.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1))) := by
  let ρτ := (1 - (τ : ℝ)) * ρ + (τ : ℝ) * gluingRadius C g
  have hρτ : 0 < ρτ := by
    dsimp [ρτ]
    nlinarith [mul_nonneg (sub_nonneg.mpr τ.2.2) hρ.le,
      mul_nonneg τ.2.1 P.radius_pos.le]
  have hρτr : ρτ ≤ gluingRadius C g := by
    dsimp [ρτ]
    nlinarith [mul_nonneg (sub_nonneg.mpr τ.2.2) (sub_nonneg.mpr hρr)]
  obtain ⟨s, hs0, hsHalf, hpoint⟩ :=
    P.componentTwoCenterLeftPolarRadius_geodParameter i hρτ hρτr
  obtain ⟨y, hy, hside⟩ := P.componentTwoCenterGeodPoint_firstHalf_mem_side
    i hball f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment
    s hs0 hsHalf
  let γ := (P.twoCenterPolarRadiusHomotopy i true ρ (gluingRadius C g)
    hρ P.radius_pos hρr le_rfl).evalAt (P.componentTwoCenterCutLeftAngle i)
  have htrack : (γ τ).1 =
      (Quotient.mk'' (gluingPolarPoint (P.centers i).1
        (P.componentTwoCenterCutLeftAngle i) ρτ) : (X i).Carrier) := by
    change (Quotient.mk'' (gluingPolarPoint (P.centers i).1
      (P.componentTwoCenterCutLeftAngle i)
      ((1 - (τ : ℝ)) * ρ + (τ : ℝ) * gluingRadius C g)) : (X i).Carrier) = _
    rfl
  have htrackPoint : (γ τ).1 = P.componentCenterGeodPoint i s := htrack.trans hpoint
  refine ⟨y, ?_, hside⟩
  apply Subtype.ext
  have hyval : y.1.1 = P.componentCenterGeodPoint i s := by
    simpa only [P.internalCenterPuncturedAmbientHomeomorph_apply_val] using
      congrArg Subtype.val hy
  simpa only [P.internalCenterPuncturedAmbientHomeomorph_apply_val] using
    hyval.trans htrackPoint.symm

/-- Every point of the actual right radial connector track is represented in
the relative local-disk cover member on the side of the right chart puncture,
with the selected closest-deck phase already removed in the quotient. -/
theorem componentTwoCenterRightRadiusTrack_point_mem_side
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) (τ : I) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap
          ((P.twoCenterPolarRadiusHomotopy i false (gluingRadius C g) ρ
            P.radius_pos hρ le_rfl hρr).evalAt
              (P.componentTwoCenterCutRightAngle i) τ) ∧
      ((p.1.im < q.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1)) ∨
       (q.1.im < p.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1))) := by
  let ρτ := (1 - (τ : ℝ)) * gluingRadius C g + (τ : ℝ) * ρ
  have hρτ : 0 < ρτ := by
    dsimp [ρτ]
    nlinarith [mul_nonneg (sub_nonneg.mpr τ.2.2) P.radius_pos.le,
      mul_nonneg τ.2.1 hρ.le]
  have hρτr : ρτ ≤ gluingRadius C g := by
    dsimp [ρτ]
    nlinarith [mul_nonneg τ.2.1 (sub_nonneg.mpr hρr)]
  obtain ⟨s, hsHalf, hs1, hpoint⟩ :=
    P.componentTwoCenterRightPolarRadius_geodParameter i hρτ hρτr
  obtain ⟨y, hy, hside⟩ := P.componentTwoCenterGeodPoint_secondHalf_mem_side
    i hball f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment
    s hsHalf hs1
  let γ := (P.twoCenterPolarRadiusHomotopy i false (gluingRadius C g) ρ
    P.radius_pos hρ le_rfl hρr).evalAt (P.componentTwoCenterCutRightAngle i)
  have htrack : (γ τ).1 =
      (Quotient.mk'' (gluingPolarPoint (P.centers i).2
        (P.componentTwoCenterCutRightAngle i) ρτ) : (X i).Carrier) := by
    change (Quotient.mk'' (gluingPolarPoint (P.centers i).2
      (P.componentTwoCenterCutRightAngle i)
      ((1 - (τ : ℝ)) * gluingRadius C g + (τ : ℝ) * ρ)) : (X i).Carrier) = _
    rfl
  have htrackPoint : (γ τ).1 = P.componentCenterGeodPoint i s := htrack.trans hpoint
  refine ⟨y, ?_, hside⟩
  apply Subtype.ext
  have hyval : y.1.1 = P.componentCenterGeodPoint i s := by
    simpa only [P.internalCenterPuncturedAmbientHomeomorph_apply_val] using
      congrArg Subtype.val hy
  simpa only [P.internalCenterPuncturedAmbientHomeomorph_apply_val] using
    hyval.trans htrackPoint.symm

/-- Every point of the first half of the actual center cut lies in the side
containing the first chart puncture; the lower/upper choice follows the actual
order of the two original chart centers. -/
theorem componentTwoCenterCutPoint_firstHalf_mem_side
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.componentPunctureInclusion i (P.componentTwoCenterCutArc i t)) ∧
      ((p.1.im < q.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1)) ∨
       (q.1.im < p.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1))) := by
  let s := P.componentTwoCenterCutCoordinate i t
  have hs := P.componentTwoCenterCutCoordinate_half_bounds i t
  have hslt := hs.2.1
  have hspos := hs.1
  have hsle : (s : ℝ) ≤ 1 / 2 := hs.2.2.1 ht
  obtain ⟨y, hy, hcoord⟩ := P.componentTwoCenterCutPoint_relativeLocalDiskUnit_coordinate
    i hball f hf p q hpMap hqMap hpre hqre hi hnext hchartSegment t
  have himne : p.1.im ≠ q.1.im := by
    intro h
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact h
  have hpabs : |p.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hp
  have hqabs : |q.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hq
  rcases lt_or_gt_of_ne himne with hpLower | hqLower
  · have hpBounds := abs_lt.mp hpabs
    have hqBounds := abs_lt.mp hqabs
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_lowerSide
      hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2 hpLower s hspos hsle
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_left hpLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_right hpLower.le]
    refine ⟨y, hy, Or.inl ⟨hpLower, ?_⟩⟩
    rw [hcoord, hparamsL, hparamsU]
    exact hside
  · have hqBounds := abs_lt.mp hqabs
    have hpBounds := abs_lt.mp hpabs
    let u : I := ⟨1 - (s : ℝ), by constructor <;> linarith [hspos, hslt]⟩
    have humid : 1 / 2 ≤ (u : ℝ) := by dsimp [u]; linarith
    have hu1 : (u : ℝ) < 1 := by dsimp [u]; linarith [hspos]
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_upperSide
      hqBounds.1 hqBounds.2 hpBounds.1 hpBounds.2 hqLower u humid hu1
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_right hqLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_left hqLower.le]
    have hflip : (1 - (u : ℝ)) * q.1.im + (u : ℝ) * p.1.im =
        (1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im := by
      dsimp [u]
      ring
    have hflipC := congrArg (fun y : ℝ => (y : ℂ) * Complex.I) hflip
    refine ⟨y, hy, Or.inr ⟨hqLower, ?_⟩⟩
    rw [hcoord, ← hflipC, hparamsL, hparamsU]
    exact hside

/-- Every point of the second half of the actual center cut lies in the side
containing the second chart puncture, again without choosing an artificial
ordering of the original centers. -/
theorem componentTwoCenterCutPoint_secondHalf_mem_side
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hball : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
    (hqMap : f q = (Quotient.mk'' (P.centers i).2 : (X i).Carrier))
    (hpre : p.1.re = 0) (hqre : q.1.re = 0)
    (hp : ‖p.1‖ < 1) (hq : ‖q.1‖ < 1) (hpq : p ≠ q)
    (hi : 0 < i.1) (hnext : i.1 + 1 < n)
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s)
    (t : I) (ht : 1 / 2 ≤ (t : ℝ)) :
    ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
        w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
      y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
        hpMap hqMap (P.componentPunctureInclusion i (P.componentTwoCenterCutArc i t)) ∧
      ((p.1.im < q.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskUpperSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1)) ∨
       (q.1.im < p.1.im ∧
        (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
          f hf p q 1 one_pos hball hpre hqre y : ℂ) ∈
            twoPuncturedDiskLowerSide
              (embeddedTwoPunctureLowerParameter p q 1)
              (embeddedTwoPunctureUpperParameter p q 1))) := by
  let s := P.componentTwoCenterCutCoordinate i t
  have hs := P.componentTwoCenterCutCoordinate_half_bounds i t
  have hslt := hs.2.1
  have hspos := hs.1
  have hsge : 1 / 2 ≤ (s : ℝ) := hs.2.2.2 ht
  obtain ⟨y, hy, hcoord⟩ := P.componentTwoCenterCutPoint_relativeLocalDiskUnit_coordinate
    i hball f hf p q hpMap hqMap hpre hqre hi hnext hchartSegment t
  have himne : p.1.im ≠ q.1.im := by
    intro h
    apply hpq
    apply Subtype.ext
    apply Complex.ext
    · exact hpre.trans hqre.symm
    · exact h
  have hpabs : |p.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hp
  have hqabs : |q.1.im| < 1 := (Complex.abs_im_le_norm _).trans_lt hq
  rcases lt_or_gt_of_ne himne with hpLower | hqLower
  · have hpBounds := abs_lt.mp hpabs
    have hqBounds := abs_lt.mp hqabs
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_upperSide
      hpBounds.1 hpBounds.2 hqBounds.1 hqBounds.2 hpLower s hsge hslt
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_left hpLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_right hpLower.le]
    refine ⟨y, hy, Or.inl ⟨hpLower, ?_⟩⟩
    rw [hcoord, hparamsL, hparamsU]
    exact hside
  · have hqBounds := abs_lt.mp hqabs
    have hpBounds := abs_lt.mp hpabs
    let u : I := ⟨1 - (s : ℝ), by constructor <;> linarith [hspos, hslt]⟩
    have hu0 : 0 < (u : ℝ) := by dsimp [u]; linarith [hslt]
    have humid : (u : ℝ) ≤ 1 / 2 := by dsimp [u]; linarith
    have hside := twoPuncturedDiskVerticalCenterSegment_mem_lowerSide
      hqBounds.1 hqBounds.2 hpBounds.1 hpBounds.2 hqLower u hu0 humid
    have hparamsL : embeddedTwoPunctureLowerParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_right hqLower.le]
    have hparamsU : embeddedTwoPunctureUpperParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_left hqLower.le]
    have hflip : (1 - (u : ℝ)) * q.1.im + (u : ℝ) * p.1.im =
        (1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im := by
      dsimp [u]
      ring
    have hflipC := congrArg (fun y : ℝ => (y : ℂ) * Complex.I) hflip
    refine ⟨y, hy, Or.inr ⟨hqLower, ?_⟩⟩
    rw [hcoord, ← hflipC, hparamsL, hparamsU]
    exact hside

private theorem nestedTrans_firstHalf_mem
    {α : Type*} [TopologicalSpace α]
    {a b c d e f : α}
    (A : Path a b) (B : Path b c) (C : Path c d)
    (D : Path d e) (E : Path e f) (Q : α → Prop)
    (hA : ∀ t : I, Q (A t)) (hB : ∀ t : I, Q (B t))
    (hC : ∀ t : I, (t : ℝ) ≤ 1 / 2 → Q (C t)) :
    ∀ t : I, (t : ℝ) ≤ 5 / 8 →
      Q (((A.trans B).trans (C.trans (D.trans E))) t) := by
  intro t ht
  by_cases houter : (t : ℝ) ≤ 1 / 2
  · let u : I := ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.2.1, houter]⟩
    have hu : (u : ℝ) ≤ 1 := by dsimp [u]; nlinarith [houter]
    rw [Path.trans_apply]
    simp only [dif_pos houter]
    change Q ((A.trans B) u)
    by_cases hinner : (u : ℝ) ≤ 1 / 2
    · rw [Path.trans_apply]
      simp only [dif_pos hinner]
      exact hA _
    · rw [Path.trans_apply]
      simp only [dif_neg hinner]
      exact hB _
  · let u : I := ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.2.1, houter]⟩
    have huHalf : (u : ℝ) ≤ 1 / 2 := by
      dsimp [u]
      nlinarith [ht]
    rw [Path.trans_apply]
    simp only [dif_neg houter]
    change Q ((C.trans (D.trans E)) u)
    rw [Path.trans_apply]
    simp only [dif_pos huHalf]
    let v : I := ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.2.1, huHalf]⟩
    have hvHalf : (v : ℝ) ≤ 1 / 2 := by
      dsimp [v]
      nlinarith [ht]
    change Q (C v)
    exact hC v hvHalf

private theorem nestedTrans_secondHalf_mem
    {α : Type*} [TopologicalSpace α]
    {a b c d e f : α}
    (A : Path a b) (B : Path b c) (C : Path c d)
    (D : Path d e) (E : Path e f) (Q : α → Prop)
    (hC : ∀ t : I, 1 / 2 ≤ (t : ℝ) → Q (C t))
    (hD : ∀ t : I, Q (D t)) (hE : ∀ t : I, Q (E t)) :
    ∀ t : I, 5 / 8 ≤ (t : ℝ) →
      Q (((A.trans B).trans (C.trans (D.trans E))) t) := by
  intro t ht
  have houter : ¬ (t : ℝ) ≤ 1 / 2 := by linarith
  let u : I := ⟨2 * (t : ℝ) - 1, by constructor <;> nlinarith [t.2.1, t.2.2, ht]⟩
  have huLower : 1 / 4 ≤ (u : ℝ) := by dsimp [u]; linarith
  rw [Path.trans_apply]
  simp only [dif_neg houter]
  change Q ((C.trans (D.trans E)) u)
  by_cases hmiddle : (u : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply]
    simp only [dif_pos hmiddle]
    let v : I := ⟨2 * (u : ℝ), by constructor <;> nlinarith [u.2.1, hmiddle]⟩
    have hvLower : 1 / 2 ≤ (v : ℝ) := by dsimp [v]; linarith [huLower]
    change Q (C v)
    exact hC v hvLower
  · rw [Path.trans_apply]
    simp only [dif_neg hmiddle]
    let v : I := ⟨2 * (u : ℝ) - 1, by constructor <;> nlinarith [u.2.1, u.2.2, hmiddle]⟩
    rw [Path.trans_apply]
    split_ifs with htail
    · exact hD _
    · exact hE _

private theorem componentTwoCenterSmallConnectorLeftHalf_apply
    {α : Type*} [TopologicalSpace α] {a b : α}
    (γ : Path a b) (t : I) :
    ((γ.subpath 0 componentTwoCenterSmallConnectorMidpointTime).cast
      (Path.source _).symm rfl) t =
      γ ⟨(5 / 8) * (t : ℝ), by constructor <;> nlinarith [t.2.1, t.2.2]⟩ := by
  apply congrArg γ
  apply Subtype.ext
  simp [componentTwoCenterSmallConnectorMidpointTime, Icc.convexComb]
  ring

private theorem componentTwoCenterSmallConnectorRightHalf_apply
    {α : Type*} [TopologicalSpace α] {a b : α}
    (γ : Path a b) (t : I) :
    ((γ.subpath componentTwoCenterSmallConnectorMidpointTime 1).cast
      rfl (Path.target _).symm) t =
      γ ⟨5 / 8 + (3 / 8) * (t : ℝ), by constructor <;> nlinarith [t.2.1, t.2.2]⟩ := by
  apply congrArg γ
  apply Subtype.ext
  simp [componentTwoCenterSmallConnectorMidpointTime, Icc.convexComb]
  ring

/-- The two literal half-paths of the selected small connector stay in their
actual relative local-disk sides. The side assignment follows the actual
vertical ordering of the chart centers, and the split uses the candidate's
exact global time `5/8`. -/
theorem exists_componentTwoCenterSmallConnector_halves_mem_relativeSides_with_comparisonData
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
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
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ t : I,
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      Nonempty (TwoCenterPolarSideComparisonData p q m a b ρ ha hb) ∧
      ((p.1.im < q.1.im ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide p.1.im q.1.im) ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide p.1.im q.1.im)) ∨
       (q.1.im < p.1.im ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide q.1.im p.1.im) ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide q.1.im p.1.im))) := by
  obtain ⟨ρ, hρ, hρr, hcircles, hcandidate, hcomparison, horder⟩ :=
    P.exists_componentTwoCenterPolarArcs_mem_relativeSides_with_comparisonData i hU hballU f hf p q
      hpMap hqMap hpre hqre hp hq hpq hi hnext γ m a b ha hb hformula
      hleft hright hsegment
  let θL := P.componentTwoCenterCutLeftAngle i
  let θR := P.componentTwoCenterCutRightAngle i
  let A := (Circle.path 1 θL).map
    (P.twoCenterPolarBoundaryMap i true ρ hρ hρr).continuous
  let B := (P.twoCenterPolarRadiusHomotopy i true ρ (gluingRadius C g)
    hρ P.radius_pos hρr le_rfl).evalAt θL
  let D := (P.twoCenterPolarRadiusHomotopy i false (gluingRadius C g) ρ
    P.radius_pos hρ le_rfl hρr).evalAt θR
  let E := (Circle.path θR 1).map
    (P.twoCenterPolarBoundaryMap i false ρ hρ hρr).continuous
  have hcutL : P.twoCenterPolarBoundaryMap i true
      (gluingRadius C g) P.radius_pos le_rfl θL =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
    rw [P.twoCenterPolarBoundaryMap_gluingRadius_left]
    exact (P.componentTwoCenterCutLeftAngle_spec i).trans
      (congrArg (P.componentPunctureInclusion i) (by rfl))
  have hcutR : P.twoCenterPolarBoundaryMap i false
      (gluingRadius C g) P.radius_pos le_rfl θR =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
    rw [P.twoCenterPolarBoundaryMap_gluingRadius_right]
    exact (P.componentTwoCenterCutRightAngle_spec i).trans
      (congrArg (P.componentPunctureInclusion i) (by rfl))
  let Cpath := ((P.componentTwoCenterCutArc i).map
    (P.componentPunctureInclusion i).continuous).cast hcutL hcutR
  have hCpathVal (t : I) : Cpath t =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i t) := rfl
  let candidate := P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr
  have hcandidateEq : candidate = ((A.trans B).trans (Cpath.trans (D.trans E))) := rfl
  have hleftEval (t : I) :
      (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr) t =
        candidate ⟨(5 / 8) * (t : ℝ), by
          constructor <;> nlinarith [t.2.1, t.2.2]⟩ := by
    simpa [componentTwoCenterSmallConnectorLeftHalf, candidate] using
      componentTwoCenterSmallConnectorLeftHalf_apply candidate t
  have hrightEval (t : I) :
      (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr) t =
        candidate ⟨5 / 8 + (3 / 8) * (t : ℝ), by
          constructor <;> nlinarith [t.2.1, t.2.2]⟩ := by
    simpa [componentTwoCenterSmallConnectorRightHalf, candidate] using
      componentTwoCenterSmallConnectorRightHalf_apply candidate t
  let H := P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext hpMap hqMap
  let LocalPoint := {w : embeddedTwoPunctureAmbientPoint f p q //
    w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1}
  let coord := fun (y : LocalPoint) =>
    (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
      f hf p q 1 one_pos hballU hpre hqre y : ℂ)
  let Q := fun (S : Set ℂ) (x : P.CenterPuncturedChainComponent i) =>
    ∃ y : LocalPoint, y.1 = H x ∧ coord y ∈ S
  rcases horder with horder | horder
  · rcases horder with ⟨hpqOrder, hleftCircle, hrightCircle⟩
    let Sleft := twoPuncturedDiskLowerSide p.1.im q.1.im
    let Sright := twoPuncturedDiskUpperSide p.1.im q.1.im
    have hparamL : embeddedTwoPunctureLowerParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_left hpqOrder.le]
    have hparamU : embeddedTwoPunctureUpperParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_right hpqOrder.le]
    have hA : ∀ t : I, Q Sleft (A t) := by
      intro t
      obtain ⟨y, hy, hcoord⟩ := hleftCircle ((Circle.path 1 θL) t)
      refine ⟨y, ?_, hcoord⟩
      simpa [A, H] using hy
    have hB : ∀ t : I, Q Sleft (B t) := by
      intro t
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterLeftRadiusTrack_point_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment
        ρ hρ hρr t
      have hcoord : coord y ∈ Sleft := by
        rcases hside with hcorrect | hwrong
        · exact (by simpa [Sleft, coord, hparamL, hparamU] using hcorrect.2)
        · exact False.elim (not_lt_of_ge hpqOrder.le hwrong.1)
      refine ⟨y, ?_, hcoord⟩
      simpa [B, H] using hy
    have hC : ∀ t : I, (t : ℝ) ≤ 1 / 2 → Q Sleft (Cpath t) := by
      intro t ht
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterCutPoint_firstHalf_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment t ht
      have hcoord : coord y ∈ Sleft := by
        rcases hside with hcorrect | hwrong
        · exact (by simpa [Sleft, coord, hparamL, hparamU] using hcorrect.2)
        · exact False.elim (not_lt_of_ge hpqOrder.le hwrong.1)
      refine ⟨y, ?_, hcoord⟩
      rw [hCpathVal]
      exact hy
    have hD : ∀ t : I, Q Sright (D t) := by
      intro t
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterRightRadiusTrack_point_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment
        ρ hρ hρr t
      have hcoord : coord y ∈ Sright := by
        rcases hside with hcorrect | hwrong
        · exact (by simpa [Sright, coord, hparamL, hparamU] using hcorrect.2)
        · exact False.elim (not_lt_of_ge hpqOrder.le hwrong.1)
      refine ⟨y, ?_, hcoord⟩
      simpa [D, H] using hy
    have hE : ∀ t : I, Q Sright (E t) := by
      intro t
      obtain ⟨y, hy, hcoord⟩ := hrightCircle ((Circle.path θR 1) t)
      refine ⟨y, ?_, hcoord⟩
      simpa [E, H] using hy
    have hCright : ∀ t : I, 1 / 2 ≤ (t : ℝ) → Q Sright (Cpath t) := by
      intro t ht
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterCutPoint_secondHalf_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment t ht
      have hcoord : coord y ∈ Sright := by
        rcases hside with hcorrect | hwrong
        · exact (by simpa [Sright, coord, hparamL, hparamU] using hcorrect.2)
        · exact False.elim (not_lt_of_ge hpqOrder.le hwrong.1)
      refine ⟨y, ?_, hcoord⟩
      rw [hCpathVal]
      exact hy
    have hleftNested : ∀ t : I, (t : ℝ) ≤ 5 / 8 → Q Sleft (candidate t) := by
      intro t ht
      rw [hcandidateEq]
      exact nestedTrans_firstHalf_mem A B Cpath D E (Q Sleft) hA hB hC t ht
    have hrightNested : ∀ t : I, 5 / 8 ≤ (t : ℝ) → Q Sright (candidate t) := by
      intro t ht
      rw [hcandidateEq]
      exact nestedTrans_secondHalf_mem A B Cpath D E (Q Sright) hCright hD hE t ht
    refine ⟨ρ, hρ, hρr, hcircles, hcandidate, hcomparison, Or.inl ⟨hpqOrder, ?_, ?_⟩⟩
    · intro t
      let u : I := ⟨(5 / 8) * (t : ℝ), by constructor <;> nlinarith [t.2.1, t.2.2]⟩
      obtain ⟨y, hy, hcoord⟩ := hleftNested u (by dsimp [u]; nlinarith [t.2.2])
      refine ⟨y, ?_, ?_⟩
      · simpa [hleftEval, u, H] using hy
      · simpa [coord, Sleft] using hcoord
    · intro t
      let u : I := ⟨5 / 8 + (3 / 8) * (t : ℝ), by
        constructor <;> nlinarith [t.2.1, t.2.2]⟩
      obtain ⟨y, hy, hcoord⟩ := hrightNested u (by dsimp [u]; nlinarith [t.2.1])
      refine ⟨y, ?_, ?_⟩
      · simpa [hrightEval, u, H] using hy
      · simpa [coord, Sright] using hcoord
  · rcases horder with ⟨hqpOrder, hleftCircle, hrightCircle⟩
    let Sleft := twoPuncturedDiskUpperSide q.1.im p.1.im
    let Sright := twoPuncturedDiskLowerSide q.1.im p.1.im
    have hparamL : embeddedTwoPunctureLowerParameter p q 1 = q.1.im := by
      simp [embeddedTwoPunctureLowerParameter, min_eq_right hqpOrder.le]
    have hparamU : embeddedTwoPunctureUpperParameter p q 1 = p.1.im := by
      simp [embeddedTwoPunctureUpperParameter, max_eq_left hqpOrder.le]
    have hA : ∀ t : I, Q Sleft (A t) := by
      intro t
      obtain ⟨y, hy, hcoord⟩ := hleftCircle ((Circle.path 1 θL) t)
      refine ⟨y, ?_, hcoord⟩
      simpa [A, H] using hy
    have hB : ∀ t : I, Q Sleft (B t) := by
      intro t
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterLeftRadiusTrack_point_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment
        ρ hρ hρr t
      have hcoord : coord y ∈ Sleft := by
        rcases hside with hwrong | hcorrect
        · exact False.elim (not_lt_of_ge hqpOrder.le hwrong.1)
        · exact (by simpa [Sleft, coord, hparamL, hparamU] using hcorrect.2)
      refine ⟨y, ?_, hcoord⟩
      simpa [B, H] using hy
    have hC : ∀ t : I, (t : ℝ) ≤ 1 / 2 → Q Sleft (Cpath t) := by
      intro t ht
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterCutPoint_firstHalf_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment t ht
      have hcoord : coord y ∈ Sleft := by
        rcases hside with hwrong | hcorrect
        · exact False.elim (not_lt_of_ge hqpOrder.le hwrong.1)
        · exact (by simpa [Sleft, coord, hparamL, hparamU] using hcorrect.2)
      refine ⟨y, ?_, hcoord⟩
      rw [hCpathVal]
      exact hy
    have hD : ∀ t : I, Q Sright (D t) := by
      intro t
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterRightRadiusTrack_point_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment
        ρ hρ hρr t
      have hcoord : coord y ∈ Sright := by
        rcases hside with hwrong | hcorrect
        · exact False.elim (not_lt_of_ge hqpOrder.le hwrong.1)
        · exact (by simpa [Sright, coord, hparamL, hparamU] using hcorrect.2)
      refine ⟨y, ?_, hcoord⟩
      simpa [D, H] using hy
    have hE : ∀ t : I, Q Sright (E t) := by
      intro t
      obtain ⟨y, hy, hcoord⟩ := hrightCircle ((Circle.path θR 1) t)
      refine ⟨y, ?_, hcoord⟩
      simpa [E, H] using hy
    have hCright : ∀ t : I, 1 / 2 ≤ (t : ℝ) → Q Sright (Cpath t) := by
      intro t ht
      obtain ⟨y, hy, hside⟩ := P.componentTwoCenterCutPoint_secondHalf_mem_side
        i hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext hchartSegment t ht
      have hcoord : coord y ∈ Sright := by
        rcases hside with hwrong | hcorrect
        · exact False.elim (not_lt_of_ge hqpOrder.le hwrong.1)
        · exact (by simpa [Sright, coord, hparamL, hparamU] using hcorrect.2)
      refine ⟨y, ?_, hcoord⟩
      rw [hCpathVal]
      exact hy
    have hleftNested : ∀ t : I, (t : ℝ) ≤ 5 / 8 → Q Sleft (candidate t) := by
      intro t ht
      rw [hcandidateEq]
      exact nestedTrans_firstHalf_mem A B Cpath D E (Q Sleft) hA hB hC t ht
    have hrightNested : ∀ t : I, 5 / 8 ≤ (t : ℝ) → Q Sright (candidate t) := by
      intro t ht
      rw [hcandidateEq]
      exact nestedTrans_secondHalf_mem A B Cpath D E (Q Sright) hCright hD hE t ht
    refine ⟨ρ, hρ, hρr, hcircles, hcandidate, hcomparison, Or.inr ⟨hqpOrder, ?_, ?_⟩⟩
    · intro t
      let u : I := ⟨(5 / 8) * (t : ℝ), by constructor <;> nlinarith [t.2.1, t.2.2]⟩
      obtain ⟨y, hy, hcoord⟩ := hleftNested u (by dsimp [u]; nlinarith [t.2.2])
      refine ⟨y, ?_, ?_⟩
      · simpa [hleftEval, u, H] using hy
      · simpa [coord, Sleft] using hcoord
    · intro t
      let u : I := ⟨5 / 8 + (3 / 8) * (t : ℝ), by
        constructor <;> nlinarith [t.2.1, t.2.2]⟩
      obtain ⟨y, hy, hcoord⟩ := hrightNested u (by dsimp [u]; nlinarith [t.2.1])
      refine ⟨y, ?_, ?_⟩
      · simpa [hrightEval, u, H] using hy
      · simpa [coord, Sright] using hcoord

/-- The original half-path contract follows at the identical selected
radius; the stronger producer also retains the genuine Fermi certificates. -/
theorem exists_componentTwoCenterSmallConnector_halves_mem_relativeSides
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {U : Set ℂ} (hU : IsOpen U)
    (hballU : Metric.closedBall (0 : ℂ) 1 ⊆ U)
    (f : C(U, (X i).Carrier)) (hf : Topology.IsOpenEmbedding (f : U → (X i).Carrier))
    (p q : U) (hpMap : f p = (Quotient.mk'' (P.centers i).1 : (X i).Carrier))
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
    (hchartSegment : ∀ s : I, ∃ z : U,
      z.1 = (((1 - (s : ℝ)) * p.1.im + (s : ℝ) * q.1.im : ℝ) : ℂ) * Complex.I ∧
      ‖z.1‖ < 1 ∧ f z = P.componentCenterGeodPoint i s) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ, ∃ hρr : ρ ≤ gluingRadius C g,
      (∀ (b : Bool) (θ : Circle),
        (P.twoCenterPolarBoundaryMap i b ρ hρ hρr θ).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      (∀ t : I,
        (P.componentTwoCenterSmallDiskConnectorCandidate i ρ hρ hρr t).val ∈
          embeddedCoordinatePunctureDisk f) ∧
      ((p.1.im < q.1.im ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide p.1.im q.1.im) ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide p.1.im q.1.im)) ∨
       (q.1.im < p.1.im ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorLeftHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskUpperSide q.1.im p.1.im) ∧
        (∀ t : I,
          ∃ y : {w : embeddedTwoPunctureAmbientPoint f p q //
              w ∈ embeddedTwoPunctureLocalDiskRelativeSide f p q 1},
            y.1 = P.internalCenterPuncturedAmbientHomeomorph i f p q hi hnext
              hpMap hqMap
              (P.componentTwoCenterSmallConnectorRightHalf i ρ hρ hρr t) ∧
            (embeddedTwoPunctureRelativeLocalDiskUnitHomeomorph
              f hf p q 1 one_pos hballU hpre hqre y : ℂ) ∈
                twoPuncturedDiskLowerSide q.1.im p.1.im))) := by
  obtain ⟨ρ, hρ, hρr, hcircles, hcandidate, _hcomparison, horder⟩ :=
    P.exists_componentTwoCenterSmallConnector_halves_mem_relativeSides_with_comparisonData
      i hU hballU f hf p q hpMap hqMap hpre hqre hp hq hpq hi hnext
      γ m a b ha hb hformula hleft hright hsegment hchartSegment
  exact ⟨ρ, hρ, hρr, hcircles, hcandidate, horder⟩

end

end ExerciseGluingPreparation
end SystolicGrowth

#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterSmallConnector_halves_homotopic_candidate
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterSmallConnector_midpoint_value
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterAxisChart_affineSegment
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterCutCoordinate_half_bounds
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterCutPoint_relativeLocalDiskUnit_coordinate
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterGeodPoint_relativeLocalDiskUnit_coordinate
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterGeodPoint_firstHalf_mem_side
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterGeodPoint_secondHalf_mem_side
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftPolarRadius_geodParameter
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightPolarRadius_geodParameter
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftRadiusTrack_point_mem_side
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightRadiusTrack_point_mem_side
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterCutPoint_firstHalf_mem_side
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterCutPoint_secondHalf_mem_side
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftPolarPoint_mem_lowerSide
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftPolarPoint_mem_upperSide
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightPolarPoint_mem_upperSide
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightPolarPoint_mem_lowerSide
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterPolarArcs_mem_relativeSides
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterSmallConnector_halves_mem_relativeSides
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterPolarArcs_mem_relativeSides_with_comparisonData
#print axioms SystolicGrowth.ExerciseGluingPreparation.exists_componentTwoCenterSmallConnector_halves_mem_relativeSides_with_comparisonData
