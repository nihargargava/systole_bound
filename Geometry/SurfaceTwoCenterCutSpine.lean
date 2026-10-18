module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceTwoCenterBoundarySpine
public import Geometry.GluingSeamOverlap

@[expose] public section

/-!
# An embedded metric cut between the two actual puncture circles

An attained closest deck translate gives a shortest center-to-center
hyperbolic segment in the original quotient. Its exact quotient distances
are proved from the minimizing endpoints and the triangle inequality.
Truncating one deleted-disk radius from each end gives an embedded arc in
the actual retained component, meeting each original puncture circle only
at its corresponding endpoint.

This constructs the physical cut arc, not a claimed deformation retraction
of its complement. Both original polar boundary representatives are retained.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane Topology unitInterval ContinuousMap

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The attained closest translate of the actual second center. -/
def componentCenterClosestDeck (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    (X i).deckGroup :=
  Classical.choose ((X i).exists_liftOrbitDist_eq_dist (P.centers i).1 (P.centers i).2)

/-- Literal projection of the minimizing hyperbolic center segment. -/
def componentCenterGeodPoint (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (t : I) : (X i).Carrier :=
  Quotient.mk'' (Vendored.RiemannDynamics.geodInterp (P.centers i).1
    (P.componentCenterClosestDeck i • (P.centers i).2) t)

private theorem centerGeod_lift_length (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    dist (P.centers i).1 (P.componentCenterClosestDeck i • (P.centers i).2) =
      dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
  rw [(X i).carrier_dist_eq_orbitDist, (X i).orbitDist_mk]
  exact (Classical.choose_spec
    ((X i).exists_liftOrbitDist_eq_dist (P.centers i).1 (P.centers i).2)).symm

@[simp]
theorem componentCenterGeodPoint_zero (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentCenterGeodPoint i 0 = (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
  simp only [componentCenterGeodPoint, Set.Icc.coe_zero,
    Vendored.RiemannDynamics.geodInterp_zero]

@[simp]
theorem componentCenterGeodPoint_one (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentCenterGeodPoint i 1 = (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
  simp only [componentCenterGeodPoint, Set.Icc.coe_one,
    Vendored.RiemannDynamics.geodInterp_one]
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr
    (MulAction.mem_orbit_iff.mpr ⟨P.componentCenterClosestDeck i, rfl⟩)

theorem componentCenterGeodPoint_continuous (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) : Continuous (P.componentCenterGeodPoint i) := by
  apply continuous_quotient_mk'.comp
  exact Vendored.RiemannDynamics.continuous_geodInterp.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val))

private theorem centerGeod_dist_le (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    (s t : I) :
    dist (P.componentCenterGeodPoint i s) (P.componentCenterGeodPoint i t) ≤
      |(s : ℝ) - t| *
        dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
  rw [componentCenterGeodPoint, componentCenterGeodPoint,
    (X i).carrier_dist_eq_orbitDist, (X i).orbitDist_mk]
  have h := (X i).liftOrbitDist_le
    (Vendored.RiemannDynamics.geodInterp (P.centers i).1
      (P.componentCenterClosestDeck i • (P.centers i).2) s)
    (Vendored.RiemannDynamics.geodInterp (P.centers i).1
      (P.componentCenterClosestDeck i • (P.centers i).2) t) 1
  simpa only [one_smul, Vendored.RiemannDynamics.dist_geodInterp_pair,
    centerGeod_lift_length] using h

/-- Every subsegment has its exact native quotient distance, not just an upstairs bound. -/
theorem componentCenterGeodPoint_dist (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (s t : I) :
    dist (P.componentCenterGeodPoint i s) (P.componentCenterGeodPoint i t) =
      |(s : ℝ) - t| *
        dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
  have hordered : ∀ s t : I, (s : ℝ) ≤ t →
      dist (P.componentCenterGeodPoint i s) (P.componentCenterGeodPoint i t) =
        ((t : ℝ) - s) *
          dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
    intro s t hst
    have hupper := P.centerGeod_dist_le i s t
    rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] at hupper
    have hfirst := P.centerGeod_dist_le i 0 s
    have hlast := P.centerGeod_dist_le i t 1
    simp only [componentCenterGeodPoint_zero, Set.Icc.coe_zero, zero_sub, abs_neg,
      abs_of_nonneg s.2.1] at hfirst
    simp only [componentCenterGeodPoint_one, Set.Icc.coe_one,
      abs_of_nonpos (sub_nonpos.mpr t.2.2), neg_sub] at hlast
    have htri := dist_triangle (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (P.componentCenterGeodPoint i s) (Quotient.mk'' (P.centers i).2)
    have htri' := dist_triangle (P.componentCenterGeodPoint i s)
      (P.componentCenterGeodPoint i t) (Quotient.mk'' (P.centers i).2)
    linarith
  rcases le_total (s : ℝ) t with hst | hts
  · rw [abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    exact hordered s t hst
  · rw [dist_comm, abs_of_nonneg (sub_nonneg.mpr hts)]
    exact hordered t s hts

theorem cut_length_pos (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    0 < dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) -
      2 * gluingRadius C g := by
  linarith [P.carrier_centers_outer_add_inner_le_dist i, P.radius_lt_embeddedRadius]

theorem center_distance_pos (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    0 < dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) := by
  linarith [P.cut_length_pos i, P.radius_pos]

/-- Exact affine truncation by the actual deleted disk radius at both ends. -/
def componentTwoCenterCutCoordinate (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (t : I) : I :=
  ⟨(gluingRadius C g + t.val *
      (dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) -
        2 * gluingRadius C g)) /
    dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2), by
    constructor
    · apply div_nonneg
      · nlinarith [P.radius_pos, P.cut_length_pos i, t.2.1]
      · exact (P.center_distance_pos i).le
    · apply (div_le_one (P.center_distance_pos i)).mpr
      nlinarith [P.radius_pos, P.cut_length_pos i, t.2.2]⟩

/-- The actual quotient point of the physical cut arc. -/
def componentTwoCenterCutPoint (P : ExerciseGluingPreparation C g n genera X)
    (i : Fin n) (t : I) : (X i).Carrier :=
  P.componentCenterGeodPoint i (P.componentTwoCenterCutCoordinate i t)

theorem componentTwoCenterCutPoint_continuous
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Continuous (P.componentTwoCenterCutPoint i) := by
  apply (P.componentCenterGeodPoint_continuous i).comp
  apply Continuous.subtype_mk
  fun_prop

/-- Native distance from the left center is the literal affine cut coordinate. -/
theorem componentTwoCenterCutPoint_dist_left
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    dist (P.componentTwoCenterCutPoint i t) (Quotient.mk'' (P.centers i).1 : (X i).Carrier) =
      gluingRadius C g + t.val *
        (dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) -
          2 * gluingRadius C g) := by
  rw [dist_comm, ← P.componentCenterGeodPoint_zero i, componentTwoCenterCutPoint,
    componentCenterGeodPoint_dist]
  rw [Set.Icc.coe_zero, zero_sub, abs_neg,
    abs_of_nonneg (P.componentTwoCenterCutCoordinate i t).2.1]
  rw [componentCenterGeodPoint_zero]
  change (_ / _) * _ = _
  exact div_mul_cancel₀ _ (P.center_distance_pos i).ne'

/-- Native distance from the right center decreases to the original second circle. -/
theorem componentTwoCenterCutPoint_dist_right
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    dist (P.componentTwoCenterCutPoint i t) (Quotient.mk'' (P.centers i).2 : (X i).Carrier) =
      gluingRadius C g + (1 - t.val) *
        (dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier) (Quotient.mk'' (P.centers i).2) -
          2 * gluingRadius C g) := by
  rw [← P.componentCenterGeodPoint_one i, componentTwoCenterCutPoint, componentCenterGeodPoint_dist,
    Set.Icc.coe_one, abs_of_nonpos (sub_nonpos.mpr (P.componentTwoCenterCutCoordinate i t).2.2), neg_sub]
  rw [componentCenterGeodPoint_one]
  change (1 - (gluingRadius C g + t.val * _) / _) * _ = _
  rw [sub_mul, one_mul, div_mul_cancel₀ _ (P.center_distance_pos i).ne']
  ring

/-- Every point of the cut stays in the actual retained component. -/
theorem componentTwoCenterCutPoint_mem_retained
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    P.componentTwoCenterCutPoint i t ∈ (X i).puncturedComponentSet
      (P.centers i).1 (P.centers i).2 (gluingRadius C g) i := by
  have hl : gluingRadius C g ≤ dist (P.componentTwoCenterCutPoint i t)
      (Quotient.mk'' (P.centers i).1 : (X i).Carrier) := by
    rw [componentTwoCenterCutPoint_dist_left]
    nlinarith [P.cut_length_pos i, t.2.1]
  have hr : gluingRadius C g ≤ dist (P.componentTwoCenterCutPoint i t)
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier) := by
    rw [componentTwoCenterCutPoint_dist_right]
    nlinarith [P.cut_length_pos i, t.2.2]
  rintro (hleft | hright)
  · change P.componentTwoCenterCutPoint i t ∈
      (if 0 < i.val then (X i).orbitBall (P.centers i).1 (gluingRadius C g) else ∅) at hleft
    split_ifs at hleft
    · rw [← (X i).carrier_ball_eq_orbitBall] at hleft
      exact (not_lt_of_ge hl) hleft
    · exact hleft.elim
  · change P.componentTwoCenterCutPoint i t ∈
      (if i.val + 1 < n then (X i).orbitBall (P.centers i).2 (gluingRadius C g) else ∅) at hright
    split_ifs at hright
    · rw [← (X i).carrier_ball_eq_orbitBall] at hright
      exact (not_lt_of_ge hr) hright
    · exact hright.elim

/-- The actual interior of the cut avoids both closed deleted disks. -/
theorem componentTwoCenterCutPoint_mem_interior
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I)
    (ht : t.val ∈ Ioo (0 : ℝ) 1) :
    P.componentTwoCenterCutPoint i t ∈ P.componentInteriorSet i := by
  apply P.mem_componentInteriorSet_of_radius_lt_dist
  · rw [componentTwoCenterCutPoint_dist_left]
    nlinarith [P.cut_length_pos i, ht.1]
  · rw [componentTwoCenterCutPoint_dist_right]
    nlinarith [P.cut_length_pos i, ht.2]

/-- Injectivity follows from the strictly increasing actual center-distance coordinate. -/
theorem componentTwoCenterCutPoint_injective
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Function.Injective (P.componentTwoCenterCutPoint i) := by
  intro s t h
  have hd := congrArg (fun q => dist q (Quotient.mk'' (P.centers i).1 : (X i).Carrier)) h
  rw [componentTwoCenterCutPoint_dist_left, componentTwoCenterCutPoint_dist_left] at hd
  apply Subtype.ext
  nlinarith [P.cut_length_pos i]

/-- This is an embedded physical interval in the original surface quotient. -/
theorem componentTwoCenterCutPoint_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsEmbedding (P.componentTwoCenterCutPoint i) :=
  ((P.componentTwoCenterCutPoint_continuous i).isClosedEmbedding
    (P.componentTwoCenterCutPoint_injective i)).isEmbedding

private theorem inner_twice_lt_systole (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    2 * gluingRadius C g < (X i).systole := by
  linarith [P.radius_lt_embeddedRadius, P.twice_outer_lt_systole i]

/-- The first endpoint is on the actual incoming puncture circle. -/
theorem componentTwoCenterCutPoint_zero_mem_leftCircle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentTwoCenterCutPoint i 0 ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) := by
  rw [ClosedHyperbolicSurface.punctureCircle,
    (X i).image_quotientMk_sphere_eq_carrier_sphere _ _ (P.inner_twice_lt_systole i), mem_sphere]
  simp only [componentTwoCenterCutPoint_dist_left, Set.Icc.coe_zero, zero_mul, add_zero]

/-- The second endpoint is on the actual outgoing puncture circle. -/
theorem componentTwoCenterCutPoint_one_mem_rightCircle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentTwoCenterCutPoint i 1 ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) := by
  rw [ClosedHyperbolicSurface.punctureCircle,
    (X i).image_quotientMk_sphere_eq_carrier_sphere _ _ (P.inner_twice_lt_systole i), mem_sphere]
  simp only [componentTwoCenterCutPoint_dist_right, Set.Icc.coe_one, sub_self, zero_mul, add_zero]

/-- The embedded interval meets the entire actual left circle only at its first endpoint. -/
theorem componentTwoCenterCutPoint_mem_leftCircle_iff
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    P.componentTwoCenterCutPoint i t ∈ (X i).punctureCircle (P.centers i).1 (gluingRadius C g) ↔
      t = 0 := by
  constructor
  · intro ht
    rw [ClosedHyperbolicSurface.punctureCircle,
      (X i).image_quotientMk_sphere_eq_carrier_sphere _ _ (P.inner_twice_lt_systole i),
      mem_sphere, componentTwoCenterCutPoint_dist_left] at ht
    apply Subtype.ext
    change t.val = 0
    nlinarith [P.cut_length_pos i, t.2.1]
  · rintro rfl
    exact P.componentTwoCenterCutPoint_zero_mem_leftCircle i

/-- The embedded interval meets the entire actual right circle only at its last endpoint. -/
theorem componentTwoCenterCutPoint_mem_rightCircle_iff
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) (t : I) :
    P.componentTwoCenterCutPoint i t ∈ (X i).punctureCircle (P.centers i).2 (gluingRadius C g) ↔
      t = 1 := by
  constructor
  · intro ht
    rw [ClosedHyperbolicSurface.punctureCircle,
      (X i).image_quotientMk_sphere_eq_carrier_sphere _ _ (P.inner_twice_lt_systole i),
      mem_sphere, componentTwoCenterCutPoint_dist_right] at ht
    apply Subtype.ext
    change t.val = 1
    nlinarith [P.cut_length_pos i, t.2.2]
  · rintro rfl
    exact P.componentTwoCenterCutPoint_one_mem_rightCircle i

/-- The genuine embedded cut as a path in the actual retained component. -/
def componentTwoCenterCutArc (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (⟨P.componentTwoCenterCutPoint i 0, P.componentTwoCenterCutPoint_mem_retained i 0⟩ :
      P.ChainComponent i)
      ⟨P.componentTwoCenterCutPoint i 1, P.componentTwoCenterCutPoint_mem_retained i 1⟩ where
  toFun t := ⟨P.componentTwoCenterCutPoint i t, P.componentTwoCenterCutPoint_mem_retained i t⟩
  continuous_toFun := (P.componentTwoCenterCutPoint_continuous i).subtype_mk _
  source' := rfl
  target' := rfl

theorem componentTwoCenterCutArc_isEmbedding
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Topology.IsEmbedding (P.componentTwoCenterCutArc i) := by
  exact ((P.componentTwoCenterCutArc i).continuous.isClosedEmbedding
    (fun s t h => P.componentTwoCenterCutPoint_injective i (congrArg Subtype.val h))).isEmbedding

private theorem sphere_point_eq_polarPoint
    (P : ExerciseGluingPreparation C g n genera X) (o : ℍ) (z : ℍ)
    (hz : z ∈ sphere o (gluingRadius C g)) :
    ∃ θ : Circle, gluingPolarPoint o θ (gluingRadius C g) = z := by
  have hrad : dist o z = gluingRadius C g := by
    simpa only [mem_sphere, dist_comm] using hz
  let a : GluingPolarAnnulus o (gluingRadius C g / 2) (gluingEmbeddedRadius C g) :=
    ⟨z, by
      rw [hrad]
      exact ⟨by linarith [P.radius_pos], P.radius_lt_embeddedRadius⟩⟩
  let H := gluingPolarCollarHomeomorph o (gluingRadius C g / 2) (gluingEmbeddedRadius C g)
    (half_pos P.radius_pos)
  refine ⟨(H a).1, ?_⟩
  have h := congrArg Subtype.val (H.symm_apply_apply a)
  change gluingPolarPoint o (H a).1 (dist o z) = z at h
  rwa [hrad] at h

theorem Internal.SurfaceTwoCenterCutSpineHelpers.exists_cut_left_angle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ θ : Circle, P.componentLeftPolarBoundaryMap i θ =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) := by
  obtain ⟨z, hz, hq⟩ := P.componentTwoCenterCutPoint_zero_mem_leftCircle i
  obtain ⟨θ, hθ⟩ := sphere_point_eq_polarPoint P (P.centers i).1 z hz
  refine ⟨θ, Subtype.ext ?_⟩
  change (Quotient.mk'' (gluingPolarPoint (P.centers i).1 θ (gluingRadius C g)) : (X i).Carrier) =
    P.componentTwoCenterCutPoint i 0
  rw [hθ]
  exact hq

theorem Internal.SurfaceTwoCenterCutSpineHelpers.exists_cut_right_angle
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    ∃ θ : Circle, P.componentRightPolarBoundaryMap i θ =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) := by
  obtain ⟨z, hz, hq⟩ := P.componentTwoCenterCutPoint_one_mem_rightCircle i
  obtain ⟨θ, hθ⟩ := sphere_point_eq_polarPoint P (P.centers i).2 z hz
  refine ⟨θ, Subtype.ext ?_⟩
  change (Quotient.mk'' (gluingPolarPoint (P.centers i).2 θ (gluingRadius C g)) : (X i).Carrier) =
    P.componentTwoCenterCutPoint i 1
  rw [hθ]
  exact hq

/-- Actual polar angle at which the embedded cut meets the original left circle. -/
def componentTwoCenterCutLeftAngle (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) : Circle :=
  Classical.choose (Internal.SurfaceTwoCenterCutSpineHelpers.exists_cut_left_angle P i)

/-- Actual polar angle at which the embedded cut meets the original right circle. -/
def componentTwoCenterCutRightAngle (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) : Circle :=
  Classical.choose (Internal.SurfaceTwoCenterCutSpineHelpers.exists_cut_right_angle P i)

theorem componentTwoCenterCutLeftAngle_spec
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentLeftPolarBoundaryMap i (P.componentTwoCenterCutLeftAngle i) =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0) :=
  Classical.choose_spec (Internal.SurfaceTwoCenterCutSpineHelpers.exists_cut_left_angle P i)

theorem componentTwoCenterCutRightAngle_spec
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    P.componentRightPolarBoundaryMap i (P.componentTwoCenterCutRightAngle i) =
      P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1) :=
  Classical.choose_spec (Internal.SurfaceTwoCenterCutSpineHelpers.exists_cut_right_angle P i)

/-- Literal positive-circle connector from the original angle-one left basepoint to the cut. -/
def componentTwoCenterCutLeftConnector (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentLeftPolarBoundaryMap i 1)
      (P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 0)) :=
  ((Circle.path 1 (P.componentTwoCenterCutLeftAngle i)).map
    (P.componentLeftPolarBoundaryMap i).continuous).cast rfl
      (P.componentTwoCenterCutLeftAngle_spec i).symm

/-- Literal positive-circle connector from the cut to the original angle-one right basepoint. -/
def componentTwoCenterCutRightConnector (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentPunctureInclusion i (P.componentTwoCenterCutArc i 1))
      (P.componentRightPolarBoundaryMap i 1) :=
  ((Circle.path (P.componentTwoCenterCutRightAngle i) 1).map
    (P.componentRightPolarBoundaryMap i).continuous).cast
      (P.componentTwoCenterCutRightAngle_spec i).symm rfl

/-- A concrete path through the embedded cut, with both untouched literal polar basepoints.
The circle connectors are retained explicitly rather than silently changing either loop. -/
def componentTwoCenterCutBasedPath (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentLeftPolarBoundaryMap i 1) (P.componentRightPolarBoundaryMap i 1) :=
  ((P.componentTwoCenterCutLeftConnector i).trans
    ((P.componentTwoCenterCutArc i).map (P.componentPunctureInclusion i).continuous)).trans
      (P.componentTwoCenterCutRightConnector i)

/-- The original right one-turn representative, based at the original left basepoint
along the concrete physical cut and its explicit polar connectors. -/
def componentRightPolarBoundaryLoopAlongCut
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    Path (P.componentLeftPolarBoundaryMap i 1) (P.componentLeftPolarBoundaryMap i 1) :=
  (P.componentTwoCenterCutBasedPath i).trans
    ((P.componentRightPolarBoundaryLoop i).trans (P.componentTwoCenterCutBasedPath i).symm)

#print axioms componentCenterGeodPoint_dist
#print axioms componentTwoCenterCutPoint_mem_interior
#print axioms componentTwoCenterCutPoint_isEmbedding
#print axioms componentTwoCenterCutArc_isEmbedding
#print axioms componentTwoCenterCutPoint_mem_leftCircle_iff
#print axioms componentTwoCenterCutBasedPath
#print axioms componentRightPolarBoundaryLoopAlongCut

end

end SystolicGrowth.ExerciseGluingPreparation
