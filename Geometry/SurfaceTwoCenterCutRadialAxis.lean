module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.DirichletPuncturePolarLoop
public import Geometry.FermiDiskPositiveWinding
public import Geometry.SurfaceTwoCenterCutSpine

@[expose] public section

/-!
# Polar radial tracks on an actual hyperbolic geodesic axis

This module isolates the geometric criterion needed by the two-center disk
connector: a polar point lies on the finite geodesic segment when its angle
is the endpoint's radial direction and its radius does not exceed the
endpoint distance.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

/-- Every positive polar point in the endpoint's radial direction lies on
the finite geodesic segment, provided its radius is no larger than the
endpoint distance. The radius comparison is converted to the disk-chart
norm order by the exact hyperbolic radial formula. -/
theorem gluingPolarPoint_mem_geodSeg_of_radialDirection
    {o w : ℍ} (θ : Circle) {ρ : ℝ} (hρ : 0 < ρ)
    (hdir : hyperbolicRadialDirection o w = (θ : ℂ))
    (hρw : ρ ≤ dist o w) :
    gluingPolarPoint o θ ρ ∈ Vendored.RiemannDynamics.geodSeg o w := by
  have hne : gluingPolarPoint o θ ρ ≠ o := by
    intro h
    have hd := dist_gluingPolarPoint o θ hρ.le
    rw [h, dist_self] at hd
    linarith

  apply mem_geodSeg_of_radialDirection_eq_of_norm_le
    hne
  · rw [hyperbolicRadialDirection_gluingPolarPoint o θ hρ, hdir]
  · rw [norm_discChart_eq_tanh_half_dist,
      norm_discChart_eq_tanh_half_dist,
      dist_gluingPolarPoint o θ hρ.le]
    by_contra hnot
    have hrev : Real.tanh (dist o w / 2) < Real.tanh (ρ / 2) := lt_of_not_ge hnot
    have hart := Real.artanh_lt_artanh
      (Real.neg_one_lt_tanh _) (Real.tanh_lt_one _) hrev
    have hdist : dist o w / 2 < ρ / 2 := by
      simpa only [Real.artanh_tanh] using hart
    linarith

end SystolicGrowth

#print axioms SystolicGrowth.gluingPolarPoint_mem_geodSeg_of_radialDirection

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The chosen left cut angle has the radial direction of the actual closest
lift of the right center. Its radius-`r` lift is exactly the first cut point. -/
theorem componentTwoCenterLeftCutAngle_lift_eq
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    gluingPolarPoint (P.centers i).1 (P.componentTwoCenterCutLeftAngle i)
        (gluingRadius C g) =
      Vendored.RiemannDynamics.geodInterp (P.centers i).1
        (P.componentCenterClosestDeck i • (P.centers i).2)
        (P.componentTwoCenterCutCoordinate i 0).val := by
  let p := (P.centers i).1
  let q := P.componentCenterClosestDeck i • (P.centers i).2
  let θ := P.componentTwoCenterCutLeftAngle i
  let t := P.componentTwoCenterCutCoordinate i 0
  let D := dist (Quotient.mk'' (P.centers i).1 : (X i).Carrier)
      (Quotient.mk'' (P.centers i).2 : (X i).Carrier)
  have hD : dist p q = D := by
    have hchoose : (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 =
        dist p q := by
      dsimp [p, q, componentCenterClosestDeck]
      exact Classical.choose_spec
        ((X i).exists_liftOrbitDist_eq_dist (P.centers i).1 (P.centers i).2)
    calc
      dist p q = (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 := hchoose.symm
      _ = D := by
        dsimp [D]
  have hDpos : 0 < D := by
    have hsep := P.carrier_centers_outer_add_inner_le_dist i
    dsimp [D, gluingEmbeddedRadius] at hsep ⊢
    linarith [P.radius_pos, P.depth_pos]
  have hmul : t.val * D = gluingRadius C g := by
    have ht : t.val = gluingRadius C g / D := by
      dsimp [t, componentTwoCenterCutCoordinate, D]
      simp
    rw [ht]
    exact div_mul_cancel₀ _ hDpos.ne'
  have hzdist : dist p
      (Vendored.RiemannDynamics.geodInterp p q t.val) = gluingRadius C g := by
    rw [Vendored.RiemannDynamics.dist_geodInterp_left_abs,
      abs_of_nonneg t.2.1, hD]
    exact hmul
  have hballPolar : gluingPolarPoint p θ (gluingRadius C g) ∈
      Metric.ball p (gluingEmbeddedRadius C g) := by
    rw [Metric.mem_ball, dist_comm, dist_gluingPolarPoint _ _ P.radius_pos.le]
    exact P.radius_lt_embeddedRadius
  have hballGeod : Vendored.RiemannDynamics.geodInterp p q t.val ∈
      Metric.ball p (gluingEmbeddedRadius C g) := by
    rw [Metric.mem_ball, dist_comm, hzdist]
    exact P.radius_lt_embeddedRadius
  have hquot : (Quotient.mk'' (gluingPolarPoint p θ (gluingRadius C g)) :
      (X i).Carrier) = Quotient.mk'' (Vendored.RiemannDynamics.geodInterp p q t.val) := by
    have hspec := P.componentTwoCenterCutLeftAngle_spec i
    have hval := congrArg (fun z : P.CenterPuncturedChainComponent i => z.1) hspec
    change (Quotient.mk'' (gluingPolarPoint p θ (gluingRadius C g)) :
      (X i).Carrier) = P.componentTwoCenterCutPoint i 0 at hval
    change (Quotient.mk'' (gluingPolarPoint p θ (gluingRadius C g)) :
      (X i).Carrier) = Quotient.mk'' (Vendored.RiemannDynamics.geodInterp p q t.val) at hval
    exact hval
  apply P.quotient_injOn_outer_ball i p hballPolar hballGeod hquot

/-- Geodesic-segment membership is transitive along nested initial
subsegments; this is the metric betweenness proof, not an assumed ray axiom. -/
theorem mem_geodSeg_of_mem_geodSeg_mem_geodSeg
    {a b c z : ℍ} (hz : z ∈ Vendored.RiemannDynamics.geodSeg a b)
    (hb : b ∈ Vendored.RiemannDynamics.geodSeg a c) :
    z ∈ Vendored.RiemannDynamics.geodSeg a c := by
  rw [Vendored.RiemannDynamics.mem_geodSeg] at hz hb ⊢
  have htri₁ := dist_triangle z b c
  have htri₂ := dist_triangle a z c
  nlinarith

/-- After transporting the right polar coordinate by the actual minimizing
deck transformation, the radius-`r` point is the literal right cut endpoint
lift. -/
theorem componentTwoCenterRightCutAngle_lift_eq
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n) :
    gluingPolarPoint
        (P.componentCenterClosestDeck i • (P.centers i).2)
        (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 *
          P.componentTwoCenterCutRightAngle i)
        (gluingRadius C g) =
      Vendored.RiemannDynamics.geodInterp (P.centers i).1
        (P.componentCenterClosestDeck i • (P.centers i).2)
        (P.componentTwoCenterCutCoordinate i 1).val := by
  let p := (P.centers i).1
  let q := (P.centers i).2
  let δ := P.componentCenterClosestDeck i
  let q' := δ • q
  let θ := P.componentTwoCenterCutRightAngle i
  let θ' := gluingPolarSLPhase δ q * θ
  let t := P.componentTwoCenterCutCoordinate i 1
  let z := Vendored.RiemannDynamics.geodInterp p q' t.val
  let D := dist (Quotient.mk'' p : (X i).Carrier)
      (Quotient.mk'' q : (X i).Carrier)
  have hchoose : (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 =
      dist p q' := by
    dsimp [p, q, q', δ, componentCenterClosestDeck]
    exact Classical.choose_spec
      ((X i).exists_liftOrbitDist_eq_dist (P.centers i).1 (P.centers i).2)
  have hD : dist p q' = D := by
    calc
      dist p q' = (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 := hchoose.symm
      _ = D := by dsimp [D]
  have hOrbit : (X i).liftOrbitDist (P.centers i).1 (P.centers i).2 = D := by
    calc
      _ = dist p q' := hchoose
      _ = D := hD
  have hDpos : 0 < D := by
    have hsep := P.carrier_centers_outer_add_inner_le_dist i
    dsimp [D, gluingEmbeddedRadius] at hsep ⊢
    linarith [P.radius_pos, P.depth_pos]
  have hmul : (1 - t.val) * D = gluingRadius C g := by
    have ht : t.val = (D - gluingRadius C g) / D := by
      dsimp [t, componentTwoCenterCutCoordinate]
      rw [hOrbit]
      dsimp [D]
      ring
    rw [ht]
    field_simp [hDpos.ne']
    ring
  have hzdist : dist q' z = gluingRadius C g := by
    change dist q' (Vendored.RiemannDynamics.geodInterp p q' t.val) = _
    rw [dist_comm, Vendored.RiemannDynamics.dist_geodInterp_right_abs, hD]
    rw [abs_of_nonneg (by linarith [t.2.2])]
    nlinarith [hmul]
  have hballPolar : gluingPolarPoint q' θ' (gluingRadius C g) ∈
      Metric.ball q' (gluingEmbeddedRadius C g) := by
    rw [Metric.mem_ball, dist_comm, dist_gluingPolarPoint _ _ P.radius_pos.le]
    exact P.radius_lt_embeddedRadius
  have hballGeod : z ∈ Metric.ball q' (gluingEmbeddedRadius C g) := by
    rw [Metric.mem_ball, dist_comm, hzdist]
    exact P.radius_lt_embeddedRadius
  have hproj (w : ℍ) :
      (Quotient.mk'' (δ • w) : (X i).Carrier) = Quotient.mk'' w := by
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr
      (MulAction.mem_orbit_iff.mpr ⟨δ, rfl⟩)
  have hquot' : (Quotient.mk'' (gluingPolarPoint q' θ' (gluingRadius C g)) :
      (X i).Carrier) = Quotient.mk'' z := by
    calc
      _ = Quotient.mk'' (δ • gluingPolarPoint q θ (gluingRadius C g)) := by
        exact congrArg Quotient.mk''
          (gluingPolarPoint_smul (↑δ) q θ (gluingRadius C g)).symm
      _ = Quotient.mk'' (gluingPolarPoint q θ (gluingRadius C g)) := hproj _
      _ = Quotient.mk'' z := by
        have hspec := P.componentTwoCenterCutRightAngle_spec i
        have hval := congrArg (fun w : P.CenterPuncturedChainComponent i => w.1) hspec
        change (Quotient.mk'' (gluingPolarPoint q θ (gluingRadius C g)) :
          (X i).Carrier) = P.componentTwoCenterCutPoint i 1 at hval
        simpa [componentTwoCenterCutPoint, componentCenterGeodPoint, z, t, p, q'] using hval
  apply P.quotient_injOn_outer_ball i q' hballPolar hballGeod hquot'

/-- Every actual right polar radius track at the angle where the minimizing
cut meets the right circle lies on the full lifted center segment. The phase
is the one induced by the actual closest deck transformation. -/
theorem componentTwoCenterRightPolarRadius_mem_centerGeodesic
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    gluingPolarPoint
        (P.componentCenterClosestDeck i • (P.centers i).2)
        (gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 *
          P.componentTwoCenterCutRightAngle i) ρ ∈
      Vendored.RiemannDynamics.geodSeg (P.centers i).1
        (P.componentCenterClosestDeck i • (P.centers i).2) := by
  let p := (P.centers i).1
  let q' := P.componentCenterClosestDeck i • (P.centers i).2
  let θ := gluingPolarSLPhase (P.componentCenterClosestDeck i) (P.centers i).2 *
    P.componentTwoCenterCutRightAngle i
  let z := Vendored.RiemannDynamics.geodInterp p q'
    (P.componentTwoCenterCutCoordinate i 1).val
  have hLift := P.componentTwoCenterRightCutAngle_lift_eq i
  have hdir : hyperbolicRadialDirection q' z = (θ : ℂ) := by
    have h := hyperbolicRadialDirection_gluingPolarPoint
      q' θ P.radius_pos
    rw [hLift] at h
    simpa [q', z, θ] using h
  have hzdist : dist q' z = gluingRadius C g := by
    have h := dist_gluingPolarPoint q' θ P.radius_pos.le
    rw [hLift] at h
    simpa [q', z, θ] using h
  have hlocal := gluingPolarPoint_mem_geodSeg_of_radialDirection θ hρ hdir
    (by rw [hzdist]; exact hρr)
  have hzseg : z ∈ Vendored.RiemannDynamics.geodSeg q' p := by
    rw [Vendored.RiemannDynamics.geodSeg_comm]
    exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg p q'
      (P.componentTwoCenterCutCoordinate i 1).2
  have hwhole :=
    SystolicGrowth.ExerciseGluingPreparation.mem_geodSeg_of_mem_geodSeg_mem_geodSeg
      hlocal hzseg
  rw [Vendored.RiemannDynamics.geodSeg_comm] at hwhole
  simpa [p, q'] using hwhole

/-- Every actual left polar radius track at the angle where the minimizing
cut leaves the left circle lies on the full lifted center geodesic segment. -/
theorem componentTwoCenterLeftPolarRadius_mem_centerGeodesic
    (P : ExerciseGluingPreparation C g n genera X) (i : Fin n)
    {ρ : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ gluingRadius C g) :
    gluingPolarPoint (P.centers i).1 (P.componentTwoCenterCutLeftAngle i) ρ ∈
      Vendored.RiemannDynamics.geodSeg (P.centers i).1
        (P.componentCenterClosestDeck i • (P.centers i).2) := by
  let p := (P.centers i).1
  let q := P.componentCenterClosestDeck i • (P.centers i).2
  let θ := P.componentTwoCenterCutLeftAngle i
  let z := Vendored.RiemannDynamics.geodInterp p q
    (P.componentTwoCenterCutCoordinate i 0).val
  have hLift := P.componentTwoCenterLeftCutAngle_lift_eq i
  have hdir : hyperbolicRadialDirection p z = (θ : ℂ) := by
    have h := hyperbolicRadialDirection_gluingPolarPoint
      (P.centers i).1 (P.componentTwoCenterCutLeftAngle i) P.radius_pos
    rw [hLift] at h
    simpa [p, q, z, θ] using h
  have hzdist : dist p z = gluingRadius C g := by
    have h := dist_gluingPolarPoint (P.centers i).1
      (P.componentTwoCenterCutLeftAngle i) P.radius_pos.le
    rw [hLift] at h
    simpa [p, q, z, θ] using h
  have hlocal := gluingPolarPoint_mem_geodSeg_of_radialDirection θ hρ hdir
    (by rw [hzdist]; exact hρr)
  have hzseg : z ∈ Vendored.RiemannDynamics.geodSeg p q :=
    Vendored.RiemannDynamics.geodInterp_mem_geodSeg p q
      (P.componentTwoCenterCutCoordinate i 0).2
  exact mem_geodSeg_of_mem_geodSeg_mem_geodSeg hlocal hzseg

end SystolicGrowth.ExerciseGluingPreparation

#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftCutAngle_lift_eq
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterLeftPolarRadius_mem_centerGeodesic
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightCutAngle_lift_eq
#print axioms SystolicGrowth.ExerciseGluingPreparation.componentTwoCenterRightPolarRadius_mem_centerGeodesic
