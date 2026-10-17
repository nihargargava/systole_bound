module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceOrbitMetric

@[expose] public section

/-!
# Actual isometric small-ball charts for the surface orbit metric

A quotient chart is injective under `2ρ < systole`; preserving all
pairwise distances on the entire chart is proved here using the stronger
small-ball bound `4ρ < systole`. An actual minimizing deck translate
cannot be nonidentity: its displacement would be less than `4ρ`.
The metric and quotient topology are exactly those already constructed
on the surface carrier.
-/

open Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ClosedHyperbolicSurface

/-- On a ball of radius below one quarter of the systole, the identity
translate attains the actual orbit-distance minimum. -/
theorem liftOrbitDist_eq_dist_of_mem_small_ball
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (hρ : 4 * ρ < X.systole) {z w : ℍ}
    (hz : z ∈ Metric.ball o ρ) (hw : w ∈ Metric.ball o ρ) :
    X.liftOrbitDist z w = dist z w := by
  obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist z w
  have hmin : dist z (γ • w) ≤ dist z w := by
    rw [← hγ]
    simpa only [one_smul] using X.liftOrbitDist_le z w 1
  have hdzw : dist z w < 2 * ρ := by
    calc
      dist z w ≤ dist z o + dist o w := dist_triangle _ _ _
      _ < ρ + ρ := add_lt_add hz (by simpa only [mem_ball, dist_comm] using hw)
      _ = 2 * ρ := by ring
  have hone : γ = 1 := by
    by_contra hne
    have hsys := X.systole_le_displacement γ hne w
    have hdisplacement : dist w (γ • w) ≤ 2 * dist z w := by
      calc
        dist w (γ • w) ≤ dist w z + dist z (γ • w) := dist_triangle _ _ _
        _ ≤ dist z w + dist z w := by
          rw [dist_comm w z]
          exact add_le_add (le_refl _) hmin
        _ = 2 * dist z w := by ring
    linarith
  simpa only [hone, one_smul] using hγ

/-- The actual quotient images retain upstairs distance throughout the
small ball; no local-isometry field is assumed. -/
theorem carrier_dist_mk_eq_of_mem_small_ball
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (hρ : 4 * ρ < X.systole) {z w : ℍ}
    (hz : z ∈ Metric.ball o ρ) (hw : w ∈ Metric.ball o ρ) :
    dist (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z)
      (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) w) = dist z w := by
  rw [X.carrier_dist_eq_orbitDist, X.orbitDist_mk]
  exact X.liftOrbitDist_eq_dist_of_mem_small_ball o ρ hρ hz hw

/-- The restriction of the actual quotient projection is an isometry on
a sufficiently small ball, for the unchanged surface quotient metric. -/
theorem quotientSmallBall_isometry
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (hρ : 4 * ρ < X.systole) :
    Isometry (fun z : Metric.ball o ρ =>
      Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z.1) := by
  apply Isometry.of_dist_eq
  intro z w
  exact X.carrier_dist_mk_eq_of_mem_small_ball o ρ hρ z.2 w.2

/-- The metric chart is also an embedding for the original quotient topology. -/
theorem quotientSmallBall_isEmbedding
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (hρ : 4 * ρ < X.systole) :
    Topology.IsEmbedding (fun z : Metric.ball o ρ =>
      Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z.1) :=
  (X.quotientSmallBall_isometry o ρ hρ).isEmbedding

/-- Distances from the chart center are preserved even on the closed ball
under the weaker half-systole bound. This does not assert all-pairs distance
preservation on that larger chart. -/
theorem carrier_dist_mk_center_eq_of_mem_closedBall
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (ρ : ℝ)
    (hρ : 2 * ρ < X.systole) {z : ℍ}
    (hz : z ∈ Metric.closedBall o ρ) :
    dist (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) o)
      (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z) = dist o z := by
  rw [X.carrier_dist_eq_orbitDist, X.orbitDist_mk]
  obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist o z
  have hmin : dist o (γ • z) ≤ dist o z := by
    rw [← hγ]
    simpa only [one_smul] using X.liftOrbitDist_le o z 1
  have hdist : dist o z ≤ ρ := by simpa only [mem_closedBall, dist_comm] using hz
  have hone : γ = 1 := by
    by_contra hne
    have hsys := X.systole_le_displacement γ hne z
    have hdisplacement : dist z (γ • z) ≤ 2 * dist o z := by
      calc
        dist z (γ • z) ≤ dist z o + dist o (γ • z) := dist_triangle _ _ _
        _ ≤ dist o z + dist o z := by
          rw [dist_comm z o]
          exact add_le_add (le_refl _) hmin
        _ = 2 * dist o z := by ring
    linarith
  simpa only [hone, one_smul] using hγ

/-- The image of an actual small upstairs circle is exactly the sphere in
the existing surface quotient metric. Attainment of the orbit distance
also proves the reverse inclusion, rather than assuming lifted spheres. -/
theorem image_quotientMk_sphere_eq_carrier_sphere
    {g : ℕ} (X : ClosedHyperbolicSurface g) (o : ℍ) (r : ℝ)
    (hr : 2 * r < X.systole) :
    (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)) '' Metric.sphere o r =
      Metric.sphere (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) o) r := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hdist := X.carrier_dist_mk_center_eq_of_mem_closedBall o r hr
      (Metric.sphere_subset_closedBall hz)
    have hrad : dist o z = r := by simpa only [Metric.mem_sphere, dist_comm] using hz
    simpa only [Metric.mem_sphere, dist_comm] using hdist.trans hrad
  · intro hq
    obtain ⟨z, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist o z
    have hrad : dist o (γ • z) = r := by
      rw [← hγ, ← X.orbitDist_mk, ← X.carrier_dist_eq_orbitDist]
      simpa only [Metric.mem_sphere, dist_comm] using hq
    refine ⟨γ • z, by simpa only [Metric.mem_sphere, dist_comm] using hrad, ?_⟩
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ, rfl⟩)

#print axioms carrier_dist_mk_eq_of_mem_small_ball
#print axioms quotientSmallBall_isometry
#print axioms quotientSmallBall_isEmbedding
#print axioms carrier_dist_mk_center_eq_of_mem_closedBall
#print axioms image_quotientMk_sphere_eq_carrier_sphere

end SystolicGrowth.ClosedHyperbolicSurface
