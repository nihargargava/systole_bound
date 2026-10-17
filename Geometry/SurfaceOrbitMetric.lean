module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.QuotientOrbitBall
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
# The actual orbit metric of a closed hyperbolic surface

Proper discontinuity on the proper hyperbolic plane gives an attained
minimum of the distances between two orbits. This distance descends to the
existing surface carrier and defines a metric with exactly its original
quotient topology. Its open balls are the previously constructed orbit
images of upstairs hyperbolic balls.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth.ClosedHyperbolicSurface

/-- The attained minimum distance from one lift to the orbit of another. -/
noncomputable def liftOrbitDist {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) : ℝ :=
  dist z ((Classical.choose (exists_smul_minimizing_distance
    (G := X.deckGroup) z w)) • w)

theorem liftOrbitDist_le {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) (γ : X.deckGroup) :
    X.liftOrbitDist z w ≤ dist z (γ • w) :=
  Classical.choose_spec (exists_smul_minimizing_distance (G := X.deckGroup) z w) γ

theorem exists_liftOrbitDist_eq_dist {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) : ∃ γ : X.deckGroup, X.liftOrbitDist z w = dist z (γ • w) :=
  ⟨Classical.choose (exists_smul_minimizing_distance (G := X.deckGroup) z w), rfl⟩

/-- The attained distance is also the infimum over all actual deck labels. -/
theorem liftOrbitDist_eq_sInf {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) : X.liftOrbitDist z w = sInf (range (fun γ : X.deckGroup => dist z (γ • w))) := by
  symm
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (range_nonempty _)
  · rintro a ⟨γ, rfl⟩
    exact X.liftOrbitDist_le z w γ
  · intro a ha
    obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist z w
    exact ⟨dist z (γ • w), ⟨γ, rfl⟩, hγ ▸ ha⟩

theorem liftOrbitDist_nonneg {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) : 0 ≤ X.liftOrbitDist z w := dist_nonneg

theorem liftOrbitDist_self {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z : ℍ) : X.liftOrbitDist z z = 0 := by
  apply le_antisymm
  · simpa using X.liftOrbitDist_le z z 1
  · exact X.liftOrbitDist_nonneg z z

theorem liftOrbitDist_smul_right {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) (γ : X.deckGroup) :
    X.liftOrbitDist z (γ • w) = X.liftOrbitDist z w := by
  obtain ⟨η, hη⟩ := X.exists_liftOrbitDist_eq_dist z w
  obtain ⟨κ, hκ⟩ := X.exists_liftOrbitDist_eq_dist z (γ • w)
  apply le_antisymm
  · have h := X.liftOrbitDist_le z (γ • w) (η * γ⁻¹)
    simpa only [mul_smul, inv_smul_smul, ← hη] using h
  · have h := X.liftOrbitDist_le z w (κ * γ)
    simpa only [mul_smul, ← hκ] using h

theorem liftOrbitDist_smul_left {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) (γ : X.deckGroup) :
    X.liftOrbitDist (γ • z) w = X.liftOrbitDist z w := by
  obtain ⟨η, hη⟩ := X.exists_liftOrbitDist_eq_dist z w
  obtain ⟨κ, hκ⟩ := X.exists_liftOrbitDist_eq_dist (γ • z) w
  apply le_antisymm
  · have h := X.liftOrbitDist_le (γ • z) w (γ * η)
    simpa only [mul_smul, dist_smul, ← hη] using h
  · have h := X.liftOrbitDist_le z w (γ⁻¹ * κ)
    have heq : dist z ((γ⁻¹ * κ) • w) = dist (γ • z) (κ • w) := by
      rw [← dist_smul γ z ((γ⁻¹ * κ) • w)]
      simp only [mul_smul, smul_inv_smul]
    exact h.trans_eq (heq.trans hκ.symm)

theorem liftOrbitDist_comm {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : ℍ) : X.liftOrbitDist z w = X.liftOrbitDist w z := by
  have hle (a b : ℍ) : X.liftOrbitDist a b ≤ X.liftOrbitDist b a := by
    obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist b a
    have h := X.liftOrbitDist_le a b γ⁻¹
    have heq : dist a (γ⁻¹ • b) = dist b (γ • a) := by
      rw [← dist_smul γ a (γ⁻¹ • b), smul_inv_smul, dist_comm]
    exact h.trans_eq (heq.trans hγ.symm)
  exact le_antisymm (hle z w) (hle w z)

theorem liftOrbitDist_triangle {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w u : ℍ) : X.liftOrbitDist z u ≤ X.liftOrbitDist z w + X.liftOrbitDist w u := by
  obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist z w
  obtain ⟨η, hη⟩ := X.exists_liftOrbitDist_eq_dist w u
  calc
    X.liftOrbitDist z u ≤ dist z ((γ * η) • u) := X.liftOrbitDist_le z u _
    _ ≤ dist z (γ • w) + dist (γ • w) ((γ * η) • u) := dist_triangle _ _ _
    _ = X.liftOrbitDist z w + X.liftOrbitDist w u := by
      rw [mul_smul, dist_smul, ← hγ, ← hη]

theorem liftOrbitDist_congr {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w z' w' : ℍ) (hz : MulAction.orbitRel X.deckGroup ℍ z z')
    (hw : MulAction.orbitRel X.deckGroup ℍ w w') :
    X.liftOrbitDist z w = X.liftOrbitDist z' w' := by
  obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hz)
  obtain ⟨η, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hw)
  rw [X.liftOrbitDist_smul_left, X.liftOrbitDist_smul_right]

/-- The actual orbit distance, well-defined on the existing carrier. -/
noncomputable def orbitDist {g : ℕ} (X : ClosedHyperbolicSurface g) :
    X.Carrier → X.Carrier → ℝ :=
  Quotient.lift₂ X.liftOrbitDist (X.liftOrbitDist_congr)

@[simp] theorem orbitDist_mk {g : ℕ} (X : ClosedHyperbolicSurface g) (z w : ℍ) :
    X.orbitDist (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) z)
      (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) w) = X.liftOrbitDist z w := rfl

theorem orbitDist_self {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z : X.Carrier) : X.orbitDist z z = 0 := by
  induction z using Quotient.inductionOn with
  | h z => exact X.liftOrbitDist_self z

theorem orbitDist_comm {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : X.Carrier) : X.orbitDist z w = X.orbitDist w z := by
  induction z, w using Quotient.inductionOn₂ with
  | h z w => exact X.liftOrbitDist_comm z w

theorem orbitDist_triangle {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w u : X.Carrier) : X.orbitDist z u ≤ X.orbitDist z w + X.orbitDist w u := by
  induction z, w, u using Quotient.inductionOn₃ with
  | h z w u => exact X.liftOrbitDist_triangle z w u

theorem eq_of_orbitDist_eq_zero {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : X.Carrier) (h : X.orbitDist z w = 0) : z = w := by
  induction z, w using Quotient.inductionOn₂ with
  | h z w =>
    obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist z w
    have heq : z = γ • w := dist_eq_zero.mp (hγ.symm.trans h)
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨γ, heq.symm⟩)

/-- Balls for the constructed distance are exactly the actual orbit images. -/
theorem orbitDist_ball_eq_orbitBall {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r : ℝ) :
    {q : X.Carrier | X.orbitDist (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) o) q < r} =
      X.orbitBall o r := by
  ext q
  induction q using Quotient.inductionOn with
  | h z =>
    rw [Set.mem_setOf_eq, X.orbitDist_mk, X.mem_orbitBall_mk_iff]
    constructor
    · intro h
      obtain ⟨γ, hγ⟩ := X.exists_liftOrbitDist_eq_dist o z
      exact ⟨γ, by simpa only [mem_ball, dist_comm, ← hγ] using h⟩
    · rintro ⟨γ, hγ⟩
      exact (X.liftOrbitDist_le o z γ).trans_lt (by simpa only [mem_ball, dist_comm] using hγ)

theorem isOpen_orbitDist_ball {g : ℕ} (X : ClosedHyperbolicSurface g)
    (q : X.Carrier) (r : ℝ) : IsOpen {p : X.Carrier | X.orbitDist q p < r} := by
  obtain ⟨o, rfl⟩ := Quotient.mk_surjective q
  rw [X.orbitDist_ball_eq_orbitBall]
  exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap _ Metric.isOpen_ball

/-- The constructed distance gives exactly the pre-existing quotient topology. -/
theorem isOpen_iff_orbitDist {g : ℕ} (X : ClosedHyperbolicSurface g)
    (s : Set X.Carrier) :
    IsOpen s ↔ ∀ q ∈ s, ∃ ε > 0, ∀ p, X.orbitDist q p < ε → p ∈ s := by
  constructor
  · intro hs q hq
    obtain ⟨o, rfl⟩ := Quotient.mk_surjective q
    have hopen := hs.preimage (continuous_quot_mk :
      Continuous (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)))
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen o hq
    refine ⟨ε, hε, ?_⟩
    intro p hp
    have himage : X.orbitBall o ε ⊆ s := Set.image_subset_iff.mpr hsub
    exact himage ((X.orbitDist_ball_eq_orbitBall o ε) ▸ hp)
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    obtain ⟨ε, hε, hsub⟩ := h q hq
    apply _root_.mem_nhds_iff.mpr
    refine ⟨{p : X.Carrier | X.orbitDist q p < ε}, hsub,
      X.isOpen_orbitDist_ball q ε, ?_⟩
    simpa only [Set.mem_setOf_eq, X.orbitDist_self] using hε

/-- The actual quotient metric, retaining the carrier topology definitionally. -/
noncomputable instance carrierMetricSpace {g : ℕ} (X : ClosedHyperbolicSurface g) :
    MetricSpace X.Carrier :=
  MetricSpace.ofDistTopology X.orbitDist X.orbitDist_self X.orbitDist_comm
    X.orbitDist_triangle X.isOpen_iff_orbitDist X.eq_of_orbitDist_eq_zero

@[simp] theorem carrier_dist_eq_orbitDist {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z w : X.Carrier) : dist z w = X.orbitDist z w := rfl

/-- Actual downstairs metric balls are the existing upstairs-ball images. -/
theorem carrier_ball_eq_orbitBall {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (r : ℝ) :
    Metric.ball (Quotient.mk (MulAction.orbitRel X.deckGroup ℍ) o) r = X.orbitBall o r := by
  simpa only [Metric.ball, X.carrier_dist_eq_orbitDist, X.orbitDist_comm] using
    X.orbitDist_ball_eq_orbitBall o r

#print axioms carrierMetricSpace
#print axioms carrier_ball_eq_orbitBall

end SystolicGrowth.ClosedHyperbolicSurface
