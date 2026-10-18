module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingPuncturedComponents
public import Geometry.SurfaceOrbitLocalIsometry

@[expose] public section

/-!
# Continuous lifts through actual embedded orbit balls

The quotient projection restricts to a homeomorphism below half the systole.
Its inverse lifts any continuous map confined to that actual orbit ball.
Only distance from the center is identified on the whole lifted ball; nearby
pairwise distances are identified separately on quarter-systole charts.
-/

open Set Metric
open scoped UpperHalfPlane Topology

namespace SystolicGrowth.ClosedHyperbolicSurface

/-- The actual upstairs ball is homeomorphic to its quotient image under
the half-systole injectivity bound. No all-pairs isometry is asserted. -/
noncomputable def orbitBallHomeomorph {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) :
    Metric.ball o R ≃ₜ X.orbitBall o R :=
  (X.quotientBall_isOpenEmbedding o R hR).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext q
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.1, z.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩))

@[simp] theorem orbitBallHomeomorph_apply_coe {g : ℕ} (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole) (z : Metric.ball o R) :
    (X.orbitBallHomeomorph o R hR z : X.Carrier) = (Quotient.mk'' z.1 : X.Carrier) := rfl

/-- A continuous map confined to an actual embedded orbit ball has a
continuous lift into the original upstairs ball. The existing orbit metric
retains the exact radial distance from its center. -/
theorem exists_continuous_lift_into_orbitBall
    {g : ℕ} {A : Type*} [TopologicalSpace A] (X : ClosedHyperbolicSurface g)
    (o : ℍ) (R : ℝ) (hR : 2 * R < X.systole)
    (f : A → X.Carrier) (hf : Continuous f) (hball : ∀ t, f t ∈ X.orbitBall o R) :
    ∃ σ : A → ℍ, Continuous σ ∧
      (∀ t, (Quotient.mk'' (σ t) : X.Carrier) = f t) ∧
      (∀ t, σ t ∈ Metric.ball o R) ∧
      (∀ t, dist (Quotient.mk'' o : X.Carrier) (f t) = dist o (σ t)) := by
  let e := X.orbitBallHomeomorph o R hR
  let fball : A → X.orbitBall o R := fun t => ⟨f t, hball t⟩
  let σball : A → Metric.ball o R := e.symm ∘ fball
  let σ : A → ℍ := fun t => (σball t).1
  have hσ : Continuous σ :=
    continuous_subtype_val.comp (e.symm.continuous.comp (hf.subtype_mk hball))
  have hlift : ∀ t, (Quotient.mk'' (σ t) : X.Carrier) = f t := by
    intro t
    have heq := congrArg Subtype.val (e.apply_symm_apply (fball t))
    exact heq
  refine ⟨σ, hσ, hlift, fun t => (σball t).2, ?_⟩
  intro t
  rw [← hlift t]
  exact X.carrier_dist_mk_center_eq_of_mem_closedBall o R hR
    (Metric.ball_subset_closedBall (σball t).2)

/-- Every continuous actual lift preserves pairwise quotient distances on
a parameter neighborhood. The proof uses a freshly centered radius below
one quarter of the systole, independently of any larger containing ball. -/
theorem continuous_lift_locally_dist_eq
    {g : ℕ} {A : Type*} [MetricSpace A] (X : ClosedHyperbolicSurface g)
    (hsys : 0 < X.systole) (σ : A → ℍ) (hσ : Continuous σ)
    (f : A → X.Carrier) (hlift : ∀ t, (Quotient.mk'' (σ t) : X.Carrier) = f t) (t : A) :
    ∃ η > 0, ∀ u v : A, dist u t < η → dist v t < η →
      dist (σ u) (σ v) = dist (f u) (f v) := by
  let ρ := X.systole / 8
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρsys : 4 * ρ < X.systole := by dsimp only [ρ]; linarith
  have hpre : σ ⁻¹' Metric.ball (σ t) ρ ∈ 𝓝 t :=
    hσ.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  obtain ⟨η, hη, hsmall⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨η, hη, ?_⟩
  intro u v hu hv
  have heq := X.carrier_dist_mk_eq_of_mem_small_ball (σ t) ρ hρsys
    (hsmall hu) (hsmall hv)
  change dist (Quotient.mk'' (σ u) : X.Carrier) (Quotient.mk'' (σ v) : X.Carrier) =
    dist (σ u) (σ v) at heq
  rw [hlift u, hlift v] at heq
  exact heq.symm

#print axioms orbitBallHomeomorph
#print axioms exists_continuous_lift_into_orbitBall
#print axioms continuous_lift_locally_dist_eq

end SystolicGrowth.ClosedHyperbolicSurface
