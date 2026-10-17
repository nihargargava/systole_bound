module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Core.SystolicCore
public import Vendored.RiemannDynamics.Hyperbolic.PlaneGeometry.TriangleArea
public import Vendored.RiemannDynamics.Teichmuller.CompactCovering
public import Vendored.RiemannDynamics.Teichmuller.DirichletFundamentalDomain
public import Mathlib.SetTheory.Cardinal.Free

@[expose] public section

open MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise UpperHalfPlane

namespace SystolicGrowth

/-! # Project bridges for the vendored RiemannDynamics geometry

This module keeps upstream declarations in their attributed vendored namespace
and exposes only the specializations used by this repository.
-/

namespace ClosedHyperbolicSurface

/-- A closed hyperbolic surface admits a compact subset of the upper half
plane meeting every deck-group orbit. -/
theorem exists_compact_covering {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ z : ℍ, ∃ γ : X.deckGroup, γ • z ∈ K := by
  exact Vendored.RiemannDynamics.exists_compact_covering
    X.deckGroup X.carrierCompactSpace

/-- The compact orbit-covering set has finite hyperbolic area.  This is the
measure-theoretic form used when an orbit-cover is converted into a bounded
quotient-area estimate. -/
theorem exists_compact_covering_finite_volume {g : ℕ}
    (X : ClosedHyperbolicSurface g) :
    ∃ K : Set ℍ, IsCompact K ∧ volume K ≠ ∞ ∧
      ∀ z : ℍ, ∃ γ : X.deckGroup, γ • z ∈ K := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  refine ⟨K, hK, ?_, hcover⟩
  exact ne_of_lt hK.measure_lt_top

/-- The closed Dirichlet region centered at any point is a measurable
fundamental domain for a closed hyperbolic surface's deck action. -/
theorem dirichletDomain_isFundamentalDomain {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    IsFundamentalDomain X.deckGroup
      (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) volume := by
  exact Vendored.RiemannDynamics.isFundamentalDomain_dirichletDomain
    (Γ := X.deckGroup) (τ₀ := o) (hproper := inferInstance)
    (hfree := fun γ hγ ↦ X.free γ o hγ)

/-- The hyperbolic covolume of the deck action is the area of its canonical
Dirichlet domain. This fixes the quotient-area quantity that a future
Gauss--Bonnet argument must evaluate in terms of the genus. -/
theorem covolume_eq_dirichletDomain_volume {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ) :
    covolume X.deckGroup ℍ volume =
      volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  letI : Countable (SurfaceGroup g) := by
    change Countable (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure ({surfaceRelator g} : Set (FreeGroup (SurfaceGenerator g))))))
    infer_instance
  letI : Countable X.deckGroup :=
    (Equiv.countable_iff X.marking.toEquiv).mpr inferInstance
  letI : SMulInvariantMeasure X.deckGroup ℍ volume :=
    ⟨fun γ s hs => SMulInvariantMeasure.measure_preimage_smul
      (M := GL (Fin 2) ℝ)
      (Matrix.SpecialLinearGroup.mapGL ℝ
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)) hs⟩
  exact (X.dirichletDomain_isFundamentalDomain o).covolume_eq_volume volume

/-! ## Compactness of the canonical Dirichlet region

The compact orbit-cover is enough to bound the Dirichlet region itself.  This
is the missing geometric step before applying finite-volume measure facts: a
point in the Dirichlet region can be moved into the compact cover, and the
Dirichlet inequalities then bound its distance from the center. -/

theorem isCompact_dirichletDomain_of_compact_covering {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ)
    (K : Set ℍ) (hK : IsCompact K)
    (hcover : ∀ z : ℍ, ∃ γ : X.deckGroup, γ • z ∈ K) :
    IsCompact (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Vendored.RiemannDynamics.isClosed_dirichletDomain X.deckGroup o
  · obtain ⟨R, hR⟩ :=
      (Metric.isBounded_iff_subset_closedBall o).mp hK.isBounded
    apply (Metric.isBounded_iff_subset_closedBall o).mpr
    refine ⟨R, ?_⟩
    intro z hz
    obtain ⟨γ, hγK⟩ := hcover z
    have hdist : dist (γ • z) o ≤ R := by
      exact hR hγK
    have hdir := (Vendored.RiemannDynamics.mem_dirichletDomain.mp hz) γ⁻¹
    have hrewrite : dist z ((γ⁻¹ : X.deckGroup) • o) = dist (γ • z) o := by
      rw [← dist_smul γ z ((γ⁻¹ : X.deckGroup) • o)]
      simp
    rw [hrewrite] at hdir
    exact hdir.trans hdist

theorem dirichletDomain_finite_volume_of_compact_covering {g : ℕ}
    (X : ClosedHyperbolicSurface g) (o : ℍ)
    (K : Set ℍ) (hK : IsCompact K)
    (hcover : ∀ z : ℍ, ∃ γ : X.deckGroup, γ • z ∈ K) :
    volume (Vendored.RiemannDynamics.dirichletDomain X.deckGroup o) ≠ ∞ :=
  (isCompact_dirichletDomain_of_compact_covering X o K hK hcover).measure_lt_top.ne

/-- A closed marked hyperbolic surface has finite deck-group covolume. -/
theorem covolume_ne_top {g : ℕ} (X : ClosedHyperbolicSurface g) :
    covolume X.deckGroup ℍ volume ≠ ∞ := by
  obtain ⟨K, hK, hcover⟩ := X.exists_compact_covering
  rw [X.covolume_eq_dirichletDomain_volume (I : ℍ)]
  exact X.dirichletDomain_finite_volume_of_compact_covering I K hK hcover

end ClosedHyperbolicSurface

/-! ## Hyperbolic triangle area -/

/-- The vendored triangle-area theorem in the repository namespace. -/
theorem volume_geodesicTriangle_eq_angleDeficit
    (v₁ v₂ v₃ : ℍ) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    volume (Vendored.RiemannDynamics.hyperbolicTriangle v₁ v₂ v₃) =
      ENNReal.ofReal
        (Real.pi - Vendored.RiemannDynamics.sectorAngle v₁ v₂ v₃
          - Vendored.RiemannDynamics.sectorAngle v₂ v₁ v₃
          - Vendored.RiemannDynamics.sectorAngle v₃ v₁ v₂) :=
  Vendored.RiemannDynamics.volume_hyperbolicTriangle v₁ v₂ v₃ h₁₂ h₁₃ h₂₃

/-- The angle deficit of a nondegenerate geodesic triangle is nonnegative. -/
theorem geodesicTriangle_angleDeficit_nonneg
    (v₁ v₂ v₃ : ℍ) (h₁₂ : v₁ ≠ v₂) (h₁₃ : v₁ ≠ v₃) (h₂₃ : v₂ ≠ v₃) :
    0 ≤ Real.pi - Vendored.RiemannDynamics.sectorAngle v₁ v₂ v₃
      - Vendored.RiemannDynamics.sectorAngle v₂ v₁ v₃
      - Vendored.RiemannDynamics.sectorAngle v₃ v₁ v₂ :=
  Vendored.RiemannDynamics.deficit_nonneg v₁ v₂ v₃ h₁₂ h₁₃ h₂₃

end SystolicGrowth
