module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Core.SystolicCore
public import Geometry.CoveringCompactLift
public import Vendored.DifferentialGeometry.DeckGroup

@[expose] public section

/-!
# The actual covering and deck group of a marked hyperbolic surface

The original orbit projection is a covering, and its full group of continuous
deck transformations is the given marked group. No replacement of the carrier,
topology, upper-half-plane metric, or faithful SL(2,R) representation is made.
-/

open scoped UpperHalfPlane
open scoped unitInterval

namespace SystolicGrowth.ClosedHyperbolicSurface

noncomputable section

/-- The quotient projection on the original surface carrier. -/
def orbitProjection {g : ℕ} (X : ClosedHyperbolicSurface g) : ℍ → X.Carrier :=
  Quotient.mk (MulAction.orbitRel X.deckGroup ℍ)

/-- Freeness and proper discontinuity make the native orbit projection a covering. -/
theorem orbitProjection_isQuotientCoveringMap {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsQuotientCoveringMap X.orbitProjection X.deckGroup := by
  letI : IsCancelSMul X.deckGroup ℍ :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr X.free
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem orbitProjection_isCoveringMap {g : ℕ} (X : ClosedHyperbolicSurface g) :
    IsCoveringMap X.orbitProjection :=
  X.orbitProjection_isQuotientCoveringMap.isCoveringMap

/-- **Math.** Compactness of the closed quotient gives an actual compact set in `ℍ`
meeting every orbit of the marked deck group. The construction uses the
quotient covering map, not a presumed compact Dirichlet domain. -/
theorem exists_compact_orbit_cover {g : ℕ} (X : ClosedHyperbolicSurface g) :
    ∃ K : Set ℍ, IsCompact K ∧
      ∀ z : ℍ, ∃ γ : X.deckGroup, γ • z ∈ K := by
  letI : CompactSpace X.Carrier := X.carrierCompactSpace
  obtain ⟨K, hK, hprojection⟩ :=
    exists_compact_set_surjecting_under_covering X.orbitProjection
      X.orbitProjection_isCoveringMap X.orbitProjection_isQuotientCoveringMap.surjective
  refine ⟨K, hK, ?_⟩
  intro z
  have hz : X.orbitProjection z ∈ X.orbitProjection '' K := by
    rw [hprojection]
    exact Set.mem_univ _
  obtain ⟨k, hk, hquotient⟩ := hz
  have horbit : z ∈ MulAction.orbit X.deckGroup k :=
    X.orbitProjection_isQuotientCoveringMap.apply_eq_iff_mem_orbit.mp hquotient.symm
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp horbit
  refine ⟨γ⁻¹, ?_⟩
  rw [← hγ, inv_smul_smul]
  exact hk

/-- All actual continuous deck transformations of this projection. -/
abbrev actualDeckGroup {g : ℕ} (X : ClosedHyperbolicSurface g) :=
  Vendored.DifferentialGeometry.coveringDeckGroup X.orbitProjection

/-- The full actual deck group, not an assumed subgroup, is the marked acting group. -/
noncomputable def actualDeckGroupEquiv {g : ℕ} (X : ClosedHyperbolicSurface g) :
    X.actualDeckGroup ≃* X.deckGroup :=
  X.orbitProjection_isQuotientCoveringMap.deckGroupMulEquiv.symm

@[simp] theorem actualDeckGroupEquiv_smul {g : ℕ} (X : ClosedHyperbolicSurface g)
    (δ : X.actualDeckGroup) (z : ℍ) :
    X.actualDeckGroupEquiv δ • z = δ • z :=
  X.orbitProjection_isQuotientCoveringMap.deckGroupMulEquiv_symm_apply δ z

/-- The original genus marking transported to all actual deck transformations. -/
noncomputable def actualDeckGroupMarking {g : ℕ} (X : ClosedHyperbolicSurface g) :
    X.actualDeckGroup ≃* SurfaceGroup g :=
  X.actualDeckGroupEquiv.trans X.marking

/-- The fundamental group of the marked quotient is the opposite of its
marked deck group.  This is Mathlib's quotient-covering classification:
`ℍ` is simply connected, and the opposite records the monodromy convention.
The result is the topological marking bridge needed when constructing
holonomy from a replacement surface. -/
noncomputable def fundamentalGroupMarking {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z : ℍ) : FundamentalGroup X.Carrier (X.orbitProjection z) ≃* (SurfaceGroup g)ᵐᵒᵖ :=
  X.orbitProjection_isQuotientCoveringMap.fundamentalGroupEquiv
    (⟨z, rfl⟩ : X.orbitProjection ⁻¹' {X.orbitProjection z}) |>.trans
      (MulEquiv.op X.marking)

/-- The actual lift of a based loop, starting at the specified point of ℍ. -/
def loopLift {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) : C(I, ℍ) :=
  X.orbitProjection_isCoveringMap.liftPath γ z γ.source

@[simp] theorem loopLift_zero {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) :
    X.loopLift z γ 0 = z :=
  X.orbitProjection_isCoveringMap.liftPath_zero γ z γ.source

@[simp] theorem orbitProjection_loopLift {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z : ℍ) (γ : Path (X.orbitProjection z) (X.orbitProjection z)) (t : I) :
    X.orbitProjection (X.loopLift z γ t) = γ t :=
  congrFun (X.orbitProjection_isCoveringMap.liftPath_lifts γ z γ.source) t

/-- Uniqueness is for all continuous lifts, not merely for a chosen lift. -/
theorem eq_loopLift_iff {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) (Γ : C(I, ℍ)) :
    Γ = X.loopLift z γ ↔ X.orbitProjection ∘ Γ = γ ∧ Γ 0 = z :=
  X.orbitProjection_isCoveringMap.eq_liftPath_iff' γ.source

/-- The marked deck element represented by a loop. The opposite in the marking
is removed only after evaluation, preserving Mathlib's monodromy convention. -/
def loopDeckElement {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) : X.deckGroup :=
  X.marking.symm (X.fundamentalGroupMarking z (FundamentalGroup.fromPath (.mk γ))).unop

/-- A lifted loop ends at the translate by precisely its marked deck element. -/
theorem loopLift_one {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) :
    X.loopLift z γ 1 = X.loopDeckElement z γ • z := by
  have h := X.orbitProjection_isQuotientCoveringMap.unop_fundamentalGroupToMulOpposite_smul
    (e := (⟨z, rfl⟩ : X.orbitProjection ⁻¹' {X.orbitProjection z}))
    (γ := FundamentalGroup.fromPath (.mk γ))
  have hdeck : X.loopDeckElement z γ =
      (X.orbitProjection_isQuotientCoveringMap.fundamentalGroupToMulOpposite
        (⟨z, rfl⟩ : X.orbitProjection ⁻¹' {X.orbitProjection z})
        (FundamentalGroup.fromPath (.mk γ))).unop := by
    exact X.marking.symm_apply_apply _
  rw [hdeck]
  exact h.symm

/-- The deck element is trivial exactly for nullhomotopic based loops. -/
theorem loopDeckElement_eq_one_iff {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) :
    X.loopDeckElement z γ = 1 ↔ γ.Homotopic (Path.refl (X.orbitProjection z)) := by
  rw [loopDeckElement, X.marking.symm.map_eq_one_iff,
    MulOpposite.unop_eq_one_iff, (X.fundamentalGroupMarking z).map_eq_one_iff,
    FundamentalGroup.one_def]
  exact Path.Homotopic.Quotient.eq

/-- Closure of the actual lift detects nullhomotopy downstairs. -/
theorem loopLift_one_eq_iff {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (γ : Path (X.orbitProjection z) (X.orbitProjection z)) :
    X.loopLift z γ 1 = z ↔ γ.Homotopic (Path.refl (X.orbitProjection z)) := by
  rw [loopLift_one, ← loopDeckElement_eq_one_iff]
  exact ⟨X.free _ z, fun h => by rw [h, one_smul]⟩

/-- Project a path between a point and one of its deck translates to a based loop. -/
def projectedDeckPath {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (δ : X.deckGroup) (Γ : Path z (δ • z)) :
    Path (X.orbitProjection z) (X.orbitProjection z) :=
  (Γ.map X.orbitProjection_isCoveringMap.continuous).cast rfl
    (X.orbitProjection_isQuotientCoveringMap.map_smul δ).symm

/-- The lift recovers the original path, not just its endpoints. -/
theorem loopLift_projectedDeckPath {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ)
    (δ : X.deckGroup) (Γ : Path z (δ • z)) :
    X.loopLift z (X.projectedDeckPath z δ Γ) = (Γ : C(I, ℍ)) := by
  symm
  apply (X.eq_loopLift_iff z _ _).mpr
  exact ⟨rfl, Γ.source⟩

/-- Any path to a nonidentity deck translate projects to an essential loop.
This holds at every basepoint, without restricting to a translation axis. -/
theorem projectedDeckPath_nullhomotopic_iff {g : ℕ} (X : ClosedHyperbolicSurface g)
    (z : ℍ) (δ : X.deckGroup) (Γ : Path z (δ • z)) :
    (X.projectedDeckPath z δ Γ).Homotopic (Path.refl (X.orbitProjection z)) ↔ δ = 1 := by
  rw [← X.loopLift_one_eq_iff, X.loopLift_projectedDeckPath]
  change Γ 1 = z ↔ δ = 1
  rw [Γ.target]
  exact ⟨X.free δ z, fun h => by rw [h, one_smul]⟩

/-- Every actual deck transformation preserves the original Poincare metric. -/
theorem actualDeckGroup_isometry {g : ℕ} (X : ClosedHyperbolicSurface g)
    (δ : X.actualDeckGroup) : Isometry (fun z : ℍ => δ • z) := by
  have heq : (fun z : ℍ => δ • z) =
      (fun z : ℍ => X.actualDeckGroupEquiv δ • z) := by
    funext z
    exact (X.actualDeckGroupEquiv_smul δ z).symm
  rw [heq]
  exact isometry_smul ℍ (X.actualDeckGroupEquiv δ : Matrix.SpecialLinearGroup (Fin 2) ℝ)

#print axioms orbitProjection_isCoveringMap
#print axioms actualDeckGroupEquiv
#print axioms actualDeckGroupMarking
#print axioms fundamentalGroupMarking
#print axioms exists_compact_orbit_cover
#print axioms loopLift_one
#print axioms loopDeckElement_eq_one_iff
#print axioms loopLift_one_eq_iff
#print axioms projectedDeckPath_nullhomotopic_iff
#print axioms actualDeckGroup_isometry

end

end SystolicGrowth.ClosedHyperbolicSurface
