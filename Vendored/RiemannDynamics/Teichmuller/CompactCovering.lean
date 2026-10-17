module

/-
Copyright (c) 2026 Will (Ziang) Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will (Ziang) Li
-/

/-
## Vendoring provenance

The theorem in this file is ported from
`RiemannDynamics/Teichmuller/Compactness/Covolume.lean` at immutable upstream commit
`b3fa37cc0f18a23ea66b654ea3f73eb472129010` of
https://github.com/will1491/RiemannDynamics. The upstream file is Apache-2.0 licensed.
The upstream Mumford import was replaced by the two direct mathlib imports below, and the
namespace was nested under `SystolicGrowth.Vendored`; the proof itself is unchanged.
-/

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Topology.Algebra.ConstMulAction

@[expose] public section

/-!
# Compact covering sets for cocompact upper-half-plane actions

A cocompact subgroup of `SL(2, ℝ)` acting on the upper half plane admits a compact set meeting
every orbit.
-/

namespace SystolicGrowth.Vendored.RiemannDynamics

/-- A cocompact action on the upper half plane admits a compact set meeting every orbit. -/
theorem exists_compact_covering (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (hcc : CompactSpace (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ τ : UpperHalfPlane, ∃ γ : Γ, γ • τ ∈ K := by
  have : ContinuousConstSMul (↥Γ) UpperHalfPlane :=
    ⟨fun c => (isometry_smul UpperHalfPlane
      (c : Matrix.SpecialLinearGroup (Fin 2) ℝ)).continuous⟩
  have hq : IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane)) :=
    MulAction.isOpenQuotientMap_quotientMk
  have hcover : (Set.univ : Set (Quotient (MulAction.orbitRel Γ UpperHalfPlane))) ⊆
      ⋃ τ : UpperHalfPlane,
        Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) '' Metric.ball τ 1 := by
    rintro x -
    obtain ⟨τ, rfl⟩ := hq.surjective x
    exact Set.mem_iUnion.mpr ⟨τ, Set.mem_image_of_mem _ (Metric.mem_ball_self one_pos)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun τ : UpperHalfPlane =>
      Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) '' Metric.ball τ 1)
    (fun τ => hq.isOpenMap _ Metric.isOpen_ball) hcover
  refine ⟨⋃ i ∈ t, Metric.closedBall i 1,
    t.finite_toSet.isCompact_biUnion fun i _ => isCompact_closedBall i 1, fun τ => ?_⟩
  have hmem := ht (Set.mem_univ (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) τ))
  obtain ⟨i, hi, y, hy, hqy⟩ := Set.mem_iUnion₂.mp hmem
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact hqy))
  exact ⟨γ, hγ ▸ Set.mem_biUnion hi (Metric.ball_subset_closedBall hy)⟩

end SystolicGrowth.Vendored.RiemannDynamics
