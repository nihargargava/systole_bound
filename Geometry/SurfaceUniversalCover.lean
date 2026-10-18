module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SurfaceDeckCovering
public import Vendored.TauCeti.AlgebraicTopology.UniversalCover.Covering
public import Vendored.TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Covering
public import Vendored.TauCeti.Topology.IsLocalHomeomorph

@[expose] public section

/-!
# Universal covers and the native hyperbolic quotient

Tau Ceti supplies the generic based-path universal cover, absent from the pinned
Mathlib. The identification of simply connected covers and all lifting below use
Mathlib directly. This is a topological identification; it does not assert an
isometry for an arbitrary replacement metric or lift projective holonomy to SL₂.
-/

open scoped UpperHalfPlane

namespace SystolicGrowth

noncomputable section

/-- A loop lifts to a closed loop in a simply connected covering space exactly
when it is nullhomotopic downstairs. This uses Mathlib's path and homotopy
lifting at an arbitrary point of the total space, without a deck-group marking. -/
theorem simplyConnectedCover_liftPath_one_eq_iff
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [SimplyConnectedSpace E] {p : E → B} (hp : IsCoveringMap p)
    (e : E) (β : Path (p e) (p e)) :
    hp.liftPath β e β.source 1 = e ↔ β.Homotopic (Path.refl (p e)) := by
  constructor
  · intro h
    let Γ : Path e e := ⟨hp.liftPath β e β.source,
      hp.liftPath_zero β e β.source, h⟩
    have hΓ : Γ.map hp.continuous = β := by
      ext t
      exact congrFun (hp.liftPath_lifts β e β.source) t
    have hrefl : (Path.refl e).map hp.continuous = Path.refl (p e) := by
      ext t
      rfl
    simpa only [hΓ, hrefl] using
      (SimplyConnectedSpace.paths_homotopic Γ (Path.refl e)).map ⟨p, hp.continuous⟩
  · intro h
    have hone := hp.liftPath_apply_one_eq_of_homotopicRel h e β.source rfl
    change hp.liftPath β e β.source 1 =
      hp.liftPath (ContinuousMap.const _ (p e)) e rfl 1 at hone
    rw [hp.liftPath_const (e := e) rfl] at hone
    exact hone

/-- Based simply connected covers of the same space are homeomorphic over that
space. Both inverse maps are supplied by Mathlib's unique lifting theorem. -/
def simplyConnectedCoverEquiv
    {E F B : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
    [SimplyConnectedSpace E] [SimplyConnectedSpace F]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace F]
    {p : E → B} {q : F → B} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (e : E) (f : F) (he : p e = q f) :
    {h : E ≃ₜ F // q ∘ h = p ∧ h e = f} := by
  let liftsL := hq.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ e f he.symm
  let liftsR := hp.existsUnique_continuousMap_lifts ⟨q, hq.continuous⟩ f e he
  let L := liftsL.choose
  let R := liftsR.choose
  have hL : L e = f ∧ q ∘ L = p := liftsL.choose_spec.1
  have hR : R f = e ∧ p ∘ R = q := liftsR.choose_spec.1
  have hRL : (R : F → E) ∘ L = id := hp.eq_of_comp_eq
    (R.continuous.comp L.continuous) continuous_id (by
      funext x
      change p (R (L x)) = p x
      exact (congrFun hR.2 (L x)).trans (congrFun hL.2 x)) e (by
      change R (L e) = e
      rw [hL.1, hR.1])
  have hLR : (L : E → F) ∘ R = id := hq.eq_of_comp_eq
    (L.continuous.comp R.continuous) continuous_id (by
      funext x
      change q (L (R x)) = q x
      exact (congrFun hL.2 (R x)).trans (congrFun hR.2 x)) f (by
      change L (R f) = f
      rw [hR.1, hL.1])
  exact ⟨{
    toFun := L
    invFun := R
    left_inv := congrFun hRL
    right_inv := congrFun hLR
    continuous_toFun := L.continuous
    continuous_invFun := R.continuous }, hL.2, hL.1⟩

namespace ClosedHyperbolicSurface

/-- The original quotient satisfies the standing hypothesis for the generic
universal-cover construction, because its actual cover ℍ is simply connected. -/
instance carrierSemilocallySimplyConnectedSpace {g : ℕ} (X : ClosedHyperbolicSurface g) :
    TauCeti.SemilocallySimplyConnectedSpace X.Carrier :=
  TauCeti.SemilocallySimplyConnectedSpace.of_isCoveringMap
    X.orbitProjection_isCoveringMap X.orbitProjection_isQuotientCoveringMap.surjective

/-- The generic based-path universal cover of the original surface. -/
abbrev basedUniversalCover {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ) :=
  TauCeti.UniversalCover (X.orbitProjection z)

instance basedUniversalCoverLocallyPathConnectedSpace {g : ℕ}
    (X : ClosedHyperbolicSurface g) (z : ℍ) :
    LocallyPathConnectedSpace (X.basedUniversalCover z) :=
  IsLocalHomeomorph.locallyPathConnectedSpace
    (TauCeti.UniversalCover.isCoveringMap (X.orbitProjection z)).isLocalHomeomorph

/-- The based-path cover is the existing hyperbolic cover, over the unchanged
surface carrier and with the constant-path basepoint corresponding to `z`. -/
def basedUniversalCoverEquiv {g : ℕ} (X : ClosedHyperbolicSurface g) (z : ℍ) :
    {h : X.basedUniversalCover z ≃ₜ ℍ //
      X.orbitProjection ∘ h = TauCeti.UniversalCover.proj ∧
      h (TauCeti.UniversalCover.basepointLift (X.orbitProjection z)) = z} :=
  simplyConnectedCoverEquiv
    (TauCeti.UniversalCover.isCoveringMap (X.orbitProjection z))
    X.orbitProjection_isCoveringMap
    (TauCeti.UniversalCover.basepointLift (X.orbitProjection z)) z
    (TauCeti.UniversalCover.proj_basepointLift (X.orbitProjection z))

#print axioms basedUniversalCoverEquiv

end ClosedHyperbolicSurface

#print axioms simplyConnectedCoverEquiv
#print axioms simplyConnectedCover_liftPath_one_eq_iff

end

end SystolicGrowth
