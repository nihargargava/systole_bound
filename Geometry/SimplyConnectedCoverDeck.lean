module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homeomorph.Defs

@[expose] public section

/-!
# Deck transformations of simply connected covering spaces

For a covering with simply connected, locally path-connected total space,
fiber points are related by a unique projection-preserving homeomorphism once
its value at one point is fixed. The proof uses Mathlib's unique lifting
theorem in both directions.
-/

namespace SystolicGrowth

noncomputable section

universe u v

/-- A simply connected covering space has a deck homeomorphism taking any
point to any other point in the same fiber. -/
theorem exists_simplyConnectedCoverDeckHomeomorph
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p)
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (e₀ e₁ : E) (h₀₁ : p e₀ = p e₁) :
    ∃ τ : E ≃ₜ E, τ e₀ = e₁ ∧ ∀ e, p (τ e) = p e := by
  let pC : C(E, B) := ⟨p, hp.continuous⟩
  obtain ⟨τ, ⟨hτ₀, hτp⟩, hτuniq⟩ :=
    hp.existsUnique_continuousMap_lifts pC e₀ e₁ h₀₁.symm
  obtain ⟨σ, ⟨hσ₀, hσp⟩, hσuniq⟩ :=
    hp.existsUnique_continuousMap_lifts pC e₁ e₀ h₀₁
  obtain ⟨ι₀, ⟨hι₀, hι₀p⟩, hι₀uniq⟩ :=
    hp.existsUnique_continuousMap_lifts pC e₀ e₀ rfl
  obtain ⟨ι₁, ⟨hι₁, hι₁p⟩, hι₁uniq⟩ :=
    hp.existsUnique_continuousMap_lifts pC e₁ e₁ rfl
  have hστ₀ : (σ.comp τ) e₀ = e₀ := by
    simp only [ContinuousMap.comp_apply, hτ₀, hσ₀]
  have hστp : p ∘ (σ.comp τ) = pC := by
    funext e
    change p (σ (τ e)) = p e
    calc
      p (σ (τ e)) = p (τ e) := congrFun hσp (τ e)
      _ = p e := congrFun hτp e
  have hτσ₁ : (τ.comp σ) e₁ = e₁ := by
    simp only [ContinuousMap.comp_apply, hσ₀, hτ₀]
  have hτσp : p ∘ (τ.comp σ) = pC := by
    funext e
    change p (τ (σ e)) = p e
    calc
      p (τ (σ e)) = p (σ e) := congrFun hτp (σ e)
      _ = p e := congrFun hσp e
  have hId₀ : (ContinuousMap.id E) e₀ = e₀ ∧ p ∘ (ContinuousMap.id E) = pC := by
    constructor
    · rfl
    · funext e
      rfl
  have hId₁ : (ContinuousMap.id E) e₁ = e₁ ∧ p ∘ (ContinuousMap.id E) = pC := by
    constructor
    · rfl
    · funext e
      rfl
  have hστ : σ.comp τ = ContinuousMap.id E := by
    exact (hι₀uniq (σ.comp τ) ⟨hστ₀, hστp⟩).trans
      (hι₀uniq (ContinuousMap.id E) hId₀).symm
  have hτσ : τ.comp σ = ContinuousMap.id E := by
    exact (hι₁uniq (τ.comp σ) ⟨hτσ₁, hτσp⟩).trans
      (hι₁uniq (ContinuousMap.id E) hId₁).symm
  let e : E ≃ E := {
    toFun := τ
    invFun := σ
    left_inv x := by
      simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply] using
        congrArg (fun f : C(E, E) => f x) hστ
    right_inv x := by
      simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply] using
        congrArg (fun f : C(E, E) => f x) hτσ }
  refine ⟨Homeomorph.mk e τ.continuous σ.continuous, hτ₀, ?_⟩
  intro x
  exact congrFun hτp x

/-- A projection-preserving homeomorphism of a simply connected cover is
determined by its value at a single point; in particular, a fixed point
forces it to be the identity. -/
theorem simplyConnectedCoverDeckHomeomorph_eq_refl
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p)
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
    (τ : E ≃ₜ E) (hproj : ∀ e, p (τ e) = p e)
    (e₀ : E) (hfix : τ e₀ = e₀) : τ = Homeomorph.refl E := by
  let pC : C(E, B) := ⟨p, hp.continuous⟩
  let τC : C(E, E) := ⟨τ, τ.continuous⟩
  obtain ⟨ι, ⟨hι₀, hιp⟩, hιuniq⟩ :=
    hp.existsUnique_continuousMap_lifts pC e₀ e₀ rfl
  have hτ : τC e₀ = e₀ ∧ p ∘ τC = pC := by
    constructor
    · exact hfix
    · funext e
      exact hproj e
  have hid : (ContinuousMap.id E) e₀ = e₀ ∧ p ∘ (ContinuousMap.id E) = pC := by
    constructor
    · rfl
    · funext e
      rfl
  have hτeq := hιuniq τC hτ
  have hideq := hιuniq (ContinuousMap.id E) hid
  apply Homeomorph.ext
  intro e
  have hcoe : τC = ContinuousMap.id E := hτeq.trans hideq.symm
  change τ e = e
  simpa [τC] using congrArg (fun f : C(E, E) => f e) hcoe

#print axioms exists_simplyConnectedCoverDeckHomeomorph
#print axioms simplyConnectedCoverDeckHomeomorph_eq_refl

end
end SystolicGrowth
