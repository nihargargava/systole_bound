module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SimplyConnectedCoverDeck

@[expose] public section

/-!
# Local neighborhoods separated from nontrivial deck translates

Around any point in the total space of a simply connected covering, the
covering projection is injective on a small open neighborhood. A deck map
whose image of this neighborhood meets it must therefore fix a point, and
fixed-point rigidity forces that deck map to be the identity.
-/

namespace SystolicGrowth

universe u v

/-- Every point in the total space of a simply connected, locally path-connected
covering has an open neighborhood disjoint from every nontrivial deck translate.
No properness or freeness assumption on a deck action is needed: separation
follows from local injectivity of the covering map and fixed-point rigidity. -/
theorem exists_open_disjoint_nontrivial_coverDeck_translate
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p)
    [SimplyConnectedSpace E] [LocallyPathConnectedSpace E] (e : E) :
    ∃ U : Set E, IsOpen U ∧ e ∈ U ∧
      ∀ τ : E ≃ₜ E, (∀ z, p (τ z) = p z) → τ ≠ Homeomorph.refl E →
        Disjoint U (τ '' U) := by
  obtain ⟨U, hUopen, heU, hUinj⟩ := hp.isLocalHomeomorph.isLocallyInjective e
  refine ⟨U, hUopen, heU, ?_⟩
  intro τ hτproj hτne
  apply Set.disjoint_left.mpr
  intro x hxU hximage
  obtain ⟨y, hyU, hxy⟩ := hximage
  have hfix : τ y = y := by
    apply hUinj
    · simpa [hxy] using hxU
    · exact hyU
    · simpa [hxy] using hτproj y
  have hτeq := simplyConnectedCoverDeckHomeomorph_eq_refl hp τ hτproj y hfix
  exact hτne hτeq

#print axioms exists_open_disjoint_nontrivial_coverDeck_translate

end SystolicGrowth
