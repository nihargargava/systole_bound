module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCover
public import Geometry.SimplyConnectedCoverDeck
public import Geometry.SimplyConnectedCoverDeckNeighborhoods

@[expose] public section

/-!
# Actual deck transformations of the native glued universal cover

The deck group consists of the genuine homeomorphisms preserving the original
endpoint projection. Fiber transitivity and fixed-point freeness are derived
from unique lifting, not assumed for an abstract replacement action.
-/

open Set
open scoped unitInterval ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Math. The actual projection-preserving deck subgroup of the native cover. -/
def gluedUniversalCoverDeckGroup
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Subgroup (P.basedTopologicalUniversalCover x ≃ₜ P.basedTopologicalUniversalCover x) where
  carrier := {τ | ∀ e, P.gluedUniversalCoverProjection x (τ e) =
    P.gluedUniversalCoverProjection x e}
  one_mem' := by intro e; rfl
  mul_mem' := by
    intro τ₁ τ₂ hτ₁ hτ₂ e
    exact (hτ₁ (τ₂ e)).trans (hτ₂ e)
  inv_mem' := by
    intro τ hτ e
    rw [Homeomorph.inv_apply]
    simpa only [Homeomorph.apply_symm_apply] using (hτ (τ.symm e)).symm

/-- Math. Every actual deck transformation preserves the original projection. -/
@[simp] theorem gluedUniversalCoverDeck_projection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (e : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverProjection x (τ.val e) = P.gluedUniversalCoverProjection x e :=
  τ.property e

/-- Math. The native deck group acts transitively on each original cover fiber. -/
theorem exists_gluedUniversalCoverDeck_of_projection_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x)
    (h : P.gluedUniversalCoverProjection x e₀ = P.gluedUniversalCoverProjection x e₁) :
    ∃ τ : P.gluedUniversalCoverDeckGroup x, τ.val e₀ = e₁ := by
  obtain ⟨τ, hτ, hproj⟩ := exists_simplyConnectedCoverDeckHomeomorph
    (P.gluedUniversalCoverProjection_isCoveringMap x) e₀ e₁ h
  exact ⟨⟨τ, hproj⟩, hτ⟩

/-- Math. A native deck transformation with one fixed point is the identity. -/
theorem gluedUniversalCoverDeck_eq_one_of_fixedPoint
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (e : P.basedTopologicalUniversalCover x)
    (h : τ.val e = e) : τ = 1 := by
  apply Subtype.ext
  exact simplyConnectedCoverDeckHomeomorph_eq_refl
    (P.gluedUniversalCoverProjection_isCoveringMap x) τ.val τ.property e h

/-- Math. Every nonidentity native deck transformation moves every cover point. -/
theorem gluedUniversalCoverDeck_ne_of_ne_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (hτ : τ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) : τ.val e ≠ e :=
  fun he => hτ (P.gluedUniversalCoverDeck_eq_one_of_fixedPoint x τ e he)

/-- Math. The genuine deck homeomorphisms act by their original point maps. -/
noncomputable instance gluedUniversalCoverDeckMulAction
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    MulAction (P.gluedUniversalCoverDeckGroup x) (P.basedTopologicalUniversalCover x) where
  smul τ e := τ.val e
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Math. Native local sheets are disjoint from every nonidentity deck translate. -/
theorem exists_open_disjoint_gluedUniversalCoverDeck_translate
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    ∃ U : Set (P.basedTopologicalUniversalCover x), IsOpen U ∧ e ∈ U ∧
      ∀ τ : P.gluedUniversalCoverDeckGroup x, τ ≠ 1 → Disjoint U (τ.val '' U) := by
  obtain ⟨U, hU, he, hsep⟩ := exists_open_disjoint_nontrivial_coverDeck_translate
    (P.gluedUniversalCoverProjection_isCoveringMap x) e
  refine ⟨U, hU, he, ?_⟩
  intro τ hτ
  apply hsep τ.val τ.property
  intro heq
  exact hτ (Subtype.ext heq)

/-- Math. Every projected path to a nonidentity native deck translate pays the target. -/
theorem targetSystole_le_variation_of_deck_path
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (hτ : τ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) (Γ : Path e (τ.val e)) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤
      eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ := by
  exact P.targetSystole_le_variation_of_universalCover_path x
    (P.gluedUniversalCoverDeck_projection x τ e)
    (P.gluedUniversalCoverDeck_ne_of_ne_one x τ hτ e) Γ

#print axioms gluedUniversalCoverDeckGroup
#print axioms exists_gluedUniversalCoverDeck_of_projection_eq
#print axioms gluedUniversalCoverDeck_eq_one_of_fixedPoint
#print axioms gluedUniversalCoverDeckMulAction
#print axioms exists_open_disjoint_gluedUniversalCoverDeck_translate
#print axioms targetSystole_le_variation_of_deck_path

end SystolicGrowth.ExerciseGluingPreparation
