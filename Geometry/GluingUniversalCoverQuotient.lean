module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverDeck

@[expose] public section

/-!
# The native glued surface as the quotient by its actual deck group

The projection fibers are exactly the orbits of the genuine projection-
preserving deck homeomorphisms. Since the endpoint projection is an open
surjective covering, its induced map from the deck-orbit quotient is a
homeomorphism onto the original glued carrier.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Equality of projected points is exactly the orbit relation for the
actual deck group of the native glued universal cover. -/
theorem gluedUniversalCoverDeck_orbitRel_iff_projection_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x) :
    MulAction.orbitRel (P.gluedUniversalCoverDeckGroup x)
      (P.basedTopologicalUniversalCover x) e₀ e₁ ↔
        P.gluedUniversalCoverProjection x e₀ =
          P.gluedUniversalCoverProjection x e₁ := by
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    calc
      P.gluedUniversalCoverProjection x e₀ =
          P.gluedUniversalCoverProjection x (τ • e₁) := congrArg
            (P.gluedUniversalCoverProjection x) hτ.symm
      _ = P.gluedUniversalCoverProjection x e₁ := by
        change P.gluedUniversalCoverProjection x (τ.val e₁) = _
        exact P.gluedUniversalCoverDeck_projection x τ e₁
  · intro h
    obtain ⟨τ, hτ⟩ := P.exists_gluedUniversalCoverDeck_of_projection_eq x e₁ e₀ h.symm
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨τ, by change τ.val e₁ = e₀; exact hτ⟩

/-- The endpoint projection descended to the quotient by the actual deck
action. -/
noncomputable def gluedUniversalCoverDeckOrbitProjection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Quotient (MulAction.orbitRel (P.gluedUniversalCoverDeckGroup x)
      (P.basedTopologicalUniversalCover x)) → P.GluedCarrier :=
  Quotient.lift (P.gluedUniversalCoverProjection x) (by
    intro e₀ e₁ h
    exact (P.gluedUniversalCoverDeck_orbitRel_iff_projection_eq x e₀ e₁).mp h)

@[simp] theorem gluedUniversalCoverDeckOrbitProjection_mk
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverDeckOrbitProjection x (Quotient.mk _ e) =
      P.gluedUniversalCoverProjection x e := rfl

theorem gluedUniversalCoverDeckOrbitProjection_surjective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Function.Surjective (P.gluedUniversalCoverDeckOrbitProjection x) := by
  intro y
  obtain ⟨e, he⟩ := P.gluedUniversalCoverProjection_surjective x y
  refine ⟨Quotient.mk _ e, ?_⟩
  simp [he]

theorem gluedUniversalCoverDeckOrbitProjection_injective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
  Function.Injective (P.gluedUniversalCoverDeckOrbitProjection x) := by
  intro q₀ q₁ h
  revert h
  refine Quotient.inductionOn₂ q₀ q₁ ?_
  intro e₀ e₁ h'
  apply Quotient.sound
  exact (P.gluedUniversalCoverDeck_orbitRel_iff_projection_eq x e₀ e₁).mpr
    (by simpa using h')

theorem gluedUniversalCoverDeckOrbitProjection_isQuotientMap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Topology.IsQuotientMap (P.gluedUniversalCoverDeckOrbitProjection x) := by
  apply (isQuotientMap_quotient_mk'.of_comp_iff).mp
  change Topology.IsQuotientMap (P.gluedUniversalCoverProjection x)
  exact (P.gluedUniversalCoverProjection_isCoveringMap x).isQuotientMap
    (P.gluedUniversalCoverProjection_surjective x)

/-- The original glued carrier is homeomorphic to the quotient by all and
only the actual deck transformations. This supplies an actual compact
quotient once compactness of the original carrier is used. -/
noncomputable def gluedUniversalCoverDeckOrbitHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Quotient (MulAction.orbitRel (P.gluedUniversalCoverDeckGroup x)
      (P.basedTopologicalUniversalCover x)) ≃ₜ P.GluedCarrier :=
  ((isHomeomorph_iff_isQuotientMap_injective).mpr
    ⟨P.gluedUniversalCoverDeckOrbitProjection_isQuotientMap x,
      P.gluedUniversalCoverDeckOrbitProjection_injective x⟩).homeomorph
        (P.gluedUniversalCoverDeckOrbitProjection x)

@[simp] theorem gluedUniversalCoverDeckOrbitHomeomorph_mk
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverDeckOrbitHomeomorph x (Quotient.mk _ e) =
      P.gluedUniversalCoverProjection x e := by
  change P.gluedUniversalCoverDeckOrbitProjection x (Quotient.mk _ e) = _
  exact P.gluedUniversalCoverDeckOrbitProjection_mk x e

#print axioms gluedUniversalCoverDeck_orbitRel_iff_projection_eq
#print axioms gluedUniversalCoverDeckOrbitProjection
#print axioms gluedUniversalCoverDeckOrbitProjection_isQuotientMap
#print axioms gluedUniversalCoverDeckOrbitHomeomorph

end SystolicGrowth.ExerciseGluingPreparation
