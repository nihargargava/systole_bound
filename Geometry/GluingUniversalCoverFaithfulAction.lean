module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.SimplyConnectedCoverMonodromyDeck
public import Geometry.GluingUniversalCoverCocompact
public import Mathlib.Algebra.Group.Equiv.Opposite

@[expose] public section

/-!
# The faithful fundamental-group action on the native glued cover

Monodromy identifies the based fundamental group with the opposite of the
actual native deck group. Composing with inversion on the opposite group
produces a coherent homomorphism to the actual deck group. Its value is the
inverse of the deck element whose translate records the lifted-loop endpoint.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The reflexive path class is the actual selected lift over the basepoint. -/
noncomputable def gluedUniversalCoverBasepointFiber
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    P.gluedUniversalCoverProjection x ⁻¹' {x} :=
  TauCeti.UniversalCover.basepointLift x

/-- Turn monodromy's opposite-valued equivalence into the honest coherent
homomorphism to the actual native deck group. Its convention is inverse
monodromy. -/
noncomputable def gluedUniversalCoverFundamentalGroupDeckEquiv
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    FundamentalGroup P.GluedCarrier x ≃*
      P.gluedUniversalCoverDeckGroup x :=
  (P.gluedUniversalCoverDeckFundamentalGroupEquiv x
      (P.gluedUniversalCoverBasepointFiber x)).trans
    (MulEquiv.inv' (P.gluedUniversalCoverDeckGroup x)).symm

/-- The coherent native deck element is exactly the inverse of the
monodromy deck element associated to the same loop. -/
theorem gluedUniversalCoverFundamentalGroupDeckEquiv_apply_eq_inverse_monodromy
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) :
    P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ =
      (MulOpposite.unop
        (P.gluedUniversalCoverDeckFundamentalGroupEquiv x
          (P.gluedUniversalCoverBasepointFiber x) γ))⁻¹ := by
  rfl

/-- The value of the inverse coherent deck element applied at the basepoint
is the actual lifted-loop endpoint from monodromy. -/
theorem gluedUniversalCoverFundamentalGroupDeckEquiv_inv_smul_basepoint
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) :
    ((P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ)⁻¹).val
        (P.gluedUniversalCoverBasepointFiber x).1 =
      (P.gluedUniversalCoverProjection_isCoveringMap x).monodromy γ
        (P.gluedUniversalCoverBasepointFiber x) := by
  rw [P.gluedUniversalCoverFundamentalGroupDeckEquiv_apply_eq_inverse_monodromy]
  exact P.gluedUniversalCoverDeckFundamentalGroupEquiv_apply_smul x
    (P.gluedUniversalCoverBasepointFiber x) γ

/-- The genuine based monodromy homomorphism is injective. -/
theorem gluedUniversalCoverFundamentalGroupDeckEquiv_injective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    Function.Injective (P.gluedUniversalCoverFundamentalGroupDeckEquiv x) :=
  (P.gluedUniversalCoverFundamentalGroupDeckEquiv x).injective

/-- A nonidentity based loop gives a nonidentity actual deck map. -/
theorem gluedUniversalCoverFundamentalGroupDeckEquiv_ne_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) (hγ : γ ≠ 1) :
    P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ ≠ 1 := by
  intro h
  exact hγ ((P.gluedUniversalCoverFundamentalGroupDeckEquiv x).injective
    (by simpa using h))

/-- Compose the actual deck action with the coherent fundamental-group
homomorphism. This is an honest action on the native universal cover. -/
@[instance_reducible] noncomputable def gluedUniversalCoverFundamentalGroupMulAction
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    MulAction (FundamentalGroup P.GluedCarrier x)
      (P.basedTopologicalUniversalCover x) :=
  MulAction.compHom _ (P.gluedUniversalCoverFundamentalGroupDeckEquiv x).toMonoidHom

/-- The action is the original deck action through the actual coherent
fundamental-group homomorphism. -/
theorem gluedUniversalCoverFundamentalGroup_smul_def
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverFundamentalGroupMulAction x
    γ • e = (P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val e := by
  rfl

/-- The coherent fundamental-group action is fixed-point-free away from the
identity, by rigidity of the actual native deck transformations. -/
theorem gluedUniversalCoverFundamentalGroup_smul_ne_self
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) (hγ : γ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverFundamentalGroupMulAction x
    γ • e ≠ e := by
  change (P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val e ≠ e
  exact P.gluedUniversalCoverDeck_ne_of_ne_one x _
    (P.gluedUniversalCoverFundamentalGroupDeckEquiv_ne_one x γ hγ) e

/-- A based loop fixes one cover point under the coherent action exactly when
it is the identity element. -/
theorem gluedUniversalCoverFundamentalGroup_smul_eq_self_iff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverFundamentalGroupMulAction x
    γ • e = e ↔ γ = 1 := by
  letI := P.gluedUniversalCoverFundamentalGroupMulAction x
  constructor
  · intro h
    by_contra hγ
    exact (P.gluedUniversalCoverFundamentalGroup_smul_ne_self x γ hγ e) h
  · rintro rfl
    exact one_smul _ _

/-- Around any native cover point, one open neighborhood is disjoint from
all its translates by nonidentity elements of the coherent monodromy action. -/
theorem exists_open_disjoint_gluedUniversalCoverFundamentalGroup_translate
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    ∃ U : Set (P.basedTopologicalUniversalCover x), IsOpen U ∧ e ∈ U ∧
      ∀ γ : FundamentalGroup P.GluedCarrier x, γ ≠ 1 →
        Disjoint U ((P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val '' U) := by
  obtain ⟨U, hU, he, hdis⟩ := P.exists_open_disjoint_gluedUniversalCoverDeck_translate x e
  refine ⟨U, hU, he, ?_⟩
  intro γ hγ
  exact hdis (P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ)
    (P.gluedUniversalCoverFundamentalGroupDeckEquiv_ne_one x γ hγ)

/-- The actual compact native set meets every orbit of the coherent
fundamental-group homomorphism. -/
theorem exists_compact_gluedUniversalCover_fundamentalGroup_orbit_cover
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ∃ K : Set (P.basedTopologicalUniversalCover x), IsCompact K ∧
      ∀ e : P.basedTopologicalUniversalCover x,
        ∃ γ : FundamentalGroup P.GluedCarrier x,
          e ∈ (P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val '' K := by
  refine ⟨P.gluedUniversalCoverCompactSet x,
    P.gluedUniversalCoverCompactSet_isCompact x, ?_⟩
  intro e
  obtain ⟨τ, k, hk, hτ⟩ := P.gluedUniversalCoverCompactSet_orbit_cover x e
  obtain ⟨γ, hγ⟩ := (P.gluedUniversalCoverFundamentalGroupDeckEquiv x).surjective τ
  refine ⟨γ, k, hk, ?_⟩
  simpa [hγ] using hτ

/-- The same chosen compact set meets every coherent fundamental-group orbit,
in the exact action-based direction used by the final constructor. -/
theorem gluedUniversalCoverCompactSet_fundamentalGroup_meets_orbit
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverFundamentalGroupMulAction x
    ∃ γ : FundamentalGroup P.GluedCarrier x,
      γ • e ∈ P.gluedUniversalCoverCompactSet x := by
  letI := P.gluedUniversalCoverFundamentalGroupMulAction x
  obtain ⟨τ, k, hk, hke⟩ := P.gluedUniversalCoverCompactSet_orbit_cover x e
  obtain ⟨γ, hγ⟩ := (P.gluedUniversalCoverFundamentalGroupDeckEquiv x).surjective τ⁻¹
  refine ⟨γ, ?_⟩
  change (P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val e ∈
    P.gluedUniversalCoverCompactSet x
  rw [hγ]
  change τ.val.symm e ∈ P.gluedUniversalCoverCompactSet x
  rw [← hke, τ.val.symm_apply_apply]
  exact hk

/-- Every path from a cover point to its nonidentity coherent translate
projects to a path whose variation pays the target systole. -/
theorem targetSystole_le_variation_of_fundamentalGroup_deck_path
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) (hγ : γ ≠ 1)
    (e : P.basedTopologicalUniversalCover x)
    (Γ : Path e ((P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val e)) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ENNReal.ofReal (targetSystole C g) ≤
      eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ := by
  exact P.targetSystole_le_variation_of_deck_path x _
    (P.gluedUniversalCoverFundamentalGroupDeckEquiv_ne_one x γ hγ) e Γ

#print axioms gluedUniversalCoverFundamentalGroupDeckEquiv
#print axioms gluedUniversalCoverFundamentalGroupDeckEquiv_apply_eq_inverse_monodromy
#print axioms gluedUniversalCoverFundamentalGroupDeckEquiv_inv_smul_basepoint
#print axioms gluedUniversalCoverFundamentalGroupDeckEquiv_injective
#print axioms gluedUniversalCoverFundamentalGroupDeckEquiv_ne_one
#print axioms gluedUniversalCoverFundamentalGroupMulAction
#print axioms gluedUniversalCoverFundamentalGroup_smul_def
#print axioms gluedUniversalCoverFundamentalGroup_smul_ne_self
#print axioms gluedUniversalCoverFundamentalGroup_smul_eq_self_iff
#print axioms exists_open_disjoint_gluedUniversalCoverFundamentalGroup_translate
#print axioms exists_compact_gluedUniversalCover_fundamentalGroup_orbit_cover
#print axioms gluedUniversalCoverCompactSet_fundamentalGroup_meets_orbit
#print axioms targetSystole_le_variation_of_fundamentalGroup_deck_path

end SystolicGrowth.ExerciseGluingPreparation
