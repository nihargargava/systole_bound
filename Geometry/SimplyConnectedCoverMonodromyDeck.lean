module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverQuotient
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

/-!
# Monodromy identifies the native deck group with the fundamental group

The based-path universal cover is a quotient covering by its genuine deck
homeomorphisms. Mathlib's monodromy equivalence then identifies its deck group
with the opposite fundamental group, with the action on a chosen fiber given
by lifting loops.
-/

open Set

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual deck group acts continuously on the native universal cover. -/
instance gluedUniversalCoverDeckContinuousConstSMul
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    ContinuousConstSMul (P.gluedUniversalCoverDeckGroup x)
      (P.basedTopologicalUniversalCover x) where
  continuous_const_smul τ := τ.val.continuous

/-- The native endpoint projection is a quotient covering by the genuine
projection-preserving deck homeomorphisms. -/
theorem gluedUniversalCover_isQuotientCoveringMap
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier) :
    IsQuotientCoveringMap (P.gluedUniversalCoverProjection x)
      (P.gluedUniversalCoverDeckGroup x) := by
  letI := P.gluedUniversalCoverDeckMulAction x
  letI := P.gluedUniversalCoverDeckContinuousConstSMul x
  refine {
    toIsQuotientMap := (P.gluedUniversalCoverProjection_isCoveringMap x).isQuotientMap
      (P.gluedUniversalCoverProjection_surjective x)
    continuous_const_smul := continuous_const_smul
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro e₀ e₁
    constructor
    · intro h
      obtain ⟨τ, hτ⟩ := P.exists_gluedUniversalCoverDeck_of_projection_eq x e₀ e₁ h
      refine ⟨τ⁻¹, ?_⟩
      change τ.val.symm e₁ = e₀
      rw [← hτ]
      exact τ.val.symm_apply_apply e₀
    · rintro ⟨τ, hτ⟩
      change τ.val e₁ = e₀ at hτ
      rw [← hτ]
      exact P.gluedUniversalCoverDeck_projection x τ e₁
  · intro e
    obtain ⟨U, hU, heU, hsep⟩ :=
      P.exists_open_disjoint_gluedUniversalCoverDeck_translate x e
    refine ⟨U, hU.mem_nhds heU, ?_⟩
    intro τ hne
    by_contra hτ
    have hdis := hsep τ hτ
    rcases hne with ⟨z, hz⟩
    change z ∈ τ.val '' U ∧ z ∈ U at hz
    exact (Set.disjoint_left.mp hdis) hz.2 hz.1

/-- Monodromy gives the actual native deck group as the opposite of the
fundamental group, for any chosen point in the fiber over the basepoint. -/
noncomputable def gluedUniversalCoverDeckFundamentalGroupEquiv
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.gluedUniversalCoverProjection x ⁻¹' {x}) :
    FundamentalGroup P.GluedCarrier x ≃*
      MulOpposite (P.gluedUniversalCoverDeckGroup x) :=
  (P.gluedUniversalCover_isQuotientCoveringMap x).fundamentalGroupEquiv e

/-- Under the preceding equivalence, the deck element associated to a loop
sends the selected lift to the endpoint of the lifted loop (monodromy). -/
theorem gluedUniversalCoverDeckFundamentalGroupEquiv_apply_smul
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.gluedUniversalCoverProjection x ⁻¹' {x})
    (γ : FundamentalGroup P.GluedCarrier x) :
    (MulOpposite.unop (P.gluedUniversalCoverDeckFundamentalGroupEquiv x e γ)) • e.1 =
      (P.gluedUniversalCoverProjection_isCoveringMap x).monodromy γ e := by
  change (MulOpposite.unop
    ((P.gluedUniversalCover_isQuotientCoveringMap x).fundamentalGroupToMulOpposite e γ)) • e.1 =
      (P.gluedUniversalCoverProjection_isCoveringMap x).monodromy γ e
  exact (P.gluedUniversalCover_isQuotientCoveringMap x)
    |>.unop_fundamentalGroupToMulOpposite_smul

#print axioms gluedUniversalCover_isQuotientCoveringMap
#print axioms gluedUniversalCoverDeckFundamentalGroupEquiv
#print axioms gluedUniversalCoverDeckFundamentalGroupEquiv_apply_smul

end SystolicGrowth.ExerciseGluingPreparation
