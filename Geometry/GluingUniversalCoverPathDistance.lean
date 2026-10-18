module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingUniversalCoverDeck
public import Geometry.GluingUniversalCoverCocompact
public import Geometry.GluingUniversalCoverFaithfulAction
public import Geometry.MetricPathVariation

@[expose] public section

/-!
# Canonical extended path distance on the native universal cover

Measure paths upstairs only by the intrinsic variation of their actual
projection to the original glued carrier. This defines an ENNReal path
distance; no topology or metric on the cover is replaced or assumed.
-/

open Set
open scoped ENNReal unitInterval

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The downstairs intrinsic variation of a literal path in the native
based-path cover. -/
noncomputable def gluedUniversalCoverProjectedPathVariation
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ : P.basedTopologicalUniversalCover x}
    (Γ : Path e₀ e₁) : ℝ≥0∞ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  exact eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ

/-- The canonical extended intrinsic path distance: the infimum of the
downstairs variations over all continuous paths in the actual cover. -/
noncomputable def gluedUniversalCoverPathDistance
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x) : ℝ≥0∞ :=
  ⨅ Γ : Path e₀ e₁, P.gluedUniversalCoverProjectedPathVariation x Γ

/-- Projection never increases this canonical path distance below the
actual downstairs extended distance. -/
theorem gluedUniversalCover_edist_le_pathDistance
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x) :
    letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
    edist (P.gluedUniversalCoverProjection x e₀)
      (P.gluedUniversalCoverProjection x e₁) ≤
        P.gluedUniversalCoverPathDistance x e₀ e₁ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  apply le_iInf
  intro Γ
  change edist (P.gluedUniversalCoverProjection x e₀)
      (P.gluedUniversalCoverProjection x e₁) ≤
    eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ) univ
  simpa only [Function.comp_apply, Γ.source, Γ.target] using
    (eVariationOn.edist_le
      (P.gluedUniversalCoverProjection x ∘ Γ) (mem_univ 0) (mem_univ 1))

/-- Every particular lifted path bounds the infimum from above. -/
theorem gluedUniversalCoverPathDistance_le_projectedPathVariation
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ : P.basedTopologicalUniversalCover x} (Γ : Path e₀ e₁) :
    P.gluedUniversalCoverPathDistance x e₀ e₁ ≤
      P.gluedUniversalCoverProjectedPathVariation x Γ := by
  exact iInf_le _ Γ

/-- Constant paths have zero projected variation. -/
theorem gluedUniversalCoverProjectedPathVariation_refl
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverProjectedPathVariation x (Path.refl e) = 0 := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  apply (eVariationOn.eq_zero_iff _).2
  intro t ht u hu
  change edist ((P.gluedUniversalCoverProjection x ∘ Path.refl e) t)
    ((P.gluedUniversalCoverProjection x ∘ Path.refl e) u) = 0
  simp [Path.refl_apply]

/-- The canonical path distance vanishes on the diagonal. -/
theorem gluedUniversalCoverPathDistance_self
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverPathDistance x e e = 0 := by
  unfold gluedUniversalCoverPathDistance
  apply le_antisymm
  · calc
      (⨅ Γ : Path e e, P.gluedUniversalCoverProjectedPathVariation x Γ) ≤
          P.gluedUniversalCoverProjectedPathVariation x (Path.refl e) := iInf_le _ _
      _ = 0 := P.gluedUniversalCoverProjectedPathVariation_refl x e
  · exact bot_le

/-- Total variation on a path is unchanged by reversing its parameter. -/
private theorem eVariationOn_comp_unitInterval_symm
    {M : Type*} [PseudoEMetricSpace M] (f : unitInterval → M) :
    eVariationOn (f ∘ unitInterval.symm) univ = eVariationOn f univ := by
  let φ : unitInterval → unitInterval := fun t => unitInterval.symm t
  have hanti : AntitoneOn φ univ := by
    intro s hs t ht hst
    change (unitInterval.symm t : ℝ) ≤ (unitInterval.symm s : ℝ)
    rw [unitInterval.coe_symm_eq, unitInterval.coe_symm_eq]
    have hst' : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
    linarith
  have hcomp := eVariationOn.comp_eq_of_antitoneOn f φ hanti
  have himage : φ '' (univ : Set unitInterval) = univ := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact mem_univ _
    · intro ht
      exact ⟨unitInterval.symm t, mem_univ _, by simp [φ]⟩
  change eVariationOn (f ∘ φ) univ = eVariationOn f univ
  simpa [himage, φ] using hcomp

/-- Reversing a lifted path does not change its projected variation. -/
theorem gluedUniversalCoverProjectedPathVariation_symm
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ : P.basedTopologicalUniversalCover x} (Γ : Path e₀ e₁) :
    P.gluedUniversalCoverProjectedPathVariation x Γ.symm =
      P.gluedUniversalCoverProjectedPathVariation x Γ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  change eVariationOn (P.gluedUniversalCoverProjection x ∘ Γ.symm) univ = _
  have hfun : (P.gluedUniversalCoverProjection x ∘ Γ.symm) =
      (P.gluedUniversalCoverProjection x ∘ Γ) ∘ unitInterval.symm := by
    funext t
    rfl
  rw [hfun]
  exact eVariationOn_comp_unitInterval_symm
    (P.gluedUniversalCoverProjection x ∘ Γ)

/-- The canonical extended path distance is symmetric. -/
theorem gluedUniversalCoverPathDistance_comm
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverPathDistance x e₀ e₁ =
      P.gluedUniversalCoverPathDistance x e₁ e₀ := by
  unfold gluedUniversalCoverPathDistance
  apply le_antisymm
  · refine le_iInf fun Γ => ?_
    calc
      (⨅ Δ : Path e₀ e₁, P.gluedUniversalCoverProjectedPathVariation x Δ) ≤
          P.gluedUniversalCoverProjectedPathVariation x Γ.symm := iInf_le _ _
      _ = P.gluedUniversalCoverProjectedPathVariation x Γ :=
        P.gluedUniversalCoverProjectedPathVariation_symm x Γ
  · refine le_iInf fun Γ => ?_
    calc
      (⨅ Δ : Path e₁ e₀, P.gluedUniversalCoverProjectedPathVariation x Δ) ≤
          P.gluedUniversalCoverProjectedPathVariation x Γ.symm := iInf_le _ _
      _ = P.gluedUniversalCoverProjectedPathVariation x Γ :=
        P.gluedUniversalCoverProjectedPathVariation_symm x Γ

/-- Concatenation adds the projected path variations. -/
private theorem gluedUniversalCoverProjectedPathVariation_trans
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ e₂ : P.basedTopologicalUniversalCover x}
    (p : Path e₀ e₁) (q : Path e₁ e₂) :
    P.gluedUniversalCoverProjectedPathVariation x (p.trans q) =
      P.gluedUniversalCoverProjectedPathVariation x p +
        P.gluedUniversalCoverProjectedPathVariation x q := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  change eVariationOn (P.gluedUniversalCoverProjection x ∘ (p.trans q)) univ = _
  let c := (P.gluedUniversalCoverProjection_isCoveringMap x).continuous
  calc
    eVariationOn (P.gluedUniversalCoverProjection x ∘ (p.trans q)) univ =
        eVariationOn ((p.map c).trans (q.map c)) univ := by
          apply eVariationOn.congr
          intro t ht
          simp only [Path.trans_apply, Path.map_coe, Function.comp_apply]
          split_ifs <;> rfl
    _ = eVariationOn (p.map c) univ + eVariationOn (q.map c) univ :=
      eVariationOn_path_trans (p.map c) (q.map c)
    _ = P.gluedUniversalCoverProjectedPathVariation x p +
        P.gluedUniversalCoverProjectedPathVariation x q := rfl

/-- The canonical extended path distance satisfies the triangle inequality. -/
theorem gluedUniversalCoverPathDistance_triangle
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ e₂ : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverPathDistance x e₀ e₂ ≤
      P.gluedUniversalCoverPathDistance x e₀ e₁ +
        P.gluedUniversalCoverPathDistance x e₁ e₂ := by
  change (⨅ Γ : Path e₀ e₂, P.gluedUniversalCoverProjectedPathVariation x Γ) ≤
      (⨅ Γ : Path e₀ e₁, P.gluedUniversalCoverProjectedPathVariation x Γ) +
        ⨅ Γ : Path e₁ e₂, P.gluedUniversalCoverProjectedPathVariation x Γ
  apply ENNReal.le_iInf_add_iInf
  intro p q
  calc
    (⨅ Γ : Path e₀ e₂, P.gluedUniversalCoverProjectedPathVariation x Γ) ≤
        P.gluedUniversalCoverProjectedPathVariation x (p.trans q) := iInf_le _ _
    _ = P.gluedUniversalCoverProjectedPathVariation x p +
        P.gluedUniversalCoverProjectedPathVariation x q :=
      P.gluedUniversalCoverProjectedPathVariation_trans x p q

/-- If the projected endpoints differ, the downstairs metric separation
already separates them in the path-distance infimum. -/
theorem gluedUniversalCoverPathDistance_separates_of_projection_ne
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x)
    (h : P.gluedUniversalCoverProjection x e₀ ≠
      P.gluedUniversalCoverProjection x e₁) :
    0 < P.gluedUniversalCoverPathDistance x e₀ e₁ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  have hpos : 0 < edist (P.gluedUniversalCoverProjection x e₀)
      (P.gluedUniversalCoverProjection x e₁) := by
    exact edist_pos.mpr h
  exact hpos.trans_le (P.gluedUniversalCover_edist_le_pathDistance x e₀ e₁)

/-- The canonical path distance separates distinct points over one base
point by at least the actual target systole. -/
theorem target_le_gluedUniversalCoverPathDistance_of_same_fiber_ne
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    {e₀ e₁ : P.basedTopologicalUniversalCover x}
    (h : P.gluedUniversalCoverProjection x e₁ =
      P.gluedUniversalCoverProjection x e₀) (hne : e₁ ≠ e₀) :
    ENNReal.ofReal (targetSystole C g) ≤
      P.gluedUniversalCoverPathDistance x e₀ e₁ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  apply le_iInf
  intro Γ
  exact P.targetSystole_le_variation_of_universalCover_path x h hne Γ

/-- Zero canonical path distance implies equality of cover points. -/
theorem gluedUniversalCoverPathDistance_eq_zero_iff
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (e₀ e₁ : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverPathDistance x e₀ e₁ = 0 ↔ e₀ = e₁ := by
  constructor
  · intro hzero
    by_cases heq : e₀ = e₁
    · exact heq
    · by_cases hproj : P.gluedUniversalCoverProjection x e₀ =
          P.gluedUniversalCoverProjection x e₁
      · have hne01 : e₁ ≠ e₀ := fun h => heq h.symm
        have hsys := P.target_le_gluedUniversalCoverPathDistance_of_same_fiber_ne
          x (e₀ := e₀) (e₁ := e₁) hproj.symm hne01
        rw [hzero] at hsys
        exact False.elim ((not_lt_of_ge hsys) (ENNReal.ofReal_pos.mpr P.target_pos))
      · have hpos := P.gluedUniversalCoverPathDistance_separates_of_projection_ne
          x e₀ e₁ hproj
        rw [hzero] at hpos
        exact False.elim ((lt_irrefl 0) hpos)
  · rintro rfl
    exact P.gluedUniversalCoverPathDistance_self x e₀

/-- Every path to a nonidentity actual deck translate pays the target in
the infimum, not only in each individual path estimate. -/
theorem target_le_gluedUniversalCoverPathDistance_of_deck_ne_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (hτ : τ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) :
    ENNReal.ofReal (targetSystole C g) ≤
      P.gluedUniversalCoverPathDistance x e (τ.val e) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  apply le_iInf
  intro Γ
  exact P.targetSystole_le_variation_of_deck_path x τ hτ e Γ

/-- Every path to a nontrivial based-loop translate pays the target in
the infimum, using the genuine inverse-monodromy deck homomorphism. -/
theorem target_le_gluedUniversalCoverPathDistance_of_nontrivial_fundamentalGroup
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (γ : FundamentalGroup P.GluedCarrier x) (hγ : γ ≠ 1)
    (e : P.basedTopologicalUniversalCover x) :
    ENNReal.ofReal (targetSystole C g) ≤
      P.gluedUniversalCoverPathDistance x e
        ((P.gluedUniversalCoverFundamentalGroupDeckEquiv x γ).val e) := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  apply le_iInf
  intro Γ
  exact P.targetSystole_le_variation_of_fundamentalGroup_deck_path
    x γ hγ e Γ

/-- The path-distance obstruction is preserved under every actual native
deck translate because the projected path cost is unchanged. -/
theorem gluedUniversalCoverPathDistance_deck_invariant
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x)
    (e₀ e₁ : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverPathDistance x (τ.val e₀) (τ.val e₁) =
      P.gluedUniversalCoverPathDistance x e₀ e₁ := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  let E : Path e₀ e₁ ≃ Path (τ.val e₀) (τ.val e₁) := {
    toFun := fun p => p.map τ.val.continuous
    invFun := fun q =>
      (q.map τ.val.symm.continuous).cast
        (by simp) (by simp)
    left_inv := by
      intro p
      apply Path.ext
      funext t
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
        Homeomorph.symm_apply_apply]
    right_inv := by
      intro q
      apply Path.ext
      funext t
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply,
        Homeomorph.apply_symm_apply] }
  have hcost (p : Path e₀ e₁) :
      P.gluedUniversalCoverProjectedPathVariation x (E p) =
        P.gluedUniversalCoverProjectedPathVariation x p := by
    apply eVariationOn.congr
    intro t ht
    change P.gluedUniversalCoverProjection x (τ.val (p t)) =
      P.gluedUniversalCoverProjection x (p t)
    exact P.gluedUniversalCoverDeck_projection x τ (p t)
  have hcostInv (q : Path (τ.val e₀) (τ.val e₁)) :
      P.gluedUniversalCoverProjectedPathVariation x (E.symm q) =
        P.gluedUniversalCoverProjectedPathVariation x q := by
    calc
      P.gluedUniversalCoverProjectedPathVariation x (E.symm q) =
          P.gluedUniversalCoverProjectedPathVariation x (E (E.symm q)) :=
        (hcost (E.symm q)).symm
      _ = P.gluedUniversalCoverProjectedPathVariation x q := by
        rw [E.apply_symm_apply]
  apply le_antisymm
  · unfold gluedUniversalCoverPathDistance
    apply le_iInf
    intro p
    calc
      (⨅ q : Path (τ.val e₀) (τ.val e₁),
        P.gluedUniversalCoverProjectedPathVariation x q) ≤
          P.gluedUniversalCoverProjectedPathVariation x (E p) := iInf_le _ _
      _ = P.gluedUniversalCoverProjectedPathVariation x p := hcost p
  · unfold gluedUniversalCoverPathDistance
    apply le_iInf
    intro q
    calc
      (⨅ p : Path e₀ e₁, P.gluedUniversalCoverProjectedPathVariation x p) ≤
          P.gluedUniversalCoverProjectedPathVariation x (E.symm q) := iInf_le _ _
      _ = P.gluedUniversalCoverProjectedPathVariation x q := hcostInv q

#print axioms gluedUniversalCoverProjectedPathVariation
#print axioms gluedUniversalCoverPathDistance_le_projectedPathVariation
#print axioms gluedUniversalCoverPathDistance
#print axioms gluedUniversalCover_edist_le_pathDistance
#print axioms gluedUniversalCoverPathDistance_self
#print axioms gluedUniversalCoverProjectedPathVariation_symm
#print axioms gluedUniversalCoverPathDistance_comm
#print axioms gluedUniversalCoverPathDistance_triangle
#print axioms gluedUniversalCoverPathDistance_eq_zero_iff
#print axioms target_le_gluedUniversalCoverPathDistance_of_deck_ne_one
#print axioms target_le_gluedUniversalCoverPathDistance_of_nontrivial_fundamentalGroup
#print axioms gluedUniversalCoverPathDistance_deck_invariant

end SystolicGrowth.ExerciseGluingPreparation
