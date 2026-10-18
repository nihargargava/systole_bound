module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingChainClosedMarkedAssembly
public import Geometry.GluingUniversalCoverPathMetric

@[expose] public section

/-!
# The marked surface-group action on the native chain cover

The actual genus marking, inverse-monodromy deck equivalence, and native
path metric give a faithful coherent isometric action of the standard
surface group. This is still the native cover, not an identification with ℍ.
-/

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The standard surface group is the genuine native deck group, using the
constructed genus marking and the fixed inverse-monodromy convention. -/
def gluedUniversalCoverSurfaceGroupDeckEquiv
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier) :
    SurfaceGroup g ≃* P.gluedUniversalCoverDeckGroup x :=
  (P.gluedChainFullMarkedSurfaceGroupEquiv hn hsum x).symm.trans
    (P.gluedUniversalCoverFundamentalGroupDeckEquiv x)

/-- **Math.** Pull back the actual deck action through the internally constructed
surface-group marking. -/
@[instance_reducible]
def gluedUniversalCoverSurfaceGroupMulAction
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier) :
    MulAction (SurfaceGroup g) (P.basedTopologicalUniversalCover x) :=
  MulAction.compHom _ (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).toMonoidHom

/-- **Math.** The same marking gives a coherent homomorphism into the actual isometry
group of the native metric, rather than isolated pointwise deck choices. -/
def gluedUniversalCoverSurfaceGroupIsometryHom
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    SurfaceGroup g →*
      (P.basedTopologicalUniversalCover x ≃ᵢ P.basedTopologicalUniversalCover x) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  refine {
    toFun := fun γ => {
      toEquiv := (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x γ).val.toEquiv
      isometry_toFun := P.gluedUniversalCoverDeck_pathMetric_isometry x _ }
    map_one' := ?_
    map_mul' := ?_ }
  · apply IsometryEquiv.ext
    intro e
    change (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x 1).val e = e
    rw [map_one]
    rfl
  · intro γ δ
    apply IsometryEquiv.ext
    intro e
    change (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x (γ * δ)).val e =
      (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x γ).val
        ((P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x δ).val e)
    rw [map_mul]
    rfl

/-- **Math.** The constructed isometry homomorphism is faithful on the actual standard
surface group, by faithfulness of its native genus and deck equivalences. -/
theorem gluedUniversalCoverSurfaceGroupIsometryHom_injective
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    Function.Injective (P.gluedUniversalCoverSurfaceGroupIsometryHom hn hsum x) := by
  letI := P.gluedUniversalCoverPathMetricSpace x
  intro γ δ h
  apply (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).injective
  apply Subtype.ext
  apply Homeomorph.ext
  intro e
  exact congrArg (fun σ :
    P.basedTopologicalUniversalCover x ≃ᵢ P.basedTopologicalUniversalCover x => σ e) h

/-- **Math.** The marked surface action remains the literal native deck map. -/
theorem gluedUniversalCoverSurfaceGroup_smul_def
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (γ : SurfaceGroup g) (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverSurfaceGroupMulAction hn hsum x
    γ • e = (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x γ).val e := rfl

/-- **Math.** No nonidentity element of the standard marked group fixes a native
cover point. -/
theorem gluedUniversalCoverSurfaceGroup_smul_ne_self
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (γ : SurfaceGroup g) (hγ : γ ≠ 1) (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverSurfaceGroupMulAction hn hsum x
    γ • e ≠ e := by
  have hdeck : P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x γ ≠ 1 := by
    intro h
    apply hγ
    exact (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).injective
      (h.trans (map_one _).symm)
  exact P.gluedUniversalCoverDeck_ne_of_ne_one x _ hdeck e

/-- **Math.** Every marked-group translate preserves the actual native cover metric. -/
theorem gluedUniversalCoverSurfaceGroup_pathMetric_isometry
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (γ : SurfaceGroup g) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    letI := P.gluedUniversalCoverSurfaceGroupMulAction hn hsum x
    Isometry (fun e : P.basedTopologicalUniversalCover x => γ • e) :=
  P.gluedUniversalCoverDeck_pathMetric_isometry x _

/-- **Math.** Every nonidentity marked-group element pays the target at every native
cover point, without a further geometric or representation premise. -/
theorem targetSystole_le_gluedUniversalCoverSurfaceGroup_displacement
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (γ : SurfaceGroup g) (hγ : γ ≠ 1) (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverPathMetricSpace x
    letI := P.gluedUniversalCoverSurfaceGroupMulAction hn hsum x
    targetSystole C g ≤ dist e (γ • e) := by
  have hdeck : P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x γ ≠ 1 := by
    intro h
    apply hγ
    exact (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).injective
      (h.trans (map_one _).symm)
  exact P.targetSystole_le_gluedUniversalCoverDeck_displacement x _ hdeck e

/-- **Math.** The same actual compact set meets every orbit of the marked surface
group in the direction needed by the final compact-cover contract. -/
theorem gluedUniversalCoverCompactSet_surfaceGroup_meets_orbit
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (e : P.basedTopologicalUniversalCover x) :
    letI := P.gluedUniversalCoverSurfaceGroupMulAction hn hsum x
    ∃ γ : SurfaceGroup g, γ • e ∈ P.gluedUniversalCoverCompactSet x := by
  obtain ⟨τ, k, hk, hke⟩ := P.gluedUniversalCoverCompactSet_orbit_cover x e
  obtain ⟨γ, hγ⟩ :=
    (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).surjective τ⁻¹
  refine ⟨γ, ?_⟩
  change (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x γ).val e ∈ _
  rw [hγ]
  change τ.val.symm e ∈ P.gluedUniversalCoverCompactSet x
  rw [← hke, τ.val.symm_apply_apply]
  exact hk

#print axioms gluedUniversalCoverSurfaceGroupDeckEquiv
#print axioms gluedUniversalCoverSurfaceGroupIsometryHom
#print axioms gluedUniversalCoverSurfaceGroupIsometryHom_injective
#print axioms gluedUniversalCoverSurfaceGroup_smul_ne_self
#print axioms gluedUniversalCoverSurfaceGroup_pathMetric_isometry
#print axioms targetSystole_le_gluedUniversalCoverSurfaceGroup_displacement
#print axioms gluedUniversalCoverCompactSet_surfaceGroup_meets_orbit

end
end SystolicGrowth.ExerciseGluingPreparation
