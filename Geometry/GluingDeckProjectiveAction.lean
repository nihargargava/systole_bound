module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingDeckConjugacyOrientation
public import Geometry.HalfPlaneProjectiveHolonomy
public import Geometry.GluingUniversalCoverCocompact

@[expose] public section

/-!
# Projective deck action from a genuine smooth metric identification

The source metric is the actual pullback of a genuine smooth base metric.
An actual same-map tensor isometry to the Poincaré plane transports its deck
action. Metric preservation, orientation, group laws, faithfulness and compact
orbit representatives are derived; no projective realization is assumed.
This does not construct a constant-curvature replacement of the base metric.
-/

open Bundle Manifold Riemannian UpperHalfPlane Set
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

private theorem genuineIsometry_trans
    {M N Q : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace Q]
    [ChartedSpace ℂ M] [ChartedSpace ℂ N] [ChartedSpace ℂ Q]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ N]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ Q]
    (gM : RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (gN : RiemannianMetric (modelWithCornersSelf ℝ ℂ) N)
    (gQ : RiemannianMetric (modelWithCornersSelf ℝ ℂ) Q)
    (e : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (f : N ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ Q)
    (he : LeeLib.Ch02.IsIsometry gM gN e) (hf : LeeLib.Ch02.IsIsometry gN gQ f) :
    LeeLib.Ch02.IsIsometry gM gQ (e.trans f) := by
  intro p
  ext v w
  rw [LeeLib.Ch02.pullbackForm_apply]
  have hd (u : TangentSpace (modelWithCornersSelf ℝ ℂ) p) :=
    mfderiv_comp_apply p (f.mdifferentiable (by simp) (e p))
      (e.mdifferentiable (by simp) p) u
  change gQ.inner (f (e p))
    (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      ((f : N → Q) ∘ (e : M → N)) p v)
    (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      ((f : N → Q) ∘ (e : M → N)) p w) = _
  rw [hd v, hd w]
  rw [hf.inner_mfderiv, he.inner_mfderiv]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Each original deck transformation preserves the actual
pullback of any genuine smooth base metric. -/
theorem gluedUniversalCover_deck_isIsometry_coveringMetric
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) :
    LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      (P.gluedUniversalCoverDeckDiffeomorph x τ) :=
  smoothCoveringMetric_deck_isIsometry
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x) g0
    (P.gluedUniversalCoverSmoothDeckAut x τ)

/-- **Math.** The conjugate preserves the genuine Poincaré tensor because
the given same-map isometry and its genuine inverse preserve tensors. -/
theorem gluedUniversalCoverDeckConjugateDiffeomorph_isIsometry
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (τ : P.gluedUniversalCoverDeckGroup x) :
    LeeLib.Ch02.IsIsometry upperHalfPlanePoincareMetric upperHalfPlanePoincareMetric
      (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ) :=
  genuineIsometry_trans _ _ _ _ Φ
    (genuineIsometry_trans _ _ _ Φ.symm (P.gluedUniversalCoverDeckDiffeomorph x τ)
      hΦ.symm (P.gluedUniversalCover_deck_isIsometry_coveringMetric x g0 τ)) hΦ

@[simp] theorem gluedUniversalCoverDeckConjugateDiffeomorph_one
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (p : ℍ) :
    P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ 1 p = p := by
  change Φ (Φ.symm p) = p
  exact Φ.apply_symm_apply p

/-- **Math.** The conjugate action retains the original deck multiplication
law literally, before choosing any projective representative. -/
theorem gluedUniversalCoverDeckConjugateDiffeomorph_mul
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (a b : P.gluedUniversalCoverDeckGroup x) (p : ℍ) :
    P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ (a * b) p =
      P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ a
        (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ b p) := by
  change Φ (a.val (b.val (Φ.symm p))) =
    Φ (a.val (Φ.symm (Φ (b.val (Φ.symm p)))))
  rw [Φ.symm_apply_apply]

/-- **Math.** Conjugating actual deck maps by a genuine bijection retains
faithfulness, without assuming faithfulness of the projective action. -/
theorem gluedUniversalCoverDeckConjugateDiffeomorph_injective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) :
    Function.Injective (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ) := by
  intro a b hab
  apply Subtype.ext
  apply Homeomorph.ext
  intro q
  have he := congrArg (fun d : ℍ ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
    modelWithCornersSelf ℝ ℂ⟯ ℍ => d (Φ q)) hab
  change Φ (a.val (Φ.symm (Φ q))) = Φ (b.val (Φ.symm (Φ q))) at he
  rw [Φ.symm_apply_apply] at he
  exact Φ.injective he

/-- **Math.** The actual faithful projective deck representation from a
genuine smooth tensor isometry of the actual pulled-back base metric.
Analyticity, positive orientation and coherence are proved internally. -/
def gluedUniversalCoverProjectiveDeckHom
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) : P.gluedUniversalCoverDeckGroup x →* PSL(2, ℝ) :=
  poincareIsometryActionProjectiveHom (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ)
    (P.gluedUniversalCoverDeckConjugateDiffeomorph_isIsometry x g0 Φ hΦ)
    (P.gluedUniversalCoverDeckConjugateDiffeomorph_mfderiv_det_pos x Φ)
    (P.gluedUniversalCoverDeckConjugateDiffeomorph_one x Φ)
    (P.gluedUniversalCoverDeckConjugateDiffeomorph_mul x Φ)

/-- **Math.** The PSL₂ action is literally the transported original deck action. -/
@[simp] theorem gluedUniversalCoverProjectiveDeckHom_smul
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (τ : P.gluedUniversalCoverDeckGroup x) (p : ℍ) :
    P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • p = Φ (τ.val (Φ.symm p)) :=
  poincareIsometryActionProjectiveHom_smul _ _ _ _ _ τ p

theorem gluedUniversalCoverProjectiveDeckHom_injective
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    Function.Injective (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ) :=
  poincareIsometryActionProjectiveHom_injective _ _ _ _ _
    (P.gluedUniversalCoverDeckConjugateDiffeomorph_injective x Φ)

/-- **Math.** Transport the already constructed compact native orbit set,
without choosing an unrelated abstract fundamental domain. -/
def gluedUniversalCoverHalfPlaneCompactSet
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) : Set ℍ :=
  Φ '' P.gluedUniversalCoverCompactSet x

theorem gluedUniversalCoverHalfPlaneCompactSet_isCompact
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) :
    IsCompact (P.gluedUniversalCoverHalfPlaneCompactSet x Φ) :=
  (P.gluedUniversalCoverCompactSet_isCompact x).image Φ.continuous

/-- **Math.** Every actual projective orbit has a representative in the
transported compact native set. -/
theorem gluedUniversalCoverHalfPlaneCompactSet_meets_orbit
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (p : ℍ) :
    ∃ τ : P.gluedUniversalCoverDeckGroup x,
      P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • p ∈
        P.gluedUniversalCoverHalfPlaneCompactSet x Φ := by
  obtain ⟨τ, hτ⟩ := P.gluedUniversalCoverCompactSet_meets_orbit x (Φ.symm p)
  refine ⟨τ, ?_⟩
  rw [P.gluedUniversalCoverProjectiveDeckHom_smul]
  exact mem_image_of_mem Φ hτ

/-- **Math.** The genuine tensor identification preserves the actual
canonical pullback distance and the existing hyperbolic distance on `ℍ`. -/
theorem gluedUniversalCoverHalfPlane_isometry_coveringMetric
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
      LeeLib.Ch02.RiemannianMetric.toMetricSpace
        ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    Isometry (Φ : P.basedTopologicalUniversalCover x → ℍ) := by
  let gc := (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0
  letI : MetricSpace (P.basedTopologicalUniversalCover x) := gc.toMetricSpace
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type _) := ⟨gc.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℍ → Type _) :=
    ⟨upperHalfPlanePoincareMetric.toRiemannianMetric⟩
  intro a b
  rw [upperHalfPlanePoincareMetric_isRiemannianDist.out]
  exact hΦ.riemannianEDist_comp a b

/-- **Math.** The projective displacement is exactly the displacement in
the actual smooth pullback metric, not in an assumed replacement distance. -/
theorem gluedUniversalCoverProjectiveDeckHom_displacement_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ)
    (τ : P.gluedUniversalCoverDeckGroup x) (q : P.basedTopologicalUniversalCover x) :
    letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
      LeeLib.Ch02.RiemannianMetric.toMetricSpace
        ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    dist (Φ q) (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • Φ q) =
      dist q (τ.val q) := by
  letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
    LeeLib.Ch02.RiemannianMetric.toMetricSpace
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
  rw [P.gluedUniversalCoverProjectiveDeckHom_smul, Φ.symm_apply_apply]
  exact (P.gluedUniversalCoverHalfPlane_isometry_coveringMetric x g0 Φ hΦ).dist_eq q (τ.val q)

#print axioms gluedUniversalCoverDeckConjugateDiffeomorph_isIsometry
#print axioms gluedUniversalCoverProjectiveDeckHom
#print axioms gluedUniversalCoverProjectiveDeckHom_smul
#print axioms gluedUniversalCoverProjectiveDeckHom_injective
#print axioms gluedUniversalCoverHalfPlaneCompactSet_meets_orbit
#print axioms gluedUniversalCoverProjectiveDeckHom_displacement_eq

end ExerciseGluingPreparation
end
end SystolicGrowth
