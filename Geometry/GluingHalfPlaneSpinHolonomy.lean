module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingHalfPlaneSpinMonodromy
public import Geometry.GluingHalfPlaneUnitProjectionEquivariance
public import Geometry.SpinCoverPullbackAction
public import Geometry.HalfPlaneSpinLift

@[expose] public section

/-!
# Coherent special-linear holonomy from the actual global spin cover

The genuine global spin cover is pulled back along the actual physical
unit-tangent projection. Its proved odd fiber monodromy constructs a
canonical half-plane spin identification. Literal deck reindexing of the
pullback then gives coherent continuous spin maps, whose uniquely determined
signed matrices form a faithful special-linear representation. Neither a
spin identification nor a coherent signed lift is supplied as an input.

The genuine smooth metric and its tensor isometry to the Poincaré plane
remain the geometric inputs; this does not construct their replacement.
-/

open Bundle Manifold Riemannian UpperHalfPlane
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
  (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
  (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
    modelWithCornersSelf ℝ ℂ⟯ ℍ)
  (hΦ : LeeLib.Ch02.IsIsometry
    ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    upperHalfPlanePoincareMetric Φ)

/-- **Math.** The actual global spin cover, pulled back through the full
physical unit differential, is the canonical half-plane spin cover. Its
identification is produced from actual antipodal monodromy, not assumed. -/
theorem exists_gluedHalfPlaneSpinCoverHomeomorph :
    ∃ H : HalfPlaneSpinFrame ≃ₜ
      P.MetricSpinPullback g0.toContinuousRiemannianMetric
        (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ),
      (∀ q, P.metricSpinPullbackProjection g0.toContinuousRiemannianMetric
        (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ) (H q) = halfPlaneSpinSquare q) ∧
      (∀ q, H (halfPlaneSpinAntipode q) =
        P.metricSpinPullbackAntipode g0.toContinuousRiemannianMetric
          (P.gluedHalfPlaneUnitProjection x g0 Φ hΦ) (H q)) := by
  let m := g0.toContinuousRiemannianMetric
  let F := P.gluedHalfPlaneUnitProjection x g0 Φ hΦ
  let p := P.metricSpinPullbackProjection m F
  have hp : IsCoveringMap p := P.metricSpinPullbackProjection_isCoveringMap m F
    (P.gluedHalfPlaneUnitProjection_continuous x g0 Φ hΦ)
  obtain ⟨e₀, he₀⟩ := P.metricSpinPullbackProjection_surjective m F
    halfPlaneStandardTangentFrame
  obtain ⟨H, hH, hHA, _⟩ := exists_halfPlaneSpinCoverHomeomorph p hp
    (P.metricSpinPullbackAntipode m F)
    (P.metricSpinPullbackAntipode_continuous m F)
    (P.metricSpinPullbackAntipode_involutive m F)
    (P.metricSpinPullbackAntipode_ne m F)
    (P.metricSpinPullbackProjection_eq_iff m F) e₀ he₀
    (P.liftPath_gluedHalfPlaneStandardFrameOneTurn x g0 Φ hΦ e₀ he₀)
  exact ⟨H, hH, hHA⟩

/-- **Math.** The internally constructed global spin structure determines
a faithful coherent SL₂ lift of the actual projective deck representation.
The choice of projective representatives does not supply matrix coherence:
coherence follows from the literal action on the genuine spin pullback. -/
theorem exists_gluedUniversalCoverSLDeckHom :
    ∃ ρ : P.gluedUniversalCoverDeckGroup x →* SL(2, ℝ),
      (∀ τ, QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (ρ τ) =
        P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ) ∧
      Function.Injective ρ := by
  classical
  let m := g0.toContinuousRiemannianMetric
  let F := P.gluedHalfPlaneUnitProjection x g0 Φ hΦ
  let p := P.metricSpinPullbackProjection m F
  let ψ := P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ
  letI : MulAction (P.gluedUniversalCoverDeckGroup x) HalfPlaneTangentFrame :=
    MulAction.compHom HalfPlaneTangentFrame ψ
  letI : ContinuousConstSMul (P.gluedUniversalCoverDeckGroup x)
      HalfPlaneTangentFrame :=
    ⟨fun τ => (show Continuous (fun q : HalfPlaneTangentFrame => ψ τ • q) from
      continuous_const_smul (ψ τ))⟩
  have hinv : ∀ (τ : P.gluedUniversalCoverDeckGroup x) (q : HalfPlaneTangentFrame),
      F (τ • q) = F q := fun τ q =>
    P.gluedHalfPlaneUnitProjection_projective_deck_invariant x g0 Φ hΦ τ q
  obtain ⟨H, hH, _⟩ := P.exists_gluedHalfPlaneSpinCoverHomeomorph x g0 Φ hΦ
  have hHsymm (e : P.MetricSpinPullback m F) :
      halfPlaneSpinSquare (H.symm e) = p e := by
    simpa only [H.apply_symm_apply] using (hH (H.symm e)).symm
  let f : P.gluedUniversalCoverDeckGroup x → HalfPlaneSpinFrame → HalfPlaneSpinFrame :=
    fun τ q => H.symm (P.metricSpinPullbackAction m F hinv τ (H q))
  have hf (τ : P.gluedUniversalCoverDeckGroup x) : Continuous (f τ) :=
    H.symm.continuous.comp
      ((P.metricSpinPullbackAction_continuous_const m F hinv τ).comp H.continuous)
  have hone (q : HalfPlaneSpinFrame) : f 1 q = q := by
    simp only [f, P.metricSpinPullbackAction_one, H.symm_apply_apply]
  have hmul (a b : P.gluedUniversalCoverDeckGroup x) (q : HalfPlaneSpinFrame) :
      f (a * b) q = f a (f b q) := by
    dsimp only [f]
    rw [H.apply_symm_apply, P.metricSpinPullbackAction_mul]
  have hrep : ∀ τ : P.gluedUniversalCoverDeckGroup x,
      ∃ A : SL(2, ℝ), QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) A = ψ τ :=
    fun τ => QuotientGroup.mk'_surjective (Subgroup.center SL(2, ℝ)) (ψ τ)
  choose A hA using hrep
  have hsquare (τ : P.gluedUniversalCoverDeckGroup x) (q : HalfPlaneSpinFrame) :
      halfPlaneSpinSquare (f τ q) = A τ • halfPlaneSpinSquare q := by
    change halfPlaneSpinSquare
      (H.symm (P.metricSpinPullbackAction m F hinv τ (H q))) = _
    rw [hHsymm]
    change P.metricSpinPullbackProjection m F
      (P.metricSpinPullbackAction m F hinv τ (H q)) = _
    rw [P.metricSpinPullbackAction_proj, hH]
    change ψ τ • halfPlaneSpinSquare q = A τ • halfPlaneSpinSquare q
    rw [← hA τ, projective_mk_halfPlaneTangentFrame_smul]
  obtain ⟨ρ, _, hρ⟩ := exists_sl2_hom_of_continuous_halfPlaneSpinAction
    A f hf hsquare hone hmul
  have hprojective (τ : P.gluedUniversalCoverDeckGroup x) :
      QuotientGroup.mk' (Subgroup.center SL(2, ℝ)) (ρ τ) = ψ τ :=
    (hρ τ).trans (hA τ)
  refine ⟨ρ, hprojective, ?_⟩
  intro a b hab
  apply P.gluedUniversalCoverProjectiveDeckHom_injective x g0 Φ hΦ
  exact (hprojective a).symm.trans
    ((congrArg (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))) hab).trans (hprojective b))

#print axioms exists_gluedHalfPlaneSpinCoverHomeomorph
#print axioms exists_gluedUniversalCoverSLDeckHom

end SystolicGrowth.ExerciseGluingPreparation
