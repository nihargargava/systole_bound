module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingHalfPlaneSpinHolonomy
public import Geometry.GluingMetricIsometryLiftedOutput

@[expose] public section

/-!
# Actual marked output with the geometric spin lift constructed internally

The internally constructed faithful spin holonomy is composed with the
genuine genus marking. Its image supplies the existing marked surface and
lifted-chain output adapters, without a representation or lift input.
The systole-preserving replacement metric remains to be constructed.
-/

open Manifold Riemannian UpperHalfPlane
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane ENNReal

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}
  (P : ExerciseGluingPreparation C g n genera X)
  (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
  (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
  (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
    modelWithCornersSelf ℝ ℂ⟯ ℍ)
  (hΦ : LeeLib.Ch02.IsIsometry
    ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    upperHalfPlanePoincareMetric Φ)

/-- **Math.** Carry the genuinely constructed coherent spin holonomy
through the actual genus marking. No representation or relator sign is
supplied as an extra hypothesis. -/
theorem exists_gluedUniversalCoverSurfaceGroupSLHom :
    ∃ ρ : SurfaceGroup g →* SL(2, ℝ),
      (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
        P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ := by
  obtain ⟨ρ, hρ, _⟩ := P.exists_gluedUniversalCoverSLDeckHom x g0 Φ hΦ
  refine ⟨ρ.comp (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).toMonoidHom, ?_⟩
  apply DFunLike.ext
  intro a
  exact hρ (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x a)

/-- **Math.** Choose the actual internally constructed marked spin lift;
its coherence has already been proved geometrically. -/
def gluedUniversalCoverSurfaceGroupSLHom : SurfaceGroup g →* SL(2, ℝ) :=
  (P.exists_gluedUniversalCoverSurfaceGroupSLHom hn hsum x g0 Φ hΦ).choose

theorem gluedUniversalCoverSurfaceGroupSLHom_projective :
    (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
      (P.gluedUniversalCoverSurfaceGroupSLHom hn hsum x g0 Φ hΦ) =
        P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ :=
  (P.exists_gluedUniversalCoverSurfaceGroupSLHom hn hsum x g0 Φ hΦ).choose_spec

variable (L : ℝ) (hL : 0 < L)
  (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
    ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)

/-- **Math.** The image of the constructed geometric spin lift gives the
actual marked free discrete SL₂ surface; it is not the full inverse image
of projective holonomy, which would contain the central `-I`. -/
def gluedMetricSpinLiftedSurface : ClosedHyperbolicSurface g :=
  P.gluedMetricIsometryLiftedSurface hn hsum x g0 Φ hΦ L hL hsys
    (P.gluedUniversalCoverSurfaceGroupSLHom hn hsum x g0 Φ hΦ)
    (P.gluedUniversalCoverSurfaceGroupSLHom_projective hn hsum x g0 Φ hΦ)

theorem le_gluedMetricSpinLiftedSurface_systole :
    L ≤ (P.gluedMetricSpinLiftedSurface hn hsum x g0 Φ hΦ L hL hsys).systole :=
  P.le_gluedMetricIsometryLiftedSurface_systole hn hsum x g0 Φ hΦ L hL hsys
    (P.gluedUniversalCoverSurfaceGroupSLHom hn hsum x g0 Φ hΦ)
    (P.gluedUniversalCoverSurfaceGroupSLHom_projective hn hsum x g0 Φ hΦ)

/-- **Math.** All lifted-chain fields follow from the genuine geometric
metric identification and its systole bound, with the coherent SL₂ lift
constructed internally. Replacement existence is still a separate theorem. -/
def gluedMetricSpinLiftedOutput : ExerciseLiftedChainOutput g L :=
  P.gluedMetricIsometryLiftedOutput hn hsum x g0 Φ hΦ L hL hsys
    (P.gluedUniversalCoverSurfaceGroupSLHom hn hsum x g0 Φ hΦ)
    (P.gluedUniversalCoverSurfaceGroupSLHom_projective hn hsum x g0 Φ hΦ)

#print axioms exists_gluedUniversalCoverSurfaceGroupSLHom
#print axioms gluedMetricSpinLiftedSurface
#print axioms le_gluedMetricSpinLiftedSurface_systole
#print axioms gluedMetricSpinLiftedOutput

end

end SystolicGrowth.ExerciseGluingPreparation
