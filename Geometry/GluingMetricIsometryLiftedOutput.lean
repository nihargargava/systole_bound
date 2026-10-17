module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingDeckProjectiveSystole
public import Geometry.HyperbolicDisplacementAction
public import Geometry.SurfaceProjectiveLift

@[expose] public section

/-!
# The actual marked surface produced by a metric identification and lift

The image of a genuine coherent special-linear lift is the deck subgroup.
Its faithful marking, freeness, discreteness, compact quotient and systole
bound follow from the actual supplied smooth base metric and same-map
Poincaré identification. The existing lifted-output adapter is then used.
This module neither asserts replacement-metric existence nor constructs the
geometric special-linear lift: these remain genuine construction inputs.
-/

open Manifold Riemannian UpperHalfPlane Set
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane ENNReal

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth.ExerciseGluingPreparation

noncomputable section

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

private theorem genuineProjectiveLift_smul
    (ρbar : SurfaceGroup g →* PSL(2, ℝ)) (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ = ρbar)
    (a : SurfaceGroup g) (p : ℍ) : ρ a • p = ρbar a • p := by
  have h := congrArg (fun γ : PSL(2, ℝ) => γ • p) (DFunLike.congr_fun hρ a)
  exact h

/-- **Math.** Every nonidentity element in the actual lifted image pays
the actual supplied base-loop systole lower bound. Coherence is used only
to identify its genuine action, not as an assumed displacement conclusion. -/
theorem gluedMetricIsometryLift_displacement_lower
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (L : ℝ)
    (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
      ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)
    (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ) :
    ∀ γ : ρ.range, γ ≠ 1 → ∀ p : ℍ, L ≤ dist p (γ • p) := by
  intro γ hγ p
  obtain ⟨a, ha⟩ := γ.property
  have hane : a ≠ 1 := by
    intro heq
    apply hγ
    apply Subtype.ext
    rw [← ha, heq, map_one]
    rfl
  change L ≤ dist p (γ.val • p)
  rw [← ha, genuineProjectiveLift_smul _ ρ hρ]
  exact P.le_gluedUniversalCoverSurfaceGroupProjectiveHom_dist_of_le_metricHomotopySystole
    hn hsum x g0 Φ hΦ L hsys a hane p

/-- **Math.** The compact native orbit set covers every orbit of the
actual lifted image; the full projective inverse image is never substituted. -/
theorem gluedMetricIsometryLift_compact_orbit_cover
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ)
    (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ) :
    ∀ p : ℍ, ∃ γ : ρ.range, γ • p ∈ P.gluedUniversalCoverHalfPlaneCompactSet x Φ := by
  intro p
  obtain ⟨a, ha⟩ := P.gluedUniversalCoverHalfPlaneCompactSet_meets_surfaceGroup_orbit
    hn hsum x g0 Φ hΦ p
  refine ⟨⟨ρ a, ⟨a, rfl⟩⟩, ?_⟩
  change ρ a • p ∈ _
  rw [genuineProjectiveLift_smul _ ρ hρ]
  exact ha

/-- **Math.** Construct the actual marked closed hyperbolic surface from
the image of the genuine lift. All required geometric fields are derived
from the supplied actual metric identification and geometric systole bound. -/
def gluedMetricIsometryLiftedSurface
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (L : ℝ) (hL : 0 < L)
    (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
      ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)
    (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ) :
    ClosedHyperbolicSurface g := by
  have hfaithful := injective_surfaceGroup_projective_lift _ ρ hρ
    (P.gluedUniversalCoverSurfaceGroupProjectiveHom_injective hn hsum x g0 Φ hΦ)
  have hdisplacement := P.gluedMetricIsometryLift_displacement_lower
    hn hsum x g0 Φ hΦ L hsys ρ hρ
  exact
    { deckGroup := ρ.range
      discrete := subgroup_isDiscrete_of_displacement_lower ρ.range hL hdisplacement
      free := subgroup_free_of_displacement_lower ρ.range hL hdisplacement
      compactQuotient := isCompact_orbitRel_quotient_of_compact_cover
        (P.gluedUniversalCoverHalfPlaneCompactSet x Φ)
        (P.gluedUniversalCoverHalfPlaneCompactSet_isCompact x Φ)
        (P.gluedMetricIsometryLift_compact_orbit_cover hn hsum x g0 Φ hΦ ρ hρ)
      marking := (MonoidHom.ofInjective hfaithful).symm }

/-- **Math.** The constructed surface's genuine translation-length
infimum is at least the actual base-loop systole lower bound. Positive genus
is derived from the prepared chain, not assumed independently. -/
theorem le_gluedMetricIsometryLiftedSurface_systole
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (L : ℝ) (hL : 0 < L)
    (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
      ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)
    (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ) :
    L ≤ (P.gluedMetricIsometryLiftedSurface hn hsum x g0 Φ hΦ L hL hsys ρ hρ).systole := by
  let Y := P.gluedMetricIsometryLiftedSurface hn hsum x g0 Φ hΦ L hL hsys ρ hρ
  have hg : 0 < g := by
    let i : Fin n := ⟨0, by omega⟩
    have hi := P.component_genus i
    have hle : genera i ≤ ∑ j, genera j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (genera j)) (Finset.mem_univ i)
    omega
  exact Y.le_systole_of_displacement_lower L
    (Y.translationLengths_nonempty_of_genus_pos hg)
    (P.gluedMetricIsometryLift_displacement_lower hn hsum x g0 Φ hΦ L hsys ρ hρ)

/-- **Math.** Consume the actual constructed surface through the existing
repository adapter. Replacement existence and the geometric coherent lift
are not packaged as fields of a newly assumed output certificate. -/
def gluedMetricIsometryLiftedOutput
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (L : ℝ) (hL : 0 < L)
    (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
      ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)
    (ρ : SurfaceGroup g →* SL(2, ℝ))
    (hρ : (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp ρ =
      P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ) :
    ExerciseLiftedChainOutput g L :=
  ExerciseLiftedChainOutput.ofClosedHyperbolicSurface
    (P.gluedMetricIsometryLiftedSurface hn hsum x g0 Φ hΦ L hL hsys ρ hρ)
    (P.le_gluedMetricIsometryLiftedSurface_systole hn hsum x g0 Φ hΦ L hL hsys ρ hρ)

#print axioms gluedMetricIsometryLift_displacement_lower
#print axioms gluedMetricIsometryLift_compact_orbit_cover
#print axioms gluedMetricIsometryLiftedSurface
#print axioms le_gluedMetricIsometryLiftedSurface_systole
#print axioms gluedMetricIsometryLiftedOutput

end
end SystolicGrowth.ExerciseGluingPreparation
