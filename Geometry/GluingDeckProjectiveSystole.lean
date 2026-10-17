module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingDeckProjectiveAction
public import Geometry.MetricHomotopySystole
public import Geometry.GluingChainMarkedDeckAction
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Geodesic.HopfRinow.EVariationLePathELength
public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.DiscreteSubset

@[expose] public section

/-!
# Systolic and discrete properties of the actual projective deck action

The lower bound is the genuine continuous homotopy systole of the actual
supplied smooth base metric. Distinct fiber points project nearly minimizing
cover paths to essential continuous loops. Discreteness comes from genuine
covering sheets, independently of any supplied displacement conclusion.
-/

open Bundle Manifold Riemannian UpperHalfPlane Set Filter
open scoped Manifold ContDiff Topology MatrixGroups UpperHalfPlane ENNReal unitInterval

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable section

private theorem projectiveHalfPlaneEvaluation_continuous (p : ℍ) :
    Continuous (fun γ : PSL(2, ℝ) => γ • p) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center SL(2, ℝ))).continuous_iff.mpr
  change Continuous (fun γ : SL(2, ℝ) => γ • p)
  fun_prop

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Every distinct same-fiber displacement pays the genuine
continuous homotopy systole of the supplied smooth base metric. This uses
nearly minimizing smooth paths, not a completeness or attainment assumption. -/
theorem metricHomotopySystole_le_gluedUniversalCover_coveringMetric_edist
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x)
    (hproj : P.gluedUniversalCoverProjection x b = P.gluedUniversalCoverProjection x a)
    (hne : b ≠ a) :
    letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
    letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
      LeeLib.Ch02.RiemannianMetric.toMetricSpace
        ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
    metricHomotopySystole P.GluedCarrier ≤ edist a b := by
  let gc := (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0
  letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
  letI : MetricSpace (P.basedTopologicalUniversalCover x) := gc.toMetricSpace
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.GluedCarrier → Type _) := ⟨g0.toRiemannianMetric⟩
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) :
      P.basedTopologicalUniversalCover x → Type _) := ⟨gc.toRiemannianMetric⟩
  letI : IsRiemannianManifold (modelWithCornersSelf ℝ ℂ) P.GluedCarrier :=
    ⟨fun _ _ => rfl⟩
  haveI := gc.isContinuousRiemannianBundle
  let proj := P.gluedUniversalCoverProjection x
  have hπ := (P.gluedUniversalCoverProjection_isLocalDiffeomorph x).contMDiff
  have hmetric :=
    (P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).isRiemannianCovering_coveringMetric g0
  refine le_of_forall_gt_imp_ge_of_dense (fun r hr => ?_)
  have hr' : riemannianEDist (modelWithCornersSelf ℝ ℂ) a b < r := hr
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ := exists_lt_of_riemannianEDist_lt hr'
  let Γ : Path a b :=
    { toFun := fun t => γ t
      continuous_toFun := continuousOn_iff_continuous_restrict.mp hγsmooth.continuousOn
      source' := hγ0
      target' := hγ1 }
  let ℓ : Path (proj a) (proj a) :=
    (Γ.map (P.gluedUniversalCoverProjection_isCoveringMap x).continuous).cast rfl hproj.symm
  have hess : ¬ ℓ.Homotopic (Path.refl (proj a)) := by
    intro hnull
    exact hne ((P.gluedUniversalCover_projectedPath_nullhomotopic_iff x hproj Γ).mp hnull)
  have hsys := metricHomotopySystole_le_eVariationOn ℓ hess
  have hparam : eVariationOn ℓ univ = eVariationOn (proj ∘ γ) (Icc (0 : ℝ) 1) := by
    change eVariationOn (fun t : I => proj (γ t)) univ = _
    simpa only [Function.comp_def, image_univ, Subtype.range_coe_subtype, setOf_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn (proj ∘ γ)
        (t := univ) (fun t : I => (t : ℝ)) (fun _ _ _ _ h => h)
  have hvar := OpenGA.HopfRinow.eVariationOn_le_pathELength
    ((hπ.of_le (by simp)).comp_contMDiffOn hγsmooth)
  have hlength := hmetric.2.pathELength_comp hπ hγsmooth
  rw [hparam] at hsys
  exact ((hsys.trans hvar).trans_eq hlength).trans hγlen.le

/-- **Math.** Every nonidentity actual projective deck transformation has
displacement at least the continuous-loop systole of the actual base metric. -/
theorem metricHomotopySystole_le_gluedUniversalCoverProjectiveDeckHom_edist
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ)
    (τ : P.gluedUniversalCoverDeckGroup x) (hτ : τ ≠ 1) (p : ℍ) :
    letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
    metricHomotopySystole P.GluedCarrier ≤
      edist p (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • p) := by
  letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
  letI : MetricSpace (P.basedTopologicalUniversalCover x) :=
    ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0).toMetricSpace
  have h := P.metricHomotopySystole_le_gluedUniversalCover_coveringMetric_edist x g0
    (Φ.symm p) (τ.val (Φ.symm p)) (τ.property (Φ.symm p))
    (P.gluedUniversalCoverDeck_ne_of_ne_one x τ hτ (Φ.symm p))
  rw [← (P.gluedUniversalCoverHalfPlane_isometry_coveringMetric x g0 Φ hΦ).edist_eq,
    Φ.apply_symm_apply] at h
  simpa only [P.gluedUniversalCoverProjectiveDeckHom_smul] using h

/-- **Math.** A real lower bound on the actual base-loop systole supplies
the required all-point projective displacement bound. The premise is a
geometric infimum bound, not the displacement conclusion itself. -/
theorem le_gluedUniversalCoverProjectiveDeckHom_dist_of_le_metricHomotopySystole
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (L : ℝ)
    (hsys : letI : MetricSpace P.GluedCarrier := LeeLib.Ch02.RiemannianMetric.toMetricSpace g0
      ENNReal.ofReal L ≤ metricHomotopySystole P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (hτ : τ ≠ 1) (p : ℍ) :
    L ≤ dist p (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ τ • p) := by
  have h := hsys.trans
    (P.metricHomotopySystole_le_gluedUniversalCoverProjectiveDeckHom_edist x g0 Φ hΦ τ hτ p)
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp h

/-- **Math.** The projective image is discrete because an original sheet
neighborhood is disjoint from all nonidentity deck translates. Its image
under the same genuine diffeomorphism isolates each range element by evaluation. -/
theorem gluedUniversalCoverProjectiveDeckHom_range_isDiscrete
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    IsDiscrete ((P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ).range : Set PSL(2, ℝ)) := by
  let ρ := P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ
  have heval : Continuous (fun γ : ρ.range => γ.val • UpperHalfPlane.I) :=
    (projectiveHalfPlaneEvaluation_continuous UpperHalfPlane.I).comp continuous_subtype_val
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  intro α
  obtain ⟨τ₀, hτ₀⟩ := α.property
  let q₀ := Φ.symm UpperHalfPlane.I
  let q := τ₀.val q₀
  obtain ⟨U, hU, hq, hdisjoint⟩ := P.exists_open_disjoint_gluedUniversalCoverDeck_translate x q
  have hV : IsOpen (Φ '' U) := Φ.toHomeomorph.isOpenMap U hU
  have hα : α.val • UpperHalfPlane.I ∈ Φ '' U := by
    rw [← hτ₀, P.gluedUniversalCoverProjectiveDeckHom_smul]
    exact ⟨q, hq, rfl⟩
  have hsingle : ({α} : Set ρ.range) =
      (fun γ : ρ.range => γ.val • UpperHalfPlane.I) ⁻¹' (Φ '' U) := by
    ext γ
    constructor
    · intro hγ
      rw [mem_singleton_iff] at hγ
      subst γ
      exact hα
    · intro hγ
      obtain ⟨τ, hτ⟩ := γ.property
      have hτq : τ.val q₀ ∈ U := by
        have himage : Φ (τ.val q₀) ∈ Φ '' U := by
          change γ.val • UpperHalfPlane.I ∈ Φ '' U at hγ
          rw [← hτ, P.gluedUniversalCoverProjectiveDeckHom_smul] at hγ
          exact hγ
        obtain ⟨u, hu, heu⟩ := himage
        rw [← Φ.injective heu]
        exact hu
      have hδpoint : (τ * τ₀⁻¹).val q = τ.val q₀ := by
        change τ.val (τ₀.val.symm (τ₀.val q₀)) = τ.val q₀
        rw [Homeomorph.symm_apply_apply]
      have hδone : τ * τ₀⁻¹ = 1 := by
        by_contra hne
        exact Set.disjoint_left.mp (hdisjoint (τ * τ₀⁻¹) hne) hτq ⟨q, hq, hδpoint⟩
      have hτeq : τ = τ₀ := mul_inv_eq_one.mp hδone
      rw [mem_singleton_iff]
      apply Subtype.ext
      rw [← hτ, hτeq, hτ₀]
  rw [hsingle]
  exact hV.preimage heval

/-- **Math.** The internally constructed genus marking identifies the
standard surface group with the actual projective deck action. -/
def gluedUniversalCoverSurfaceGroupProjectiveHom
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) : SurfaceGroup g →* PSL(2, ℝ) :=
  (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ).comp
    (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).toMonoidHom

theorem gluedUniversalCoverSurfaceGroupProjectiveHom_injective
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    Function.Injective (P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ) :=
  (P.gluedUniversalCoverProjectiveDeckHom_injective x g0 Φ hΦ).comp
    (P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x).injective

theorem gluedUniversalCoverSurfaceGroupProjectiveHom_range
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    (P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ).range =
      (P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ).range := by
  let E := P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x
  let ρ := P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ
  ext γ
  change (∃ a, ρ (E a) = γ) ↔ ∃ τ, ρ τ = γ
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨E a, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨E.symm τ, by rw [E.apply_symm_apply]⟩

theorem gluedUniversalCoverSurfaceGroupProjectiveHom_range_isDiscrete
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) :
    IsDiscrete ((P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ).range :
      Set PSL(2, ℝ)) := by
  rw [P.gluedUniversalCoverSurfaceGroupProjectiveHom_range hn hsum x g0 Φ hΦ]
  exact P.gluedUniversalCoverProjectiveDeckHom_range_isDiscrete x g0 Φ hΦ

/-- **Math.** The marked representation satisfies the all-point
displacement field from the genuine base-loop systole lower bound. -/
theorem le_gluedUniversalCoverSurfaceGroupProjectiveHom_dist_of_le_metricHomotopySystole
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
    (γ : SurfaceGroup g) (hγ : γ ≠ 1) (p : ℍ) :
    L ≤ dist p (P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ γ • p) := by
  let E := P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x
  have hne : E γ ≠ 1 := by
    intro h
    apply hγ
    apply E.injective
    simpa using h
  exact P.le_gluedUniversalCoverProjectiveDeckHom_dist_of_le_metricHomotopySystole
    x g0 Φ hΦ L hsys (E γ) hne p

/-- **Math.** Marking does not change the actual compact orbit set. -/
theorem gluedUniversalCoverHalfPlaneCompactSet_meets_surfaceGroup_orbit
    (P : ExerciseGluingPreparation C g n genera X)
    (hn : 2 ≤ n) (hsum : (∑ i, genera i) = g) (x : P.GluedCarrier)
    (g0 : RiemannianMetric (modelWithCornersSelf ℝ ℂ) P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (hΦ : LeeLib.Ch02.IsIsometry
      ((P.gluedUniversalCoverSmoothProjection_isSmoothCoveringMap x).coveringMetric g0)
      upperHalfPlanePoincareMetric Φ) (p : ℍ) :
    ∃ γ : SurfaceGroup g,
      P.gluedUniversalCoverSurfaceGroupProjectiveHom hn hsum x g0 Φ hΦ γ • p ∈
        P.gluedUniversalCoverHalfPlaneCompactSet x Φ := by
  let E := P.gluedUniversalCoverSurfaceGroupDeckEquiv hn hsum x
  obtain ⟨τ, hτ⟩ := P.gluedUniversalCoverHalfPlaneCompactSet_meets_orbit x g0 Φ hΦ p
  refine ⟨E.symm τ, ?_⟩
  change P.gluedUniversalCoverProjectiveDeckHom x g0 Φ hΦ (E (E.symm τ)) • p ∈ _
  rw [E.apply_symm_apply]
  exact hτ

#print axioms gluedUniversalCoverProjectiveDeckHom_range_isDiscrete
#print axioms gluedUniversalCoverSurfaceGroupProjectiveHom_injective
#print axioms gluedUniversalCoverSurfaceGroupProjectiveHom_range
#print axioms gluedUniversalCoverSurfaceGroupProjectiveHom_range_isDiscrete
#print axioms le_gluedUniversalCoverSurfaceGroupProjectiveHom_dist_of_le_metricHomotopySystole
#print axioms gluedUniversalCoverHalfPlaneCompactSet_meets_surfaceGroup_orbit

#print axioms metricHomotopySystole_le_gluedUniversalCover_coveringMetric_edist
#print axioms metricHomotopySystole_le_gluedUniversalCoverProjectiveDeckHom_edist

end ExerciseGluingPreparation
end
end SystolicGrowth
