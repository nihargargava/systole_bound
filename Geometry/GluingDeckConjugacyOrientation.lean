module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCurvatureBoundedDeckOrientation
public import Geometry.UpperHalfPlaneRiemannianDistance
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Instances.Sign
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Corrected oriented charts on the original smooth universal cover

The native mixed chart transitions reverse orientation. Their seam-coordinate
conjugation correction is lifted from the base without changing the existing
cover atlas or metric. Corrected transitions have positive determinant.
-/

open Bundle Manifold Set Filter Riemannian UpperHalfPlane
open scoped Topology Manifold ContDiff ComplexConjugate Classical

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace SystolicGrowth

noncomputable section

def Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ) (z : ℂ) : ℂ := (Φ (e.symm z) : ℂ)

def Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ) (z : ℂ) : ℂ :=
  e (Φ.symm ((chartAt ℂ UpperHalfPlane.I).symm z))

private theorem orientedChartRead_contDiffAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M)
    {z : ℂ} (hz : z ∈ e.target) : ContDiffAt ℝ ∞ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) z := by
  have hm := (upperHalfPlane_coe_contMDiff_real (Φ (e.symm z))).comp z
    ((Φ.contMDiff (e.symm z)).comp z (contMDiffAt_symm_of_mem_maximalAtlas he hz))
  exact contMDiffAt_iff_contDiffAt.mp hm

private theorem orientedChartReadInv_contDiffAt
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M)
    {z : ℂ} (hz : z ∈ e.target) :
    ContDiffAt ℝ ∞ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e) (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z) := by
  let r := chartAt ℂ UpperHalfPlane.I
  have hr : r.symm (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z) = Φ (e.symm z) :=
    r.left_inv (show Φ (e.symm z) ∈ r.source from mem_univ _)
  have ht : Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z ∈ r.target :=
    r.map_source (show Φ (e.symm z) ∈ r.source from mem_univ _)
  have hs : Φ.symm (r.symm (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z)) ∈ e.source := by
    rw [hr, Diffeomorph.symm_apply_apply]
    exact e.map_target hz
  have hm := (contMDiffAt_of_mem_maximalAtlas he hs).comp (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z)
    ((Φ.symm.contMDiff (r.symm (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z))).comp _
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas UpperHalfPlane.I) ht))
  exact contMDiffAt_iff_contDiffAt.mp hm

private theorem orientedChartReadInv_read
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ) {z : ℂ} (hz : z ∈ e.target) :
    Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z) = z := by
  unfold Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead
  have hr : (chartAt ℂ UpperHalfPlane.I).symm (Φ (e.symm z) : ℂ) = Φ (e.symm z) :=
    (chartAt ℂ UpperHalfPlane.I).left_inv
      (show Φ (e.symm z) ∈ (chartAt ℂ UpperHalfPlane.I).source from mem_univ _)
  rw [hr, Diffeomorph.symm_apply_apply, e.right_inv hz]

private theorem orientedChartRead_det_inverse_mul
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M)
    {z : ℂ} (hz : z ∈ e.target) :
    LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e) (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z)).toLinearMap *
      LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) z).toLinearMap = 1 := by
  have hread := (orientedChartRead_contDiffAt Φ e he hz).differentiableAt (by simp)
  have hinv := (orientedChartReadInv_contDiffAt Φ e he hz).differentiableAt (by simp)
  have hnear : (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e ∘ Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) =ᶠ[𝓝 z] id :=
    Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hz)
      (fun y hy => orientedChartReadInv_read Φ e hy)
  have hd := (fderiv_comp z hinv hread).symm.trans hnear.fderiv_eq
  have hdet := congrArg (fun D : ℂ →L[ℝ] ℂ => LinearMap.det D.toLinearMap) hd
  rw [fderiv_id] at hdet
  change LinearMap.det
    ((fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e) (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e z)).toLinearMap.comp
      (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) z).toLinearMap) =
        LinearMap.det (LinearMap.id : ℂ →ₗ[ℝ] ℂ) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  exact hdet

private theorem orientedChartRead_det_ne_zero
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M)
    {z : ℂ} (hz : z ∈ e.target) :
    LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) z).toLinearMap ≠ 0 := by
  intro hzero
  have h := orientedChartRead_det_inverse_mul Φ e he hz
  rw [hzero, mul_zero] at h
  exact zero_ne_one h

private theorem orientedChartRead_sign_change
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
    (Φ : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ)
    (e f : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M)
    (hf : f ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M)
    {q : M} (hqe : q ∈ e.source) (hqf : q ∈ f.source)
    (hpos : 0 < LinearMap.det (fderiv ℝ (e.symm.trans f) (e q)).toLinearMap) :
    SignType.sign (LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e q)).toLinearMap) =
      SignType.sign (LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f) (f q)).toLinearMap) := by
  have hz : e q ∈ e.target := e.map_source hqe
  have hp : e.symm (e q) = q := e.left_inv hqe
  have hpf : e.symm (e q) ∈ f.source := by rw [hp]; exact hqf
  have hnear := (e.symm.continuousAt hz).eventually (f.open_source.mem_nhds hpf)
  have hread : (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) =ᶠ[𝓝 (e q)]
      Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f ∘ (e.symm.trans f) := by
    filter_upwards [hnear] with y hy
    change (Φ (e.symm y) : ℂ) = (Φ (f.symm (f (e.symm y))) : ℂ)
    rw [f.left_inv hy]
  have htrans : ContDiffAt ℝ ∞ (e.symm.trans f) (e q) := by
    have hm := (contMDiffAt_of_mem_maximalAtlas hf hpf).comp (e q)
      (contMDiffAt_symm_of_mem_maximalAtlas he hz)
    exact contMDiffAt_iff_contDiffAt.mp hm
  have hpoint : (e.symm.trans f) (e q) = f q := by
    change f (e.symm (e q)) = f q
    rw [hp]
  have hRf : DifferentiableAt ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f) ((e.symm.trans f) (e q)) := by
    rw [hpoint]
    exact (orientedChartRead_contDiffAt Φ f hf (f.map_source hqf)).differentiableAt (by simp)
  have hd := hread.fderiv_eq.trans
    (fderiv_comp (e q) hRf (htrans.differentiableAt (by simp)))
  rw [hpoint] at hd
  have hdet := congrArg (fun D : ℂ →L[ℝ] ℂ => LinearMap.det D.toLinearMap) hd
  change LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e q)).toLinearMap =
    LinearMap.det ((fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f) (f q)).toLinearMap.comp
      (fderiv ℝ (e.symm.trans f) (e q)).toLinearMap) at hdet
  rw [LinearMap.det_comp] at hdet
  rw [hdet, _root_.sign_mul, _root_.sign_pos hpos, mul_one]

private theorem conjugateChart_mem_smooth_maximalAtlas
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M) :
    gluingConjugateChart e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞ M := by
  let G := contDiffGroupoid ∞ (modelWithCornersSelf ℝ ℂ)
  have hconjSmooth : ContDiff ℝ ∞ (conj : ℂ → ℂ) := by
    have hfun : (Complex.conjCLE : ℂ → ℂ) = (conj : ℂ → ℂ) :=
      funext Complex.conjCLE_apply
    rw [← hfun]
    exact Complex.conjCLE.contDiff
  have hc : Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph ∈ G := by
    constructor <;>
      change ContDiffOn ℝ ∞ (id ∘ (conj : ℂ → ℂ) ∘ id)
        (id ⁻¹' (univ : Set ℂ) ∩ range (id : ℂ → ℂ))
    all_goals
      simpa only [Function.comp_id, Function.id_comp, preimage_id, Set.range_id, inter_univ] using
        hconjSmooth.contDiffOn (s := univ)
  change ∀ e' ∈ atlas ℂ M, _ at he ⊢
  intro e' he'
  obtain ⟨h₁, h₂⟩ := he e' he'
  constructor
  · simpa only [gluingConjugateChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using G.trans (G.symm hc) h₁
  · simpa only [gluingConjugateChart, OpenPartialHomeomorph.trans_assoc] using G.trans h₂ hc

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Correct the selected base chart only when it is a seam chart. -/
def gluedSelectedOrientedChart
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    OpenPartialHomeomorph P.GluedCarrier ℂ :=
  if P.IsGluedInteriorComplexChart (chartAt ℂ b) then chartAt ℂ b
  else gluingConjugateChart (chartAt ℂ b)

/-- **Math.** Lift precisely the same base orientation correction on each
original projection sheet, retaining the original smooth cover structure. -/
def gluedUniversalCoverOrientedChart
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    OpenPartialHomeomorph (P.basedTopologicalUniversalCover x) ℂ :=
  if P.IsGluedInteriorComplexChart (chartAt ℂ (P.gluedUniversalCoverProjection x q)) then
    chartAt ℂ q else gluingConjugateChart (chartAt ℂ q)

theorem gluedSelectedOrientedChart_mem
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :
    P.gluedSelectedOrientedChart b ∈ P.gluedOrientedComplexAtlas := by
  unfold gluedSelectedOrientedChart
  split_ifs with h
  · exact Or.inl h
  · have hnative := chart_mem_atlas ℂ b
    change P.IsGluedInteriorComplexChart (chartAt ℂ b) ∨
      ∃ (k : Fin (n - 1)) (θ : ℝ), chartAt ℂ b = P.seamAngularComplexChart k θ at hnative
    obtain ⟨k, θ, hk⟩ := hnative.resolve_left h
    exact Or.inr ⟨k, θ, by rw [hk]⟩

@[simp] theorem gluedUniversalCoverOrientedChart_source
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    (P.gluedUniversalCoverOrientedChart x q).source = (chartAt ℂ q).source := by
  unfold gluedUniversalCoverOrientedChart
  split_ifs <;> simp

theorem gluedUniversalCoverOrientedChart_mem_maximalAtlas
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverOrientedChart x q ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ∞
        (P.basedTopologicalUniversalCover x) := by
  unfold gluedUniversalCoverOrientedChart
  split_ifs
  · exact IsManifold.chart_mem_maximalAtlas q
  · exact conjugateChart_mem_smooth_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas q)

/-- **Math.** Corrected cover coordinates are the identical corrected
base coordinates of the original projection, on every sheet. -/
theorem gluedUniversalCoverOrientedChart_apply_projection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q z : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverOrientedChart x q z =
      P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x q)
        (P.gluedUniversalCoverProjection x z) := by
  unfold gluedUniversalCoverOrientedChart gluedSelectedOrientedChart
  split_ifs
  · exact P.gluedUniversalCover_chartAt_apply x q z
  · simp only [gluingConjugateChart_apply, P.gluedUniversalCover_chartAt_apply]

theorem gluedUniversalCoverOrientedChart_target_subset
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) :
    (P.gluedUniversalCoverOrientedChart x q).target ⊆
      (P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x q)).target := by
  unfold gluedUniversalCoverOrientedChart gluedSelectedOrientedChart
  split_ifs
  · intro z hz
    exact hz.1
  · intro z hz
    apply (mem_gluingConjugateChart_target _ z).mpr
    exact ((mem_gluingConjugateChart_target _ z).mp hz).1

theorem gluedUniversalCoverOrientedChart_symm_projection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q : P.basedTopologicalUniversalCover x) {z : ℂ}
    (hz : z ∈ (P.gluedUniversalCoverOrientedChart x q).target) :
    P.gluedUniversalCoverProjection x ((P.gluedUniversalCoverOrientedChart x q).symm z) =
      (P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x q)).symm z := by
  unfold gluedUniversalCoverOrientedChart at hz
  unfold gluedUniversalCoverOrientedChart gluedSelectedOrientedChart
  split_ifs at hz ⊢
  · exact P.gluedUniversalCover_chartAt_symm_projection x q hz
  · simp only [gluingConjugateChart_symm_apply]
    exact P.gluedUniversalCover_chartAt_symm_projection x q
      ((mem_gluingConjugateChart_target _ z).mp hz)

theorem gluedUniversalCoverOrientedChart_source_projection
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (q z : P.basedTopologicalUniversalCover x)
    (hz : z ∈ (P.gluedUniversalCoverOrientedChart x q).source) :
    P.gluedUniversalCoverProjection x z ∈
      (P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x q)).source := by
  rw [P.gluedUniversalCoverOrientedChart_source] at hz
  have hs : P.gluedUniversalCoverProjection x z ∈
      (chartAt ℂ (P.gluedUniversalCoverProjection x q)).source := by
    have h := hz.2
    change ((P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt q).symm z ∈
      (chartAt ℂ (P.gluedUniversalCoverProjection x q)).source at h
    rw [(P.gluedUniversalCoverProjection_isCoveringMap x).isLocalHomeomorph.localInverseAt_symm]
      at h
    exact h
  unfold gluedSelectedOrientedChart
  split_ifs <;> simpa using hs

/-- **Math.** Corrected cover transitions are literal restrictions of the
already-oriented base transitions, so their real Jacobians are positive. -/
theorem gluedUniversalCoverOrientedChart_transition_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (a b : P.basedTopologicalUniversalCover x) {z : ℂ}
    (hz : z ∈ ((P.gluedUniversalCoverOrientedChart x a).symm.trans
      (P.gluedUniversalCoverOrientedChart x b)).source) :
    0 < LinearMap.det (fderiv ℝ ((P.gluedUniversalCoverOrientedChart x a).symm.trans
      (P.gluedUniversalCoverOrientedChart x b)) z).toLinearMap := by
  let ea := P.gluedUniversalCoverOrientedChart x a
  let eb := P.gluedUniversalCoverOrientedChart x b
  let fa := P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x a)
  let fb := P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x b)
  have hsource : (ea.symm.trans eb).source ⊆ (fa.symm.trans fb).source := by
    intro y hy
    change y ∈ ea.target ∧ ea.symm y ∈ eb.source at hy
    refine ⟨P.gluedUniversalCoverOrientedChart_target_subset x a hy.1, ?_⟩
    change fa.symm y ∈ fb.source
    rw [← P.gluedUniversalCoverOrientedChart_symm_projection x a hy.1]
    exact P.gluedUniversalCoverOrientedChart_source_projection x b _ hy.2
  have heq : EqOn (ea.symm.trans eb) (fa.symm.trans fb) (ea.symm.trans eb).source := by
    intro y hy
    change eb (ea.symm y) = fb (fa.symm y)
    rw [P.gluedUniversalCoverOrientedChart_apply_projection x b,
      P.gluedUniversalCoverOrientedChart_symm_projection x a hy.1]
  have hnear : (ea.symm.trans eb : ℂ → ℂ) =ᶠ[𝓝 z] (fa.symm.trans fb) :=
    Filter.eventuallyEq_of_mem ((ea.symm.trans eb).open_source.mem_nhds hz) heq
  rw [hnear.fderiv_eq]
  exact P.gluedOrientedComplexAtlas_transition_fderiv_det_pos fa fb
    (P.gluedSelectedOrientedChart_mem _) (P.gluedSelectedOrientedChart_mem _) (hsource hz)

/-- **Math.** The sign of a genuine cover-to-half-plane diffeomorphism
is measured in the corrected oriented chart, not the discontinuously selected
raw seam/interior orientation. -/
def gluedUniversalCoverDiffeomorphOrientationSign
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (q : P.basedTopologicalUniversalCover x) : SignType :=
  SignType.sign (LinearMap.det (fderiv ℝ
    (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ (P.gluedUniversalCoverOrientedChart x q))
    (P.gluedUniversalCoverOrientedChart x q q)).toLinearMap)

/-- **Math.** Corrected orientation signs are locally constant: a fixed
smooth chart has a continuous nonzero Jacobian, and chart changes are positive. -/
theorem gluedUniversalCoverDiffeomorphOrientationSign_locallyConstant
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) :
    IsLocallyConstant (P.gluedUniversalCoverDiffeomorphOrientationSign x Φ) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro q
  let e := P.gluedUniversalCoverOrientedChart x q
  have hsource (u : P.basedTopologicalUniversalCover x) :
      u ∈ (P.gluedUniversalCoverOrientedChart x u).source := by
    rw [P.gluedUniversalCoverOrientedChart_source]
    exact mem_chart_source ℂ u
  have hq : q ∈ e.source := hsource q
  have he := P.gluedUniversalCoverOrientedChart_mem_maximalAtlas x q
  let ρ := fun u : P.basedTopologicalUniversalCover x =>
    SignType.sign (LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e u)).toLinearMap)
  have hread := orientedChartRead_contDiffAt Φ e he (e.map_source hq)
  have hfderiv : ContinuousAt (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e)) (e q) :=
    (hread.fderiv_right (m := 0) (by simp)).continuousAt
  have hdet : ContinuousAt
      (fun z : ℂ => LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) z).toLinearMap) (e q) :=
    ContinuousLinearMap.continuous_det.continuousAt.comp hfderiv
  have hsign : ContinuousAt (SignType.sign : ℝ → SignType)
      (LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e q)).toLinearMap) :=
    continuousAt_sign_of_ne_zero (orientedChartRead_det_ne_zero Φ e he (e.map_source hq))
  have hδ : ContinuousAt (fun u : P.basedTopologicalUniversalCover x =>
      LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e u)).toLinearMap) q :=
    hdet.comp (e.continuousAt hq)
  have hρ : ContinuousAt ρ q := by
    change ContinuousAt ((SignType.sign : ℝ → SignType) ∘
      (fun u : P.basedTopologicalUniversalCover x =>
        LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e u)).toLinearMap)) q
    exact ContinuousAt.comp (f := fun u : P.basedTopologicalUniversalCover x =>
      LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e u)).toLinearMap)
      (g := (SignType.sign : ℝ → SignType)) hsign hδ
  have hnear : ∀ᶠ u in 𝓝 q, ρ u = ρ q :=
    hρ ((isOpen_discrete _).mem_nhds (show ρ q ∈ ({ρ q} : Set SignType) from mem_singleton _))
  have hphase {u : P.basedTopologicalUniversalCover x} (hu : u ∈ e.source) :
      P.gluedUniversalCoverDiffeomorphOrientationSign x Φ u = ρ u := by
    let eu := P.gluedUniversalCoverOrientedChart x u
    apply orientedChartRead_sign_change Φ eu e
      (P.gluedUniversalCoverOrientedChart_mem_maximalAtlas x u) he (hsource u) hu
    apply P.gluedUniversalCoverOrientedChart_transition_det_pos x u q
    refine ⟨eu.map_source (hsource u), ?_⟩
    change eu.symm (eu u) ∈ e.source
    rw [eu.left_inv (hsource u)]
    exact hu
  filter_upwards [hnear, e.open_source.mem_nhds hq] with u hu hs
  calc
    P.gluedUniversalCoverDiffeomorphOrientationSign x Φ u = ρ u := hphase hs
    _ = ρ q := hu
    _ = P.gluedUniversalCoverDiffeomorphOrientationSign x Φ q := rfl

/-- **Math.** Connectedness of the original universal cover makes the
intrinsic corrected orientation sign constant for every genuine diffeomorphism. -/
theorem gluedUniversalCoverDiffeomorphOrientationSign_eq
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (a b : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverDiffeomorphOrientationSign x Φ a =
      P.gluedUniversalCoverDiffeomorphOrientationSign x Φ b :=
  (P.gluedUniversalCoverDiffeomorphOrientationSign_locallyConstant x Φ).apply_eq_of_preconnectedSpace a b

/-- **Math.** A deck transformation preserves the corrected coordinates,
because both its chart index and its point have exactly the same projection. -/
theorem gluedUniversalCoverOrientedChart_deck_apply
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (τ : P.gluedUniversalCoverDeckGroup x) (q u : P.basedTopologicalUniversalCover x) :
    P.gluedUniversalCoverOrientedChart x (P.gluedUniversalCoverDeckDiffeomorph x τ q)
        (P.gluedUniversalCoverDeckDiffeomorph x τ u) =
      P.gluedUniversalCoverOrientedChart x q u := by
  rw [P.gluedUniversalCoverOrientedChart_apply_projection,
    P.gluedUniversalCoverOrientedChart_apply_projection]
  change P.gluedSelectedOrientedChart (P.gluedUniversalCoverProjection x (τ.val q))
      (P.gluedUniversalCoverProjection x (τ.val u)) = _
  rw [τ.property q, τ.property u]

/-- **Math.** The genuine smooth conjugate of an original deck transformation. -/
def gluedUniversalCoverDeckConjugateDiffeomorph
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (τ : P.gluedUniversalCoverDeckGroup x) :
    ℍ ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ ℍ :=
  (Φ.symm.trans (P.gluedUniversalCoverDeckDiffeomorph x τ)).trans Φ

private theorem gluedUniversalCoverDeckConjugate_chart_derivative
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (τ : P.gluedUniversalCoverDeckGroup x)
    (q : P.basedTopologicalUniversalCover x) :
    fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ)
        (chartAt ℂ UpperHalfPlane.I)) (Φ q : ℂ) =
      (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ (P.gluedUniversalCoverOrientedChart x
          (P.gluedUniversalCoverDeckDiffeomorph x τ q)))
        (P.gluedUniversalCoverOrientedChart x q q)).comp
      (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ (P.gluedUniversalCoverOrientedChart x q))
        (Φ q : ℂ)) := by
  let d := P.gluedUniversalCoverDeckDiffeomorph x τ
  let e := P.gluedUniversalCoverOrientedChart x q
  let f := P.gluedUniversalCoverOrientedChart x (d q)
  let r := chartAt ℂ UpperHalfPlane.I
  have he := P.gluedUniversalCoverOrientedChart_mem_maximalAtlas x q
  have hf := P.gluedUniversalCoverOrientedChart_mem_maximalAtlas x (d q)
  have hqe : q ∈ e.source := by
    rw [P.gluedUniversalCoverOrientedChart_source]
    exact mem_chart_source ℂ q
  have hqf : d q ∈ f.source := by
    rw [P.gluedUniversalCoverOrientedChart_source]
    exact mem_chart_source ℂ (d q)
  have hw : r.symm (Φ q : ℂ) = Φ q :=
    r.left_inv (show Φ q ∈ r.source from mem_univ _)
  have hz : Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e (e q) = (Φ q : ℂ) := by
    change (Φ (e.symm (e q)) : ℂ) = _
    rw [e.left_inv hqe]
  have hiv : Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e (Φ q : ℂ) = e q := by
    change e (Φ.symm (r.symm (Φ q : ℂ))) = _
    rw [hw, Diffeomorph.symm_apply_apply]
  have hcoordinate : f (d q) = e q := P.gluedUniversalCoverOrientedChart_deck_apply x τ q q
  have hinv : DifferentiableAt ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e) (Φ q : ℂ) := by
    rw [← hz]
    exact (orientedChartReadInv_contDiffAt Φ e he (e.map_source hqe)).differentiableAt (by simp)
  have hread : DifferentiableAt ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f)
      (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e (Φ q : ℂ)) := by
    rw [hiv, ← hcoordinate]
    exact (orientedChartRead_contDiffAt Φ f hf (f.map_source hqf)).differentiableAt (by simp)
  have hcont : ContinuousAt (fun w : ℂ => d (Φ.symm (r.symm w))) (Φ q : ℂ) :=
    d.continuous.continuousAt.comp
      (Φ.symm.continuous.continuousAt.comp (r.symm.continuousAt
        (r.map_source (show Φ q ∈ r.source from mem_univ _))))
  have hpoint : d (Φ.symm (r.symm (Φ q : ℂ))) = d q := by
    rw [hw, Diffeomorph.symm_apply_apply]
  have hpoint_source : d (Φ.symm (r.symm (Φ q : ℂ))) ∈ f.source := by
    rw [hpoint]
    exact hqf
  have hnear := hcont.eventually (f.open_source.mem_nhds hpoint_source)
  have hreadEq : Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ) r
      =ᶠ[𝓝 (Φ q : ℂ)] Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f ∘ Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e := by
    filter_upwards [hnear] with w hw
    change (Φ (d (Φ.symm (r.symm w))) : ℂ) =
      (Φ (f.symm (e (Φ.symm (r.symm w)))) : ℂ)
    rw [← P.gluedUniversalCoverOrientedChart_deck_apply x τ q
      (Φ.symm (r.symm w)), f.left_inv hw]
  have hd := hreadEq.fderiv_eq.trans (fderiv_comp (Φ q : ℂ) hread hinv)
  rw [hiv] at hd
  exact hd

/-- **Math.** The conjugated deck map has positive real Jacobian in the
original half-plane chart. The signs of the two corrected source Jacobians
agree by connectedness, and the inverse-chart Jacobian cancels the first. -/
theorem gluedUniversalCoverDeckConjugateDiffeomorph_chart_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (τ : P.gluedUniversalCoverDeckGroup x)
    (q : P.basedTopologicalUniversalCover x) :
    0 < LinearMap.det (fderiv ℝ
      (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ)
        (chartAt ℂ UpperHalfPlane.I)) (Φ q : ℂ)).toLinearMap := by
  let d := P.gluedUniversalCoverDeckDiffeomorph x τ
  let e := P.gluedUniversalCoverOrientedChart x q
  let f := P.gluedUniversalCoverOrientedChart x (d q)
  have hqe : q ∈ e.source := by
    rw [P.gluedUniversalCoverOrientedChart_source]
    exact mem_chart_source ℂ q
  have hz : Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e (e q) = (Φ q : ℂ) := by
    change (Φ (e.symm (e q)) : ℂ) = _
    rw [e.left_inv hqe]
  have hi := orientedChartRead_det_inverse_mul Φ e
    (P.gluedUniversalCoverOrientedChart_mem_maximalAtlas x q) (e.map_source hqe)
  rw [hz] at hi
  have hc : f (d q) = e q := P.gluedUniversalCoverOrientedChart_deck_apply x τ q q
  have hs := P.gluedUniversalCoverDiffeomorphOrientationSign_eq x Φ (d q) q
  change SignType.sign (LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f) (f (d q))).toLinearMap) =
    SignType.sign (LinearMap.det (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ e) (e q)).toLinearMap) at hs
  rw [hc] at hs
  rw [P.gluedUniversalCoverDeckConjugate_chart_derivative x Φ τ q]
  change 0 < LinearMap.det
    ((fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Φ f) (e q)).toLinearMap.comp
      (fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartReadInv Φ e) (Φ q : ℂ)).toLinearMap)
  rw [LinearMap.det_comp]
  apply _root_.sign_eq_one_iff.mp
  rw [_root_.sign_mul, hs, ← _root_.sign_mul, mul_comm, hi]
  exact _root_.sign_one

/-- **Math.** Every deck conjugate by any genuine smooth cover-to-half-plane
diffeomorphism preserves orientation. No global sign hypothesis on the raw
selected seam/interior atlas is used. -/
theorem gluedUniversalCoverDeckConjugateDiffeomorph_mfderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X) (x : P.GluedCarrier)
    (Φ : P.basedTopologicalUniversalCover x ≃ₘ⟮modelWithCornersSelf ℝ ℂ,
      modelWithCornersSelf ℝ ℂ⟯ ℍ) (τ : P.gluedUniversalCoverDeckGroup x) (z : ℍ) :
    0 < LinearMap.det (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      (P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ) z).toLinearMap := by
  let Ψ := P.gluedUniversalCoverDeckConjugateDiffeomorph x Φ τ
  let r := chartAt ℂ UpperHalfPlane.I
  let D := fderiv ℝ (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Ψ r) (z : ℂ)
  have hz : z ∈ r.source := mem_univ _
  have ht : (z : ℂ) ∈ r.target := r.map_source hz
  have hh : HasFDerivAt (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Ψ r) D (z : ℂ) :=
    ((orientedChartRead_contDiffAt Ψ r
      (IsManifold.chart_mem_maximalAtlas UpperHalfPlane.I) ht).differentiableAt
        (by simp)).hasFDerivAt
  have hm : HasMFDerivAt (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
      Ψ z D := by
    refine ⟨Ψ.continuous.continuousAt, ?_⟩
    simp only [ModelWithCorners.range_eq_univ]
    change HasFDerivWithinAt (Internal.GluingDeckConjugacyOrientationHelpers.orientedChartRead Ψ r) D univ (z : ℂ)
    exact hh.hasFDerivWithinAt
  dsimp only [TangentSpace]
  rw [hm.mfderiv]
  have hp := P.gluedUniversalCoverDeckConjugateDiffeomorph_chart_det_pos x Φ τ (Φ.symm z)
  simpa only [D, Ψ, r, Diffeomorph.apply_symm_apply] using hp

#print axioms gluedUniversalCoverOrientedChart_mem_maximalAtlas
#print axioms gluedUniversalCoverOrientedChart_apply_projection
#print axioms gluedUniversalCoverOrientedChart_transition_det_pos
#print axioms gluedUniversalCoverDiffeomorphOrientationSign_eq
#print axioms gluedUniversalCoverOrientedChart_deck_apply
#print axioms gluedUniversalCoverDeckConjugateDiffeomorph_mfderiv_det_pos

end ExerciseGluingPreparation
end
end SystolicGrowth
