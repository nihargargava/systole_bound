module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSmoothAtlas
public import Geometry.GluingSeamOrientation
public import Mathlib.Analysis.Complex.OperatorNorm
public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# A consistent orientation of the original glued atlas

Interior coordinates retain the standard complex-plane orientation. Seam
coordinates are corrected by conjugation, because both signed polar branches
reverse orientation. No native charted-space or manifold instance is replaced.
-/

open Set Filter
open scoped Topology ComplexConjugate

namespace SystolicGrowth

/-- Conjugate the coordinates of a chart without changing its source. -/
noncomputable def gluingConjugateChart {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) : OpenPartialHomeomorph M ℂ :=
  e.trans Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem gluingConjugateChart_source {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) : (gluingConjugateChart e).source = e.source := by
  simp [gluingConjugateChart]

@[simp] theorem gluingConjugateChart_apply {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (q : M) : gluingConjugateChart e q = conj (e q) := rfl

@[simp] theorem gluingConjugateChart_symm_apply {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (z : ℂ) :
    (gluingConjugateChart e).symm z = e.symm (conj z) := rfl

@[simp] theorem mem_gluingConjugateChart_target {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M ℂ) (z : ℂ) :
    z ∈ (gluingConjugateChart e).target ↔ conj z ∈ e.target := by
  simp [gluingConjugateChart]
  rfl

private theorem gluing_fderiv_preconj_det {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f (conj z)) :
    LinearMap.det (fderiv ℝ (fun w => f (conj w)) z).toLinearMap =
      -LinearMap.det (fderiv ℝ f (conj z)).toLinearMap := by
  have hconj : fderiv ℝ (conj : ℂ → ℂ) z = (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
    Complex.conjCLE.fderiv
  have hc : DifferentiableAt ℝ (conj : ℂ → ℂ) z := Complex.conjCLE.differentiableAt
  change LinearMap.det (fderiv ℝ (f ∘ (conj : ℂ → ℂ)) z).toLinearMap = _
  rw [fderiv_comp z hf hc, hconj]
  change LinearMap.det ((fderiv ℝ f (conj z)).toLinearMap.comp
    Complex.conjCLE.toLinearEquiv.toLinearMap) = _
  simp

private theorem gluing_fderiv_postconj_det {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    LinearMap.det (fderiv ℝ (fun w => conj (f w)) z).toLinearMap =
      -LinearMap.det (fderiv ℝ f z).toLinearMap := by
  have hconj : fderiv ℝ (conj : ℂ → ℂ) (f z) = (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
    Complex.conjCLE.fderiv
  have hc : DifferentiableAt ℝ (conj : ℂ → ℂ) (f z) := Complex.conjCLE.differentiableAt
  change LinearMap.det (fderiv ℝ ((conj : ℂ → ℂ) ∘ f) z).toLinearMap = _
  rw [fderiv_comp z hc hf, hconj]
  change LinearMap.det (Complex.conjCLE.toLinearEquiv.toLinearMap.comp
    (fderiv ℝ f z).toLinearMap) = _
  simp

/-- Conjugating a chart stays in the original real-analytic maximal atlas.
This is a coordinate correction, not a new manifold structure. -/
theorem gluingConjugateChart_mem_maximalAtlas
    {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    (e : OpenPartialHomeomorph M ℂ)
    (he : e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ⊤ M) :
    gluingConjugateChart e ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ⊤ M := by
  let G := contDiffGroupoid ⊤ (modelWithCornersSelf ℝ ℂ)
  have hfun : (Complex.conjCLE : ℂ → ℂ) = (conj : ℂ → ℂ) :=
    funext Complex.conjCLE_apply
  have hconjSmooth : ContDiff ℝ ⊤ (conj : ℂ → ℂ) := by
    rw [← hfun]
    exact Complex.conjCLE.contDiff
  have hc : Complex.conjCLE.toHomeomorph.toOpenPartialHomeomorph ∈ G := by
    constructor <;>
      change ContDiffOn ℝ ⊤ (id ∘ (conj : ℂ → ℂ) ∘ id)
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

private theorem exists_oriented_continuousLinearEquiv_of_det_pos
    (D : ℂ →L[ℝ] ℂ) (h : 0 < LinearMap.det D.toLinearMap) :
    ∃ E : ℂ ≃L[ℝ] ℂ, (E : ℂ →L[ℝ] ℂ) = D ∧
      Orientation.map (Fin 2) E.toLinearEquiv Complex.orientation = Complex.orientation := by
  let E := D.toContinuousLinearEquivOfDetNeZero h.ne'
  have hE : (E : ℂ →L[ℝ] ℂ) = D :=
    D.coe_toContinuousLinearEquivOfDetNeZero h.ne'
  refine ⟨E, hE, (Orientation.map_eq_iff_det_pos Complex.orientation E.toLinearEquiv
    (by simp [Complex.finrank_real_complex])).mpr ?_⟩
  change 0 < LinearMap.det (E : ℂ →L[ℝ] ℂ).toLinearMap
  rw [hE]
  exact h

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Interior charts retain their coordinates; every signed seam chart is
conjugated. This atlas lives on the unchanged original glued carrier. -/
def gluedOrientedComplexAtlas (P : ExerciseGluingPreparation C g n genera X) :
    Set (OpenPartialHomeomorph P.GluedCarrier ℂ) :=
  {e | P.IsGluedInteriorComplexChart e ∨ ∃ (k : Fin (n - 1)) (θ : ℝ),
    e = gluingConjugateChart (P.seamAngularComplexChart k θ)}

/-- The corrected atlas covers every original point, including seam zero. -/
theorem exists_gluedOrientedComplexAtlas_chart
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ e ∈ P.gluedOrientedComplexAtlas, q ∈ e.source := by
  obtain ⟨e, he, hq⟩ := P.exists_gluedComplexAtlas_chart q
  rcases he with he | ⟨k, θ, rfl⟩
  · exact ⟨e, Or.inl he, hq⟩
  · exact ⟨gluingConjugateChart (P.seamAngularComplexChart k θ),
      Or.inr ⟨k, θ, rfl⟩, by simpa only [gluingConjugateChart_source] using hq⟩

/-- Every corrected chart belongs to the original carrier's analytic maximal
atlas; in particular the native tangent bundle and metric are unchanged. -/
theorem gluedOrientedComplexAtlas_subset_maximalAtlas
    (P : ExerciseGluingPreparation C g n genera X) :
    P.gluedOrientedComplexAtlas ⊆
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ⊤ P.GluedCarrier := by
  intro e he
  have hnative : P.gluedComplexAtlas ⊆
      IsManifold.maximalAtlas (modelWithCornersSelf ℝ ℂ) ⊤ P.GluedCarrier :=
    IsManifold.subset_maximalAtlas
  rcases he with he | ⟨k, θ, rfl⟩
  · exact hnative (Or.inl he)
  · exact gluingConjugateChart_mem_maximalAtlas _ (hnative (Or.inr ⟨k, θ, rfl⟩))

private theorem native_transition_contDiffAt
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    ContDiffAt ℝ ⊤ (e.symm.trans e') z :=
  (P.gluedComplexAtlas_transition_contDiffOn e e' he he').contDiffAt
    ((e.symm.trans e').open_source.mem_nhds hz)

/-- The corrected charts have analytic transitions on their literal overlaps.
Their native carrier, topology and original analytic structure are retained. -/
theorem gluedOrientedComplexAtlas_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedOrientedComplexAtlas) (he' : e' ∈ P.gluedOrientedComplexAtlas) :
    ContDiffOn ℝ ⊤ (e.symm.trans e') (e.symm.trans e').source := by
  intro z hz
  rcases he with he | ⟨k, θ, rfl⟩
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact (P.native_transition_contDiffAt e e' (Or.inl he) (Or.inl he') hz).contDiffWithinAt
    · have hs : z ∈ (e.symm.trans (P.seamAngularComplexChart l ψ)).source := by
        simpa only [OpenPartialHomeomorph.trans_source, gluingConjugateChart_source] using hz
      have h := P.native_transition_contDiffAt e (P.seamAngularComplexChart l ψ)
        (Or.inl he) (Or.inr ⟨l, ψ, rfl⟩) hs
      exact (Complex.conjCLE.contDiff.contDiffAt.comp z h).contDiffWithinAt
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · have hs : conj z ∈ ((P.seamAngularComplexChart k θ).symm.trans e').source :=
        ⟨(mem_gluingConjugateChart_target _ z).mp hz.1, hz.2⟩
      have h := P.native_transition_contDiffAt (P.seamAngularComplexChart k θ) e'
        (Or.inr ⟨k, θ, rfl⟩) (Or.inl he') hs
      exact (h.comp z Complex.conjCLE.contDiff.contDiffAt).contDiffWithinAt
    · have hs : conj z ∈ ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart l ψ)).source :=
        ⟨(mem_gluingConjugateChart_target _ z).mp hz.1,
          by
            change (P.seamAngularComplexChart k θ).symm (conj z) ∈
              (P.seamAngularComplexChart l ψ).source
            have h := hz.2
            change (gluingConjugateChart (P.seamAngularComplexChart k θ)).symm z ∈
              (gluingConjugateChart (P.seamAngularComplexChart l ψ)).source at h
            simpa only [gluingConjugateChart_source, gluingConjugateChart_symm_apply] using h⟩
      have h := P.native_transition_contDiffAt (P.seamAngularComplexChart k θ)
        (P.seamAngularComplexChart l ψ) (Or.inr ⟨k, θ, rfl⟩) (Or.inr ⟨l, ψ, rfl⟩) hs
      exact (Complex.conjCLE.contDiff.contDiffAt.comp z
        (h.comp z Complex.conjCLE.contDiff.contDiffAt)).contDiffWithinAt

/-- Every corrected coordinate transition has strictly positive real
Jacobian determinant, including all overlaps through the closing seam. -/
theorem gluedOrientedComplexAtlas_transition_fderiv_det_pos
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedOrientedComplexAtlas) (he' : e' ∈ P.gluedOrientedComplexAtlas)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    0 < LinearMap.det (fderiv ℝ (e.symm.trans e') z).toLinearMap := by
  rcases he with he | ⟨k, θ, rfl⟩
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact P.gluedInteriorComplexAtlas_transition_fderiv_det_pos e e' he he' z hz
    · have hs : z ∈ (e.symm.trans (P.seamAngularComplexChart l ψ)).source := by
        simpa only [OpenPartialHomeomorph.trans_source, gluingConjugateChart_source] using hz
      have h := (P.native_transition_contDiffAt e (P.seamAngularComplexChart l ψ)
        (Or.inl he) (Or.inr ⟨l, ψ, rfl⟩) hs).differentiableAt (by simp)
      change 0 < LinearMap.det (fderiv ℝ
        (fun w => conj ((e.symm.trans (P.seamAngularComplexChart l ψ)) w)) z).toLinearMap
      rw [gluing_fderiv_postconj_det h]
      exact neg_pos.mpr (P.interiorSeam_transition_fderiv_det_neg e he l ψ hs)
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · have hs : conj z ∈ ((P.seamAngularComplexChart k θ).symm.trans e').source :=
        ⟨(mem_gluingConjugateChart_target _ z).mp hz.1, hz.2⟩
      have h := (P.native_transition_contDiffAt (P.seamAngularComplexChart k θ) e'
        (Or.inr ⟨k, θ, rfl⟩) (Or.inl he') hs).differentiableAt (by simp)
      change 0 < LinearMap.det (fderiv ℝ
        (fun w => ((P.seamAngularComplexChart k θ).symm.trans e') (conj w)) z).toLinearMap
      rw [gluing_fderiv_preconj_det h]
      exact neg_pos.mpr (P.seamInterior_transition_fderiv_det_neg k θ e' he' hs)
    · have hs : conj z ∈ ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart l ψ)).source :=
        ⟨(mem_gluingConjugateChart_target _ z).mp hz.1,
          by
            change (P.seamAngularComplexChart k θ).symm (conj z) ∈
              (P.seamAngularComplexChart l ψ).source
            have h := hz.2
            change (gluingConjugateChart (P.seamAngularComplexChart k θ)).symm z ∈
              (gluingConjugateChart (P.seamAngularComplexChart l ψ)).source at h
            simpa only [gluingConjugateChart_source, gluingConjugateChart_symm_apply] using h⟩
      have h := (P.native_transition_contDiffAt (P.seamAngularComplexChart k θ)
        (P.seamAngularComplexChart l ψ) (Or.inr ⟨k, θ, rfl⟩)
        (Or.inr ⟨l, ψ, rfl⟩) hs).differentiableAt (by simp)
      have hc : DifferentiableAt ℝ (conj : ℂ → ℂ) z := Complex.conjCLE.differentiableAt
      change 0 < LinearMap.det (fderiv ℝ (fun w => conj
        (((P.seamAngularComplexChart k θ).symm.trans (P.seamAngularComplexChart l ψ))
          (conj w))) z).toLinearMap
      rw [gluing_fderiv_postconj_det
        (f := fun w => ((P.seamAngularComplexChart k θ).symm.trans
          (P.seamAngularComplexChart l ψ)) (conj w)) (h.comp z hc),
        gluing_fderiv_preconj_det h, neg_neg]
      exact P.seamAngularComplexChart_seam_transition_fderiv_det_pos k l θ ψ hs

/-- The actual derivative equivalence of every corrected transition preserves
Mathlib's standard orientation. Together with coverage and maximal-atlas
membership, this constructs a consistent orientation of the native surface. -/
theorem gluedOrientedComplexAtlas_transition_hasFDerivAt_oriented
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedOrientedComplexAtlas) (he' : e' ∈ P.gluedOrientedComplexAtlas)
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    ∃ D : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (e.symm.trans e') (D : ℂ →L[ℝ] ℂ) z ∧
      0 < LinearMap.det D.toLinearEquiv.toLinearMap ∧
      Orientation.map (Fin 2) D.toLinearEquiv Complex.orientation = Complex.orientation := by
  have hf := ((P.gluedOrientedComplexAtlas_transition_contDiffOn e e' he he').contDiffAt
    ((e.symm.trans e').open_source.mem_nhds hz)).differentiableAt (by simp)
  have hdet := P.gluedOrientedComplexAtlas_transition_fderiv_det_pos e e' he he' hz
  obtain ⟨D, hD, horiented⟩ := exists_oriented_continuousLinearEquiv_of_det_pos _ hdet
  refine ⟨D, ?_, ?_, horiented⟩
  · rw [hD]
    exact hf.hasFDerivAt
  · change 0 < LinearMap.det (D : ℂ →L[ℝ] ℂ).toLinearMap
    rw [hD]
    exact hdet

end ExerciseGluingPreparation

#print axioms ExerciseGluingPreparation.exists_gluedOrientedComplexAtlas_chart
#print axioms ExerciseGluingPreparation.gluedOrientedComplexAtlas_subset_maximalAtlas
#print axioms ExerciseGluingPreparation.gluedOrientedComplexAtlas_transition_fderiv_det_pos
#print axioms ExerciseGluingPreparation.gluedOrientedComplexAtlas_transition_hasFDerivAt_oriented

end SystolicGrowth
