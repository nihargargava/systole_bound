module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingNativeConformalCharts
public import Geometry.GluingCollarCurvatureChartChanges
public import Geometry.GluingOrientation
public import Geometry.GluingAtlasMetric
public import Mathlib.Analysis.Complex.Conformal
public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

/-!
# Actual overlaps of the native conformal charts

The constructed coordinate change commutes with genuine angular shifts.
Same-seam overlaps therefore retain the literal `2π` translation, including
the seam, and preserve the derived conformal weight. Interior overlaps use
the actual original deck transformations. For mixed overlaps, native metric
compatibility constructs conformality and the genuine orientation correction
constructs a complex-linear differential. Distinct seam overlaps factor
through actual interior charts; outer collars are not assumed disjoint.

The resulting oriented conformal atlas covers the unchanged native carrier
and gives a genuine complex manifold. All sources and geometric cutoffs are
the original ones; complex differentiability is proved, not supplied.
-/

open Set Filter MeasureTheory
open scoped Topology ComplexConjugate UpperHalfPlane

namespace SystolicGrowth

noncomputable section

/-- The actual complex conformal coordinate commutes with angular-origin shifts. -/
theorem gluingCollarConformalComplexCoordinate_add_im (r : ℝ) (z : ℂ) (c : ℝ) :
    gluingCollarConformalComplexCoordinate r (z + (c : ℂ) * Complex.I) =
      gluingCollarConformalComplexCoordinate r z + (c : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [gluingCollarConformalComplexCoordinate]

theorem gluingCollarConformalComplexChart_symm_conj {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (gluingCollarConformalComplexChart hr).symm (conj z) =
      conj ((gluingCollarConformalComplexChart hr).symm z) := by
  simp

theorem gluingCollarConformalComplexChart_target_conj {r : ℝ} (hr : 0 < r) (z : ℂ) :
    conj z ∈ (gluingCollarConformalComplexChart hr).target ↔
      z ∈ (gluingCollarConformalComplexChart hr).target := by
  simp [gluingCollarConformalComplexChart, gluingCollarConformalChart]

theorem gluingComplexCollarTangentForm_conj (r : ℝ) (z v w : ℂ) :
    gluingComplexCollarTangentForm r (conj z) (conj v) (conj w) =
      gluingComplexCollarTangentForm r z v w := by
  simp [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_apply]

/-- The genuine derivative of the constructed inverse complex coordinate. -/
def gluingCollarConformalComplexInverseDerivative {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ℂ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((((gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm z.re)) •
      ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
        Complex.equivRealProdCLM.toContinuousLinearMap)

@[simp] theorem gluingCollarConformalComplexInverseDerivative_apply {r : ℝ}
    (hr : 0 < r) (z v : ℂ) :
    gluingCollarConformalComplexInverseDerivative hr z v =
      ((gluingCollarWarp r ((gluingCollarConformalRadialChart hr).symm z.re) * v.re : ℝ) : ℂ) +
        (v.im : ℂ) * Complex.I := by
  simp [gluingCollarConformalComplexInverseDerivative, Complex.equivRealProdCLM_symm_apply]

/-- The inverse derivative comes from the proved genuine inverse radial
function, only on its actual target. -/
theorem gluingCollarConformalComplexChart_symm_hasFDerivAt {r : ℝ}
    (hr : 0 < r) {z : ℂ} (hz : z ∈ (gluingCollarConformalComplexChart hr).target) :
    HasFDerivAt (gluingCollarConformalComplexChart hr).symm
      (gluingCollarConformalComplexInverseDerivative hr z) z := by
  have hrad : z.re ∈ (gluingCollarConformalRadialChart hr).target := by
    simpa [gluingCollarConformalComplexChart, gluingCollarConformalChart] using hz
  have hi := (gluingCollarConformalRadialChart_symm_hasStrictDerivAt hr hrad).hasDerivAt
  have h := Complex.equivRealProdCLM.symm.hasFDerivAt.comp z
    (((hi.hasFDerivAt.comp z Complex.reCLM.hasFDerivAt).prodMk
      Complex.imCLM.hasFDerivAt))
  convert! h using 1
  ext w
  simp [gluingCollarConformalComplexInverseDerivative,
    Complex.equivRealProdCLM_symm_apply, mul_comm]

/-- The actual inverse chart differential has strictly positive Jacobian. -/
theorem gluingCollarConformalComplexInverseDerivative_det_pos {r : ℝ}
    (hr : 0 < r) (z : ℂ) :
    0 < LinearMap.det (gluingCollarConformalComplexInverseDerivative hr z).toLinearMap := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simpa [LinearMap.toMatrix_apply] using gluingCollarWarp_pos hr
    ((gluingCollarConformalRadialChart hr).symm z.re)

/-- The inverse differential converts the old original collar form to
the proved conformal Euclidean form on the actual new target. -/
theorem gluingCollarConformalComplexInverseDerivative_tangentForm {r : ℝ}
    (hr : 0 < r) {z : ℂ} (_hz : z ∈ (gluingCollarConformalComplexChart hr).target)
    (v w : ℂ) :
    gluingComplexCollarTangentForm r ((gluingCollarConformalComplexChart hr).symm z)
      (gluingCollarConformalComplexInverseDerivative hr z v)
      (gluingCollarConformalComplexInverseDerivative hr z w) =
      Real.exp (2 * gluingCollarConformalLogFactor hr z.re) * (v * conj w).re := by
  rw [gluingComplexCollarTangentForm_apply, gluingCollarConformalLogFactor_exp_two,
    gluingCollarConformalComplexChart_symm_apply]
  simp only [gluingCollarConformalComplexInverseDerivative_apply,
    gluingCollarTangentForm_apply]
  simp [Complex.mul_re, mul_assoc]
  ring

/-- Positive orientation distinguishes complex-linear from conjugate-linear
among actual conformal real differentials. -/
theorem complexLinear_of_isConformalMap_det_pos (D : ℂ →L[ℝ] ℂ)
    (hD : IsConformalMap D) (hdet : 0 < LinearMap.det D.toLinearMap) :
    ∃ E : ℂ →L[ℂ] ℂ, E.restrictScalars ℝ = D := by
  rcases hD.is_complex_or_conj_linear with h | ⟨E, hE⟩
  · exact h
  · have hnonneg : 0 ≤ LinearMap.det (E.restrictScalars ℝ).toLinearMap := by
      simpa [LinearMap.det_restrictScalars, Algebra.norm_complex_eq] using
        Complex.normSq_nonneg (E 1)
    rw [hE] at hnonneg
    change 0 ≤ LinearMap.det (D.toLinearMap.comp Complex.conjCLE.toLinearEquiv.toLinearMap) at hnonneg
    rw [LinearMap.det_comp] at hnonneg
    simp only [Complex.det_conjAe, Complex.conjCLE_toLinearEquiv, mul_neg_one] at hnonneg
    linarith

/-- Actual conformal weighted inner-product identities construct
conformality of the real differential; no conformality premise is needed. -/
theorem isConformalMap_of_complex_weighted_inner (D : ℂ →L[ℝ] ℂ)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hmetric : ∀ v w : ℂ, A * ((D v) * conj (D w)).re = B * (v * conj w).re) :
    IsConformalMap D := by
  rw [isConformalMap_iff]
  refine ⟨B / A, div_pos hB hA, ?_⟩
  intro v w
  have hm := hmetric w v
  rw [Complex.inner, Complex.inner, div_mul_eq_mul_div]
  exact (eq_div_iff hA.ne').mpr (by simpa [mul_comm] using hm)

/-- The genuine positive real Jacobian excludes a zero complex derivative. -/
theorem complex_deriv_ne_zero_of_det_pos {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z)
    (hdet : 0 < LinearMap.det (fderiv ℝ f z).toLinearMap) : deriv f z ≠ 0 := by
  intro hzero
  rw [(hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv] at hdet
  simp [hzero] at hdet

/-- A genuine intermediate native chart locally factors the actual
transition, and therefore transports complex differentiability. -/
theorem gluingConformalTransition_differentiableAt_of_middle
    {M : Type*} [TopologicalSpace M] (e₁ e₂ e : OpenPartialHomeomorph M ℂ)
    {z : ℂ} (hz : z ∈ e₁.target) (he : e₁.symm z ∈ e.source)
    (h₁ : DifferentiableAt ℂ (e₁.symm.trans e) z)
    (h₂ : DifferentiableAt ℂ (e.symm.trans e₂) (e (e₁.symm z))) :
    DifferentiableAt ℂ (e₁.symm.trans e₂) z := by
  have hnear : ∀ᶠ w in nhds z, e₁.symm w ∈ e.source :=
    (e₁.symm.continuousAt hz).eventually (e.open_source.mem_nhds he)
  have hlocal : (e₁.symm.trans e₂ : ℂ → ℂ) =ᶠ[nhds z]
      ((e.symm.trans e₂ : ℂ → ℂ) ∘ (e₁.symm.trans e : ℂ → ℂ)) := by
    filter_upwards [hnear] with w hw
    change e₂ (e₁.symm w) = e₂ (e.symm (e (e₁.symm w)))
    rw [e.left_inv hw]
  exact (h₂.comp z h₁).congr_of_eventuallyEq hlocal

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Native interior transitions are genuinely holomorphic by the actual
original deck action, not just real-smooth or orientation preserving. -/
theorem gluedInteriorComplexAtlas_transition_differentiableAt_complex
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : P.IsGluedInteriorComplexChart e) (he' : P.IsGluedInteriorComplexChart e')
    {z : ℂ} (hz : z ∈ (e.symm.trans e').source) :
    DifferentiableAt ℂ (e.symm.trans e') z := by
  obtain ⟨hzim, γ, hγ⟩ :=
    P.gluedInteriorComplexAtlas_transition_eventually_eq_deck e e' he he' z hz
  exact ((gluingDeckComplex_hasDerivAt γ hzim).congr_of_eventuallyEq hγ).differentiableAt

/-- Correct the actual conformal seam chart's orientation by conjugation,
as required by the original signed polar metric and deck orientation. -/
def seamOrientedConformalComplexChart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) : OpenPartialHomeomorph P.GluedCarrier ℂ :=
  gluingConjugateChart (P.seamConformalComplexChart k θ)

@[simp] theorem seamOrientedConformalComplexChart_source
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamOrientedConformalComplexChart k θ).source =
      (P.seamAngularComplexChart k θ).source := by
  simp [seamOrientedConformalComplexChart]

/-- The existing native orientation correction and the actual inverse
conformal coordinate commute, pointwise on the original carrier. -/
theorem seamOrientedConformalComplexChart_transition_eq_comp
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) :
    ((P.seamOrientedConformalComplexChart k θ).symm.trans e : ℂ → ℂ) =
      ((gluingConjugateChart (P.seamAngularComplexChart k θ)).symm.trans e : ℂ → ℂ) ∘
        (gluingCollarConformalComplexChart P.radius_pos).symm := by
  funext z
  change e ((P.seamAngularComplexChart k θ).symm
    ((gluingCollarConformalComplexChart P.radius_pos).symm (conj z))) =
      e ((P.seamAngularComplexChart k θ).symm
        (conj ((gluingCollarConformalComplexChart P.radius_pos).symm z)))
  rw [gluingCollarConformalComplexChart_symm_conj]

/-- Literal native overlap membership supplies both the inverse-coordinate
domain and the original orientation-corrected overlap domain. -/
theorem seamOrientedConformalComplexChart_transition_source
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) {z : ℂ}
    (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans e).source) :
    z ∈ (gluingCollarConformalComplexChart P.radius_pos).target ∧
      (gluingCollarConformalComplexChart P.radius_pos).symm z ∈
        ((gluingConjugateChart (P.seamAngularComplexChart k θ)).symm.trans e).source := by
  have hc : conj z ∈ (P.seamConformalComplexChart k θ).target :=
    (mem_gluingConjugateChart_target _ _).mp hz.1
  have hcz : z ∈ (gluingCollarConformalComplexChart P.radius_pos).target :=
    (gluingCollarConformalComplexChart_target_conj P.radius_pos z).mp hc.1
  refine ⟨hcz, ?_, ?_⟩
  · apply (mem_gluingConjugateChart_target _ _).mpr
    rw [← gluingCollarConformalComplexChart_symm_conj]
    exact hc.2
  · have h := hz.2
    change (P.seamAngularComplexChart k θ).symm
      ((gluingCollarConformalComplexChart P.radius_pos).symm (conj z)) ∈ e.source at h
    rw [gluingCollarConformalComplexChart_symm_conj] at h
    simpa only [gluingConjugateChart_symm_apply, OpenPartialHomeomorph.symm_symm,
      mem_preimage] using h

/-- The exact mixed transition has a genuine positive-determinant real
derivative, constructed from native orientation and the actual inverse
conformal coordinate. -/
theorem seamOrientedConformalInterior_transition_hasFDerivAt
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans e).source) :
    ∃ D : ℂ →L[ℝ] ℂ,
      HasFDerivAt ((P.seamOrientedConformalComplexChart k θ).symm.trans e) D z ∧
      0 < LinearMap.det D.toLinearMap := by
  obtain ⟨hc, hsource⟩ := P.seamOrientedConformalComplexChart_transition_source k θ e hz
  obtain ⟨D₀, hD₀, hdet₀, _horient⟩ :=
    P.gluedOrientedComplexAtlas_transition_hasFDerivAt_oriented
      (gluingConjugateChart (P.seamAngularComplexChart k θ)) e
      (Or.inr ⟨k, θ, rfl⟩) (Or.inl he) hsource
  refine ⟨(D₀ : ℂ →L[ℝ] ℂ).comp (gluingCollarConformalComplexInverseDerivative P.radius_pos z),
    ?_, ?_⟩
  · rw [P.seamOrientedConformalComplexChart_transition_eq_comp]
    exact hD₀.comp z (gluingCollarConformalComplexChart_symm_hasFDerivAt P.radius_pos hc)
  · change 0 < LinearMap.det (D₀.toLinearEquiv.toLinearMap.comp
      (gluingCollarConformalComplexInverseDerivative P.radius_pos z).toLinearMap)
    rw [LinearMap.det_comp]
    exact mul_pos hdet₀ (gluingCollarConformalComplexInverseDerivative_det_pos P.radius_pos z)

/-- Native metric compatibility yields actual weighted complex-inner-product
compatibility for the genuine mixed conformal transition. -/
theorem seamOrientedConformalInterior_transition_weighted_inner
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans e).source)
    (v w : ℂ) :
    Real.exp (2 * P.gluedConformalLogFactor e
        (((P.seamOrientedConformalComplexChart k θ).symm.trans e) z)) *
      ((fderiv ℝ ((P.seamOrientedConformalComplexChart k θ).symm.trans e) z v) *
        conj (fderiv ℝ ((P.seamOrientedConformalComplexChart k θ).symm.trans e) z w)).re =
      Real.exp (2 * gluingCollarConformalLogFactor P.radius_pos z.re) * (v * conj w).re := by
  let c := gluingCollarConformalComplexChart P.radius_pos
  let a := P.seamAngularComplexChart k θ
  let f := a.symm.trans e
  let i := gluingCollarConformalComplexInverseDerivative P.radius_pos z
  obtain ⟨hc, hsource⟩ := P.seamOrientedConformalComplexChart_transition_source k θ e hz
  have hs : conj (c.symm z) ∈ f.source := by
    refine ⟨(mem_gluingConjugateChart_target _ _).mp hsource.1, ?_⟩
    exact hsource.2
  have hd := (P.seamInterior_transition_contDiffAt k θ e he hs).differentiableAt (by simp)
  have hg : HasFDerivAt (conj : ℂ → ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (c.symm z) :=
    Complex.conjCLE.hasFDerivAt
  have hnew : HasFDerivAt ((P.seamOrientedConformalComplexChart k θ).symm.trans e)
      ((fderiv ℝ f (conj (c.symm z))).comp
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp i)) z := by
    convert! hd.hasFDerivAt.comp z
      (hg.comp z (gluingCollarConformalComplexChart_symm_hasFDerivAt P.radius_pos hc)) using 1
  have hp := P.gluingChartTangentForm_transition_pullback a e (Or.inr ⟨k, θ, rfl⟩)
    (Or.inl he) hs (conj (i v)) (conj (i w))
  have htarget : ((P.seamOrientedConformalComplexChart k θ).symm.trans e) z ∈ e.target :=
    e.map_source hz.2
  rw [← P.gluedConformalLogFactor_interior_tangentForm e he htarget, hnew.fderiv]
  change P.gluingChartTangentForm e (f (conj (c.symm z)))
    (fderiv ℝ f (conj (c.symm z)) (conj (i v)))
    (fderiv ℝ f (conj (c.symm z)) (conj (i w))) = _
  rw [hp, P.gluingChartTangentForm_seam, gluingComplexCollarTangentForm_conj]
  exact gluingCollarConformalComplexInverseDerivative_tangentForm P.radius_pos hc v w

/-- Actual mixed transitions are holomorphic after the original required
orientation correction. Conformality is proved from the native metric,
and complex linearity from the genuine positive Jacobian. -/
theorem seamOrientedConformalInterior_transition_differentiableAt_complex
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans e).source) :
    DifferentiableAt ℂ ((P.seamOrientedConformalComplexChart k θ).symm.trans e) z := by
  obtain ⟨D, hD, hdet⟩ := P.seamOrientedConformalInterior_transition_hasFDerivAt k θ e he hz
  have hm : IsConformalMap D := by
    apply isConformalMap_of_complex_weighted_inner D (Real.exp_pos _) (Real.exp_pos _)
    intro v w
    simpa only [hD.fderiv] using
      P.seamOrientedConformalInterior_transition_weighted_inner k θ e he hz v w
  obtain ⟨E, hE⟩ := complexLinear_of_isConformalMap_det_pos D hm hdet
  exact (hasFDerivAt_of_restrictScalars ℝ hD hE).differentiableAt

/-- The actual reverse mixed transition is holomorphic by the genuine
native inverse law and its proved nonzero complex differential. -/
theorem interiorSeamOrientedConformal_transition_differentiableAt_complex
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (k : Fin (n - 1)) (θ : ℝ) {z : ℂ}
    (hz : z ∈ (e.symm.trans (P.seamOrientedConformalComplexChart k θ)).source) :
    DifferentiableAt ℂ (e.symm.trans (P.seamOrientedConformalComplexChart k θ)) z := by
  let f := (P.seamOrientedConformalComplexChart k θ).symm.trans e
  have ht : z ∈ f.target := hz
  have hs : f.symm z ∈ f.source := f.map_target ht
  have hf := P.seamOrientedConformalInterior_transition_differentiableAt_complex k θ e he hs
  obtain ⟨D, hD, hdet⟩ := P.seamOrientedConformalInterior_transition_hasFDerivAt k θ e he hs
  have hnonzero : deriv f (f.symm z) ≠ 0 :=
    complex_deriv_ne_zero_of_det_pos hf (by rwa [hD.fderiv])
  exact (f.hasDerivAt_symm ht hnonzero hf.hasDerivAt).differentiableAt

/-- The actual same-seam conformal transition remains locally the same
integer-turn imaginary translation, including radial seam zero. -/
theorem seamConformalComplexChart_transition_eventually_eq_add
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {z : ℂ} (hz : z ∈ ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)).source) :
    ∃ m : ℤ, ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ) : ℂ → ℂ) =ᶠ[nhds z]
      fun w => w + (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
  let c := gluingCollarConformalComplexChart P.radius_pos
  have hzc : z ∈ c.target := by
    exact hz.1.1
  have hw : c.symm z ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart k ψ)).source := by
    refine ⟨hz.1.2, ?_⟩
    have h := hz.2
    change (P.seamAngularComplexChart k θ).symm (c.symm z) ∈
      (P.seamConformalComplexChart k ψ).source at h
    simpa only [seamConformalComplexChart_source, OpenPartialHomeomorph.symm_symm,
      mem_preimage] using h
  obtain ⟨m, hm⟩ := P.seamAngularComplexChart_transition_eventually_eq_add k θ ψ hw
  have hm' := (c.continuousAt_symm hzc).tendsto.eventually hm
  refine ⟨m, ?_⟩
  filter_upwards [hm', c.open_target.mem_nhds hzc] with w hw' hwc
  change c (P.seamAngularComplexChart k ψ ((P.seamAngularComplexChart k θ).symm
    (c.symm w))) = _
  rw [hw']
  rw [gluingCollarConformalComplexChart_apply, gluingCollarConformalComplexCoordinate_add_im,
    ← gluingCollarConformalComplexChart_apply P.radius_pos, c.right_inv hwc]

/-- Same-seam transitions are genuinely holomorphic on the exact native
overlap, proved from their actual affine local formula. -/
theorem seamConformalComplexChart_transition_hasDerivAt
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {z : ℂ} (hz : z ∈ ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)).source) :
    HasDerivAt ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)) 1 z := by
  obtain ⟨m, hm⟩ := P.seamConformalComplexChart_transition_eventually_eq_add k θ ψ hz
  exact ((hasDerivAt_id z).add_const
    ((((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)).congr_of_eventuallyEq hm

theorem seamConformalComplexChart_transition_differentiableOn
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ) :
    DifferentiableOn ℂ ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)) ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)).source :=
  fun _ hz => (P.seamConformalComplexChart_transition_hasDerivAt k θ ψ hz).differentiableAt
    |>.differentiableWithinAt

/-- Actual same-seam overlap changes preserve the genuine conformal
metric weight; the unchanged radial coordinate is proved by the transition. -/
theorem seamConformalComplexChart_transition_logFactor
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {z : ℂ} (hz : z ∈ ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)).source) :
    P.gluedConformalLogFactor (P.seamConformalComplexChart k ψ)
        (((P.seamConformalComplexChart k θ).symm.trans
          (P.seamConformalComplexChart k ψ)) z) =
      P.gluedConformalLogFactor (P.seamConformalComplexChart k θ) z := by
  obtain ⟨m, hm⟩ := P.seamConformalComplexChart_transition_eventually_eq_add k θ ψ hz
  rw [hm.self_of_nhds, P.gluedConformalLogFactor_seam, P.gluedConformalLogFactor_seam]
  simp

/-- Conjugating both genuine seam coordinates keeps the transition
holomorphic: the original integer-turn shift changes only its sign. -/
theorem seamOrientedConformalComplexChart_transition_eventually_eq_add
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {z : ℂ} (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans
      (P.seamOrientedConformalComplexChart k ψ)).source) :
    ∃ m : ℤ, ((P.seamOrientedConformalComplexChart k θ).symm.trans
      (P.seamOrientedConformalComplexChart k ψ) : ℂ → ℂ) =ᶠ[nhds z]
      fun w => w - (((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
  have hs : conj z ∈ ((P.seamConformalComplexChart k θ).symm.trans
      (P.seamConformalComplexChart k ψ)).source := by
    refine ⟨(mem_gluingConjugateChart_target _ _).mp hz.1, ?_⟩
    have h := hz.2
    change (P.seamConformalComplexChart k θ).symm (conj z) ∈
      (P.seamOrientedConformalComplexChart k ψ).source at h
    simpa only [seamOrientedConformalComplexChart, gluingConjugateChart_source,
      OpenPartialHomeomorph.symm_symm, mem_preimage] using h
  obtain ⟨m, hm⟩ := P.seamConformalComplexChart_transition_eventually_eq_add k θ ψ hs
  refine ⟨m, ?_⟩
  filter_upwards [hm.comp_tendsto Complex.continuous_conj.continuousAt.tendsto] with w hw
  change conj (((P.seamConformalComplexChart k θ).symm.trans
    (P.seamConformalComplexChart k ψ)) (conj w)) = _
  dsimp only [Function.comp_apply] at hw
  rw [hw]
  simp [sub_eq_add_neg, Complex.conj_ofNat]

theorem seamOrientedConformalComplexChart_transition_differentiableAt_complex
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ ψ : ℝ)
    {z : ℂ} (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans
      (P.seamOrientedConformalComplexChart k ψ)).source) :
    DifferentiableAt ℂ ((P.seamOrientedConformalComplexChart k θ).symm.trans
      (P.seamOrientedConformalComplexChart k ψ)) z := by
  obtain ⟨m, hm⟩ := P.seamOrientedConformalComplexChart_transition_eventually_eq_add k θ ψ hz
  exact (((hasDerivAt_id z).sub_const
    ((((m : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)).congr_of_eventuallyEq hm).differentiableAt

/-- Actual distinct collar overlaps are preserved and factor through
a genuine original interior chart; outer collars are not assumed disjoint. -/
theorem seamOrientedConformalComplexChart_distinct_transition_differentiableAt_complex
    (P : ExerciseGluingPreparation C g n genera X) (k l : Fin (n - 1)) (hkl : k ≠ l)
    (θ ψ : ℝ) {z : ℂ}
    (hz : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans
      (P.seamOrientedConformalComplexChart l ψ)).source) :
    DifferentiableAt ℂ ((P.seamOrientedConformalComplexChart k θ).symm.trans
      (P.seamOrientedConformalComplexChart l ψ)) z := by
  let c := gluingCollarConformalComplexChart P.radius_pos
  have hc : conj z ∈ (P.seamConformalComplexChart k θ).target :=
    (mem_gluingConjugateChart_target _ _).mp hz.1
  have hs : c.symm (conj z) ∈ ((P.seamAngularComplexChart k θ).symm.trans
      (P.seamAngularComplexChart l ψ)).source := by
    refine ⟨hc.2, ?_⟩
    have h := hz.2
    change (P.seamAngularComplexChart k θ).symm (c.symm (conj z)) ∈
      (P.seamOrientedConformalComplexChart l ψ).source at h
    simpa only [seamOrientedConformalComplexChart_source, OpenPartialHomeomorph.symm_symm,
      mem_preimage] using h
  obtain ⟨e, he, hsource⟩ :=
    P.seamAngularComplexChart_distinct_overlap_exists_interior_chart k l hkl θ ψ hs
  have hsource' : (P.seamOrientedConformalComplexChart k θ).symm z ∈ e.source := hsource
  have hfirst : z ∈ ((P.seamOrientedConformalComplexChart k θ).symm.trans e).source :=
    ⟨hz.1, hsource'⟩
  have hsecond : e ((P.seamOrientedConformalComplexChart k θ).symm z) ∈
      (e.symm.trans (P.seamOrientedConformalComplexChart l ψ)).source := by
    refine ⟨e.map_source hsource', ?_⟩
    change e.symm (e ((P.seamOrientedConformalComplexChart k θ).symm z)) ∈
      (P.seamOrientedConformalComplexChart l ψ).source
    rw [e.left_inv hsource']
    exact hz.2
  exact gluingConformalTransition_differentiableAt_of_middle _ _ e hz.1 hsource'
    (P.seamOrientedConformalInterior_transition_differentiableAt_complex k θ e he hfirst)
    (P.interiorSeamOrientedConformal_transition_differentiableAt_complex e he l ψ hsecond)

/-- The original interiors and genuinely conformal, orientation-corrected
seam charts on the unchanged native carrier. -/
def gluedOrientedConformalComplexAtlas (P : ExerciseGluingPreparation C g n genera X) :
    Set (OpenPartialHomeomorph P.GluedCarrier ℂ) :=
  {e | P.IsGluedInteriorComplexChart e ∨
    ∃ (k : Fin (n - 1)) (θ : ℝ), e = P.seamOrientedConformalComplexChart k θ}

/-- This holomorphic atlas covers every original native point, including
the unchanged seams, by the already constructed native conformal coverage. -/
theorem exists_gluedOrientedConformalComplexAtlas_chart
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ e ∈ P.gluedOrientedConformalComplexAtlas, q ∈ e.source := by
  obtain ⟨e, he, hq⟩ := P.exists_gluedConformalComplexAtlas_chart q
  rcases he with he | ⟨k, θ, rfl⟩
  · exact ⟨e, Or.inl he, hq⟩
  · exact ⟨P.seamOrientedConformalComplexChart k θ, Or.inr ⟨k, θ, rfl⟩,
      by simpa only [seamOrientedConformalComplexChart, gluingConjugateChart_source] using hq⟩

/-- Every actual overlap in the covered native oriented conformal atlas
is holomorphic. This includes mixed and distinct-seam overlaps with all
original radius and separation cutoffs unchanged. -/
theorem gluedOrientedConformalComplexAtlas_transition_differentiableOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedOrientedConformalComplexAtlas) (he' : e' ∈ P.gluedOrientedConformalComplexAtlas) :
    DifferentiableOn ℂ (e.symm.trans e') (e.symm.trans e').source := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  rcases he with he | ⟨k, θ, rfl⟩
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact P.gluedInteriorComplexAtlas_transition_differentiableAt_complex e e' he he' hz
    · exact P.interiorSeamOrientedConformal_transition_differentiableAt_complex e he l ψ hz
  · rcases he' with he' | ⟨l, ψ, rfl⟩
    · exact P.seamOrientedConformalInterior_transition_differentiableAt_complex k θ e' he' hz
    · by_cases hkl : k = l
      · subst l
        exact P.seamOrientedConformalComplexChart_transition_differentiableAt_complex k θ ψ hz
      · exact P.seamOrientedConformalComplexChart_distinct_transition_differentiableAt_complex
          k l hkl θ ψ hz

/-- The proved holomorphic overlaps give actual complex-analytic smooth
transitions on the precise native open overlap domains. -/
theorem gluedOrientedConformalComplexAtlas_transition_contDiffOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedOrientedConformalComplexAtlas) (he' : e' ∈ P.gluedOrientedConformalComplexAtlas) :
    ContDiffOn ℂ ⊤ (e.symm.trans e') (e.symm.trans e').source :=
  (P.gluedOrientedConformalComplexAtlas_transition_differentiableOn e e' he he').contDiffOn
    (e.symm.trans e').open_source

/-- The actual covered oriented conformal charted space, separate from
the unchanged native real smooth structure used to construct its metric. -/
@[instance_reducible] def gluedOrientedConformalChartedSpace
    (P : ExerciseGluingPreparation C g n genera X) : ChartedSpace ℂ P.GluedCarrier where
  atlas := P.gluedOrientedConformalComplexAtlas
  chartAt q := (P.exists_gluedOrientedConformalComplexAtlas_chart q).choose
  mem_chart_source q := (P.exists_gluedOrientedConformalComplexAtlas_chart q).choose_spec.2
  chart_mem_atlas q := (P.exists_gluedOrientedConformalComplexAtlas_chart q).choose_spec.1

/-- The original native glued carrier has the constructed complex manifold
structure. All holomorphic transition obligations were proved above. -/
theorem gluedOrientedConformal_isManifold
    (P : ExerciseGluingPreparation C g n genera X) :
    letI := P.gluedOrientedConformalChartedSpace
    IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ P.GluedCarrier := by
  letI := P.gluedOrientedConformalChartedSpace
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id, Set.range_id, inter_univ] using
    P.gluedOrientedConformalComplexAtlas_transition_contDiffOn e e' he he'

#print axioms seamConformalComplexChart_transition_eventually_eq_add
#print axioms seamConformalComplexChart_transition_hasDerivAt
#print axioms gluedInteriorComplexAtlas_transition_differentiableAt_complex
#print axioms seamOrientedConformalInterior_transition_weighted_inner
#print axioms seamOrientedConformalInterior_transition_differentiableAt_complex
#print axioms interiorSeamOrientedConformal_transition_differentiableAt_complex
#print axioms seamOrientedConformalComplexChart_distinct_transition_differentiableAt_complex
#print axioms gluedOrientedConformalComplexAtlas_transition_differentiableOn
#print axioms gluedOrientedConformal_isManifold

end ExerciseGluingPreparation
end
end SystolicGrowth
