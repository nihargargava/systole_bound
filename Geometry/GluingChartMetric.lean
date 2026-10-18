module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingSmoothAtlas
public import Geometry.GluingPolarMetric

@[expose] public section

/-!
# Concrete tangent forms in the actual glued charts

The complex model reads an interior chart as a point of the upper half-plane,
and a seam chart as signed radius and lifted angle. These are the actual
continuous positive bilinear coordinate forms, with bounded unit ellipsoids.
Global tangent-bundle descent still requires all transition compatibility.
-/

open Set Metric UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate

namespace SystolicGrowth

/-- The Poincare tangent form as a continuous bilinear map in complex coordinates. -/
noncomputable def gluingComplexHalfPlaneTangentForm (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (z.im ^ 2)⁻¹ •
    (Complex.reCLM.smulRight Complex.reCLM + Complex.imCLM.smulRight Complex.imCLM)

@[simp] theorem gluingComplexHalfPlaneTangentForm_apply (z v u : ℂ) :
    gluingComplexHalfPlaneTangentForm z v u = (v * conj u).re / z.im ^ 2 := by
  simp only [gluingComplexHalfPlaneTangentForm, smul_apply,
    add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, div_eq_mul_inv]
  ring

/-- The actual collar form in the same complex chart/tangent model. -/
noncomputable def gluingComplexCollarTangentForm (r : ℝ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight Complex.reCLM +
    (gluingCollarWarp r z.re) ^ 2 • Complex.imCLM.smulRight Complex.imCLM

@[simp] theorem gluingComplexCollarTangentForm_apply (r : ℝ) (z v u : ℂ) :
    gluingComplexCollarTangentForm r z v u =
      gluingCollarTangentForm r (z.re, z.im) (v.re, v.im) (u.re, u.im) := by
  simp [gluingComplexCollarTangentForm, mul_assoc]

theorem gluingComplexHalfPlaneTangentForm_symm (z v u : ℂ) :
    gluingComplexHalfPlaneTangentForm z v u = gluingComplexHalfPlaneTangentForm z u v := by
  simp only [gluingComplexHalfPlaneTangentForm_apply, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

theorem gluingComplexCollarTangentForm_symm (r : ℝ) (z v u : ℂ) :
    gluingComplexCollarTangentForm r z v u = gluingComplexCollarTangentForm r z u v := by
  simp only [gluingComplexCollarTangentForm_apply]
  exact gluingCollarTangentForm_symm r _ _ _

theorem gluingComplexHalfPlaneTangentForm_self (z v : ℂ) :
    gluingComplexHalfPlaneTangentForm z v v = ‖v‖ ^ 2 / z.im ^ 2 := by
  simp only [gluingComplexHalfPlaneTangentForm_apply, Complex.mul_conj',
    ← Complex.ofReal_pow, Complex.ofReal_re]

theorem gluingComplexHalfPlaneTangentForm_pos {z : ℂ} (hz : 0 < z.im)
    (v : ℂ) (hv : v ≠ 0) : 0 < gluingComplexHalfPlaneTangentForm z v v := by
  rw [gluingComplexHalfPlaneTangentForm_self]
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) (sq_pos_of_pos hz)

theorem gluingComplexCollarTangentForm_pos {r : ℝ} (hr : 0 < r)
    (z v : ℂ) (hv : v ≠ 0) : 0 < gluingComplexCollarTangentForm r z v v := by
  rw [gluingComplexCollarTangentForm_apply]
  apply gluingCollarTangentForm_pos hr
  intro h
  apply hv
  exact Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem gluingComplexHalfPlaneTangentForm_continuousOn :
    ContinuousOn gluingComplexHalfPlaneTangentForm {z : ℂ | 0 < z.im} := by
  unfold gluingComplexHalfPlaneTangentForm
  exact ((Complex.continuous_im.pow 2).continuousOn.inv₀
    (fun z hz => (sq_pos_of_pos hz).ne')).smul continuousOn_const

/-- Continuity of the collar coefficient includes the signed-radius zero seam. -/
theorem gluingComplexCollarTangentForm_continuous (r : ℝ) :
    Continuous (gluingComplexCollarTangentForm r) := by
  letI : ContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _
      (inferInstanceAs (AddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
      (inferInstanceAs (IsTopologicalAddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  unfold gluingComplexCollarTangentForm
  have hw : Continuous (fun z : ℂ => (gluingCollarWarp r z.re) ^ 2) :=
    (((gluingCollarWarp_continuous r).comp Complex.continuous_re).pow 2)
  have hform : Continuous (fun _ : ℂ => Complex.imCLM.smulRight Complex.imCLM) :=
    continuous_const
  exact continuous_const.add (hw.smul hform)

theorem gluingComplexHalfPlaneTangentForm_unit_norm_le {z : ℂ} (hz : 0 < z.im)
    (v : ℂ) (hv : gluingComplexHalfPlaneTangentForm z v v < 1) : ‖v‖ ≤ z.im := by
  rw [gluingComplexHalfPlaneTangentForm_self, div_lt_one (sq_pos_of_pos hz)] at hv
  nlinarith [norm_nonneg v]

theorem gluingComplexCollarTangentForm_unit_norm_le {r : ℝ} (hr : 0 < r)
    (z v : ℂ) (hv : gluingComplexCollarTangentForm r z v v < 1) :
    ‖v‖ ≤ 2 * (1 + ((gluingCollarWarp r z.re) ^ 2)⁻¹) := by
  rw [gluingComplexCollarTangentForm_apply] at hv
  have hb := gluingCollarTangentForm_unit_norm_le hr (z.re, z.im) (v.re, v.im) hv
  have hp : |v.re| ≤ 1 + ((gluingCollarWarp r z.re) ^ 2)⁻¹ ∧
      |v.im| ≤ 1 + ((gluingCollarWarp r z.re) ^ 2)⁻¹ := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hb
  calc
    ‖v‖ ≤ |v.re| + |v.im| := Complex.norm_le_abs_re_add_abs_im v
    _ ≤ _ := by linarith [hp.1, hp.2]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

theorem gluedInteriorComplexChart_target_im_pos
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ e.target) : 0 < z.im := by
  obtain ⟨i, w, ρ, hρ, _h4, hq, hf, rfl⟩ := he
  rw [P.gluedInteriorComplexChart_target] at hz
  obtain ⟨a, rfl⟩ := hz
  exact a.1.im_pos

/-- A seam chart contains a seam point, whereas genuine interior charts do not. -/
theorem seamAngularComplexChart_not_interior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    ¬ P.IsGluedInteriorComplexChart (P.seamAngularComplexChart k θ) := by
  intro he
  obtain ⟨i, z, ρ, hρ, _h4, hq, hf, he⟩ := he
  let p : GluingSeamAngularDomain C g θ :=
    (⟨0, by constructor <;> linarith [P.depth_pos]⟩,
      ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  have hp : P.seamAngularPoint k θ p ∈
      (P.gluedInteriorComplexChart i z ρ hρ hq hf).source := by
    rw [← he, P.seamAngularComplexChart_source]
    exact ⟨p, rfl⟩
  rw [P.gluedInteriorComplexChart_source] at hp
  obtain ⟨w, hw⟩ := hp
  exact P.seamAngularPoint_ne_componentInteriorPoint_of_zero k θ p rfl i
    ⟨Quotient.mk'' w.1, hq w⟩ hw.symm

/-- Coordinate forms are selected by the existing concrete atlas predicate,
not by an assumed global metric or an independently chosen covering. -/
noncomputable def gluingChartTangentForm
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  classical
  exact if P.IsGluedInteriorComplexChart e then gluingComplexHalfPlaneTangentForm z
    else gluingComplexCollarTangentForm (gluingRadius C g) z

theorem gluingChartTangentForm_interior
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e) (z : ℂ) :
    P.gluingChartTangentForm e z = gluingComplexHalfPlaneTangentForm z := by
  simp [gluingChartTangentForm, he]

theorem gluingChartTangentForm_seam
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) (z : ℂ) :
    P.gluingChartTangentForm (P.seamAngularComplexChart k θ) z =
      gluingComplexCollarTangentForm (gluingRadius C g) z := by
  simp [gluingChartTangentForm, P.seamAngularComplexChart_not_interior k θ]

theorem gluingChartTangentForm_symm
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (z v u : ℂ) :
    P.gluingChartTangentForm e z v u = P.gluingChartTangentForm e z u v := by
  classical
  by_cases he : P.IsGluedInteriorComplexChart e
  · rw [P.gluingChartTangentForm_interior e he]
    exact gluingComplexHalfPlaneTangentForm_symm z v u
  · simp only [gluingChartTangentForm, if_neg he]
    exact gluingComplexCollarTangentForm_symm _ z v u

theorem gluingChartTangentForm_pos
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) {z : ℂ} (hz : z ∈ e.target)
    (v : ℂ) (hv : v ≠ 0) : 0 < P.gluingChartTangentForm e z v v := by
  classical
  by_cases he : P.IsGluedInteriorComplexChart e
  · rw [P.gluingChartTangentForm_interior e he]
    exact gluingComplexHalfPlaneTangentForm_pos (P.gluedInteriorComplexChart_target_im_pos e he hz) v hv
  · simp only [gluingChartTangentForm, if_neg he]
    exact gluingComplexCollarTangentForm_pos P.radius_pos z v hv

theorem gluingChartTangentForm_continuousOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) :
    ContinuousOn (P.gluingChartTangentForm e) e.target := by
  classical
  by_cases he : P.IsGluedInteriorComplexChart e
  · have heq : P.gluingChartTangentForm e = gluingComplexHalfPlaneTangentForm :=
      funext (P.gluingChartTangentForm_interior e he)
    rw [heq]
    exact gluingComplexHalfPlaneTangentForm_continuousOn.mono
      (fun z hz => P.gluedInteriorComplexChart_target_im_pos e he hz)
  · have heq : P.gluingChartTangentForm e = gluingComplexCollarTangentForm (gluingRadius C g) := by
      funext z
      simp [gluingChartTangentForm, he]
    rw [heq]
    exact (gluingComplexCollarTangentForm_continuous _).continuousOn

theorem gluingChartTangentForm_isVonNBounded
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) {z : ℂ} (hz : z ∈ e.target) :
    Bornology.IsVonNBounded ℝ {v : ℂ | P.gluingChartTangentForm e z v v < 1} := by
  classical
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  by_cases he : P.IsGluedInteriorComplexChart e
  · refine ⟨z.im, fun v hv => ?_⟩
    rw [P.gluingChartTangentForm_interior e he] at hv
    exact gluingComplexHalfPlaneTangentForm_unit_norm_le
      (P.gluedInteriorComplexChart_target_im_pos e he hz) v hv
  · refine ⟨2 * (1 + ((gluingCollarWarp (gluingRadius C g) z.re) ^ 2)⁻¹), fun v hv => ?_⟩
    simp only [gluingChartTangentForm, if_neg he] at hv
    exact gluingComplexCollarTangentForm_unit_norm_le P.radius_pos z v hv

end ExerciseGluingPreparation

#print axioms gluingComplexCollarTangentForm_continuous
#print axioms ExerciseGluingPreparation.seamAngularComplexChart_not_interior
#print axioms ExerciseGluingPreparation.gluingChartTangentForm_pos
#print axioms ExerciseGluingPreparation.gluingChartTangentForm_continuousOn
#print axioms ExerciseGluingPreparation.gluingChartTangentForm_isVonNBounded

end SystolicGrowth
