module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarConformalLength
public import Geometry.GluingCurveLength
public import Geometry.HyperbolicConformalCurvature

@[expose] public section

/-!
# Genuine conformal charts for the original glued metric

Interior charts are unchanged. Every seam chart is the literal composition
of its original signed-angular chart with the proved inverse-warp
coordinate. Coverage and metric weights are derived on the original
carrier; no new native metric or coordinate-length premise is supplied.
-/

open Set Filter MeasureTheory Bundle Manifold
open scoped Manifold Topology Bundle ComplexConjugate

namespace SystolicGrowth

noncomputable section

/-- The genuine complex derivative of the original inverse-warp coordinate. -/
def gluingCollarConformalComplexDerivative (r : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
    ((gluingCollarConformalDerivative r (z.re, z.im)).comp
      Complex.equivRealProdCLM.toContinuousLinearMap)

@[simp] theorem gluingCollarConformalComplexDerivative_apply (r : ℝ) (z v : ℂ) :
    gluingCollarConformalComplexDerivative r z v = gluingCollarConformalComplexVelocity r z v := by
  simp [gluingCollarConformalComplexDerivative, gluingCollarConformalComplexVelocity,
    Complex.equivRealProdCLM_symm_apply]

/-- The complex coordinate derivative is constructed from the actual radial primitive. -/
theorem gluingCollarConformalComplexChart_hasFDerivAt {r : ℝ} (hr : 0 < r) (z : ℂ) :
    HasFDerivAt (gluingCollarConformalComplexChart hr)
      (gluingCollarConformalComplexDerivative r z) z := by
  convert! Complex.equivRealProdCLM.symm.hasFDerivAt.comp z
    ((gluingCollarConformalChart_hasFDerivAt hr (z.re, z.im)).comp z
      Complex.equivRealProdCLM.hasFDerivAt) using 1

/-- The inverse uses the actual constructed inverse radial coordinate,
while keeping the original lifted angle unchanged. -/
@[simp] theorem gluingCollarConformalComplexChart_symm_apply {r : ℝ}
    (hr : 0 < r) (z : ℂ) :
    (gluingCollarConformalComplexChart hr).symm z =
      ((gluingCollarConformalRadialChart hr).symm z.re : ℂ) +
        (z.im : ℂ) * Complex.I := by
  simp [gluingCollarConformalComplexChart, gluingCollarConformalChart,
    Complex.equivRealProdCLM_symm_apply]

/-- The literal old collar bilinear form is conformally Euclidean after
the genuine derivative, for arbitrary pairs of tangent vectors. -/
theorem gluingComplexCollarTangentForm_eq_conformal {r : ℝ} (hr : 0 < r) (z v w : ℂ) :
    gluingComplexCollarTangentForm r z v w =
      Real.exp (2 * gluingCollarConformalLogFactor hr
        (gluingCollarConformalComplexChart hr z).re) *
        ((gluingCollarConformalComplexDerivative r z v) *
          conj (gluingCollarConformalComplexDerivative r z w)).re := by
  rw [gluingComplexCollarTangentForm_apply, gluingCollarConformalComplexChart_apply,
    gluingCollarConformalComplexCoordinate_re,
    gluingCollarConformalLogFactor_exp_two, gluingCollarConformalRadialChart_left_inv]
  simpa [gluingCollarConformalComplexVelocity, Complex.mul_re] using
    gluingCollarTangentForm_eq_conformal hr (z.re, z.im) (v.re, v.im) (w.re, w.im)

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual native seam chart followed by its constructed conformal coordinate. -/
def seamConformalComplexChart (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) : OpenPartialHomeomorph P.GluedCarrier ℂ :=
  (P.seamAngularComplexChart k θ).trans (gluingCollarConformalComplexChart P.radius_pos)

/-- No source is removed by the coordinate change, including the original seam. -/
@[simp] theorem seamConformalComplexChart_source (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamConformalComplexChart k θ).source = (P.seamAngularComplexChart k θ).source := by
  simp [seamConformalComplexChart]

@[simp] theorem seamConformalComplexChart_apply (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (q : P.GluedCarrier) :
    P.seamConformalComplexChart k θ q =
      gluingCollarConformalComplexCoordinate (gluingRadius C g)
        (P.seamAngularComplexChart k θ q) := by
  simp [seamConformalComplexChart]

/-- The actual radial and angular equations, evaluated at the original native points. -/
theorem seamConformalComplexChart_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    P.seamConformalComplexChart k θ (P.seamAngularPoint k θ p) =
      (gluingCollarConformalRadius (gluingRadius C g) p.1.1 : ℂ) +
        (p.2.1 : ℂ) * Complex.I := by
  simp [gluingCollarConformalComplexCoordinate]

/-- The genuine target is exactly the image of the unchanged signed-angular target. -/
theorem seamConformalComplexChart_target (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) :
    (P.seamConformalComplexChart k θ).target =
      gluingCollarConformalComplexCoordinate (gluingRadius C g) ''
        (P.seamAngularComplexChart k θ).target := by
  rw [seamConformalComplexChart, OpenPartialHomeomorph.trans_target'']
  simp

/-- Actual inverse evaluation at the unchanged native parametrization. -/
theorem seamConformalComplexChart_symm_seamAngularPoint
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (p : GluingSeamAngularDomain C g θ) :
    (P.seamConformalComplexChart k θ).symm
      ((gluingCollarConformalRadius (gluingRadius C g) p.1.1 : ℂ) +
        (p.2.1 : ℂ) * Complex.I) = P.seamAngularPoint k θ p := by
  rw [← P.seamConformalComplexChart_seamAngularPoint]
  apply (P.seamConformalComplexChart k θ).left_inv
  rw [P.seamConformalComplexChart_source, P.seamAngularComplexChart_source]
  exact ⟨p, rfl⟩

/-- The new target is the genuine radial-domain rectangle read through
the actual inverse coordinate, not a postulated chart-domain condition. -/
theorem mem_seamConformalComplexChart_target
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) (z : ℂ) :
    z ∈ (P.seamConformalComplexChart k θ).target ↔
      z.re ∈ (gluingCollarConformalRadialChart P.radius_pos).target ∧
      (gluingCollarConformalRadialChart P.radius_pos).symm z.re ∈
        Ioo (-gluingDepth C g) (gluingDepth C g) ∧
      z.im ∈ GluingAngularInterval θ := by
  rw [seamConformalComplexChart, OpenPartialHomeomorph.trans_target]
  change (z ∈ (gluingCollarConformalComplexChart P.radius_pos).target ∧
    (gluingCollarConformalComplexChart P.radius_pos).symm z ∈
      (P.seamAngularComplexChart k θ).target) ↔ _
  rw [P.mem_seamAngularComplexChart_target, gluingCollarConformalComplexChart_symm_apply]
  have htarget : z ∈ (gluingCollarConformalComplexChart P.radius_pos).target ↔
      z.re ∈ (gluingCollarConformalRadialChart P.radius_pos).target := by
    simp [gluingCollarConformalComplexChart, gluingCollarConformalChart]
  simp [htarget]

/-- Original interior charts and the literal conformal seam charts. -/
def gluedConformalComplexAtlas (P : ExerciseGluingPreparation C g n genera X) :
    Set (OpenPartialHomeomorph P.GluedCarrier ℂ) :=
  {e | P.IsGluedInteriorComplexChart e ∨
    ∃ (k : Fin (n - 1)) (θ : ℝ), e = P.seamConformalComplexChart k θ}

/-- Existing native coverage proves coverage for the conformal charts
without changing any component, seam, radius or source cutoff. -/
theorem exists_gluedConformalComplexAtlas_chart
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedCarrier) :
    ∃ e ∈ P.gluedConformalComplexAtlas, q ∈ e.source := by
  obtain ⟨e, he, hq⟩ := P.exists_gluedComplexAtlas_chart q
  rcases he with he | ⟨k, θ, rfl⟩
  · exact ⟨e, Or.inl he, hq⟩
  · exact ⟨P.seamConformalComplexChart k θ, Or.inr ⟨k, θ, rfl⟩, by simpa using hq⟩

/-- The covered conformal charted space is constructed, without replacing
the existing smooth atlas used to define the original native metric. -/
@[instance_reducible] def gluedConformalChartedSpace (P : ExerciseGluingPreparation C g n genera X) :
    ChartedSpace ℂ P.GluedCarrier where
  atlas := P.gluedConformalComplexAtlas
  chartAt q := (P.exists_gluedConformalComplexAtlas_chart q).choose
  mem_chart_source q := (P.exists_gluedConformalComplexAtlas_chart q).choose_spec.2
  chart_mem_atlas q := (P.exists_gluedConformalComplexAtlas_chart q).choose_spec.1

/-- The actual target's radial coordinate belongs to the constructed
open conformal domain, including signed-radius zero. -/
theorem seamConformalComplexChart_target_radial
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {z : ℂ} (hz : z ∈ (P.seamConformalComplexChart k θ).target) :
    z.re ∈ (gluingCollarConformalRadialChart P.radius_pos).target := by
  rw [P.seamConformalComplexChart_target] at hz
  obtain ⟨w, _hw, rfl⟩ := hz
  rw [gluingCollarConformalComplexCoordinate_re]
  exact (gluingCollarConformalRadialChart P.radius_pos).map_source (mem_univ _)

/-- The unchanged source contains an original seam point, so these
charts are genuinely not any of the original interior charts. -/
theorem seamConformalComplexChart_not_interior
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ) :
    ¬ P.IsGluedInteriorComplexChart (P.seamConformalComplexChart k θ) := by
  intro he
  obtain ⟨i, z, ρ, hρ, _h4, hq, hf, he⟩ := he
  let p : GluingSeamAngularDomain C g θ :=
    (⟨0, by constructor <;> linarith [P.depth_pos]⟩,
      ⟨θ, by constructor <;> linarith [Real.pi_pos]⟩)
  have hp : P.seamAngularPoint k θ p ∈
      (P.gluedInteriorComplexChart i z ρ hρ hq hf).source := by
    rw [← he, P.seamConformalComplexChart_source, P.seamAngularComplexChart_source]
    exact ⟨p, rfl⟩
  rw [P.gluedInteriorComplexChart_source] at hp
  obtain ⟨w, hw⟩ := hp
  exact P.seamAngularPoint_ne_componentInteriorPoint_of_zero k θ p rfl i
    ⟨Quotient.mk'' w.1, hq w⟩ hw.symm

/-- The actual conformal weight of the constructed native atlas. -/
def gluedConformalLogFactor (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (z : ℂ) : ℝ := by
  classical
  exact if P.IsGluedInteriorComplexChart e then -Real.log z.im
    else gluingCollarConformalLogFactor P.radius_pos z.re

theorem gluedConformalLogFactor_interior (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    (z : ℂ) : P.gluedConformalLogFactor e z = -Real.log z.im := by
  simp [gluedConformalLogFactor, he]

theorem gluedConformalLogFactor_seam (P : ExerciseGluingPreparation C g n genera X)
    (k : Fin (n - 1)) (θ : ℝ) (z : ℂ) :
    P.gluedConformalLogFactor (P.seamConformalComplexChart k θ) z =
      gluingCollarConformalLogFactor P.radius_pos z.re := by
  simp [gluedConformalLogFactor, P.seamConformalComplexChart_not_interior k θ]

/-- The actual conformal atlas weights are continuous on their genuine
open targets; regularity outside a chart is neither needed nor assumed. -/
theorem gluedConformalLogFactor_continuousOn
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedConformalComplexAtlas) :
    ContinuousOn (P.gluedConformalLogFactor e) e.target := by
  rcases he with he | ⟨k, θ, rfl⟩
  · have heq : P.gluedConformalLogFactor e = fun z => -Real.log z.im :=
      funext (P.gluedConformalLogFactor_interior e he)
    rw [heq]
    exact ((Real.continuousOn_log.comp Complex.continuous_im.continuousOn
      (fun z hz => (P.gluedInteriorComplexChart_target_im_pos e he hz).ne')).neg)
  · have heq : P.gluedConformalLogFactor (P.seamConformalComplexChart k θ) =
        fun z => gluingCollarConformalLogFactor P.radius_pos z.re :=
      funext (P.gluedConformalLogFactor_seam k θ)
    rw [heq]
    exact (gluingCollarConformalLogFactor_continuousOn P.radius_pos).comp
      Complex.continuous_re.continuousOn (fun _ hz => P.seamConformalComplexChart_target_radial k θ hz)

/-- The existing native seam tangent form yields, rather than assumes,
the weight in the actual conformal target. -/
theorem seamConformalComplexChart_tangentForm
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    (q : P.GluedCarrier) (v w : ℂ) :
    P.gluingChartTangentForm (P.seamAngularComplexChart k θ)
        (P.seamAngularComplexChart k θ q) v w =
      Real.exp (2 * P.gluedConformalLogFactor (P.seamConformalComplexChart k θ)
        (P.seamConformalComplexChart k θ q)) *
        ((gluingCollarConformalComplexDerivative (gluingRadius C g)
            (P.seamAngularComplexChart k θ q) v) *
          conj (gluingCollarConformalComplexDerivative (gluingRadius C g)
            (P.seamAngularComplexChart k θ q) w)).re := by
  rw [P.gluingChartTangentForm_seam, P.gluedConformalLogFactor_seam]
  exact gluingComplexCollarTangentForm_eq_conformal P.radius_pos _ _ _

/-- Every actual differentiable native curve has the conformal-coordinate
velocity obtained from the derivative of the constructed coordinate map. -/
theorem gluedCurve_seamConformal_deriv
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {t : ℝ}
    (ht : γ t ∈ (P.seamConformalComplexChart k θ).source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    deriv (P.seamConformalComplexChart k θ ∘ γ) t =
      gluingCollarConformalComplexVelocity (gluingRadius C g)
        (P.seamAngularComplexChart k θ (γ t))
        (deriv (P.seamAngularComplexChart k θ ∘ γ) t) := by
  have ht' : γ t ∈ (P.seamAngularComplexChart k θ).source := by simpa using ht
  have hd : DifferentiableAt ℝ (P.seamAngularComplexChart k θ ∘ γ) t :=
    ((mdifferentiableAt_atlas (Or.inr ⟨k, θ, rfl⟩) ht').comp t hγ).differentiableAt
  have heq : (P.seamConformalComplexChart k θ ∘ γ) =
      gluingCollarConformalComplexCoordinate (gluingRadius C g) ∘
        (P.seamAngularComplexChart k θ ∘ γ) := by
    funext t
    simp
  rw [heq]
  exact (gluingCollarConformalComplexCoordinate_comp_hasDerivAt P.radius_pos hd.hasDerivAt).deriv

set_option backward.isDefEq.respectTransparency false in
/-- Native seam speed, including the seam, is exactly conformally
weighted ordinary Euclidean coordinate speed in the constructed chart. -/
theorem gluedCurve_speed_seamConformal
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {t : ℝ}
    (ht : γ t ∈ (P.seamConformalComplexChart k θ).source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ =
      Real.exp (P.gluedConformalLogFactor (P.seamConformalComplexChart k θ)
        (P.seamConformalComplexChart k θ (γ t))) *
          ‖deriv (P.seamConformalComplexChart k θ ∘ γ) t‖ := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  have ht' : γ t ∈ (P.seamAngularComplexChart k θ).source := by simpa using ht
  rw [P.gluedCurve_speed_in_chart _ (Or.inr ⟨k, θ, rfl⟩) ht' hγ,
    P.gluingChartTangentForm_seam, gluingCollarConformalComplexVelocity_speed P.radius_pos,
    P.gluedCurve_seamConformal_deriv k θ ht hγ, P.gluedConformalLogFactor_seam]
  simp

/-- The original hyperbolic chart weight is derived on its genuine
positive-imaginary target. -/
theorem gluedConformalLogFactor_interior_exp
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ e.target) :
    Real.exp (P.gluedConformalLogFactor e z) = 1 / z.im := by
  rw [P.gluedConformalLogFactor_interior e he, Real.exp_neg,
    Real.exp_log (P.gluedInteriorComplexChart_target_im_pos e he hz), one_div]

/-- The original interior bilinear form supplies its exact conformal
target weight, with the actual upper-half-plane chart positivity. -/
theorem gluedConformalLogFactor_interior_tangentForm
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {z : ℂ} (hz : z ∈ e.target) (v w : ℂ) :
    P.gluingChartTangentForm e z v w =
      Real.exp (2 * P.gluedConformalLogFactor e z) * (v * conj w).re := by
  rw [P.gluingChartTangentForm_interior e he, gluingComplexHalfPlaneTangentForm_apply,
    show 2 * P.gluedConformalLogFactor e z =
      P.gluedConformalLogFactor e z + P.gluedConformalLogFactor e z by ring,
    Real.exp_add, P.gluedConformalLogFactor_interior_exp e he hz]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Every actual native curve has exactly the conformal Euclidean speed
in every member of the constructed covering atlas. -/
theorem gluedCurve_speed_conformal
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedConformalComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {t : ℝ} (ht : γ t ∈ e.source)
    (hγ : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℂ) γ t) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t 1‖ =
      Real.exp (P.gluedConformalLogFactor e (e (γ t))) * ‖deriv (e ∘ γ) t‖ := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rcases he with he | ⟨k, θ, rfl⟩
  · have hp : 0 < (e (γ t)).im :=
      P.gluedInteriorComplexChart_target_im_pos e he (e.map_source ht)
    rw [P.gluedCurve_speed_in_chart e (Or.inl he) ht hγ,
      P.gluingChartTangentForm_interior e he, gluingComplexHalfPlaneTangentForm_self,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hp.le,
      P.gluedConformalLogFactor_interior_exp e he (e.map_source ht)]
    ring
  · exact P.gluedCurve_speed_seamConformal k θ ht hγ

/-- Actual native `C¹` path length in every constructed conformal chart
is the exact weighted Euclidean length, with no global differentiability
of the curve or coordinate function outside the given interval. -/
theorem gluedCurve_pathELength_conformal
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedConformalComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) e.source) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.exp (P.gluedConformalLogFactor e (e (γ t))) * ‖deriv (e ∘ γ) t‖) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t :=
    P.gluedCurve_mdifferentiableAt_Ioo hγ ht
  dsimp only
  rw [← ofReal_norm, P.gluedCurve_speed_conformal e he (hmap ⟨ht.1.le, ht.2.le⟩) hd]

#print axioms seamConformalComplexChart_source
#print axioms exists_gluedConformalComplexAtlas_chart
#print axioms gluedConformalLogFactor_continuousOn
#print axioms seamConformalComplexChart_tangentForm
#print axioms gluedCurve_speed_conformal
#print axioms gluedCurve_pathELength_conformal

end ExerciseGluingPreparation

end
end SystolicGrowth
