module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingIntrinsicMetric
public import Geometry.GluingCurveSpeed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

@[expose] public section

/-!
# Length bounds in the actual glued charts

The native tangent metric controls signed radial variation and angular
variation in a seam chart. These comparisons use the integral of the
actual native velocity, not a distance in the ambient coordinate model.
-/

open Set MeasureTheory Manifold Bundle
open scoped Manifold Bundle ENNReal

namespace SystolicGrowth

/-- The signed radial component never exceeds the actual collar speed. -/
theorem abs_re_le_sqrt_gluingCollarTangentForm (r : ℝ) (z v : ℂ) :
    |v.re| ≤ Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
  rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self]
  exact Real.abs_le_sqrt (le_add_of_nonneg_right
    (mul_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- The seam's own angular coefficient is a lower bound throughout the collar. -/
theorem sinh_mul_abs_im_le_sqrt_gluingCollarTangentForm {r : ℝ}
    (hr : 0 < r) (z v : ℂ) :
    Real.sinh r * |v.im| ≤ Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
  have hw : Real.sinh r ≤ gluingCollarWarp r z.re := by
    exact Real.sinh_le_sinh.mpr (le_add_of_nonneg_right (abs_nonneg _))
  have hs : 0 ≤ Real.sinh r := (Real.sinh_pos_iff.mpr hr).le
  have hsq : (Real.sinh r) ^ 2 ≤ (gluingCollarWarp r z.re) ^ 2 :=
    pow_le_pow_left₀ hs hw 2
  rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self]
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, sq_abs]
  exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans
    (le_add_of_nonneg_left (sq_nonneg _))

/-- Radial endpoint separation is paid for by the collar length integral. -/
theorem collar_radial_enorm_sub_le_lintegral {α : ℝ → ℂ} {a b : ℝ}
    (r : ℝ) (hα : ContDiffOn ℝ 1 α (Icc a b)) (hab : a ≤ b) :
    ‖(α b).re - (α a).re‖ₑ ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  have hq : ContDiffOn ℝ 1 (fun t => (α t).re) (Icc a b) :=
    Complex.reCLM.contDiff.comp_contDiffOn hα
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hq hab).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hd : DifferentiableAt ℝ α t :=
    ((hα t ⟨ht.1.le, ht.2.le⟩).contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
      one_ne_zero
  have hder : deriv (fun t => (α t).re) t = (deriv α t).re := by
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv
  rw [hder, ← ofReal_norm, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (abs_re_le_sqrt_gluingCollarTangentForm r _ _)

/-- Angular endpoint separation is paid for at least at the seam coefficient. -/
theorem collar_angular_enorm_sub_le_lintegral {α : ℝ → ℂ} {a b : ℝ} {r : ℝ}
    (hr : 0 < r) (hα : ContDiffOn ℝ 1 α (Icc a b)) (hab : a ≤ b) :
    ‖Real.sinh r * ((α b).im - (α a).im)‖ₑ ≤
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
  have hq : ContDiffOn ℝ 1 (fun t => Real.sinh r * (α t).im) (Icc a b) :=
    contDiffOn_const.mul (Complex.imCLM.contDiff.comp_contDiffOn hα)
  have hsub : Real.sinh r * ((α b).im - (α a).im) =
      Real.sinh r * (α b).im - Real.sinh r * (α a).im := mul_sub _ _ _
  rw [hsub]
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hq hab).trans
  apply lintegral_mono_ae
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
  have hd : DifferentiableAt ℝ α t :=
    ((hα t ⟨ht.1.le, ht.2.le⟩).contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
      one_ne_zero
  have hder : deriv (fun t => Real.sinh r * (α t).im) t =
      Real.sinh r * (deriv α t).im := by
    exact ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).const_mul _).deriv
  rw [hder, ← ofReal_norm, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.sinh_pos_iff.mpr hr)]
  exact ENNReal.ofReal_le_ofReal (sinh_mul_abs_im_le_sqrt_gluingCollarTangentForm hr _ _)

#print axioms abs_re_le_sqrt_gluingCollarTangentForm
#print axioms sinh_mul_abs_im_le_sqrt_gluingCollarTangentForm
#print axioms collar_radial_enorm_sub_le_lintegral
#print axioms collar_angular_enorm_sub_le_lintegral

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The actual native path length is the integral of the concrete chart speed.
Only ordinary C¹ regularity and containment in the actual chart are required. -/
theorem gluedCurve_pathELength_in_chart
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) e.source) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt
        (P.gluingChartTangentForm e (e (γ t)) (deriv (e ∘ γ) t) (deriv (e ∘ γ) t))) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderiv_Ioo, ← restrict_Ioo_eq_restrict_Icc]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hd : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) γ t :=
    (hγ.mdifferentiableOn one_ne_zero t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  dsimp only
  rw [← ofReal_norm, P.gluedCurve_speed_in_chart e he (hmap ⟨ht.1.le, ht.2.le⟩) hd]

/-- On a genuine hyperbolic interior chart the native length is precisely
the Poincare speed integral, using the actual positive imaginary coordinate. -/
theorem gluedCurve_pathELength_interior
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : P.IsGluedInteriorComplexChart e)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) e.source) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    pathELength (modelWithCornersSelf ℝ ℂ) γ a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal (‖deriv (e ∘ γ) t‖ / (e (γ t)).im) := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  rw [P.gluedCurve_pathELength_in_chart e (Or.inl he) hγ hmap]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hp : 0 < (e (γ t)).im :=
    P.gluedInteriorComplexChart_target_im_pos e he (e.map_source (hmap ht))
  dsimp only
  rw [P.gluingChartTangentForm_interior e he, gluingComplexHalfPlaneTangentForm_self,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hp.le]

/-- Signed radial endpoint variation is bounded by the native glued length. -/
theorem gluedCurve_seam_radial_enorm_sub_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) (P.seamAngularComplexChart k θ).source) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖(P.seamAngularComplexChart k θ (γ b)).re -
      (P.seamAngularComplexChart k θ (γ a)).re‖ₑ ≤
      pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  have he : P.seamAngularComplexChart k θ ∈ P.gluedComplexAtlas := Or.inr ⟨k, θ, rfl⟩
  rw [P.gluedCurve_pathELength_in_chart _ he hγ hmap]
  simp_rw [P.gluingChartTangentForm_seam]
  exact collar_radial_enorm_sub_le_lintegral _
    (P.gluedCurve_chart_contDiffOn _ he hγ hmap) hab

/-- Lifted angular endpoint variation is bounded at the seam's own coefficient. -/
theorem gluedCurve_seam_angular_enorm_sub_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {a b : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) (P.seamAngularComplexChart k θ).source) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ‖Real.sinh (gluingRadius C g) *
      ((P.seamAngularComplexChart k θ (γ b)).im -
        (P.seamAngularComplexChart k θ (γ a)).im)‖ₑ ≤
      pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  have he : P.seamAngularComplexChart k θ ∈ P.gluedComplexAtlas := Or.inr ⟨k, θ, rfl⟩
  rw [P.gluedCurve_pathELength_in_chart _ he hγ hmap]
  simp_rw [P.gluingChartTangentForm_seam]
  exact collar_angular_enorm_sub_le_lintegral P.radius_pos
    (P.gluedCurve_chart_contDiffOn _ he hγ hmap) hab

/-- A C¹ collar excursion starting and ending on the seam pays for both
radial legs to any intermediate point. This is an actual length bound,
not a claim that its endpoints have large intrinsic distance. -/
theorem gluedCurve_seam_radial_roundTrip_le_pathELength
    (P : ExerciseGluingPreparation C g n genera X) (k : Fin (n - 1)) (θ : ℝ)
    {γ : ℝ → P.GluedCarrier} {a b c : ℝ}
    (hγ : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 γ (Icc a b))
    (hmap : MapsTo γ (Icc a b) (P.seamAngularComplexChart k θ).source)
    (hac : a ≤ c) (hcb : c ≤ b)
    (ha : (P.seamAngularComplexChart k θ (γ a)).re = 0)
    (hb : (P.seamAngularComplexChart k θ (γ b)).re = 0) :
    letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
      ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
    ENNReal.ofReal (2 * |(P.seamAngularComplexChart k θ (γ c)).re|) ≤
      pathELength (modelWithCornersSelf ℝ ℂ) γ a b := by
  letI : RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) :=
    ⟨P.gluedContinuousRiemannianMetric.toRiemannianMetric⟩
  have hs₁ : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb
  have hs₂ : Icc c b ⊆ Icc a b := Icc_subset_Icc hac le_rfl
  have h₁ := P.gluedCurve_seam_radial_enorm_sub_le_pathELength k θ
    (hγ.mono hs₁) (fun t ht => hmap (hs₁ ht)) hac
  have h₂ := P.gluedCurve_seam_radial_enorm_sub_le_pathELength k θ
    (hγ.mono hs₂) (fun t ht => hmap (hs₂ ht)) hcb
  simp only [ha, sub_zero] at h₁
  simp only [hb, zero_sub, enorm_neg] at h₂
  calc
    ENNReal.ofReal (2 * |(P.seamAngularComplexChart k θ (γ c)).re|) =
        ‖(P.seamAngularComplexChart k θ (γ c)).re‖ₑ +
          ‖(P.seamAngularComplexChart k θ (γ c)).re‖ₑ := by
      rw [two_mul, ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      simp only [← ofReal_norm, Real.norm_eq_abs]
    _ ≤ pathELength (modelWithCornersSelf ℝ ℂ) γ a c +
        pathELength (modelWithCornersSelf ℝ ℂ) γ c b := add_le_add h₁ h₂
    _ = pathELength (modelWithCornersSelf ℝ ℂ) γ a b := pathELength_add hac hcb

#print axioms gluedCurve_pathELength_in_chart
#print axioms gluedCurve_pathELength_interior
#print axioms gluedCurve_seam_radial_enorm_sub_le_pathELength
#print axioms gluedCurve_seam_angular_enorm_sub_le_pathELength
#print axioms gluedCurve_seam_radial_roundTrip_le_pathELength

end ExerciseGluingPreparation

end SystolicGrowth
