module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarLocalizedSmoothWarp
public import Geometry.GluingCollarSmoothMetric

@[expose] public section

/-!
# Actual localized smooth collar metrics

The constructed cutoff warp supplies a genuine smooth tangent tensor, equal
exactly to the original tensor outside the seam strip. Its native path metric
retains the original topology and obeys explicit length/distance comparisons.
No ambient metric instance or global surface approximation is assumed.
-/

open Set Filter Bundle Manifold ContinuousLinearMap MeasureTheory
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

variable (b : ContDiffBump (0 : ℝ))

/-- The actual localized coefficient obeys the same explicit multiplicative bound. -/
theorem gluingCollarLocalizedSmoothWarp_multiplicative_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (t : ℝ) :
    gluingCollarWarp r t ≤ gluingCollarLocalizedSmoothWarp r ε b t ∧
      gluingCollarLocalizedSmoothWarp r ε b t ≤
        gluingCollarSmoothMetricFactor r ε * gluingCollarWarp r t := by
  refine ⟨by linarith [(gluingCollarLocalizedSmoothWarp_sub_warp_bounds r hε b t).1], ?_⟩
  exact (gluingCollarLocalizedSmoothWarp_le_smooth r hε b t).trans
    (gluingCollarSmoothWarp_multiplicative_bounds hr hε t).2

/-- The actual smooth collar bilinear form in the unchanged complex chart. -/
noncomputable def gluingComplexCollarLocalizedSmoothTangentForm (r ε : ℝ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight Complex.reCLM +
    (gluingCollarLocalizedSmoothWarp (b := b) r ε z.re) ^ 2 • Complex.imCLM.smulRight Complex.imCLM

@[simp] theorem gluingComplexCollarLocalizedSmoothTangentForm_apply (r ε : ℝ) (z v u : ℂ) :
    gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v u =
      v.re * u.re + (gluingCollarLocalizedSmoothWarp (b := b) r ε z.re) ^ 2 * v.im * u.im := by
  simp [gluingComplexCollarLocalizedSmoothTangentForm, mul_assoc]

theorem gluingComplexCollarLocalizedSmoothTangentForm_symm (r ε : ℝ) (z v u : ℂ) :
    gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v u =
      gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z u v := by
  simp only [gluingComplexCollarLocalizedSmoothTangentForm_apply (b := b)]
  ring

theorem gluingComplexCollarLocalizedSmoothTangentForm_self (r ε : ℝ) (z v : ℂ) :
    gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v =
      v.re ^ 2 + gluingCollarLocalizedSmoothWarp (b := b) r ε z.re ^ 2 * v.im ^ 2 := by
  rw [gluingComplexCollarLocalizedSmoothTangentForm_apply (b := b)]
  ring

/-- Outside the actual cutoff support the entire tangent tensor, not merely
its radial coefficient, is exactly the original tensor. -/
theorem gluingComplexCollarLocalizedSmoothTangentForm_eq_native_of_radius_ge
    (r ε : ℝ) (z : ℂ) (hz : b.rOut ≤ |z.re|) :
    gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z =
      gluingComplexCollarTangentForm r z := by
  ext v u
  rw [gluingComplexCollarLocalizedSmoothTangentForm_apply,
    gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_apply,
    gluingCollarLocalizedSmoothWarp_eq_native r ε b hz]

set_option synthInstance.maxHeartbeats 200000 in
/-- Genuine smoothness in the unchanged real complex-coordinate plane. -/
theorem gluingComplexCollarLocalizedSmoothTangentForm_contDiff (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) (n : ℕ∞) :
    ContDiff ℝ n (gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε) := by
  letI : IsBoundedSMul ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @NormedSpace.toIsBoundedSMul ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _ _
      (inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  unfold gluingComplexCollarLocalizedSmoothTangentForm
  have hw : ContDiff ℝ n
      (fun z : ℂ => gluingCollarLocalizedSmoothWarp (b := b) r ε z.re ^ 2) :=
    ((gluingCollarLocalizedSmoothWarp_contDiff r hε b n).comp Complex.reCLM.contDiff).pow 2
  exact contDiff_const.add (hw.smul contDiff_const)

/-- The actual tensors have two-sided quadratic-form comparison. -/
theorem gluingComplexCollarLocalizedSmoothTangentForm_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (z v : ℂ) :
    gluingComplexCollarTangentForm r z v v ≤ gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v ∧
      gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v ≤
        gluingCollarSmoothMetricFactor r ε ^ 2 * gluingComplexCollarTangentForm r z v v := by
  obtain ⟨hlo, hhi⟩ := gluingCollarLocalizedSmoothWarp_multiplicative_bounds (b := b) hr hε z.re
  have hf := (gluingCollarWarp_pos hr z.re).le
  have hF := (gluingCollarLocalizedSmoothWarp_pos hr hε b z.re).le
  have hK := gluingCollarSmoothMetricFactor_ge_one hr hε
  have hKnonneg : 0 ≤ gluingCollarSmoothMetricFactor r ε := by linarith
  have hsqlo : gluingCollarWarp r z.re ^ 2 ≤ gluingCollarLocalizedSmoothWarp (b := b) r ε z.re ^ 2 := by
    nlinarith
  have hsqhi : gluingCollarLocalizedSmoothWarp (b := b) r ε z.re ^ 2 ≤
      gluingCollarSmoothMetricFactor r ε ^ 2 * gluingCollarWarp r z.re ^ 2 := by
    have h := mul_le_mul hhi hhi hF (mul_nonneg hKnonneg hf)
    nlinarith only [h]
  have hrad := mul_le_mul_of_nonneg_right (show 1 ≤ gluingCollarSmoothMetricFactor r ε ^ 2 by
    nlinarith) (sq_nonneg v.re)
  have hlo' := mul_le_mul_of_nonneg_right hsqlo (sq_nonneg v.im)
  have hhi' := mul_le_mul_of_nonneg_right hsqhi (sq_nonneg v.im)
  rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self,
    gluingComplexCollarLocalizedSmoothTangentForm_self (b := b)]
  constructor <;> nlinarith only [hrad, hlo', hhi']

/-- Square roots of the genuine tangent forms have the corresponding norm
comparison, with the unsquared multiplicative error. -/
theorem gluingComplexCollarLocalizedSmoothTangentForm_sqrt_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (z v : ℂ) :
    Real.sqrt (gluingComplexCollarTangentForm r z v v) ≤
      Real.sqrt (gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v) ∧
    Real.sqrt (gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v) ≤
      gluingCollarSmoothMetricFactor r ε * Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
  obtain ⟨hlo, hhi⟩ := gluingComplexCollarLocalizedSmoothTangentForm_bounds (b := b) hr hε z v
  refine ⟨Real.sqrt_le_sqrt hlo, ?_⟩
  calc
    _ ≤ Real.sqrt (gluingCollarSmoothMetricFactor r ε ^ 2 *
        gluingComplexCollarTangentForm r z v v) := Real.sqrt_le_sqrt hhi
    _ = gluingCollarSmoothMetricFactor r ε * Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
        (zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one hr hε))]

theorem gluingComplexCollarLocalizedSmoothTangentForm_pos {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (z v : ℂ) (hv : v ≠ 0) :
    0 < gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v :=
  (gluingComplexCollarTangentForm_pos hr z v hv).trans_le
    (gluingComplexCollarLocalizedSmoothTangentForm_bounds (b := b) hr hε z v).1

set_option synthInstance.maxHeartbeats 200000 in
theorem gluingComplexCollarLocalizedSmoothTangentForm_continuous (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε) := by
  letI : ContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _
      (inferInstanceAs (AddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
      (inferInstanceAs (IsTopologicalAddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  unfold gluingComplexCollarLocalizedSmoothTangentForm
  have hw : Continuous (fun z : ℂ => gluingCollarLocalizedSmoothWarp (b := b) r ε z.re ^ 2) :=
    (((gluingCollarLocalizedSmoothWarp_contDiff (b := b) r hε 2).continuous.comp Complex.continuous_re).pow 2)
  have hform : Continuous (fun _ : ℂ => Complex.imCLM.smulRight Complex.imCLM) :=
    continuous_const
  exact continuous_const.add (hw.smul hform)

set_option backward.isDefEq.respectTransparency false in
/-- The smoothed collar form on the original native tangent fibers. -/
noncomputable def gluingCollarLocalizedSmoothModelTangentInner (r ε : ℝ) (z : ℂ) :
    TangentSpace (modelWithCornersSelf ℝ ℂ) z →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) z →L[ℝ] ℝ :=
  gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z

set_option backward.isDefEq.respectTransparency false in
/-- The constructed forms are continuous in the native tangent bundle. -/
theorem gluingCollarLocalizedSmoothModelTangentForm_continuous_section (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun z : ℂ => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) z
      (gluingCollarLocalizedSmoothModelTangentInner (b := b) r ε z)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [FiberBundle.continuousAt_section]
  convert (gluingComplexCollarLocalizedSmoothTangentForm_continuous (b := b) r hε).continuousAt (x := z₀) using 1
  funext z
  rw [hom_trivializationAt_apply]
  ext v u
  rw [inCoordinates_apply_eq₂ (by simp) (by simp) (mem_univ _)]
  have hs (w : ℂ) :
      (trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z w = w := by
    exact ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symmL_apply
      (by simp) w).symm.trans (by rw [TangentBundle.symmL_model_space]; rfl)
  have hl (a : ℝ) :
      (trivializationAt ℝ (fun _ : ℂ => ℝ) z₀).linearMapAt ℝ z a = a := by
    change (Bundle.Trivial.trivialization ℂ ℝ).linearMapAt ℝ z a = a
    rw [Bundle.Trivial.linearMapAt_trivialization]
    rfl
  change (trivializationAt ℝ (fun _ : ℂ => ℝ) z₀).linearMapAt ℝ z
    (gluingCollarLocalizedSmoothModelTangentInner (b := b) r ε z
      ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z v)
      ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z u)) = _
  rw [hs, hs, hl]
  rfl

/-- Actual positive continuous native tangent metric of the smoothed collar. -/
noncomputable def gluingCollarLocalizedSmoothModelContinuousRiemannianMetric {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    Bundle.ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) where
  inner := gluingCollarLocalizedSmoothModelTangentInner (b := b) r ε
  symm := gluingComplexCollarLocalizedSmoothTangentForm_symm (b := b) r ε
  pos := gluingComplexCollarLocalizedSmoothTangentForm_pos (b := b) hr hε.le
  isVonNBounded z := by
    change Bornology.IsVonNBounded ℝ
      {v : ℂ | gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε z v v < 1}
    apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
    refine ⟨2 * (1 + ((gluingCollarWarp r z.re) ^ 2)⁻¹), fun v hv => ?_⟩
    exact gluingComplexCollarTangentForm_unit_norm_le hr z v
      ((gluingComplexCollarLocalizedSmoothTangentForm_bounds (b := b) hr hε.le z v).1.trans_lt hv)
  continuous := gluingCollarLocalizedSmoothModelTangentForm_continuous_section (b := b) r hε

/-- Explicit smoothed bundle data; no global instance replaces the usual norm. -/
@[instance_reducible]
noncomputable def gluingCollarLocalizedSmoothModelRiemannianBundle {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
  ⟨(gluingCollarLocalizedSmoothModelContinuousRiemannianMetric (b := b) hr hε).toRiemannianMetric⟩

/-- Genuine intrinsic C¹-path distance of the smooth collar. -/
noncomputable def gluingCollarLocalizedSmoothModelEDist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) : ℝ≥0∞ := by
  letI := gluingCollarLocalizedSmoothModelRiemannianBundle (b := b) hr hε
  exact riemannianEDist (modelWithCornersSelf ℝ ℂ) z w

/-- Length computed with the actual smooth tangent metric. -/
noncomputable def gluingCollarLocalizedSmoothModelPathELength {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a c : ℝ) : ℝ≥0∞ := by
  letI := gluingCollarLocalizedSmoothModelRiemannianBundle (b := b) hr hε
  exact pathELength (modelWithCornersSelf ℝ ℂ) α a c

/-- Native extended metric with the unchanged complex topology. -/
@[instance_reducible]
noncomputable def gluingCollarLocalizedSmoothModelEMetricSpace {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) : EMetricSpace ℂ := by
  letI := gluingCollarLocalizedSmoothModelRiemannianBundle (b := b) hr hε
  exact EMetricSpace.ofRiemannianMetric (modelWithCornersSelf ℝ ℂ) ℂ

theorem gluingCollarLocalizedSmoothModelEMetricSpace_edist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    letI := gluingCollarLocalizedSmoothModelEMetricSpace (b := b) hr hε
    edist z w = gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w := rfl

theorem gluingCollarLocalizedSmoothModelEMetricSpace_topology {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    (gluingCollarLocalizedSmoothModelEMetricSpace (b := b) hr hε).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := rfl

/-- Original model connectivity gives finite distances in the smoothed metric. -/
theorem gluingCollarLocalizedSmoothModelEDist_lt_top {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w < ⊤ := by
  letI := gluingCollarLocalizedSmoothModelEMetricSpace (b := b) hr hε
  have hc : IsClopen (Metric.eball z (⊤ : ℝ≥0∞)) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have heq : Metric.eball z (⊤ : ℝ≥0∞) = univ := hc.eq_univ ⟨z, by simp⟩
  have hw : w ∈ Metric.eball z (⊤ : ℝ≥0∞) := heq.symm ▸ mem_univ w
  have hzw : edist z w < ⊤ := by
    simpa only [Metric.mem_eball, edist_comm] using hw
  rw [gluingCollarLocalizedSmoothModelEMetricSpace_edist (b := b)] at hzw
  exact hzw

/-- Actual finite smooth collar metric, retaining the original topology. -/
@[instance_reducible]
noncomputable def gluingCollarLocalizedSmoothModelMetricSpace {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) : MetricSpace ℂ := by
  letI := gluingCollarLocalizedSmoothModelEMetricSpace (b := b) hr hε
  exact EMetricSpace.toMetricSpace
    (fun z w => (gluingCollarLocalizedSmoothModelEDist_lt_top (b := b) hr hε z w).ne)

theorem gluingCollarLocalizedSmoothModelMetricSpace_edist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    letI := gluingCollarLocalizedSmoothModelMetricSpace (b := b) hr hε
    edist z w = gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w := rfl

theorem gluingCollarLocalizedSmoothModelMetricSpace_topology {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    (gluingCollarLocalizedSmoothModelMetricSpace (b := b) hr hε).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native smooth length is its literal speed integral, even without curve
regularity hypotheses. -/
theorem gluingCollarLocalizedSmoothModelPathELength_eq_lintegral {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a c : ℝ) :
    gluingCollarLocalizedSmoothModelPathELength (b := b) hr hε α a c =
      ∫⁻ t in Icc a c, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε (α t) (deriv α t) (deriv α t))) := by
  letI := gluingCollarLocalizedSmoothModelRiemannianBundle (b := b) hr hε
  unfold gluingCollarLocalizedSmoothModelPathELength
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1‖ ^ 2 =
      gluingComplexCollarLocalizedSmoothTangentForm (b := b) r ε (α t) (deriv α t) (deriv α t) := by
    calc
      _ = inner ℝ
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1)
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = _ := by rw [mfderiv_eq_fderiv]; rfl
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- A curve that remains outside the cutoff strip has literally unchanged
length. No equality of arbitrary distances outside the strip is asserted. -/
theorem gluingCollarLocalizedSmoothModelPathELength_eq_native_of_radius_ge {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a c : ℝ)
    (hα : ∀ t ∈ Icc a c, b.rOut ≤ |(α t).re|) :
    gluingCollarLocalizedSmoothModelPathELength (b := b) hr hε α a c =
      gluingCollarModelPathELength hr α a c := by
  rw [gluingCollarLocalizedSmoothModelPathELength_eq_lintegral,
    gluingCollarModelPathELength_eq_lintegral]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [gluingComplexCollarLocalizedSmoothTangentForm_eq_native_of_radius_ge
    (b := b) r ε (α t) (hα t ht)]

/-- A genuine within-C¹ curve bounds the constructed smooth distance. -/
theorem gluingCollarLocalizedSmoothModelEDist_le_pathELength {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) {α : ℝ → ℂ} {a c : ℝ}
    (hα : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 α (Icc a c))
    (hac : a ≤ c) :
    gluingCollarLocalizedSmoothModelEDist (b := b) hr hε (α a) (α c) ≤
      gluingCollarLocalizedSmoothModelPathELength (b := b) hr hε α a c := by
  letI := gluingCollarLocalizedSmoothModelRiemannianBundle (b := b) hr hε
  exact riemannianEDist_le_pathELength hα rfl rfl hac

/-- Two-sided length comparison for every literal speed integral. -/
theorem gluingCollarLocalizedSmoothModelPathELength_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a c : ℝ) :
    gluingCollarModelPathELength hr α a c ≤ gluingCollarLocalizedSmoothModelPathELength (b := b) hr hε α a c ∧
    gluingCollarLocalizedSmoothModelPathELength (b := b) hr hε α a c ≤
      ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) * gluingCollarModelPathELength hr α a c := by
  rw [gluingCollarModelPathELength_eq_lintegral, gluingCollarLocalizedSmoothModelPathELength_eq_lintegral (b := b)]
  have hk : 0 ≤ gluingCollarSmoothMetricFactor r ε :=
    zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one hr hε.le)
  constructor
  · apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal
      (gluingComplexCollarLocalizedSmoothTangentForm_sqrt_bounds (b := b) hr hε.le (α t) (deriv α t)).1
  · calc
      _ ≤ ∫⁻ t in Icc a c, ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) *
          ENNReal.ofReal (Real.sqrt
            (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
        apply lintegral_mono
        intro t
        dsimp only
        rw [← ENNReal.ofReal_mul hk]
        exact ENNReal.ofReal_le_ofReal
          (gluingComplexCollarLocalizedSmoothTangentForm_sqrt_bounds (b := b) hr hε.le (α t) (deriv α t)).2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Two-sided comparison of the actual intrinsic distances, obtained from
genuine near-minimizing C¹ curves in each of the constructed metrics. -/
theorem gluingCollarLocalizedSmoothModelEDist_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    gluingCollarModelEDist hr z w ≤ gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w ∧
    gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w ≤
      ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) * gluingCollarModelEDist hr z w := by
  constructor
  · by_contra h
    have hlt : gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w < gluingCollarModelEDist hr z w :=
      lt_of_not_ge h
    letI := gluingCollarLocalizedSmoothModelRiemannianBundle (b := b) hr hε
    change riemannianEDist (modelWithCornersSelf ℝ ℂ) z w < gluingCollarModelEDist hr z w at hlt
    obtain ⟨α, h0, h1, hα, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
    change gluingCollarLocalizedSmoothModelPathELength (b := b) hr hε α 0 1 < gluingCollarModelEDist hr z w at hlen
    have hold := gluingCollarModelEDist_le_pathELength hr hα zero_le_one
    rw [h0, h1] at hold
    exact (not_lt_of_ge (hold.trans
      (gluingCollarLocalizedSmoothModelPathELength_bounds (b := b) hr hε α 0 1).1)) hlen
  · have hkpos : 0 < gluingCollarSmoothMetricFactor r ε :=
      zero_lt_one.trans_le (gluingCollarSmoothMetricFactor_ge_one hr hε.le)
    have hk0 : ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hkpos).ne'
    have hkfin : ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) ≠ ⊤ := ENNReal.ofReal_ne_top
    by_contra h
    have hlt : ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) * gluingCollarModelEDist hr z w <
        gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w := lt_of_not_ge h
    have hnear : gluingCollarModelEDist hr z w < gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w /
        ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hk0) (Or.inl hkfin)).mpr
        (by simpa only [mul_comm] using hlt)
    letI := gluingCollarModelRiemannianBundle hr
    change riemannianEDist (modelWithCornersSelf ℝ ℂ) z w <
      gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w / ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε)
      at hnear
    obtain ⟨α, h0, h1, hα, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
    change gluingCollarModelPathELength hr α 0 1 < gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w /
      ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) at hlen
    have hnew := gluingCollarLocalizedSmoothModelEDist_le_pathELength (b := b) hr hε hα zero_le_one
    rw [h0, h1] at hnew
    have hbound := hnew.trans (gluingCollarLocalizedSmoothModelPathELength_bounds (b := b) hr hε α 0 1).2
    have hstrict := ENNReal.mul_lt_mul_right hk0 hkfin hlen
    rw [ENNReal.mul_div_cancel hk0 hkfin] at hstrict
    exact (not_lt_of_ge hbound) hstrict

set_option backward.isDefEq.respectTransparency false in
/-- The finite smooth metric's real distance is the real part of the actual
native Riemannian extended distance. -/
theorem gluingCollarLocalizedSmoothModelMetricSpace_dist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    @dist ℂ (gluingCollarLocalizedSmoothModelMetricSpace (b := b) hr hε).toDist z w =
      (gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w).toReal := rfl

/-- Two-sided comparison of the actual finite smooth and native metrics on
all endpoints, with the explicit unsquared smoothing factor. -/
theorem gluingCollarLocalizedSmoothModelDist_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w ≤
      @dist ℂ (gluingCollarLocalizedSmoothModelMetricSpace (b := b) hr hε).toDist z w ∧
    @dist ℂ (gluingCollarLocalizedSmoothModelMetricSpace (b := b) hr hε).toDist z w ≤
      gluingCollarSmoothMetricFactor r ε * @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w := by
  change (gluingCollarModelEDist hr z w).toReal ≤
      (gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w).toReal ∧
    (gluingCollarLocalizedSmoothModelEDist (b := b) hr hε z w).toReal ≤
      gluingCollarSmoothMetricFactor r ε * (gluingCollarModelEDist hr z w).toReal
  obtain ⟨hlo, hhi⟩ := gluingCollarLocalizedSmoothModelEDist_bounds (b := b) hr hε z w
  refine ⟨ENNReal.toReal_mono (gluingCollarLocalizedSmoothModelEDist_lt_top (b := b) hr hε z w).ne hlo, ?_⟩
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (gluingCollarModelEDist_lt_top hr z w).ne) hhi
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one hr hε.le))] using h

/-- Uniform metric error on every set of endpoint pairs whose native
distances are bounded. The bound tends to zero linearly in the smoothing
parameter and uses the actual constructed metrics. -/
theorem gluingCollarLocalizedSmoothModelDist_uniform_bound {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) {R : ℝ} (z w : ℂ)
    (hzw : @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w ≤ R) :
    |@dist ℂ (gluingCollarLocalizedSmoothModelMetricSpace (b := b) hr hε).toDist z w -
      @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w| ≤
        (Real.cosh r / Real.sinh r) * ε * R := by
  obtain ⟨hlo, hhi⟩ := gluingCollarLocalizedSmoothModelDist_bounds (b := b) hr hε z w
  have hq : 0 ≤ (Real.cosh r / Real.sinh r) * ε :=
    mul_nonneg (div_nonneg (Real.cosh_pos r).le (Real.sinh_pos_iff.mpr hr).le) hε.le
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hmul := mul_le_mul_of_nonneg_left hzw hq
  unfold gluingCollarSmoothMetricFactor at hhi
  nlinarith only [hhi, hmul]

#print axioms gluingCollarLocalizedSmoothModelContinuousRiemannianMetric
#print axioms gluingComplexCollarLocalizedSmoothTangentForm_contDiff
#print axioms gluingComplexCollarLocalizedSmoothTangentForm_eq_native_of_radius_ge
#print axioms gluingCollarLocalizedSmoothModelPathELength_eq_native_of_radius_ge
#print axioms gluingCollarLocalizedSmoothModelMetricSpace
#print axioms gluingCollarLocalizedSmoothModelPathELength_bounds
#print axioms gluingCollarLocalizedSmoothModelEDist_bounds
#print axioms gluingCollarLocalizedSmoothModelDist_bounds
#print axioms gluingCollarLocalizedSmoothModelDist_uniform_bound

end SystolicGrowth
