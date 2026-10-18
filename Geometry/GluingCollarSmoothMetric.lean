module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarSmoothWarp
public import Geometry.GluingCollarModelMetric

@[expose] public section

/-!
# Genuine length metrics of the smooth collar approximations

The explicit smooth coefficient supplies an actual positive continuous
Riemannian form on the original collar coordinate plane. Pointwise tensor
comparison passes to every speed integral and then to the intrinsic path
distance. All metric instances are explicit and retain the original topology.
-/

open Set Filter Bundle Manifold ContinuousLinearMap MeasureTheory
open scoped Manifold Topology Bundle ENNReal

namespace SystolicGrowth

/-- The explicit multiplicative metric error, independent of the endpoints. -/
noncomputable def gluingCollarSmoothMetricFactor (r ε : ℝ) : ℝ :=
  1 + (Real.cosh r / Real.sinh r) * ε

theorem gluingCollarSmoothMetricFactor_ge_one {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) :
    1 ≤ gluingCollarSmoothMetricFactor r ε := by
  unfold gluingCollarSmoothMetricFactor
  exact le_add_of_nonneg_right (mul_nonneg
    (div_nonneg (Real.cosh_pos r).le (Real.sinh_pos_iff.mpr hr).le) hε)

/-- The native coefficient has a uniform positive lower bound. -/
theorem sinh_le_gluingCollarWarp (r t : ℝ) : Real.sinh r ≤ gluingCollarWarp r t := by
  apply Real.sinh_le_sinh.mpr
  exact le_add_of_nonneg_right (abs_nonneg t)

/-- Literal coefficient comparison for the constructed smoothing. -/
theorem gluingCollarSmoothWarp_multiplicative_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (t : ℝ) :
    gluingCollarWarp r t ≤ gluingCollarSmoothWarp r ε t ∧
      gluingCollarSmoothWarp r ε t ≤
        gluingCollarSmoothMetricFactor r ε * gluingCollarWarp r t := by
  obtain ⟨hlo, hhi⟩ := gluingCollarSmoothWarp_sub_warp_bounds r hε t
  have hs : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have hc : 0 ≤ (Real.cosh r / Real.sinh r) * ε :=
    mul_nonneg (div_nonneg (Real.cosh_pos r).le hs.le) hε
  have hm := mul_le_mul_of_nonneg_left (sinh_le_gluingCollarWarp r t) hc
  have heq : ((Real.cosh r / Real.sinh r) * ε) * Real.sinh r = Real.cosh r * ε := by
    field_simp [hs.ne']
  rw [heq] at hm
  exact ⟨by linarith, by unfold gluingCollarSmoothMetricFactor; nlinarith⟩

/-- The actual smooth collar bilinear form in the unchanged complex chart. -/
noncomputable def gluingComplexCollarSmoothTangentForm (r ε : ℝ) (z : ℂ) :
    ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  Complex.reCLM.smulRight Complex.reCLM +
    (gluingCollarSmoothWarp r ε z.re) ^ 2 • Complex.imCLM.smulRight Complex.imCLM

@[simp] theorem gluingComplexCollarSmoothTangentForm_apply (r ε : ℝ) (z v u : ℂ) :
    gluingComplexCollarSmoothTangentForm r ε z v u =
      v.re * u.re + (gluingCollarSmoothWarp r ε z.re) ^ 2 * v.im * u.im := by
  simp [gluingComplexCollarSmoothTangentForm, mul_assoc]

theorem gluingComplexCollarSmoothTangentForm_symm (r ε : ℝ) (z v u : ℂ) :
    gluingComplexCollarSmoothTangentForm r ε z v u =
      gluingComplexCollarSmoothTangentForm r ε z u v := by
  simp only [gluingComplexCollarSmoothTangentForm_apply]
  ring

theorem gluingComplexCollarSmoothTangentForm_self (r ε : ℝ) (z v : ℂ) :
    gluingComplexCollarSmoothTangentForm r ε z v v =
      v.re ^ 2 + gluingCollarSmoothWarp r ε z.re ^ 2 * v.im ^ 2 := by
  rw [gluingComplexCollarSmoothTangentForm_apply]
  ring

/-- The actual tensors have two-sided quadratic-form comparison. -/
theorem gluingComplexCollarSmoothTangentForm_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (z v : ℂ) :
    gluingComplexCollarTangentForm r z v v ≤ gluingComplexCollarSmoothTangentForm r ε z v v ∧
      gluingComplexCollarSmoothTangentForm r ε z v v ≤
        gluingCollarSmoothMetricFactor r ε ^ 2 * gluingComplexCollarTangentForm r z v v := by
  obtain ⟨hlo, hhi⟩ := gluingCollarSmoothWarp_multiplicative_bounds hr hε z.re
  have hf := (gluingCollarWarp_pos hr z.re).le
  have hF := (gluingCollarSmoothWarp_pos hr ε z.re).le
  have hK := gluingCollarSmoothMetricFactor_ge_one hr hε
  have hKnonneg : 0 ≤ gluingCollarSmoothMetricFactor r ε := by linarith
  have hsqlo : gluingCollarWarp r z.re ^ 2 ≤ gluingCollarSmoothWarp r ε z.re ^ 2 := by
    nlinarith
  have hsqhi : gluingCollarSmoothWarp r ε z.re ^ 2 ≤
      gluingCollarSmoothMetricFactor r ε ^ 2 * gluingCollarWarp r z.re ^ 2 := by
    have h := mul_le_mul hhi hhi hF (mul_nonneg hKnonneg hf)
    nlinarith only [h]
  have hrad := mul_le_mul_of_nonneg_right (show 1 ≤ gluingCollarSmoothMetricFactor r ε ^ 2 by
    nlinarith) (sq_nonneg v.re)
  have hlo' := mul_le_mul_of_nonneg_right hsqlo (sq_nonneg v.im)
  have hhi' := mul_le_mul_of_nonneg_right hsqhi (sq_nonneg v.im)
  rw [gluingComplexCollarTangentForm_apply, gluingCollarTangentForm_self,
    gluingComplexCollarSmoothTangentForm_self]
  constructor <;> nlinarith only [hrad, hlo', hhi']

/-- Square roots of the genuine tangent forms have the corresponding norm
comparison, with the unsquared multiplicative error. -/
theorem gluingComplexCollarSmoothTangentForm_sqrt_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (z v : ℂ) :
    Real.sqrt (gluingComplexCollarTangentForm r z v v) ≤
      Real.sqrt (gluingComplexCollarSmoothTangentForm r ε z v v) ∧
    Real.sqrt (gluingComplexCollarSmoothTangentForm r ε z v v) ≤
      gluingCollarSmoothMetricFactor r ε * Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
  obtain ⟨hlo, hhi⟩ := gluingComplexCollarSmoothTangentForm_bounds hr hε z v
  refine ⟨Real.sqrt_le_sqrt hlo, ?_⟩
  calc
    _ ≤ Real.sqrt (gluingCollarSmoothMetricFactor r ε ^ 2 *
        gluingComplexCollarTangentForm r z v v) := Real.sqrt_le_sqrt hhi
    _ = gluingCollarSmoothMetricFactor r ε * Real.sqrt (gluingComplexCollarTangentForm r z v v) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq
        (zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one hr hε))]

theorem gluingComplexCollarSmoothTangentForm_pos {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (z v : ℂ) (hv : v ≠ 0) :
    0 < gluingComplexCollarSmoothTangentForm r ε z v v :=
  (gluingComplexCollarTangentForm_pos hr z v hv).trans_le
    (gluingComplexCollarSmoothTangentForm_bounds hr hε z v).1

set_option synthInstance.maxHeartbeats 200000 in
theorem gluingComplexCollarSmoothTangentForm_continuous (r : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gluingComplexCollarSmoothTangentForm r ε) := by
  letI : ContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
    @IsTopologicalAddGroup.toContinuousAdd (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) _
      (inferInstanceAs (AddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
      (inferInstanceAs (IsTopologicalAddGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)))
  unfold gluingComplexCollarSmoothTangentForm
  have hw : Continuous (fun z : ℂ => gluingCollarSmoothWarp r ε z.re ^ 2) :=
    (((gluingCollarSmoothWarp_contDiff r hε 2).continuous.comp Complex.continuous_re).pow 2)
  have hform : Continuous (fun _ : ℂ => Complex.imCLM.smulRight Complex.imCLM) :=
    continuous_const
  exact continuous_const.add (hw.smul hform)

set_option backward.isDefEq.respectTransparency false in
/-- The smoothed collar form on the original native tangent fibers. -/
noncomputable def gluingCollarSmoothModelTangentInner (r ε : ℝ) (z : ℂ) :
    TangentSpace (modelWithCornersSelf ℝ ℂ) z →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℂ) z →L[ℝ] ℝ :=
  gluingComplexCollarSmoothTangentForm r ε z

set_option backward.isDefEq.respectTransparency false in
/-- The constructed forms are continuous in the native tangent bundle. -/
theorem gluingCollarSmoothModelTangentForm_continuous_section (r : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun z : ℂ => TotalSpace.mk' (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) z
      (gluingCollarSmoothModelTangentInner r ε z)) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  rw [FiberBundle.continuousAt_section]
  convert (gluingComplexCollarSmoothTangentForm_continuous r hε).continuousAt (x := z₀) using 1
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
    (gluingCollarSmoothModelTangentInner r ε z
      ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z v)
      ((trivializationAt ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ)) z₀).symm z u)) = _
  rw [hs, hs, hl]
  rfl

/-- Actual positive continuous native tangent metric of the smoothed collar. -/
noncomputable def gluingCollarSmoothModelContinuousRiemannianMetric {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    Bundle.ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) where
  inner := gluingCollarSmoothModelTangentInner r ε
  symm := gluingComplexCollarSmoothTangentForm_symm r ε
  pos := gluingComplexCollarSmoothTangentForm_pos hr hε.le
  isVonNBounded z := by
    change Bornology.IsVonNBounded ℝ
      {v : ℂ | gluingComplexCollarSmoothTangentForm r ε z v v < 1}
    apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
    refine ⟨2 * (1 + ((gluingCollarWarp r z.re) ^ 2)⁻¹), fun v hv => ?_⟩
    exact gluingComplexCollarTangentForm_unit_norm_le hr z v
      ((gluingComplexCollarSmoothTangentForm_bounds hr hε.le z v).1.trans_lt hv)
  continuous := gluingCollarSmoothModelTangentForm_continuous_section r hε

/-- Explicit smoothed bundle data; no global instance replaces the usual norm. -/
@[instance_reducible]
noncomputable def gluingCollarSmoothModelRiemannianBundle {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    RiemannianBundle (TangentSpace (modelWithCornersSelf ℝ ℂ) : ℂ → Type) :=
  ⟨(gluingCollarSmoothModelContinuousRiemannianMetric hr hε).toRiemannianMetric⟩

/-- Genuine intrinsic C¹-path distance of the smooth collar. -/
noncomputable def gluingCollarSmoothModelEDist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) : ℝ≥0∞ := by
  letI := gluingCollarSmoothModelRiemannianBundle hr hε
  exact riemannianEDist (modelWithCornersSelf ℝ ℂ) z w

/-- Length computed with the actual smooth tangent metric. -/
noncomputable def gluingCollarSmoothModelPathELength {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ := by
  letI := gluingCollarSmoothModelRiemannianBundle hr hε
  exact pathELength (modelWithCornersSelf ℝ ℂ) α a b

/-- Native extended metric with the unchanged complex topology. -/
@[instance_reducible]
noncomputable def gluingCollarSmoothModelEMetricSpace {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) : EMetricSpace ℂ := by
  letI := gluingCollarSmoothModelRiemannianBundle hr hε
  exact EMetricSpace.ofRiemannianMetric (modelWithCornersSelf ℝ ℂ) ℂ

theorem gluingCollarSmoothModelEMetricSpace_edist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    letI := gluingCollarSmoothModelEMetricSpace hr hε
    edist z w = gluingCollarSmoothModelEDist hr hε z w := rfl

theorem gluingCollarSmoothModelEMetricSpace_topology {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    (gluingCollarSmoothModelEMetricSpace hr hε).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := rfl

/-- Original model connectivity gives finite distances in the smoothed metric. -/
theorem gluingCollarSmoothModelEDist_lt_top {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    gluingCollarSmoothModelEDist hr hε z w < ⊤ := by
  letI := gluingCollarSmoothModelEMetricSpace hr hε
  have hc : IsClopen (Metric.eball z (⊤ : ℝ≥0∞)) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have heq : Metric.eball z (⊤ : ℝ≥0∞) = univ := hc.eq_univ ⟨z, by simp⟩
  have hw : w ∈ Metric.eball z (⊤ : ℝ≥0∞) := heq.symm ▸ mem_univ w
  have hzw : edist z w < ⊤ := by
    simpa only [Metric.mem_eball, edist_comm] using hw
  rw [gluingCollarSmoothModelEMetricSpace_edist] at hzw
  exact hzw

/-- Actual finite smooth collar metric, retaining the original topology. -/
@[instance_reducible]
noncomputable def gluingCollarSmoothModelMetricSpace {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) : MetricSpace ℂ := by
  letI := gluingCollarSmoothModelEMetricSpace hr hε
  exact EMetricSpace.toMetricSpace
    (fun z w => (gluingCollarSmoothModelEDist_lt_top hr hε z w).ne)

theorem gluingCollarSmoothModelMetricSpace_edist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    letI := gluingCollarSmoothModelMetricSpace hr hε
    edist z w = gluingCollarSmoothModelEDist hr hε z w := rfl

theorem gluingCollarSmoothModelMetricSpace_topology {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    (gluingCollarSmoothModelMetricSpace hr hε).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native smooth length is its literal speed integral, even without curve
regularity hypotheses. -/
theorem gluingCollarSmoothModelPathELength_eq_lintegral {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a b : ℝ) :
    gluingCollarSmoothModelPathELength hr hε α a b =
      ∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.sqrt (gluingComplexCollarSmoothTangentForm r ε (α t) (deriv α t) (deriv α t))) := by
  letI := gluingCollarSmoothModelRiemannianBundle hr hε
  unfold gluingCollarSmoothModelPathELength
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t _ht
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1‖ ^ 2 =
      gluingComplexCollarSmoothTangentForm r ε (α t) (deriv α t) (deriv α t) := by
    calc
      _ = inner ℝ
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1)
          (mfderiv (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) α t 1) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = _ := by rw [mfderiv_eq_fderiv]; rfl
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- A genuine within-C¹ curve bounds the constructed smooth distance. -/
theorem gluingCollarSmoothModelEDist_le_pathELength {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) {α : ℝ → ℂ} {a b : ℝ}
    (hα : ContMDiffOn (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℂ) 1 α (Icc a b))
    (hab : a ≤ b) :
    gluingCollarSmoothModelEDist hr hε (α a) (α b) ≤
      gluingCollarSmoothModelPathELength hr hε α a b := by
  letI := gluingCollarSmoothModelRiemannianBundle hr hε
  exact riemannianEDist_le_pathELength hα rfl rfl hab

/-- Two-sided length comparison for every literal speed integral. -/
theorem gluingCollarSmoothModelPathELength_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (α : ℝ → ℂ) (a b : ℝ) :
    gluingCollarModelPathELength hr α a b ≤ gluingCollarSmoothModelPathELength hr hε α a b ∧
    gluingCollarSmoothModelPathELength hr hε α a b ≤
      ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) * gluingCollarModelPathELength hr α a b := by
  rw [gluingCollarModelPathELength_eq_lintegral, gluingCollarSmoothModelPathELength_eq_lintegral]
  have hk : 0 ≤ gluingCollarSmoothMetricFactor r ε :=
    zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one hr hε.le)
  constructor
  · apply lintegral_mono
    intro t
    exact ENNReal.ofReal_le_ofReal
      (gluingComplexCollarSmoothTangentForm_sqrt_bounds hr hε.le (α t) (deriv α t)).1
  · calc
      _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) *
          ENNReal.ofReal (Real.sqrt
            (gluingComplexCollarTangentForm r (α t) (deriv α t) (deriv α t))) := by
        apply lintegral_mono
        intro t
        dsimp only
        rw [← ENNReal.ofReal_mul hk]
        exact ENNReal.ofReal_le_ofReal
          (gluingComplexCollarSmoothTangentForm_sqrt_bounds hr hε.le (α t) (deriv α t)).2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Two-sided comparison of the actual intrinsic distances, obtained from
genuine near-minimizing C¹ curves in each of the constructed metrics. -/
theorem gluingCollarSmoothModelEDist_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    gluingCollarModelEDist hr z w ≤ gluingCollarSmoothModelEDist hr hε z w ∧
    gluingCollarSmoothModelEDist hr hε z w ≤
      ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) * gluingCollarModelEDist hr z w := by
  constructor
  · by_contra h
    have hlt : gluingCollarSmoothModelEDist hr hε z w < gluingCollarModelEDist hr z w :=
      lt_of_not_ge h
    letI := gluingCollarSmoothModelRiemannianBundle hr hε
    change riemannianEDist (modelWithCornersSelf ℝ ℂ) z w < gluingCollarModelEDist hr z w at hlt
    obtain ⟨α, h0, h1, hα, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
    change gluingCollarSmoothModelPathELength hr hε α 0 1 < gluingCollarModelEDist hr z w at hlen
    have hold := gluingCollarModelEDist_le_pathELength hr hα zero_le_one
    rw [h0, h1] at hold
    exact (not_lt_of_ge (hold.trans
      (gluingCollarSmoothModelPathELength_bounds hr hε α 0 1).1)) hlen
  · have hkpos : 0 < gluingCollarSmoothMetricFactor r ε :=
      zero_lt_one.trans_le (gluingCollarSmoothMetricFactor_ge_one hr hε.le)
    have hk0 : ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr hkpos).ne'
    have hkfin : ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) ≠ ⊤ := ENNReal.ofReal_ne_top
    by_contra h
    have hlt : ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) * gluingCollarModelEDist hr z w <
        gluingCollarSmoothModelEDist hr hε z w := lt_of_not_ge h
    have hnear : gluingCollarModelEDist hr z w < gluingCollarSmoothModelEDist hr hε z w /
        ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hk0) (Or.inl hkfin)).mpr
        (by simpa only [mul_comm] using hlt)
    letI := gluingCollarModelRiemannianBundle hr
    change riemannianEDist (modelWithCornersSelf ℝ ℂ) z w <
      gluingCollarSmoothModelEDist hr hε z w / ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε)
      at hnear
    obtain ⟨α, h0, h1, hα, hlen⟩ := exists_lt_of_riemannianEDist_lt hnear
    change gluingCollarModelPathELength hr α 0 1 < gluingCollarSmoothModelEDist hr hε z w /
      ENNReal.ofReal (gluingCollarSmoothMetricFactor r ε) at hlen
    have hnew := gluingCollarSmoothModelEDist_le_pathELength hr hε hα zero_le_one
    rw [h0, h1] at hnew
    have hbound := hnew.trans (gluingCollarSmoothModelPathELength_bounds hr hε α 0 1).2
    have hstrict := ENNReal.mul_lt_mul_right hk0 hkfin hlen
    rw [ENNReal.mul_div_cancel hk0 hkfin] at hstrict
    exact (not_lt_of_ge hbound) hstrict

set_option backward.isDefEq.respectTransparency false in
/-- The finite smooth metric's real distance is the real part of the actual
native Riemannian extended distance. -/
theorem gluingCollarSmoothModelMetricSpace_dist {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    @dist ℂ (gluingCollarSmoothModelMetricSpace hr hε).toDist z w =
      (gluingCollarSmoothModelEDist hr hε z w).toReal := rfl

/-- Two-sided comparison of the actual finite smooth and native metrics on
all endpoints, with the explicit unsquared smoothing factor. -/
theorem gluingCollarSmoothModelDist_bounds {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (z w : ℂ) :
    @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w ≤
      @dist ℂ (gluingCollarSmoothModelMetricSpace hr hε).toDist z w ∧
    @dist ℂ (gluingCollarSmoothModelMetricSpace hr hε).toDist z w ≤
      gluingCollarSmoothMetricFactor r ε * @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w := by
  change (gluingCollarModelEDist hr z w).toReal ≤
      (gluingCollarSmoothModelEDist hr hε z w).toReal ∧
    (gluingCollarSmoothModelEDist hr hε z w).toReal ≤
      gluingCollarSmoothMetricFactor r ε * (gluingCollarModelEDist hr z w).toReal
  obtain ⟨hlo, hhi⟩ := gluingCollarSmoothModelEDist_bounds hr hε z w
  refine ⟨ENNReal.toReal_mono (gluingCollarSmoothModelEDist_lt_top hr hε z w).ne hlo, ?_⟩
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (gluingCollarModelEDist_lt_top hr z w).ne) hhi
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal
    (zero_le_one.trans (gluingCollarSmoothMetricFactor_ge_one hr hε.le))] using h

/-- Uniform metric error on every set of endpoint pairs whose native
distances are bounded. The bound tends to zero linearly in the smoothing
parameter and uses the actual constructed metrics. -/
theorem gluingCollarSmoothModelDist_uniform_bound {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) {R : ℝ} (z w : ℂ)
    (hzw : @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w ≤ R) :
    |@dist ℂ (gluingCollarSmoothModelMetricSpace hr hε).toDist z w -
      @dist ℂ (gluingCollarModelMetricSpace hr).toDist z w| ≤
        (Real.cosh r / Real.sinh r) * ε * R := by
  obtain ⟨hlo, hhi⟩ := gluingCollarSmoothModelDist_bounds hr hε z w
  have hq : 0 ≤ (Real.cosh r / Real.sinh r) * ε :=
    mul_nonneg (div_nonneg (Real.cosh_pos r).le (Real.sinh_pos_iff.mpr hr).le) hε.le
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  have hmul := mul_le_mul_of_nonneg_left hzw hq
  unfold gluingCollarSmoothMetricFactor at hhi
  nlinarith only [hhi, hmul]

#print axioms gluingCollarSmoothModelContinuousRiemannianMetric
#print axioms gluingCollarSmoothModelMetricSpace
#print axioms gluingCollarSmoothModelPathELength_bounds
#print axioms gluingCollarSmoothModelEDist_bounds
#print axioms gluingCollarSmoothModelDist_bounds
#print axioms gluingCollarSmoothModelDist_uniform_bound

end SystolicGrowth
