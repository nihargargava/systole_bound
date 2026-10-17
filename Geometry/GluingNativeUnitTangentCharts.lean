module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingRiemannianMetric
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Normalize

@[expose] public section

/-!
# Circle coordinates on the actual native unit tangent bundle

The radial normalization uses the native chart tensor, including its nonsmooth
seam coefficient. All fiber maps use the genuine native tangent trivialization.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology

set_option backward.isDefEq.respectTransparency false

namespace SystolicGrowth

noncomputable def Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) : ℂ :=
  (Real.sqrt (B a a))⁻¹ • a

theorem Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit_self
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) (ha : 0 < B a a) :
    B (Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit B a) (Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit B a) = 1 := by
  have hs : Real.sqrt (B a a) ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  simp only [Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit, map_smul, smul_apply, smul_eq_mul]
  have hsq := Real.sq_sqrt ha.le
  field_simp
  nlinarith

private theorem bilinearRadialUnit_smul_pos
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ)
    {r : ℝ} (hr : 0 < r) :
    Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit B (r • a) = Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit B a := by
  have heq : B (r • a) (r • a) = r ^ 2 * B a a := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  simp only [Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit, heq, Real.sqrt_mul (sq_nonneg r),
    Real.sqrt_sq_eq_abs, abs_of_pos hr, mul_inv, smul_smul]
  congr 1
  rw [mul_right_comm, inv_mul_cancel₀ hr.ne', one_mul]

theorem Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit_normalize
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (v : ℂ) (hv : B v v = 1) :
    Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit B (NormedSpace.normalize v) = v := by
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  rw [NormedSpace.normalize,
    bilinearRadialUnit_smul_pos B v
      (inv_pos.2 (norm_pos_iff.2 hv0))]
  simp [Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit, hv]

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- The true native unit tangent bundle, with the inherited total-space topology. -/
abbrev NativeUnitTangentCarrier
    (P : ExerciseGluingPreparation C g n genera X) :=
  {v : TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) //
    P.gluedTangentInner v.proj v.snd v.snd = 1}

/-- The true unit fiber of the native metric at a basepoint. -/
abbrev NativeUnitTangentFiber
    (P : ExerciseGluingPreparation C g n genera X) (b : P.GluedCarrier) :=
  {v : TangentSpace (modelWithCornersSelf ℝ ℂ) b // P.gluedTangentInner b v v = 1}

/-- Normalize a coordinate-circle direction by the actual chart tensor and
apply the inverse genuine native tangent trivialization. -/
noncomputable def nativeUnitTangentParam
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (a : Circle) :
    P.NativeUnitTangentFiber b := by
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  refine ⟨t.symmL ℝ b (Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit (P.gluingChartTangentForm e (e b)) a), ?_⟩
  rw [P.gluedTangentInner_in_chart e he b hb]
  exact Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit_self _ a
    (P.gluingChartTangentForm_pos e (e.map_source hb) a a.coe_ne_zero)

/-- The literal coordinate vector of a true native unit tangent. -/
noncomputable def nativeUnitTangentCoord
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (v : P.NativeUnitTangentFiber b) : ℂ :=
  ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).continuousLinearMapAt ℝ b v.val

theorem nativeUnitTangentCoord_self
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : P.NativeUnitTangentFiber b) :
    P.gluingChartTangentForm e (e b) (P.nativeUnitTangentCoord e he b v)
      (P.nativeUnitTangentCoord e he b v) = 1 := by
  rw [← P.gluedTangentInner_in_chart e he b hb]
  unfold nativeUnitTangentCoord
  rw [Trivialization.symmL_continuousLinearMapAt
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)) (by exact hb)]
  exact v.property

theorem nativeUnitTangentCoord_ne_zero
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : P.NativeUnitTangentFiber b) :
    P.nativeUnitTangentCoord e he b v ≠ 0 := by
  intro h
  have hu := P.nativeUnitTangentCoord_self e he b hb v
  simp [h] at hu

/-- The Euclidean direction of the true native tangent coordinate. -/
noncomputable def nativeUnitTangentAngle
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : P.NativeUnitTangentFiber b) : Circle :=
  ⟨NormedSpace.normalize (P.nativeUnitTangentCoord e he b v),
    mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize
      (P.nativeUnitTangentCoord_ne_zero e he b hb v))⟩

@[simp] theorem nativeUnitTangentCoord_param
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (a : Circle) :
    P.nativeUnitTangentCoord e he b (P.nativeUnitTangentParam e he b hb a) =
      (Real.sqrt (P.gluingChartTangentForm e (e b) a a))⁻¹ • (a : ℂ) := by
  unfold nativeUnitTangentCoord nativeUnitTangentParam
  rw [Trivialization.continuousLinearMapAt_symmL _ (by exact hb)]
  rfl

@[simp] theorem nativeUnitTangentAngle_param
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (a : Circle) :
    P.nativeUnitTangentAngle e he b hb (P.nativeUnitTangentParam e he b hb a) = a := by
  apply Subtype.ext
  change NormedSpace.normalize (P.nativeUnitTangentCoord e he b
    (P.nativeUnitTangentParam e he b hb a)) = (a : ℂ)
  rw [P.nativeUnitTangentCoord_param,
    NormedSpace.normalize_smul_of_pos (inv_pos.2 (Real.sqrt_pos.2
      (P.gluingChartTangentForm_pos e (e.map_source hb) a a.coe_ne_zero)))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one a.norm_coe

@[simp] theorem nativeUnitTangentParam_angle
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : P.NativeUnitTangentFiber b) :
    P.nativeUnitTangentParam e he b hb (P.nativeUnitTangentAngle e he b hb v) = v := by
  apply Subtype.ext
  change ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b
      (Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit (P.gluingChartTangentForm e (e b))
        (NormedSpace.normalize (P.nativeUnitTangentCoord e he b v))) = v.val
  rw [Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit_normalize _ _ (P.nativeUnitTangentCoord_self e he b hb v)]
  exact Trivialization.symmL_continuousLinearMapAt _ (by exact hb) v.val

theorem nativeUnitTangentParam_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) :
    Continuous (P.nativeUnitTangentParam e he b hb) := by
  apply Continuous.subtype_mk
  apply Continuous.comp (ContinuousLinearMap.continuous _)
  have hB : Continuous (fun a : Circle => P.gluingChartTangentForm e (e b) a a) :=
    ((P.gluingChartTangentForm e (e b)).continuous.comp continuous_subtype_val).clm_apply
      continuous_subtype_val
  exact ((Real.continuous_sqrt.comp hB).inv₀ (fun a =>
    (Real.sqrt_pos.2 (P.gluingChartTangentForm_pos e (e.map_source hb) a
      a.coe_ne_zero)).ne')).smul continuous_subtype_val

theorem nativeUnitTangentAngle_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) :
    Continuous (P.nativeUnitTangentAngle e he b hb) := by
  apply Continuous.subtype_mk
  have hv : Continuous (P.nativeUnitTangentCoord e he b) :=
    (ContinuousLinearMap.continuous _).comp continuous_subtype_val
  exact (hv.norm.inv₀ (fun v =>
    (norm_pos_iff.2 (P.nativeUnitTangentCoord_ne_zero e he b hb v)).ne')).smul hv

/-- A genuine homeomorphism from the coordinate circle to the true native
unit fiber, constructed from its actual positive chart tensor. -/
noncomputable def nativeUnitTangentFiberHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) : Circle ≃ₜ P.NativeUnitTangentFiber b where
  toFun := P.nativeUnitTangentParam e he b hb
  invFun := P.nativeUnitTangentAngle e he b hb
  left_inv := P.nativeUnitTangentAngle_param e he b hb
  right_inv := P.nativeUnitTangentParam_angle e he b hb
  continuous_toFun := P.nativeUnitTangentParam_continuous e he b hb
  continuous_invFun := P.nativeUnitTangentAngle_continuous e he b hb

/-- On every actual overlap, the coordinate maps of the native tangent
bundle use the true derivative of the literal chart transition. -/
theorem nativeTangentCoordChange_apply
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (hb' : b ∈ e'.source) (a : ℂ) :
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e', he'⟩ : atlas ℂ P.GluedCarrier)).continuousLinearMapAt ℝ b
      (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
        (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b a) =
      fderiv ℝ (e.symm.trans e') (e b) a := by
  let Z := tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier
  let i : atlas ℂ P.GluedCarrier := ⟨e, he⟩
  let j : atlas ℂ P.GluedCarrier := ⟨e', he'⟩
  change (Z.localTriv j).continuousLinearMapAt ℝ b ((Z.localTriv i).symmL ℝ b a) = _
  rw [Z.localTriv_continuousLinearMapAt (by exact hb'),
    Z.localTriv_symmL (by exact hb)]
  exact (Z.coordChange_comp i (Z.indexAt b) j b
    ⟨⟨hb, Z.mem_baseSet_at b⟩, hb'⟩ a).trans
    (congrArg (fun f : ℂ →L[ℝ] ℂ => f a) (P.gluedTangentCoordChange_eq_fderiv i j b))

theorem nativeUnitTangentCoord_change
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (hb' : b ∈ e'.source)
    (v : P.NativeUnitTangentFiber b) :
    P.nativeUnitTangentCoord e' he' b v =
      fderiv ℝ (e.symm.trans e') (e b) (P.nativeUnitTangentCoord e he b v) := by
  have h := P.nativeTangentCoordChange_apply e e' he he' b hb hb'
    (P.nativeUnitTangentCoord e he b v)
  unfold nativeUnitTangentCoord at h ⊢
  rw [Trivialization.symmL_continuousLinearMapAt
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)) (by exact hb)] at h
  exact h

/-- The actual circle-coordinate transition is normalization of the
true native derivative; the old chart's metric normalization cancels. -/
theorem nativeUnitTangentAngle_transition
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (hb' : b ∈ e'.source) (a : Circle) :
    (P.nativeUnitTangentAngle e' he' b hb'
      (P.nativeUnitTangentParam e he b hb a) : ℂ) =
      NormedSpace.normalize (fderiv ℝ (e.symm.trans e') (e b) a) := by
  change NormedSpace.normalize (P.nativeUnitTangentCoord e' he' b
    (P.nativeUnitTangentParam e he b hb a)) = _
  rw [P.nativeUnitTangentCoord_change e e' he he' b hb hb',
    P.nativeUnitTangentCoord_param, map_smul]
  exact NormedSpace.normalize_smul_of_pos (inv_pos.2 (Real.sqrt_pos.2
    (P.gluingChartTangentForm_pos e (e.map_source hb) a a.coe_ne_zero))) _

/-- The true native unit tangent bundle restricted to a chart's source. -/
abbrev NativeUnitTangentOver
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) :=
  {v : P.NativeUnitTangentCarrier // v.val.proj ∈ e.source}

/-- The actual bundle chart inverse, retaining the original total-space topology. -/
noncomputable def nativeUnitTangentOverParam
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (q : e.source × Circle) : P.NativeUnitTangentOver e :=
  ⟨⟨⟨q.1.val, (P.nativeUnitTangentParam e he q.1.val q.1.property q.2).val⟩,
    (P.nativeUnitTangentParam e he q.1.val q.1.property q.2).property⟩, q.1.property⟩

/-- The actual bundle chart, reading the genuine native tangent coordinate. -/
noncomputable def nativeUnitTangentOverAngle
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (v : P.NativeUnitTangentOver e) : e.source × Circle :=
  (⟨v.val.val.proj, v.property⟩,
    P.nativeUnitTangentAngle e he v.val.val.proj v.property
      ⟨v.val.val.snd, v.val.property⟩)

@[simp] theorem nativeUnitTangentOverAngle_param
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (q : e.source × Circle) :
    P.nativeUnitTangentOverAngle e he (P.nativeUnitTangentOverParam e he q) = q := by
  apply Prod.ext
  · rfl
  · exact P.nativeUnitTangentAngle_param e he q.1.val q.1.property q.2

@[simp] theorem nativeUnitTangentOverParam_angle
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (v : P.NativeUnitTangentOver e) :
    P.nativeUnitTangentOverParam e he (P.nativeUnitTangentOverAngle e he v) = v := by
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg Subtype.val (P.nativeUnitTangentParam_angle e he
    v.val.val.proj v.property ⟨v.val.val.snd, v.val.property⟩)
  exact congrArg (TotalSpace.mk v.val.val.proj) h

theorem nativeUnitTangentOverParam_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas) :
    Continuous (P.nativeUnitTangentOverParam e he) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  have hb : Continuous (fun q : e.source × Circle => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have ha : Continuous (fun q : e.source × Circle => (q.2 : ℂ)) :=
    continuous_subtype_val.comp continuous_snd
  have hB : Continuous (fun q : e.source × Circle =>
      P.gluingChartTangentForm e (e q.1.val)) :=
    (P.gluingChartTangentForm_continuousOn e).comp_continuous
      (e.continuousOn.comp_continuous hb (fun q => q.1.property))
      (fun q => e.map_source q.1.property)
  have hself : Continuous (fun q : e.source × Circle =>
      P.gluingChartTangentForm e (e q.1.val) q.2 q.2) :=
    (hB.clm_apply ha).clm_apply ha
  have hn : Continuous (fun q : e.source × Circle =>
      Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit (P.gluingChartTangentForm e (e q.1.val)) q.2) :=
    ((Real.continuous_sqrt.comp hself).inv₀ (fun q =>
      (Real.sqrt_pos.2 (P.gluingChartTangentForm_pos e (e.map_source q.1.property)
        q.2 q.2.coe_ne_zero)).ne')).smul ha
  have hc := t.continuousOn_symm.comp_continuous (hb.prodMk hn)
    (fun q => show (q.1.val, Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit
      (P.gluingChartTangentForm e (e q.1.val)) q.2) ∈ t.target from
        ⟨q.1.property, mem_univ _⟩)
  apply hc.congr
  intro q
  change TotalSpace.mk q.1.val (t.symm q.1.val (Internal.GluingNativeUnitTangentChartsHelpers.bilinearRadialUnit
    (P.gluingChartTangentForm e (e q.1.val)) q.2)) = _
  change TotalSpace.mk q.1.val (t.symm q.1.val _) = TotalSpace.mk q.1.val (t.symmL ℝ q.1.val _)
  rw [t.symmL_apply q.1.property]

theorem nativeUnitTangentOverAngle_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas) :
    Continuous (P.nativeUnitTangentOverAngle e he) := by
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  have hv : Continuous (fun v : P.NativeUnitTangentOver e => v.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have ht := t.continuousOn.comp_continuous hv (fun v => show v.val.val ∈ t.source
    from v.property)
  have hcoord : Continuous (fun v : P.NativeUnitTangentOver e =>
      P.nativeUnitTangentCoord e he v.val.val.proj ⟨v.val.val.snd, v.val.property⟩) := by
    apply ht.snd.congr
    intro v
    exact (Trivialization.continuousLinearMapAt_apply_of_mem ℝ t v.property
      v.val.val.snd).symm
  have hb : Continuous (fun v : P.NativeUnitTangentOver e =>
      (⟨v.val.val.proj, v.property⟩ : e.source)) :=
    ((FiberBundle.continuous_proj ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)).comp hv).subtype_mk _
  have ha : Continuous (fun v : P.NativeUnitTangentOver e =>
      P.nativeUnitTangentAngle e he v.val.val.proj v.property
        ⟨v.val.val.snd, v.val.property⟩) := by
    apply Continuous.subtype_mk
    exact (hcoord.norm.inv₀ (fun v => (norm_pos_iff.2
      (P.nativeUnitTangentCoord_ne_zero e he v.val.val.proj v.property
        ⟨v.val.val.snd, v.val.property⟩)).ne')).smul hcoord
  exact hb.prodMk ha

/-- The actual unit tangent bundle over any native atlas chart is
homeomorphic to its source times the circle. Both directions are proved
continuous in the inherited native total-space topology. -/
noncomputable def nativeUnitTangentBundleHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas) :
    e.source × Circle ≃ₜ P.NativeUnitTangentOver e where
  toFun := P.nativeUnitTangentOverParam e he
  invFun := P.nativeUnitTangentOverAngle e he
  left_inv := P.nativeUnitTangentOverAngle_param e he
  right_inv := P.nativeUnitTangentOverParam_angle e he
  continuous_toFun := P.nativeUnitTangentOverParam_continuous e he
  continuous_invFun := P.nativeUnitTangentOverAngle_continuous e he

/-- Send any genuinely unit coordinate vector to the true native unit fiber. -/
noncomputable def nativeUnitTangentOfCoordinates
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : ℂ)
    (hv : P.gluingChartTangentForm e (e b) v v = 1) : P.NativeUnitTangentFiber b :=
  ⟨((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v,
    (P.gluedTangentInner_in_chart e he b hb v v).trans hv⟩

@[simp] theorem nativeUnitTangentCoord_ofCoordinates
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : ℂ)
    (hv : P.gluingChartTangentForm e (e b) v v = 1) :
    P.nativeUnitTangentCoord e he b (P.nativeUnitTangentOfCoordinates e he b hb v hv) = v := by
  exact Trivialization.continuousLinearMapAt_symmL
    ((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
      (⟨e, he⟩ : atlas ℂ P.GluedCarrier)) (by exact hb) v

/-- Genuine derivative-related unit coordinates on an actual atlas overlap
describe the same true native unit tangent. -/
theorem nativeUnitTangentOfCoordinates_overlap
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (hb' : b ∈ e'.source) (v v' : ℂ)
    (hv : P.gluingChartTangentForm e (e b) v v = 1)
    (hv' : P.gluingChartTangentForm e' (e' b) v' v' = 1)
    (htrans : v' = fderiv ℝ (e.symm.trans e') (e b) v) :
    P.nativeUnitTangentOfCoordinates e he b hb v hv =
      P.nativeUnitTangentOfCoordinates e' he' b hb' v' hv' := by
  apply Subtype.ext
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e', he'⟩ : atlas ℂ P.GluedCarrier)
  apply (t.continuousLinearEquivAt ℝ b (by exact hb')).injective
  rw [t.coe_continuousLinearEquivAt_eq (by exact hb')]
  change t.continuousLinearMapAt ℝ b
      (((tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
        (⟨e, he⟩ : atlas ℂ P.GluedCarrier)).symmL ℝ b v) =
    t.continuousLinearMapAt ℝ b (t.symmL ℝ b v')
  rw [t.continuousLinearMapAt_symmL (by exact hb')]
  exact (P.nativeTangentCoordChange_apply e e' he he' b hb hb' v).trans htrans.symm

/-- Place a genuine unit coordinate vector in the actual total unit tangent bundle. -/
noncomputable def nativeUnitTangentOfCoordinatesTotal
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (v : ℂ)
    (hv : P.gluingChartTangentForm e (e b) v v = 1) : P.NativeUnitTangentCarrier :=
  ⟨⟨b, (P.nativeUnitTangentOfCoordinates e he b hb v hv).val⟩,
    (P.nativeUnitTangentOfCoordinates e he b hb v hv).property⟩

/-- Every continuous family of true chart-unit vectors gives a continuous
family in the original native unit tangent bundle. -/
theorem nativeUnitTangentOfCoordinatesTotal_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (e : OpenPartialHomeomorph P.GluedCarrier ℂ) (he : e ∈ P.gluedComplexAtlas)
    {A : Type*} [TopologicalSpace A] (b : A → P.GluedCarrier) (v : A → ℂ)
    (hb : ∀ a, b a ∈ e.source)
    (hunit : ∀ a, P.gluingChartTangentForm e (e (b a)) (v a) (v a) = 1)
    (hbc : Continuous b) (hvc : Continuous v) :
    Continuous (fun a => P.nativeUnitTangentOfCoordinatesTotal e he
      (b a) (hb a) (v a) (hunit a)) := by
  apply Continuous.subtype_mk
  let t := (tangentBundleCore (modelWithCornersSelf ℝ ℂ) P.GluedCarrier).localTriv
    (⟨e, he⟩ : atlas ℂ P.GluedCarrier)
  have hc := t.continuousOn_symm.comp_continuous (hbc.prodMk hvc)
    (fun a => ⟨hb a, mem_univ (v a)⟩)
  apply hc.congr
  intro a
  change TotalSpace.mk (b a) (t.symm (b a) (v a)) = TotalSpace.mk (b a) (t.symmL ℝ (b a) (v a))
  rw [t.symmL_apply (hb a)]

/-- Derivative-related native unit coordinate families agree in the actual
total unit tangent bundle, not merely in a replacement fiber. -/
theorem nativeUnitTangentOfCoordinatesTotal_overlap
    (P : ExerciseGluingPreparation C g n genera X)
    (e e' : OpenPartialHomeomorph P.GluedCarrier ℂ)
    (he : e ∈ P.gluedComplexAtlas) (he' : e' ∈ P.gluedComplexAtlas)
    (b : P.GluedCarrier) (hb : b ∈ e.source) (hb' : b ∈ e'.source) (v v' : ℂ)
    (hv : P.gluingChartTangentForm e (e b) v v = 1)
    (hv' : P.gluingChartTangentForm e' (e' b) v' v' = 1)
    (htrans : v' = fderiv ℝ (e.symm.trans e') (e b) v) :
    P.nativeUnitTangentOfCoordinatesTotal e he b hb v hv =
      P.nativeUnitTangentOfCoordinatesTotal e' he' b hb' v' hv' := by
  apply Subtype.ext
  exact congrArg (fun w : P.NativeUnitTangentFiber b => TotalSpace.mk b w.val)
    (P.nativeUnitTangentOfCoordinates_overlap e e' he he' b hb hb' v v' hv hv' htrans)

#print axioms nativeUnitTangentFiberHomeomorph
#print axioms nativeTangentCoordChange_apply
#print axioms nativeUnitTangentAngle_transition
#print axioms nativeUnitTangentBundleHomeomorph
#print axioms nativeUnitTangentOfCoordinates_overlap
#print axioms nativeUnitTangentOfCoordinatesTotal_continuous

end ExerciseGluingPreparation
end SystolicGrowth
