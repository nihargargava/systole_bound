module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingNativeUnitTangentCharts

@[expose] public section

/-!
# Changing the metric on the genuine unit tangent bundle

Positive radial normalization transports the native unit tangent bundle to
that of any continuous replacement metric on the same actual tangent bundle.
This preserves basepoints and antipodes, without claiming conformality or
rotation-equivariance for arbitrary anisotropic metrics.
-/

open Set Filter Bundle ContinuousLinearMap
open scoped Manifold Topology

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth.ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** The literal unit tangent total space for an actual continuous
positive metric, retaining the original tangent-bundle topology. -/
abbrev MetricUnitTangentCarrier
    (P : ExerciseGluingPreparation C g n genera X)
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)) :=
  {v : TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) //
    m.inner v.proj v.snd v.snd = 1}

theorem Internal.GluingUnitTangentMetricChangeHelpers.normalize_bilinear_self
    (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (v : ℂ) (hv : 0 < B v v) :
    B ((Real.sqrt (B v v))⁻¹ • v) ((Real.sqrt (B v v))⁻¹ • v) = 1 := by
  have hs : Real.sqrt (B v v) ≠ 0 := (Real.sqrt_pos.2 hv).ne'
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hsq := Real.sq_sqrt hv.le
  field_simp
  nlinarith

theorem Internal.GluingUnitTangentMetricChangeHelpers.normalize_bilinear_inverse
    (A B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (v : ℂ) (hA : A v v = 1)
    (hB : 0 < B v v) :
    (Real.sqrt (A ((Real.sqrt (B v v))⁻¹ • v)
      ((Real.sqrt (B v v))⁻¹ • v)))⁻¹ • ((Real.sqrt (B v v))⁻¹ • v) = v := by
  let c := (Real.sqrt (B v v))⁻¹
  have hc : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hB)
  have hinner : A (c • v) (c • v) = c ^ 2 := by
    simp only [map_smul, smul_apply, smul_eq_mul, hA]
    ring
  change (Real.sqrt (A (c • v) (c • v)))⁻¹ • (c • v) = v
  rw [hinner, Real.sqrt_sq hc.le, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- **Math.** A genuine unit tangent is nonzero, independently of charts. -/
theorem metricUnitTangent_ne_zero
    (P : ExerciseGluingPreparation C g n genera X)
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (v : P.MetricUnitTangentCarrier m) : v.val.snd ≠ 0 := by
  intro h
  have hv := v.property
  simp [h] at hv

/-- **Math.** Positive radial renormalization into another genuine metric's
unit tangent bundle. No replacement metric is postulated by this map. -/
def unitTangentMetricChange
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (v : P.MetricUnitTangentCarrier m) : P.MetricUnitTangentCarrier m' :=
  ⟨⟨v.val.proj, (Real.sqrt (m'.inner v.val.proj v.val.snd v.val.snd))⁻¹ • v.val.snd⟩,
    Internal.GluingUnitTangentMetricChangeHelpers.normalize_bilinear_self _ _ (m'.pos _ _ (P.metricUnitTangent_ne_zero m v))⟩

@[simp] theorem unitTangentMetricChange_proj
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (v : P.MetricUnitTangentCarrier m) :
    (P.unitTangentMetricChange m m' v).val.proj = v.val.proj := rfl

@[simp] theorem unitTangentMetricChange_inverse
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (v : P.MetricUnitTangentCarrier m) :
    P.unitTangentMetricChange m' m (P.unitTangentMetricChange m m' v) = v := by
  apply Subtype.ext
  change TotalSpace.mk v.val.proj _ = TotalSpace.mk v.val.proj v.val.snd
  apply congrArg (TotalSpace.mk v.val.proj)
  exact Internal.GluingUnitTangentMetricChangeHelpers.normalize_bilinear_inverse _ _ _ v.property
    (m'.pos _ _ (P.metricUnitTangent_ne_zero m v))

private theorem metricUnitTangent_inner_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)) :
    Continuous (fun v : P.MetricUnitTangentCarrier m =>
      m'.inner v.val.proj v.val.snd v.val.snd) := by
  have hv : Continuous (fun v : P.MetricUnitTangentCarrier m => v.val) :=
    continuous_subtype_val
  have hb := (FiberBundle.continuous_proj ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)).comp hv
  rw [continuous_iff_continuousAt]
  intro v
  have h : ContinuousAt (fun w : P.MetricUnitTangentCarrier m =>
      (TotalSpace.mk' ℝ w.val.proj
        (m'.inner w.val.proj w.val.snd w.val.snd) :
          TotalSpace ℝ (Trivial P.GluedCarrier ℝ))) v :=
    ((m'.continuous.comp hb).continuousAt (x := v)).clm_bundle_apply₂
      (F₁ := ℂ) (F₂ := ℂ) hv.continuousAt hv.continuousAt
  simp only [FiberBundle.continuousAt_totalSpace] at h
  exact h.2

/-- **Math.** Metric renormalization is continuous in the genuine total-space
topology, not in an artificially chosen product topology. -/
theorem unitTangentMetricChange_continuous
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)) :
    Continuous (P.unitTangentMetricChange m m') := by
  apply Continuous.subtype_mk
  have hv : Continuous (fun v : P.MetricUnitTangentCarrier m => v.val) :=
    continuous_subtype_val
  have hb := (FiberBundle.continuous_proj ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)).comp hv
  let c : P.MetricUnitTangentCarrier m → ℝ := fun v =>
    (Real.sqrt (m'.inner v.val.proj v.val.snd v.val.snd))⁻¹
  have hc : Continuous c := (Real.continuous_sqrt.comp
    (P.metricUnitTangent_inner_continuous m m')).inv₀ (fun v =>
      (Real.sqrt_pos.2 (m'.pos _ _ (P.metricUnitTangent_ne_zero m v))).ne')
  rw [continuous_iff_continuousAt]
  intro v₀
  rw [FiberBundle.continuousAt_totalSpace ℂ]
  have hread := (FiberBundle.continuousAt_totalSpace ℂ _).mp (hv.continuousAt (x := v₀))
  refine ⟨hread.1, ?_⟩
  let t := trivializationAt ℂ
    (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type) v₀.val.proj
  have hcoord := hc.continuousAt.smul hread.2
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.preimage_mem_nhds
    (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' v₀.val.proj))] with v hv'
  change v.val.proj ∈ t.baseSet at hv'
  change (t ⟨v.val.proj, c v • v.val.snd⟩).2 = c v • (t v.val).2
  calc
    _ = t.continuousLinearMapAt ℝ v.val.proj (c v • v.val.snd) :=
      (t.continuousLinearMapAt_apply_of_mem ℝ hv' _).symm
    _ = c v • t.continuousLinearMapAt ℝ v.val.proj v.val.snd := map_smul _ _ _
    _ = _ := congrArg (fun z : ℂ => c v • z)
      (t.continuousLinearMapAt_apply_of_mem ℝ hv' _)

/-- **Math.** The actual unit tangent bundle is independent of the choice of
positive continuous metric up to a constructed base-preserving homeomorphism. -/
def unitTangentMetricHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)) :
    P.MetricUnitTangentCarrier m ≃ₜ P.MetricUnitTangentCarrier m' where
  toFun := P.unitTangentMetricChange m m'
  invFun := P.unitTangentMetricChange m' m
  left_inv := P.unitTangentMetricChange_inverse m m'
  right_inv := P.unitTangentMetricChange_inverse m' m
  continuous_toFun := P.unitTangentMetricChange_continuous m m'
  continuous_invFun := P.unitTangentMetricChange_continuous m' m

/-- **Math.** The actual antipodal unit tangent, in the same genuine fiber. -/
def metricUnitTangentAntipode
    (P : ExerciseGluingPreparation C g n genera X)
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (v : P.MetricUnitTangentCarrier m) : P.MetricUnitTangentCarrier m :=
  ⟨⟨v.val.proj, -v.val.snd⟩, by
    simp only [map_neg, neg_apply, neg_neg]
    exact v.property⟩

/-- **Math.** The actual metric-change homeomorphism preserves antipodes,
so a transported spin covering keeps its genuine central involution. -/
theorem unitTangentMetricChange_antipode
    (P : ExerciseGluingPreparation C g n genera X)
    (m m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (v : P.MetricUnitTangentCarrier m) :
    P.unitTangentMetricChange m m' (P.metricUnitTangentAntipode m v) =
      P.metricUnitTangentAntipode m' (P.unitTangentMetricChange m m' v) := by
  apply Subtype.ext
  change TotalSpace.mk v.val.proj
    ((Real.sqrt (m'.inner v.val.proj (-v.val.snd) (-v.val.snd)))⁻¹ • (-v.val.snd)) =
      TotalSpace.mk v.val.proj
        (-((Real.sqrt (m'.inner v.val.proj v.val.snd v.val.snd))⁻¹ • v.val.snd))
  simp only [map_neg, neg_apply, neg_neg, smul_neg]

/-- **Math.** The native unit tangent bundle transfers to any actual
continuous replacement metric on the same carrier by the proved radial map. -/
def nativeUnitTangentMetricHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type)) :
    P.NativeUnitTangentCarrier ≃ₜ P.MetricUnitTangentCarrier m :=
  P.unitTangentMetricHomeomorph P.gluedContinuousRiemannianMetric m

#print axioms unitTangentMetricChange_inverse
#print axioms unitTangentMetricChange_continuous
#print axioms unitTangentMetricHomeomorph
#print axioms unitTangentMetricChange_antipode
#print axioms nativeUnitTangentMetricHomeomorph

end SystolicGrowth.ExerciseGluingPreparation
