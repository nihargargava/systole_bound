module

public import Geometry.GluingMetricSpinCover

@[expose] public section

/-!
# Actual circle parametrizations of clutched tangent fibers

The genuine physical circle action is transitive on every retained component
fiber. The already constructed native tangent identification transfers that
fact across the actual seams, so each clutched fiber is literally a circle.
Positive metric normalization then gives the corresponding homeomorphism
onto the real metric-unit fiber, without assuming rotation equivariance.
-/

open Set Bundle UpperHalfPlane
open scoped Manifold Topology MatrixGroups UpperHalfPlane

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SystolicGrowth

namespace ClosedHyperbolicSurface

/-- **Math.** Two genuine component frames with the same underlying surface
point differ by a physical circle phase. -/
theorem exists_circle_smul_of_tangentFrameBase_eq {g : ℕ}
    (X : ClosedHyperbolicSurface g) (q r : X.TangentFrameCarrier)
    (h : X.tangentFrameBase q = X.tangentFrameBase r) :
    ∃ a : Circle, a • q = r := by
  induction q using Quotient.inductionOn with
  | h q =>
    induction r using Quotient.inductionOn with
    | h r =>
      obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp
        (MulAction.orbitRel_apply.mp (Quotient.exact h.symm))
      change (A : SL(2, ℝ)) • q.point = r.point at hA
      let a : Circle := r.phase / ((A : SL(2, ℝ)) • q).phase
      have he : (A : SL(2, ℝ)) • (a • q) = r := by
        rw [← halfPlaneTangentFrame_circle_smul_comm]
        apply HalfPlaneTangentFrame.ext
        · exact hA
        · change a * ((A : SL(2, ℝ)) • q).phase = r.phase
          exact div_mul_cancel _ _
      refine ⟨a, ?_⟩
      change Quotient.mk _ (a • q) = Quotient.mk _ r
      exact (Quotient.sound (MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit_iff.mpr ⟨A, he⟩))).symm

end ClosedHyperbolicSurface

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- **Math.** Every two points of one actual clutched tangent fiber are
related by the literal physical circle action. The complete retained-patch
fiber theorem puts the second frame in the first frame's real component. -/
theorem exists_circle_smul_of_gluedTangentBase_eq
    (P : ExerciseGluingPreparation C g n genera X) (q r : P.GluedTangentCarrier)
    (h : P.gluedTangentBase q = P.gluedTangentBase r) :
    ∃ a : Circle, a • q = r := by
  induction q using Quotient.inductionOn with
  | h q =>
    have hv : (P.gluedTangentNativeUnit r).val.proj =
        (P.nativeTangentChainComponent q.fst q.snd).val.proj := by
      rw [P.gluedTangentNativeUnit_proj, P.nativeTangentChainComponent_proj]
      exact h.symm
    obtain ⟨r', hr', _⟩ := P.nativeTangentChainComponent_surjective_fiber
      q.fst q.snd (P.gluedTangentNativeUnit r) hv
    have hbase := congrArg (fun v : P.NativeUnitTangentCarrier => v.val.proj) hr'
    rw [P.nativeTangentChainComponent_proj, P.gluedTangentNativeUnit_proj] at hbase
    have hb : P.tangentChainComponentBase q.fst q.snd =
        P.tangentChainComponentBase q.fst r' := by
      apply P.gluedMk_injective_component q.fst
      exact h.trans hbase.symm
    obtain ⟨a, ha⟩ := (X q.fst).exists_circle_smul_of_tangentFrameBase_eq
      q.snd.val r'.val (congrArg Subtype.val hb)
    refine ⟨a, P.gluedTangentNativeUnit_injective ?_⟩
    change P.nativeTangentChainComponent q.fst
      (P.tangentChainComponentCircleAction q.fst a q.snd) = P.gluedTangentNativeUnit r
    have he : P.tangentChainComponentCircleAction q.fst a q.snd = r' := Subtype.ext ha
    rw [he]
    exact hr'

/-- **Math.** The actual clutched circle action is free, hence its orbit
parametrization in any one genuine tangent fiber is injective. -/
theorem gluedTangent_circle_smul_injective
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) :
    Function.Injective (fun a : Circle => a • q) := by
  intro a b hab
  change a • q = b • q at hab
  have hfix : (b⁻¹ * a) • q = q := by
    rw [mul_smul, hab, inv_smul_smul]
  have he := (P.gluedTangent_circle_smul_eq_self_iff (b⁻¹ * a) q).mp hfix
  exact (inv_mul_eq_one.mp he).symm

/-- **Math.** The physical phase action is a genuine homeomorphism from the
circle onto the entire literal clutched tangent fiber. -/
def gluedTangentCircleFiberHomeomorph
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) :
    Circle ≃ₜ {r : P.GluedTangentCarrier // P.gluedTangentBase r = P.gluedTangentBase q} :=
  IsHomeomorph.homeomorph
    (fun a => ⟨a • q, P.gluedTangentBase_circle_smul a q⟩)
    (isHomeomorph_iff_continuous_bijective.mpr ⟨
      (continuous_id.smul continuous_const).subtype_mk _,
      fun _ _ h => P.gluedTangent_circle_smul_injective q (congrArg Subtype.val h),
      fun r => by
        obtain ⟨a, ha⟩ := P.exists_circle_smul_of_gluedTangentBase_eq q r.val r.property.symm
        exact ⟨a, Subtype.ext ha⟩⟩)

@[simp] theorem gluedTangentCircleFiberHomeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X) (q : P.GluedTangentCarrier) (a : Circle) :
    (P.gluedTangentCircleFiberHomeomorph q a).val = a • q := rfl

/-- **Math.** The same genuine circle fiber, transported by the actual
positive metric normalization, exhausts the literal metric-unit fiber. Its
phase is the original physical action, not an assumed metric rotation. -/
def gluedMetricUnitFiberCircleHomeomorph
    (P : ExerciseGluingPreparation C g n genera X)
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (q : P.GluedTangentCarrier) :
    Circle ≃ₜ {v : P.MetricUnitTangentCarrier m // v.val.proj = P.gluedTangentBase q} := by
  let f : Circle → {v : P.MetricUnitTangentCarrier m //
      v.val.proj = P.gluedTangentBase q} := fun a =>
    ⟨P.gluedTangentMetricUnitHomeomorph m (a • q),
      (P.gluedTangentMetricUnitHomeomorph_proj m (a • q)).trans
        (P.gluedTangentBase_circle_smul a q)⟩
  have hf : Continuous f :=
    ((P.gluedTangentMetricUnitHomeomorph m).continuous.comp
      (continuous_id.smul continuous_const)).subtype_mk _
  have hinj : Function.Injective f := by
    intro a b h
    exact P.gluedTangent_circle_smul_injective q
      ((P.gluedTangentMetricUnitHomeomorph m).injective (congrArg Subtype.val h))
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨r, hr⟩ := (P.gluedTangentMetricUnitHomeomorph m).surjective v.val
    have hb : P.gluedTangentBase r = P.gluedTangentBase q := by
      rw [← P.gluedTangentMetricUnitHomeomorph_proj m r, hr]
      exact v.property
    obtain ⟨a, ha⟩ := P.exists_circle_smul_of_gluedTangentBase_eq q r hb.symm
    exact ⟨a, Subtype.ext ((congrArg (P.gluedTangentMetricUnitHomeomorph m) ha).trans hr)⟩
  exact IsHomeomorph.homeomorph f
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hinj, hsurj⟩)

@[simp] theorem gluedMetricUnitFiberCircleHomeomorph_apply
    (P : ExerciseGluingPreparation C g n genera X)
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : P.GluedCarrier → Type))
    (q : P.GluedTangentCarrier) (a : Circle) :
    (P.gluedMetricUnitFiberCircleHomeomorph m q a).val =
      P.gluedTangentMetricUnitHomeomorph m (a • q) := rfl

#print axioms exists_circle_smul_of_gluedTangentBase_eq
#print axioms gluedTangentCircleFiberHomeomorph
#print axioms gluedMetricUnitFiberCircleHomeomorph

end ExerciseGluingPreparation

end SystolicGrowth
