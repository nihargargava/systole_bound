module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Geometry.ConstantCurvatureHalfPlaneModel

@[expose] public section

/-!
# Genuine unit tangent transport by a metric-preserving diffeomorphism

The derivative map acts in the original tangent total-space topology. Its
inverse is the actual inverse derivative, and metric preservation for that
inverse is derived from the given forward tensor identity.
-/

open Bundle
open scoped Manifold Topology ContDiff

namespace SystolicGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ℂ M] [ChartedSpace ℂ N]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ N]

/-- **Math.** The actual unit subtype in a complex-model real manifold's tangent total
space, for its specified positive continuous metric. -/
abbrev ManifoldMetricUnitTangentCarrier
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type)) :=
  {v : TotalSpace ℂ (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type) //
    m.inner v.proj v.snd v.snd = 1}

/-- **Math.** A genuine tensor isometry, stated on every actual pair of tangent vectors,
not as a supplied unit-bundle map. -/
def DiffeomorphPreservesMetric
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N) : Prop :=
  ∀ (x : M) (v w : TangentSpace (modelWithCornersSelf ℝ ℂ) x),
    m'.inner (f x)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f x v)
      (mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f x w) =
    m.inner x v w

omit [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ N] in
/-- **Math.** The manifold chain rule proves the full inverse identity in the genuine
tangent total space, including its actual base point. -/
theorem tangentMap_diffeomorph_left_inverse
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N) :
    Function.LeftInverse
      (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f.symm)
      (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f) := by
  have hcomp := tangentMap_comp (f.symm.mdifferentiable (by simp))
    (f.mdifferentiable (by simp))
  have heq : (f.symm : N → M) ∘ (f : M → N) = id :=
    funext f.symm_apply_apply
  rw [heq, tangentMap_id] at hcomp
  intro v
  exact (congrFun hcomp v).symm

omit [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ N] in
theorem tangentMap_diffeomorph_right_inverse
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N) :
    Function.RightInverse
      (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f.symm)
      (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f) :=
  tangentMap_diffeomorph_left_inverse f.symm

/-- **Math.** Forward transport is the actual differential of the actual diffeomorphism.
The metric identity proves that its image really has unit norm. -/
def metricUnitTangentDiffeomorph
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f)
    (v : ManifoldMetricUnitTangentCarrier m) : ManifoldMetricUnitTangentCarrier m' :=
  ⟨tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f v.val,
    (hf v.val.proj v.val.snd v.val.snd).trans v.property⟩

/-- **Math.** The inverse derivative preserves unit vectors by the forward tensor
identity and the actual tangent-map inverse law; no inverse metric premise
is added. -/
def metricUnitTangentDiffeomorphInverse
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f)
    (v : ManifoldMetricUnitTangentCarrier m') : ManifoldMetricUnitTangentCarrier m := by
  let w := tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f.symm v.val
  refine ⟨w, ?_⟩
  have h := hf w.proj w.snd w.snd
  change m'.inner (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f w).proj
    (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f w).snd
    (tangentMap (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f w).snd =
      m.inner w.proj w.snd w.snd at h
  rw [tangentMap_diffeomorph_right_inverse f v.val] at h
  exact h.symm.trans v.property

theorem metricUnitTangentDiffeomorph_left_inverse
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) :
    Function.LeftInverse (metricUnitTangentDiffeomorphInverse m m' f hf)
      (metricUnitTangentDiffeomorph m m' f hf) := by
  intro v
  apply Subtype.ext
  exact tangentMap_diffeomorph_left_inverse f v.val

theorem metricUnitTangentDiffeomorph_right_inverse
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) :
    Function.RightInverse (metricUnitTangentDiffeomorphInverse m m' f hf)
      (metricUnitTangentDiffeomorph m m' f hf) := by
  intro v
  apply Subtype.ext
  exact tangentMap_diffeomorph_right_inverse f v.val

/-- **Math.** A genuine metric-preserving smooth diffeomorphism gives a homeomorphism
of the literal positive-unit tangent bundles by its actual derivative. -/
def metricUnitTangentDiffeomorphHomeomorph
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) :
    ManifoldMetricUnitTangentCarrier m ≃ₜ ManifoldMetricUnitTangentCarrier m' where
  toFun := metricUnitTangentDiffeomorph m m' f hf
  invFun := metricUnitTangentDiffeomorphInverse m m' f hf
  left_inv := metricUnitTangentDiffeomorph_left_inverse m m' f hf
  right_inv := metricUnitTangentDiffeomorph_right_inverse m m' f hf
  continuous_toFun :=
    ((f.contMDiff.continuous_tangentMap (by simp)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((f.symm.contMDiff.continuous_tangentMap (by simp)).comp continuous_subtype_val).subtype_mk _

@[simp] theorem metricUnitTangentDiffeomorphHomeomorph_proj
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) (v : ManifoldMetricUnitTangentCarrier m) :
    (metricUnitTangentDiffeomorphHomeomorph m m' f hf v).val.proj = f v.val.proj := rfl

@[simp] theorem metricUnitTangentDiffeomorphHomeomorph_vector
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) (v : ManifoldMetricUnitTangentCarrier m) :
    (metricUnitTangentDiffeomorphHomeomorph m m' f hf v).val.snd =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f v.val.proj v.val.snd := rfl

@[simp] theorem metricUnitTangentDiffeomorphHomeomorph_symm_proj
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) (v : ManifoldMetricUnitTangentCarrier m') :
    ((metricUnitTangentDiffeomorphHomeomorph m m' f hf).symm v).val.proj = f.symm v.val.proj := rfl

@[simp] theorem metricUnitTangentDiffeomorphHomeomorph_symm_vector
    (m : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : M → Type))
    (m' : ContinuousRiemannianMetric ℂ
      (TangentSpace (modelWithCornersSelf ℝ ℂ) : N → Type))
    (f : M ≃ₘ⟮modelWithCornersSelf ℝ ℂ, modelWithCornersSelf ℝ ℂ⟯ N)
    (hf : DiffeomorphPreservesMetric m m' f) (v : ManifoldMetricUnitTangentCarrier m') :
    ((metricUnitTangentDiffeomorphHomeomorph m m' f hf).symm v).val.snd =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ) f.symm v.val.proj v.val.snd := rfl

#print axioms tangentMap_diffeomorph_left_inverse
#print axioms metricUnitTangentDiffeomorphHomeomorph
#print axioms metricUnitTangentDiffeomorphHomeomorph_vector

end

noncomputable section ConstantCurvatureConsumer

variable {M : Type*} [MetricSpace M] [ChartedSpace ℂ M]
  [IsManifold (modelWithCornersSelf ℝ ℂ) ∞ M]
  [SigmaCompactSpace M] [CompleteSpace M] [ConnectedSpace M]
  [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]

local instance : NeZero (Module.finrank ℝ ℂ) :=
  ⟨by rw [Complex.finrank_real_complex]; norm_num⟩

/-- **Math.** The constructed normal-coordinate model, not a separately assumed unit
bundle map, identifies the actual unit tangents of every complete simply
connected constant-curvature surface with the literal Poincaré unit bundle.
Constructing the eventual replacement metric remains a separate theorem. -/
def constantCurvatureHalfPlaneUnitTangentHomeomorph
    (g : Riemannian.RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u) :
    ManifoldMetricUnitTangentCarrier g.toContinuousRiemannianMetric ≃ₜ
      ManifoldMetricUnitTangentCarrier upperHalfPlanePoincareMetric.toContinuousRiemannianMetric :=
  metricUnitTangentDiffeomorphHomeomorph g.toContinuousRiemannianMetric
    upperHalfPlanePoincareMetric.toContinuousRiemannianMetric
    (constantCurvatureHalfPlaneDiffeomorph g hg p hK)
    (fun a u v => (constantCurvatureHalfPlaneDiffeomorph_isIsometry g hg p hK).inner_mfderiv a u v)

/-- **Math.** The actual unit-bundle model lies over the already verified marked
normal-coordinate diffeomorphism, with no change of the source basepoint. -/
theorem constantCurvatureHalfPlaneUnitTangentHomeomorph_proj
    (g : Riemannian.RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (q : ManifoldMetricUnitTangentCarrier g.toContinuousRiemannianMetric) :
    (constantCurvatureHalfPlaneUnitTangentHomeomorph g hg p hK q).val.proj =
      constantCurvatureHalfPlaneDiffeomorph g hg p hK q.val.proj := rfl

/-- **Math.** The actual unit vector is transported by the full real differential of
the constructed half-plane model, not just by its complex coordinate phase. -/
theorem constantCurvatureHalfPlaneUnitTangentHomeomorph_vector
    (g : Riemannian.RiemannianMetric (modelWithCornersSelf ℝ ℂ) M)
    (hg : g.IsRiemannianDist) (p : M)
    (hK : ∀ (a : M) (u v : TangentSpace (modelWithCornersSelf ℝ ℂ) a),
      g.metricInner a u u * g.metricInner a v v -
        g.metricInner a u v * g.metricInner a u v =
      g.metricInner a (g.leviCivitaConnection.curvatureOperatorAt a u v v) u)
    (q : ManifoldMetricUnitTangentCarrier g.toContinuousRiemannianMetric) :
    (constantCurvatureHalfPlaneUnitTangentHomeomorph g hg p hK q).val.snd =
      mfderiv (modelWithCornersSelf ℝ ℂ) (modelWithCornersSelf ℝ ℂ)
        (constantCurvatureHalfPlaneDiffeomorph g hg p hK) q.val.proj q.val.snd := rfl

#print axioms constantCurvatureHalfPlaneUnitTangentHomeomorph
#print axioms constantCurvatureHalfPlaneUnitTangentHomeomorph_vector

end ConstantCurvatureConsumer

end SystolicGrowth
