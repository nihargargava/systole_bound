module

public import Vendored.DoCarmo.LeeLib.Ch02.RiemannianCovering
public import Vendored.DoCarmo.LeeLib.Ch06.CompleteLocalIsometry

@[expose] public section

/-!
# The actual pullback covering metric and deck transformations

The smooth covering metric is invariant under genuine covering automorphisms:
this follows from the differential of their defining projection equation, not
from an additional metric-invariance assumption. Thus the actual deck
diffeomorphisms preserve its intrinsic Riemannian distance.

The completeness consumer retains exact compatibility with the base's ambient
distance. These are smooth-cover statements; they neither construct a smooth
replacement of the native glued surface nor identify its nonsmooth metric.
-/

open scoped Manifold ContDiff

namespace SystolicGrowth

open Bundle LeeLib.Ch02

section DeckMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {projection : C^∞⟮I, M; I', M'⟯}

/-- **Math.** The metric pulled back along a genuine smooth covering is automatically
invariant under every genuine covering automorphism. -/
theorem smoothCoveringMetric_isCoveringAutInvariant
    (hprojection : IsSmoothCoveringMap projection) (g' : RiemannianMetric I' M') :
    IsCoveringAutInvariant (hprojection.coveringMetric g') projection := by
  intro φ p
  ext v w
  rw [pullbackForm_apply]
  change g'.inner (projection (φ.toDiffeomorph p))
      (mfderiv I I' projection (φ.toDiffeomorph p) (mfderiv I I φ.toDiffeomorph p v))
      (mfderiv I I' projection (φ.toDiffeomorph p) (mfderiv I I φ.toDiffeomorph p w)) =
    g'.inner (projection p) (mfderiv I I' projection p v) (mfderiv I I' projection p w)
  have hproj : (projection : M → M') ∘ (φ.toDiffeomorph : M → M) = (projection : M → M') :=
    funext φ.proj_comp
  have hderiv (u : TangentSpace I p) :
      mfderiv I I' projection (φ.toDiffeomorph p) (mfderiv I I φ.toDiffeomorph p u) =
        mfderiv I I' projection p u := by
    have hcomp := mfderiv_comp_apply (I' := I) (I'' := I') p
      (hprojection.isLocalDiffeomorph.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
      (φ.toDiffeomorph.mdifferentiable (by simp) p) u
    rw [hproj] at hcomp
    exact hcomp.symm
  have hmetric : (g'.inner (projection (φ.toDiffeomorph p)) :
      E' →L[ℝ] E' →L[ℝ] ℝ) = g'.inner (projection p) :=
    congrArg (α := M') (β := E' →L[ℝ] E' →L[ℝ] ℝ)
      (fun q : M' => (g'.inner q : E' →L[ℝ] E' →L[ℝ] ℝ)) (φ.proj_comp p)
  calc
    _ = g'.inner (projection p)
        (mfderiv I I' projection (φ.toDiffeomorph p)
          (mfderiv I I φ.toDiffeomorph p v))
        (mfderiv I I' projection (φ.toDiffeomorph p)
          (mfderiv I I φ.toDiffeomorph p w)) :=
      congrArg (fun form : E' →L[ℝ] E' →L[ℝ] ℝ => form
        (mfderiv I I' projection (φ.toDiffeomorph p)
          (mfderiv I I φ.toDiffeomorph p v))
        (mfderiv I I' projection (φ.toDiffeomorph p)
          (mfderiv I I φ.toDiffeomorph p w))) hmetric
    _ = _ := congrArg₂ (fun a b : E' => g'.inner (projection p) a b)
      (hderiv v) (hderiv w)

/-- **Math.** Each actual deck diffeomorphism is an isometry of the constructed
covering metric, without assuming deck-metric invariance. -/
theorem smoothCoveringMetric_deck_isIsometry
    (hprojection : IsSmoothCoveringMap projection) (g' : RiemannianMetric I' M')
    (φ : CoveringAut projection) :
    IsIsometry (hprojection.coveringMetric g') (hprojection.coveringMetric g') φ.toDiffeomorph :=
  smoothCoveringMetric_isCoveringAutInvariant hprojection g' φ

/-- **Math.** Genuine deck transformations preserve the actual covering metric's
intrinsic extended Riemannian distance. -/
theorem smoothCoveringMetric_deck_riemannianEDist
    (hprojection : IsSmoothCoveringMap projection) (g' : RiemannianMetric I' M')
    (φ : CoveringAut projection) (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(hprojection.coveringMetric g').toRiemannianMetric⟩
    Manifold.riemannianEDist I (φ x) (φ y) = Manifold.riemannianEDist I x y :=
  (smoothCoveringMetric_deck_isIsometry hprojection g' φ).riemannianEDist_comp x y

/-- **Math.** With the canonical metric induced by the actual covering metric, genuine
deck transformations are metric-space isometries as well. -/
theorem smoothCoveringMetric_deck_isometry [T3Space M] [PreconnectedSpace M]
    (hprojection : IsSmoothCoveringMap projection) (g' : RiemannianMetric I' M')
    (φ : CoveringAut projection) :
    letI : MetricSpace M := (hprojection.coveringMetric g').toMetricSpace
    Isometry (φ : M → M) := by
  letI : MetricSpace M := (hprojection.coveringMetric g').toMetricSpace
  intro x y
  exact smoothCoveringMetric_deck_riemannianEDist hprojection g' φ x y

end DeckMetric

section CompatibleMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PreconnectedSpace M]

/-- **Math.** Exact Riemannian-distance compatibility identifies the canonical metric
with the existing metric, including its uniform structure. -/
theorem smoothMetric_toMetricSpace_eq (g : RiemannianMetric I M)
    (hg : Riemannian.RiemannianMetric.IsRiemannianDist g) :
    g.toMetricSpace = ‹MetricSpace M› := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply MetricSpace.ext
  ext x y
  change (Manifold.riemannianEDist I x y).toReal = dist x y
  rw [← hg.out x y, edist_dist, ENNReal.toReal_ofReal dist_nonneg]

end CompatibleMetric

section CompleteCoveringMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [ConnectedSpace M]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'} [I'.Boundaryless]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [ConnectedSpace M'] [CompleteSpace M']
  {projection : C^∞⟮I, M; I', M'⟯}

/-- **Math.** The actual pullback covering metric is complete when the original base
metric is complete and equals the smooth base metric's Riemannian distance. -/
theorem smoothCoveringMetric_complete_of_complete_base
    (hprojection : IsSmoothCoveringMap projection) (g' : RiemannianMetric I' M')
    (hg' : Riemannian.RiemannianMetric.IsRiemannianDist g') :
    letI : MetricSpace M := (hprojection.coveringMetric g').toMetricSpace
    CompleteSpace M := by
  have heq : g'.toMetricSpace = ‹MetricSpace M'› :=
    smoothMetric_toMetricSpace_eq g' hg'
  have hbase : letI : MetricSpace M' := g'.toMetricSpace; CompleteSpace M' := by
    rw [heq]
    infer_instance
  letI : MetricSpace M := (hprojection.coveringMetric g').toMetricSpace
  letI : MetricSpace M' := g'.toMetricSpace
  exact (LeeLib.Ch06.complete_iff_of_riemannianCovering
    (hprojection.coveringMetric g') g' projection (hprojection.isRiemannianCovering_coveringMetric g')).mpr hbase

end CompleteCoveringMetric

end SystolicGrowth
