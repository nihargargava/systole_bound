module

/-
Vendored from frenzymath/Poincare-Conjecture (Apache-2.0).
Immutable commit: 5a9e2acd61c33320a2e6232e502d2189385f5157.
Original path: references/DoCarmo/DoCarmoLib/Riemannian/Manifold/PullbackMetric.lean.
Original headers, namespaces and mathematical contracts are retained.
Local changes: import prefixes, upstream options and proof-preserving API/linter compatibility.
See Code-Attribution.md and Vendored/DoCarmo/LICENSE.
-/
public import Vendored.DoCarmo.DoCarmoLib.Riemannian.Manifold.ExpandingMap
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.LocallyConvex.Bounded

@[expose] public section

-- Port: preserve the upstream DoCarmo package's elaboration options locally.
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
-- Port: retain upstream typeclass binders; this new linter changes no proof checks.
set_option linter.overlappingInstances false


/-!
# Pullback of a Riemannian metric along a smooth immersion (do Carmo Ch. 7, §3, Hadamard core)

do Carmo's proof of the Hadamard theorem (`thm:dc-ch7-3-1`) and of the poles remark
(`rem:dc-ch7-3-4`) equips the tangent space `T_pM` with the **pulled-back metric**
`(\exp_p)^* g`, chosen precisely so that `\exp_p : T_pM → M` becomes a **local isometry**
(hence a metric-expander) out of the flat `T_pM`. This file isolates that construction as
reusable infrastructure, abstracted away from the exponential map: given *any* smooth
immersion `f : M → M'` and a Riemannian metric `g'` on `M'`, the pullback
`f^*g'` — `⟨u, v⟩^{f^*g'}_p := g'_{f p}(df_p u, df_p v)` — is a Riemannian metric on `M`.

The source manifold `M` is required to already carry a Riemannian bundle
(`[Bundle.RiemannianBundle (TangentSpace I)]`), which supplies the fibre norms the
construction is stated against; in the Hadamard application `M = T_pM` is a vector space
and this is the canonical flat instance (`riemannianMetricVectorSpace`). The pulled-back
inner product on the fibres is a *different* inner product from that ambient one.

* `RiemannianMetric.pullbackInner g' f b` — the pulled-back inner product at `b`, the
  continuous bilinear form `(u, v) ↦ g'_{f b}(df_b u, df_b v)` via
  `ContinuousLinearMap.bilinearComp`.
* `RiemannianMetric.pullback g' f himm hsmooth` — the pulled-back Riemannian metric,
  packaging `pullbackInner` into a `ContMDiffRiemannianMetric`. Symmetry is `g'`'s
  symmetry; positive-definiteness uses the **immersion** hypothesis
  `himm : ∀ b, Injective (df_b)`; von-Neumann boundedness of the unit sub-level set is
  transported from `g'`'s across the injective finite-dimensional `df_b`
  (`AffineMap.antilipschitzWith_of_finiteDimensional`). The **smoothness** of the metric
  section — the one genuinely analytic obligation — is kept as an explicit hypothesis
  `hsmooth` in `pullback`, so the algebraic content is available independently, but it is
  **no longer a residual**: `isPullbackMetricSmooth_of_contMDiff` discharges it from
  `ContMDiff I I' ∞ f` alone (the pullback-form section is do Carmo Ch. 1's `DCInducedForm`,
  whose bundle smoothness `DCInducedForm_contMDiff` was already established via
  `ContMDiffAt.mfderiv_const` and `gN.contMDiff`).
* `RiemannianMetric.isPullbackMetricSmooth_of_contMDiff` — the discharge of `hsmooth` from
  smoothness of `f`; and `RiemannianMetric.pullbackOfSmoothImmersion` (with
  `dcPreservesMetric_pullbackOfSmoothImmersion` / `dcExpandsMetric_pullbackOfSmoothImmersion`)
  — the `hsmooth`-free entry point building `f^*g'` and its `DCExpandsMetric` witness from a
  bare `DCSmoothImmersion f`. This is the form the Hadamard proof instantiates at `f = exp_p`.
* `RiemannianMetric.dcPreservesMetric_pullback` / `dcExpandsMetric_pullback` — `f`
  **preserves**, hence **expands**, the pullback metric (do Carmo Def. 2.2 / Lemma 3.3
  hypothesis). The latter is the `DCExpandsMetric` input consumed by the Hadamard assembly
  `DCExpandsMetric.diffeomorphOfSimplyConnected`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Theorem 3.1 (Hadamard) and
Remark 3.4 (poles).
-/

open Bundle Manifold Set Function Bornology
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** The **pulled-back inner product** at `b : M` along `f : M → M'`:
`(u, v) ↦ g'_{f b}(df_b u, df_b v)`, a continuous bilinear form on `T_bM`, built by
composing the fibre inner product `g'.inner (f b)` with the differential `df_b` in both
slots (`ContinuousLinearMap.bilinearComp`). -/
def pullbackInner (g' : RiemannianMetric I' M') (f : M → M') (b : M) :
    TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  (g'.inner (f b)).bilinearComp (mfderiv I I' f b) (mfderiv I I' f b)

@[simp]
theorem pullbackInner_apply (g' : RiemannianMetric I' M') (f : M → M') (b : M)
    (u v : TangentSpace I b) :
    pullbackInner g' f b u v = g'.inner (f b) (mfderiv I I' f b u) (mfderiv I I' f b v) := by
  letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
  exact (g'.inner (f b)).bilinearComp_apply _ _ u v

/-- **Math.** **Smoothness of the pulled-back metric section** — the sole analytic
obligation in the pullback construction. It says the section `b ↦ [(u,v) ↦ pullbackInner]`
of the bundle of continuous bilinear forms on `T_bM` is smooth, exactly the `contMDiff`
field of a `ContMDiffRiemannianMetric`. It is provable from `ContMDiff I I' ∞ f` via the
smoothness of the tangent map (`ContMDiff.contMDiff_tangentMap`) and of `g'`; here it is
kept as a named predicate so the algebraic content of `pullback` is available
independently. -/
def IsPullbackMetricSmooth (g' : RiemannianMetric I' M') (f : M → M') : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun b : M ↦ TotalSpace.mk' (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun b : M ↦ TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) b
      (pullbackInner g' f b))

/-- **Math.** The pullback-metric smoothness obligation `IsPullbackMetricSmooth` is **discharged
from `ContMDiff I I' ∞ f`** — it is no longer an extra assumption. The pullback-form section
`b ↦ pullbackInner g' f b`, `pullbackInner g' f b = (g'.inner (f b)).bilinearComp (df_b) (df_b)`,
is definitionally the do Carmo Ch.1 Ex. 2.5 pullback form `DCInducedForm g' f b`, whose bundle
smoothness `Riemannian.DCInducedForm_contMDiff` was already established from smoothness of `f`
alone (via `ContMDiffAt.mfderiv_const` for the differential read in tangent coordinates and
`gN.contMDiff` for the target metric section, composed by `clm_comp`/`clm_precomp`). This closes
the sole analytic residual isolated in `pullback`. -/
theorem isPullbackMetricSmooth_of_contMDiff (g' : RiemannianMetric I' M') {f : M → M'}
    (hf : ContMDiff I I' ∞ f) :
    IsPullbackMetricSmooth (I := I) g' f :=
  DCInducedForm_contMDiff (I := I) (I' := I') g' hf

/-- **Math.** **The pullback Riemannian metric `f^*g'`** (do Carmo Ch. 7, §3). For a smooth
immersion `f : M → M'` and a Riemannian metric `g'` on `M'`, the assignment
`b ↦ [(u, v) ↦ g'_{f b}(df_b u, df_b v)]` is a Riemannian metric on `M`.

Symmetry and positive-definiteness are algebraic (`g'.symm`, `g'.pos` together with the
immersion hypothesis `himm`); the smoothness of the metric section is supplied as the
hypothesis `hsmooth` — the sole analytic ingredient, provable from `ContMDiff I I' ∞ f`. -/
def pullback (g' : RiemannianMetric I' M') (f : M → M')
    (himm : ∀ b : M, Function.Injective (mfderiv I I' f b))
    (hsmooth : IsPullbackMetricSmooth (I := I) g' f) :
    RiemannianMetric I M where
  inner b := pullbackInner g' f b
  symm b v w := by
    simp only [pullbackInner_apply]
    letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    exact g'.symm (f b) _ _
  pos b v hv := by
    simp only [pullbackInner_apply]
    letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    have hdv : mfderiv I I' f b v ≠ 0 := fun h => hv (himm b (by rw [h, map_zero]))
    exact g'.pos (f b) _ hdv
  isVonNBounded b := by
    letI : Bundle.RiemannianBundle (TangentSpace I' : M' → Type _) := ⟨g'.toRiemannianMetric⟩
    have hset : {v : TangentSpace I b | pullbackInner g' f b v v < 1}
        = (mfderiv I I' f b) ⁻¹' {w : TangentSpace I' (f b) | g'.inner (f b) w w < 1} := by
      ext v; simp only [pullbackInner_apply, Set.mem_setOf_eq, Set.mem_preimage]
    rw [hset]
    have hbdd : IsBounded {w : TangentSpace I' (f b) | g'.inner (f b) w w < 1} :=
      (NormedSpace.isVonNBounded_iff ℝ).mp (g'.isVonNBounded (f b))
    obtain ⟨K, hK⟩ := AffineMap.antilipschitzWith_of_finiteDimensional
      (f := (mfderiv I I' f b).toLinearMap.toAffineMap) (himm b)
    refine (NormedSpace.isVonNBounded_iff ℝ).mpr ?_
    exact hK.isBounded_preimage hbdd
  contMDiff := hsmooth

@[simp]
theorem pullback_metricInner (g' : RiemannianMetric I' M') (f : M → M')
    (himm : ∀ b : M, Function.Injective (mfderiv I I' f b))
    (hsmooth : IsPullbackMetricSmooth (I := I) g' f)
    (b : M) (u v : TangentSpace I b) :
    (pullback g' f himm hsmooth).metricInner b u v
      = g'.metricInner (f b) (mfderiv I I' f b u) (mfderiv I I' f b v) :=
  pullbackInner_apply g' f b u v

/-- **Math.** **`f` preserves its own pullback metric** (do Carmo Ch. 1, Def. 2.2): with the
pulled-back metric `f^*g'` on the source, `f` is a local isometry,
`⟨u, v⟩^{f^*g'}_b = g'_{f b}(df_b u, df_b v)`, by construction. This is the fact do Carmo
uses in the Hadamard proof: `\exp_p` is a local isometry for the pulled-back metric. -/
theorem dcPreservesMetric_pullback (g' : RiemannianMetric I' M') (f : M → M')
    (himm : ∀ b : M, Function.Injective (mfderiv I I' f b))
    (hsmooth : IsPullbackMetricSmooth (I := I) g' f) :
    DCPreservesMetric (pullback g' f himm hsmooth) g' f :=
  fun b u v => pullback_metricInner g' f himm hsmooth b u v

/-- **Math.** **`f` expands its own pullback metric** (do Carmo Ch. 7, Lemma 3.3
hypothesis): a metric-preserving map is in particular a metric-expander, so
`DCExpandsMetric (f^*g') g' f`. This is exactly the `DCExpandsMetric` input consumed by the
Hadamard assembly `DCExpandsMetric.diffeomorphOfSimplyConnected`. -/
theorem dcExpandsMetric_pullback (g' : RiemannianMetric I' M') (f : M → M')
    (himm : ∀ b : M, Function.Injective (mfderiv I I' f b))
    (hsmooth : IsPullbackMetricSmooth (I := I) g' f) :
    DCExpandsMetric (pullback g' f himm hsmooth) g' f :=
  (dcPreservesMetric_pullback g' f himm hsmooth).dcExpandsMetric

/-- **Math.** **The pullback metric of a smooth immersion**, with the smoothness obligation
discharged. Given a `DCSmoothImmersion f` (do Carmo Ch. 0/1: `f` smooth and `df_b` injective for
all `b`) and a Riemannian metric `g'` on `M'`, this is the pulled-back metric `f^*g'`, built via
`pullback` with the analytic hypothesis `hsmooth` supplied internally by
`isPullbackMetricSmooth_of_contMDiff`. This is the `hsmooth`-free entry point for the Hadamard
proof, where `f = exp_p` is the smooth immersion (a pole / `K ≤ 0` local diffeomorphism). -/
noncomputable def pullbackOfSmoothImmersion (g' : RiemannianMetric I' M') (f : M → M')
    (himm : DCSmoothImmersion (I := I) (I' := I') f) :
    RiemannianMetric I M :=
  pullback g' f himm.2 (isPullbackMetricSmooth_of_contMDiff g' himm.1)

@[simp]
theorem pullbackOfSmoothImmersion_metricInner (g' : RiemannianMetric I' M') (f : M → M')
    (himm : DCSmoothImmersion (I := I) (I' := I') f) (b : M) (u v : TangentSpace I b) :
    (pullbackOfSmoothImmersion g' f himm).metricInner b u v
      = g'.metricInner (f b) (mfderiv I I' f b u) (mfderiv I I' f b v) :=
  pullback_metricInner g' f himm.2 (isPullbackMetricSmooth_of_contMDiff g' himm.1) b u v

/-- **Math.** `f` **preserves** its own pullback metric (do Carmo Ch. 1, Def. 2.2): with `f^*g'`
on the source, `f` is a local isometry. The `DCSmoothImmersion`, `hsmooth`-free form of
`dcPreservesMetric_pullback`. -/
theorem dcPreservesMetric_pullbackOfSmoothImmersion (g' : RiemannianMetric I' M') (f : M → M')
    (himm : DCSmoothImmersion (I := I) (I' := I') f) :
    DCPreservesMetric (pullbackOfSmoothImmersion g' f himm) g' f :=
  dcPreservesMetric_pullback g' f himm.2 (isPullbackMetricSmooth_of_contMDiff g' himm.1)

/-- **Math.** `f` **expands** its own pullback metric (do Carmo Ch. 7, Lemma 3.3 hypothesis),
from just a `DCSmoothImmersion`. This is the `DCExpandsMetric` input consumed by the Hadamard
assembly `DCExpandsMetric.diffeomorphOfSimplyConnected` / `…OfGeodesicCompleteAt`, now depending
only on smoothness and injectivity of `df` — the separate smoothness-of-the-pullback-metric
assumption is discharged. -/
theorem dcExpandsMetric_pullbackOfSmoothImmersion (g' : RiemannianMetric I' M') (f : M → M')
    (himm : DCSmoothImmersion (I := I) (I' := I') f) :
    DCExpandsMetric (pullbackOfSmoothImmersion g' f himm) g' f :=
  dcExpandsMetric_pullback g' f himm.2 (isPullbackMetricSmooth_of_contMDiff g' himm.1)

end Riemannian.RiemannianMetric

end
