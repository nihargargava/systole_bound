module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.ConformalRiemannianMetric
public import Geometry.MetricHomotopySystole
public import Vendored.DoCarmo.LeeLib.Ch02.Distance

@[expose] public section

/-!
# Same-atlas conformal metric domination preserves homotopy systole

The actual path integrands are compared first. Taking the actual infimum
over admissible `C¹` curves then gives intrinsic-distance domination.
Both canonical metric topologies are the unchanged manifold topology, so
the identity is a genuine one-Lipschitz homeomorphism from the new metric
to the old metric. The continuous essential-loop systole comparison uses
this proved homeomorphism, not a distance-domination hypothesis.
-/

open Bundle Manifold Riemannian Set MeasureTheory
open scoped ContDiff Manifold Topology ENNReal

namespace SystolicGrowth

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The actual Riemannian length of a curve, with its metric
specified as data rather than a competing global bundle instance. -/
def riemannianMetricPathELength (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength I γ a b

theorem riemannianMetricPathELength_eq_lintegral (g : RiemannianMetric I M)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianMetricPathELength g γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal
      (Real.sqrt (g.metricInner (γ t)
        (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1))) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  unfold riemannianMetricPathELength
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  dsimp only
  have hsq : ‖mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1‖ ^ 2 =
      g.metricInner (γ t) (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1)
        (mfderiv (modelWithCornersSelf ℝ ℝ) I γ t 1) :=
    (real_inner_self_eq_norm_sq _).symm
  rw [← hsq, Real.sqrt_sq (norm_nonneg _), ofReal_norm]

/-- **Math.** Every curve has nondecreasing length under the actual
conformal scaling. No extra smoothness or seam-avoidance restriction is
needed; in particular this includes every permitted smooth piece. -/
theorem conformalRiemannianMetric_pathELength_ge
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) (hupos : ∀ p, 0 ≤ u p)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianMetricPathELength g γ a b ≤
      riemannianMetricPathELength (conformalRiemannianMetric g u hu) γ a b := by
  rw [riemannianMetricPathELength_eq_lintegral, riemannianMetricPathELength_eq_lintegral]
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (conformalRiemannianMetric_sqrt_self_ge g u hu (γ t) (hupos _) _)

/-- **Math.** The actual intrinsic distance is the existing Riemannian
infimum, with the smooth metric supplied explicitly. -/
def riemannianMetricIntrinsicEDist (g : RiemannianMetric I M) (x y : M) : ℝ≥0∞ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist I x y

/-- **Math.** Increasing every permitted path length increases their
actual infimum. No intrinsic-distance inequality is postulated. -/
theorem conformalRiemannianMetric_intrinsicEDist_ge
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) (hupos : ∀ p, 0 ≤ u p)
    (x y : M) :
    riemannianMetricIntrinsicEDist g x y ≤
      riemannianMetricIntrinsicEDist (conformalRiemannianMetric g u hu) x y := by
  by_contra h
  have hlt : riemannianMetricIntrinsicEDist (conformalRiemannianMetric g u hu) x y <
      riemannianMetricIntrinsicEDist g x y := lt_of_not_ge h
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(conformalRiemannianMetric g u hu).toRiemannianMetric⟩
  change Manifold.riemannianEDist I x y < riemannianMetricIntrinsicEDist g x y at hlt
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  change riemannianMetricPathELength (conformalRiemannianMetric g u hu) γ 0 1 <
    riemannianMetricIntrinsicEDist g x y at hlen
  have hold : riemannianMetricIntrinsicEDist g x y ≤ riemannianMetricPathELength g γ 0 1 := by
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one
  exact (not_lt_of_ge (hold.trans (conformalRiemannianMetric_pathELength_ge g u hu hupos γ 0 1))) hlen

variable [T3Space M] [PreconnectedSpace M]

/-- **Math.** Domination holds for the actual finite canonical metric
distances, not only a separately chosen extended-distance expression. -/
theorem conformalRiemannianMetric_dist_ge
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) (hupos : ∀ p, 0 ≤ u p)
    (x y : M) :
    @dist M (LeeLib.Ch02.RiemannianMetric.toMetricSpace g).toDist x y ≤
      @dist M (LeeLib.Ch02.RiemannianMetric.toMetricSpace
        (conformalRiemannianMetric g u hu)).toDist x y := by
  change (riemannianMetricIntrinsicEDist g x y).toReal ≤
    (riemannianMetricIntrinsicEDist (conformalRiemannianMetric g u hu) x y).toReal
  have hfinite : riemannianMetricIntrinsicEDist (conformalRiemannianMetric g u hu) x y ≠ ⊤ := by
    exact LeeLib.Ch02.RiemannianMetric.riemannianEDist_ne_top (conformalRiemannianMetric g u hu) x y
  exact ENNReal.toReal_mono hfinite (conformalRiemannianMetric_intrinsicEDist_ge g u hu hupos x y)

/-- **Math.** The canonical metrics have the SAME original manifold
topology, so the literal identity is a homeomorphism between them. -/
def conformalMetricIdentityHomeomorph (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) :
    @Homeomorph M M
      (LeeLib.Ch02.RiemannianMetric.toMetricSpace (conformalRiemannianMetric g u hu)).toUniformSpace.toTopologicalSpace
      (LeeLib.Ch02.RiemannianMetric.toMetricSpace g).toUniformSpace.toTopologicalSpace :=
  @Homeomorph.refl M (inferInstance : TopologicalSpace M)

theorem conformalMetricIdentityHomeomorph_lipschitz
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) (hupos : ∀ p, 0 ≤ u p) :
    @LipschitzWith M M
      (LeeLib.Ch02.RiemannianMetric.toMetricSpace (conformalRiemannianMetric g u hu)).toPseudoEMetricSpace
      (LeeLib.Ch02.RiemannianMetric.toMetricSpace g).toPseudoEMetricSpace 1
      (conformalMetricIdentityHomeomorph g u hu) := by
  apply @LipschitzWith.of_dist_le_mul M M
    (LeeLib.Ch02.RiemannianMetric.toMetricSpace (conformalRiemannianMetric g u hu)).toPseudoMetricSpace
    (LeeLib.Ch02.RiemannianMetric.toMetricSpace g).toPseudoMetricSpace 1
    (conformalMetricIdentityHomeomorph g u hu)
  intro x y
  simpa only [conformalMetricIdentityHomeomorph, Homeomorph.refl_apply, id_eq, NNReal.coe_one, one_mul] using
    conformalRiemannianMetric_dist_ge g u hu hupos x y

/-- **Math.** Every essential continuous loop is compared by the actual
one-Lipschitz identity homeomorphism; hence the actual homotopy systole
cannot decrease under the nonnegative conformal scaling. -/
theorem conformalRiemannianMetric_homotopySystole_ge
    (g : RiemannianMetric I M) (u : M → ℝ)
    (hu : ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ u) (hupos : ∀ p, 0 ≤ u p) :
    @metricHomotopySystole M (LeeLib.Ch02.RiemannianMetric.toMetricSpace g).toPseudoMetricSpace ≤
      @metricHomotopySystole M (LeeLib.Ch02.RiemannianMetric.toMetricSpace
        (conformalRiemannianMetric g u hu)).toPseudoMetricSpace := by
  simpa only [ENNReal.coe_one, one_mul] using
    @metricHomotopySystole_le_mul_of_lipschitz_homeomorph M M
      (LeeLib.Ch02.RiemannianMetric.toMetricSpace (conformalRiemannianMetric g u hu)).toPseudoMetricSpace
      (LeeLib.Ch02.RiemannianMetric.toMetricSpace g).toPseudoMetricSpace
      (conformalMetricIdentityHomeomorph g u hu) 1 zero_lt_one
      (conformalMetricIdentityHomeomorph_lipschitz g u hu hupos)

#print axioms conformalRiemannianMetric_pathELength_ge
#print axioms conformalRiemannianMetric_intrinsicEDist_ge
#print axioms conformalRiemannianMetric_dist_ge
#print axioms conformalMetricIdentityHomeomorph_lipschitz
#print axioms conformalRiemannianMetric_homotopySystole_ge

end

end SystolicGrowth
