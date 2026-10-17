module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFiniteMetricBlocks
public import Geometry.MetricGluingGeodesics
public import Geometry.MetricConvexGluingMidpoints
public import Geometry.MetricMidpointComparisonInductiveLimit

@[expose] public section

/-!
# Comparison for the actual finite augmented Fermi blocks

The closed hyperbolic slab supplies the initial comparison. The genuine
complete convex upper fin supplies every seam interval; its reflected
isometric embedding supplies the lower seam. Thus the original finite block
carriers and their native metrics are retained throughout the induction.
-/

open Set

namespace SystolicGrowth

/-- The original hyperbolic radial slab satisfies all-test midpoint-cosh
comparison, with the actual induced hyperbolic distances. -/
theorem gluingFinFermiRadialWindow_exists_midpoint_cosh_all_test
    {lam R : ℝ} (hlam : 0 < lam) (x y : gluingFinFermiRadialWindow lam R) :
    ∃ m : gluingFinFermiRadialWindow lam R,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : gluingFinFermiRadialWindow lam R,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  obtain ⟨m, hxm, hmy, hcompare⟩ := exists_subtype_hyperbolic_midpoint_cosh
    (fun _ ha _ hb => gluingFinFermiRadialWindow_geodSeg_subset hlam ha hb) x y
  exact ⟨m, hxm, hmy, fun z => (hcompare z).le⟩

/-- The native complete convex fin has genuine arc-length intervals. These
same intervals are used on both sides of each block attachment. -/
theorem gluingCollarFiniteUpperFin_exists_isometric_interval
    {r R lam ε : ℝ}
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆ gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingCollarFiniteUpperFin r R lam ε) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → gluingCollarFiniteUpperFin r R lam ε,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  letI := gluingCollarFiniteUpperFin_completeSpace r R lam ε
  let m : gluingCollarFiniteUpperFin r R lam ε →
      gluingCollarFiniteUpperFin r R lam ε → gluingCollarFiniteUpperFin r R lam ε :=
    fun a b => (exists_subtype_hyperbolic_midpoint_cosh hconv a b).choose
  have hm : ∀ a b, dist a (m a b) = dist a b / 2 ∧
      dist (m a b) b = dist a b / 2 := by
    intro a b
    exact ⟨(exists_subtype_hyperbolic_midpoint_cosh hconv a b).choose_spec.1,
      (exists_subtype_hyperbolic_midpoint_cosh hconv a b).choose_spec.2.1⟩
  obtain ⟨γ, hγ⟩ := exists_midpoint_metric_path m hm x y
  exact metric_path_exists_isometric_interval γ hγ

namespace GluingCollarFiniteMetricBlockData

variable {r R lam ε : ℝ}
  [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]

/-- The actual left attachment inherits comparison from the already proved
block and the new slab; the seam interval is constructed in the native fin. -/
theorem attachLeft_exists_midpoint_cosh_all_test
    (hlam : 0 < lam)
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆ gluingCollarFiniteUpperFin r R lam ε)
    (B : GluingCollarFiniteMetricBlockData lam R)
    (hB : ∀ x y : B.Space, ∃ m : B.Space,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B.Space, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (x y : (B.attachLeft (r := r) (ε := ε)).Space) :
    ∃ m : (B.attachLeft (r := r) (ε := ε)).Space,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : (B.attachLeft (r := r) (ε := ε)).Space,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  letI := gluingCollarFiniteUpperFin_completeSpace r R lam ε
  exact metricGlue_exists_midpoint_cosh_all_test
    (B.left_isometry.comp (gluingCollarFiniteMetricGlueRight_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε) hB
    (gluingFinFermiRadialWindow_exists_midpoint_cosh_all_test hlam)
    (gluingCollarFiniteUpperFin_exists_isometric_interval hconv) x y

/-- The actual right attachment inherits comparison with the same native
complete fin and its existing reflected isometric seam embedding. -/
theorem attachRight_exists_midpoint_cosh_all_test
    (hlam : 0 < lam)
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆ gluingCollarFiniteUpperFin r R lam ε)
    (B : GluingCollarFiniteMetricBlockData lam R)
    (hB : ∀ x y : B.Space, ∃ m : B.Space,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B.Space, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (x y : (B.attachRight (r := r) (ε := ε)).Space) :
    ∃ m : (B.attachRight (r := r) (ε := ε)).Space,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : (B.attachRight (r := r) (ε := ε)).Space,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  letI := gluingCollarFiniteUpperFin_completeSpace r R lam ε
  exact metricGlue_exists_midpoint_cosh_all_test
    (B.right_isometry.comp (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε))
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) hB
    (gluingFinFermiRadialWindow_exists_midpoint_cosh_all_test hlam)
    (gluingCollarFiniteUpperFin_exists_isometric_interval hconv) x y

end GluingCollarFiniteMetricBlockData

/-- Every genuine symmetric finite Fermi block has all-test midpoint-cosh
comparison. The block comparison is proved inductively, not supplied as an
assumption; the native fin convexity is the only gluing curvature input. -/
theorem gluingCollarFiniteMetricBlockSpace_exists_midpoint_cosh_all_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆ gluingCollarFiniteUpperFin r R lam ε)
    (n : ℕ) (x y : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n) :
    ∃ m : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : gluingCollarFiniteMetricBlockSpace (r := r) (ε := ε) hR hlam n,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  letI := gluingCollarFiniteUpperFin_nonempty (r := r) (ε := ε) hR hlam
  induction n with
  | zero => exact gluingFinFermiRadialWindow_exists_midpoint_cosh_all_test hlam x y
  | succ n ih =>
      exact GluingCollarFiniteMetricBlockData.attachRight_exists_midpoint_cosh_all_test
        hlam hconv
        ((gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n).attachLeft
          (r := r) (ε := ε))
        (GluingCollarFiniteMetricBlockData.attachLeft_exists_midpoint_cosh_all_test
          hlam hconv (gluingCollarFiniteMetricBlockData (r := r) (ε := ε) hR hlam n) ih) x y

/-- All-test comparison passes to the actual metric inductive limit of the
original symmetric blocks. This does not identify that limit with the
whole-chain path quotient; that independent distance bridge is still needed. -/
theorem gluingCollarFiniteMetricBlockInductiveLimit_exists_midpoint_cosh_all_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆ gluingCollarFiniteUpperFin r R lam ε)
    (x y : Metric.InductiveLimit
      (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam)) :
    ∃ m, dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y) := by
  exact exists_midpoint_cosh_all_test_inductiveLimit
    (gluingCollarFiniteMetricBlockInclusion_isometry (r := r) (ε := ε) hR hlam)
    (gluingCollarFiniteMetricBlockSpace_exists_midpoint_cosh_all_test hR hlam hconv) x y

#print axioms gluingFinFermiRadialWindow_exists_midpoint_cosh_all_test
#print axioms gluingCollarFiniteUpperFin_exists_isometric_interval
#print axioms gluingCollarFiniteMetricBlockSpace_exists_midpoint_cosh_all_test
#print axioms gluingCollarFiniteMetricBlockInductiveLimit_exists_midpoint_cosh_all_test

end SystolicGrowth
