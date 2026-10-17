module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarMetricBlockNativeConvergence
public import Geometry.GluingCollarFiniteMetricBlockComparison
public import Geometry.GluingCollarModelProper
public import Geometry.MetricMidpointComparisonLimit

@[expose] public section

/-!
# Hyperbolic midpoint comparison in the original collar metric

Actual convex finite-block limits approximate each fixed native radial
window. Their genuine retractions and distance convergence transport the
all-test inequality to the proper native metric, without changing its
carrier or using the Euclidean coordinate metric. Larger windows then test
one fixed native midpoint against every point of the whole collar.
-/

open Set Filter
open scoped Topology

namespace SystolicGrowth

/-- Every fixed radial window has all-test midpoint-cosh comparison for the
restricted original collar metric. Approximating midpoints and retractions
are constructed in the actual finite-block metric limit. -/
theorem gluingCollarModelMetric_window_exists_midpoint_cosh_all_test
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (x y : {z : ℂ // z.re ∈ Icc (-R) R}) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    ∃ m : {z : ℂ // z.re ∈ Icc (-R) R},
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : {z : ℂ // z.re ∈ Icc (-R) R},
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  letI := gluingCollarModelMetric_window_properSpace hr R
  obtain ⟨N, hN, hconv⟩ := eventually_gluingCollarFiniteFins_geodSeg_subset hr hR
  let ε : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (N + n)
  have hεpos (n : ℕ) : 0 < ε n := pow_pos (by norm_num) _
  have hεlt (n : ℕ) : ε n < 1 := by
    have hn : 2 ≤ N + n := by omega
    have hpow : (1 / 2 : ℝ) ^ (N + n) ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    norm_num at hpow
    exact hpow.trans_lt (by norm_num)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa only [ε, pow_add, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ) ^ N)
        atTop (𝓝 ((1 / 2 : ℝ) ^ N))).mul hp
  let lam : ℕ → ℝ := fun n => Real.sqrt (1 - ε n)
  have hlam (n : ℕ) : 0 < lam n := Real.sqrt_pos.mpr (sub_pos.mpr (hεlt n))
  let T : ℕ → Type := fun n =>
    gluingCollarFiniteMetricBlockLimit (r := r) (ε := ε n) hR (hlam n)
  let F : ∀ n, {z : ℂ // z.re ∈ Icc (-R) R} → T n := fun n =>
    gluingCollarFiniteMetricBlockNativeForward (r := r) hR (hlam n) (hεpos n) 0
  let G : ∀ n, T n → {z : ℂ // z.re ∈ Icc (-R) R} := fun n =>
    gluingCollarFiniteMetricBlockNativeRetraction hr hR (hlam n) (hεpos n).le 0
  let B : ℕ → ℝ := fun n => (1 + ε n * Real.cosh (|r| + R)) ^ 2 / lam n
  have hBpos (n : ℕ) : 0 < B n :=
    gluingCollarMetricBlock_distortion_pos (hεpos n).le (hlam n)
  have hBlim : Tendsto B atTop (𝓝 1) :=
    gluingCollarMetricBlock_distortion_tendsto r R ε hεlim
  have hinv (n : ℕ) (a : {z : ℂ // z.re ∈ Icc (-R) R}) : G n (F n a) = a :=
    gluingCollarFiniteMetricBlockNativeRetraction_forward hr hR (hlam n) (hεpos n) 0 a
  have hG (n : ℕ) (p q : T n) : dist (G n p) (G n q) ≤ B n * dist p q :=
    gluingCollarFiniteMetricBlockNativeRetraction_dist_le hr hR (hlam n) (hεpos n).le 0 p q
  have happrox (a b : {z : ℂ // z.re ∈ Icc (-R) R}) :
      Tendsto (fun n => dist (F n a) (F n b)) atTop (𝓝 (dist a b)) :=
    gluingCollarFiniteMetricBlockNativeForward_dist_tendsto (c := 0)
      hr hR ε hεpos hεlt hεlim a b
  have hmid (n : ℕ) (a b : T n) :
      ∃ m : T n, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
      ∀ z : T n, 2 * Real.cosh ((1 : ℝ) * dist a b / 2) *
        Real.cosh ((1 : ℝ) * dist z m) ≤
          Real.cosh ((1 : ℝ) * dist z a) + Real.cosh ((1 : ℝ) * dist z b) := by
    have hupper := (hconv (N + n) (by omega)).1
    have hc : ∀ p ∈ gluingCollarFiniteUpperFin r R (lam n) (ε n),
        ∀ q ∈ gluingCollarFiniteUpperFin r R (lam n) (ε n),
          Vendored.RiemannDynamics.geodSeg p q ⊆
            gluingCollarFiniteUpperFin r R (lam n) (ε n) :=
      fun p hp q hq => hupper p q hp hq
    simpa only [one_mul] using
      gluingCollarFiniteMetricBlockInductiveLimit_exists_midpoint_cosh_all_test hR (hlam n) hc a b
  exact @exists_midpoint_cosh_all_test_of_proper_retract_metric_limit
    {z : ℂ // z.re ∈ Icc (-R) R} inferInstance
    (gluingCollarModelMetric_window_properSpace hr R) T (fun _ => inferInstance)
    F G B (fun _ => 1)
    hBpos (fun _ => by norm_num) hBlim tendsto_const_nhds hinv hG happrox hmid x y

/-- The entire original collar has a midpoint chosen independently of its
test point. Larger native windows test that same midpoint via uniqueness. -/
theorem gluingCollarModelMetric_exists_midpoint_cosh_all_test
    {r : ℝ} (hr : 0 < r) (x y : ℂ) :
    letI := gluingCollarModelMetricSpace hr
    letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
    ∃ m : ℂ, dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : ℂ, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y) := by
  letI := gluingCollarModelMetricSpace hr
  letI := (gluingCollarModelMetricSpace hr).toPseudoMetricSpace
  let R₀ := max |x.re| |y.re|
  have hR₀ : 0 ≤ R₀ := (abs_nonneg x.re).trans (le_max_left _ _)
  have hx : x.re ∈ Icc (-R₀) R₀ := abs_le.mp (le_max_left _ _)
  have hy : y.re ∈ Icc (-R₀) R₀ := abs_le.mp (le_max_right _ _)
  obtain ⟨m, hxm, hmy, _⟩ := gluingCollarModelMetric_window_exists_midpoint_cosh_all_test
    hr hR₀ ⟨x, hx⟩ ⟨y, hy⟩
  refine ⟨m.1, hxm, hmy, ?_⟩
  intro z
  let R := max R₀ (max |m.1.re| |z.re|)
  have hR : 0 ≤ R := hR₀.trans (le_max_left _ _)
  have hxR : x.re ∈ Icc (-R) R :=
    abs_le.mp ((le_max_left |x.re| |y.re|).trans (le_max_left R₀ _))
  have hyR : y.re ∈ Icc (-R) R :=
    abs_le.mp ((le_max_right |x.re| |y.re|).trans (le_max_left R₀ _))
  have hmR : m.1.re ∈ Icc (-R) R :=
    abs_le.mp ((le_max_left |m.1.re| |z.re|).trans (le_max_right R₀ _))
  have hzR : z.re ∈ Icc (-R) R :=
    abs_le.mp ((le_max_right |m.1.re| |z.re|).trans (le_max_right R₀ _))
  have hcomparison := cosh_comparison_at_specified_midpoint
    (gluingCollarModelMetric_window_exists_midpoint_cosh_all_test hr hR ⟨x, hxR⟩ ⟨y, hyR⟩)
    (show dist (⟨x, hxR⟩ : {z : ℂ // z.re ∈ Icc (-R) R}) ⟨m.1, hmR⟩ =
      dist (⟨x, hxR⟩ : {z : ℂ // z.re ∈ Icc (-R) R}) ⟨y, hyR⟩ / 2 from hxm)
    (show dist (⟨m.1, hmR⟩ : {z : ℂ // z.re ∈ Icc (-R) R}) ⟨y, hyR⟩ =
      dist (⟨x, hxR⟩ : {z : ℂ // z.re ∈ Icc (-R) R}) ⟨y, hyR⟩ / 2 from hmy)
    ⟨z, hzR⟩
  exact hcomparison

#print axioms gluingCollarModelMetric_window_exists_midpoint_cosh_all_test
#print axioms gluingCollarModelMetric_exists_midpoint_cosh_all_test

end SystolicGrowth
