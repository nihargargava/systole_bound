module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainComparison
public import Geometry.GluingCollarFinChainGeodesic
public import Geometry.MetricSplitPathCosh
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# All-point midpoint comparison for the actual finite-fin quotient

The attained two-leg path supplies one common junction. Same-copy comparison
holds on each leg and the junction is represented in both copies. The proved
scalar local-to-global theorem therefore gives the comparison against every
test point, including the formerly missing opposite-copy test case.
-/

open Set UpperHalfPlane
open scoped UpperHalfPlane

namespace SystolicGrowth

theorem exists_unit_parameter_path_of_isometric_interval
    {M : Type*} [MetricSpace M] {d : ℝ} (hd : 0 < d)
    (σ : Icc (0 : ℝ) d → M) (hσ : Isometry σ) (τ : Icc (0 : ℝ) d) :
    ∃ γ : ℝ → M, Continuous γ ∧
      (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
        γ t = σ ⟨d * t, ⟨mul_nonneg hd.le ht.1,
          by simpa using mul_le_mul_of_nonneg_left ht.2 hd.le⟩⟩) ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        dist (γ u) (γ v) = d * |u - v|) ∧
      γ 0 = σ ⟨0, ⟨le_rfl, hd.le⟩⟩ ∧
      γ 1 = σ ⟨d, ⟨hd.le, le_rfl⟩⟩ ∧
      γ (τ.1 / d) = σ τ := by
  let γ : ℝ → M := fun t => σ (projIcc 0 d hd.le (d * t))
  have hscale (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : d * t ∈ Icc (0 : ℝ) d :=
    ⟨mul_nonneg hd.le ht.1, by simpa using mul_le_mul_of_nonneg_left ht.2 hd.le⟩
  have hγon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ t = σ ⟨d * t, hscale t ht⟩ := by
    dsimp [γ]
    rw [projIcc_of_mem hd.le (hscale t ht)]
  refine ⟨γ, hσ.continuous.comp
      (continuous_projIcc.comp (continuous_const.mul continuous_id)), hγon, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    rw [hγon u hu, hγon v hv, hσ.dist_eq, Subtype.dist_eq, Real.dist_eq,
      show d * u - d * v = d * (u - v) by ring, abs_mul, abs_of_pos hd]
  · rw [hγon 0 (by norm_num)]
    congr 1
    exact Subtype.ext (mul_zero d)
  · rw [hγon 1 (by norm_num)]
    congr 1
    exact Subtype.ext (mul_one d)
  · have hs : τ.1 / d ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg τ.2.1 hd.le, (div_le_one hd).mpr τ.2.2⟩
    rw [hγon _ hs]
    congr 1
    apply Subtype.ext
    dsimp
    rw [mul_div_cancel₀ _ hd.ne']

/-- Every left/right endpoint pair has an actual metric midpoint satisfying
cosh comparison against every point of the quotient. The same attained seam
and its original two hyperbolic legs supply all local comparisons. -/
theorem gluingCollarFiniteMetricGlue_cross_exists_midpoint_cosh_all_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingFinFermiRadialWindow lam R) :
    let L := Metric.toGlueL
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    let Rg := Metric.toGlueR
      (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
      (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist (L x) m = dist (L x) (Rg y) / 2 ∧
      dist m (Rg y) = dist (L x) (Rg y) / 2 ∧
      ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
        2 * Real.cosh (dist (L x) (Rg y) / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z (L x)) + Real.cosh (dist z (Rg y)) := by
  dsimp
  let I := gluingCollarFiniteMetricGlueLeft r R lam ε
  let L := Metric.toGlueL
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let Rg := Metric.toGlueR
    (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
    (gluingCollarFiniteMetricGlueRight_isometry r R lam ε)
  let d := dist (L x) (Rg y)
  by_cases hd0 : d = 0
  · have hxy : L x = Rg y := dist_eq_zero.mp hd0
    refine ⟨L x, ?_, ?_, ?_⟩
    · change dist (L x) (L x) = d / 2
      simp [hd0]
    · change dist (L x) (Rg y) = d / 2
      simp [hxy, d]
    · intro z
      change 2 * Real.cosh (d / 2) * Real.cosh (dist z (L x)) ≤
        Real.cosh (dist z (L x)) + Real.cosh (dist z (Rg y))
      rw [hd0, hxy]
      simp only [zero_div, Real.cosh_zero, mul_one]
      exact (two_mul _).le
  · have hd : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    obtain ⟨q, _, τ, σ, hσ, hσ0, hσ1, _, hσjoin, hσleft, hσright⟩ :=
      gluingCollarFiniteMetricGlue_cross_exists_twoLeg_isometric_segment
        (r := r) (ε := ε) hR hlam x y
    obtain ⟨γ, hcont, hγon, hdist, hγ0, hγ1, hγjoin⟩ :=
      exists_unit_parameter_path_of_isometric_interval hd σ hσ τ
    let s := τ.1 / d
    have hs : s ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg τ.2.1 hd.le, (div_le_one hd).mpr τ.2.2⟩
    have hstart : γ 0 = L x := hγ0.trans hσ0
    have hfinish : γ 1 = Rg y := hγ1.trans hσ1
    have hjoinpoint : γ s = L (I q) := hγjoin.trans hσjoin
    have hleft : ∀ t ∈ Icc (0 : ℝ) s, γ t ∈ Set.range L := by
      intro t ht
      rw [hγon t ⟨ht.1, ht.2.trans hs.2⟩]
      apply hσleft
      have hts : t ≤ τ.1 / d := ht.2
      simpa only [mul_comm] using (le_div_iff₀ hd).mp hts
    have hright : ∀ t ∈ Icc s (1 : ℝ), γ t ∈ Set.range Rg := by
      intro t ht
      rw [hγon t ⟨hs.1.trans ht.1, ht.2⟩]
      apply hσright
      have hst : τ.1 / d ≤ t := ht.1
      simpa only [mul_comm] using (div_le_iff₀ hd).mp hst
    have hA : ∀ a ∈ Set.range L, ∀ b ∈ Set.range L,
        ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
          dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
          ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
            2 * Real.cosh (dist a b / 2) * Real.cosh (dist z m) ≤
              Real.cosh (dist z a) + Real.cosh (dist z b) := by
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
      exact gluingCollarFiniteMetricGlue_left_midpoint_cosh_all_test hR hlam hconv a' b'
    have hB : ∀ a ∈ Set.range Rg, ∀ b ∈ Set.range Rg,
        ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
          dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
          ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
            2 * Real.cosh (dist a b / 2) * Real.cosh (dist z m) ≤
              Real.cosh (dist z a) + Real.cosh (dist z b) := by
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
      exact gluingCollarFiniteMetricGlue_right_midpoint_cosh_all_test hR hlam hconv a' b'
    have hjoin : ∀ a ∈ Set.range L, ∀ b ∈ Set.range Rg,
        dist a (γ s) = dist a b / 2 → dist (γ s) b = dist a b / 2 →
        ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
          2 * Real.cosh (dist a b / 2) * Real.cosh (dist z (γ s)) ≤
            Real.cosh (dist z a) + Real.cosh (dist z b) := by
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩ ham hmb
      have h := gluingCollarFiniteMetricGlue_cross_midpoint_cosh_all_test_of_commonFin_midpoint
        hR hlam hconv a' b' q
      rw [hjoinpoint] at ham hmb ⊢
      exact h ham hmb
    have hcomparison := cosh_midpoint_comparison_of_split_metric_path
      hd γ hcont.continuousOn hdist hs (Set.range L) (Set.range Rg) hleft hright hA hB hjoin
    have hxm : dist (L x) (γ (1 / 2)) = d / 2 := by
      rw [← hstart, hdist 0 (by norm_num) (1 / 2) (by norm_num)]
      norm_num
      ring
    have hmy : dist (γ (1 / 2)) (Rg y) = d / 2 := by
      rw [← hfinish, hdist (1 / 2) (by norm_num) 1 (by norm_num)]
      norm_num
      ring
    refine ⟨γ (1 / 2), hxm, hmy, ?_⟩
    intro z
    have h := hcomparison z
    rw [hstart, hfinish] at h
    exact h

/-- Every pair of points of the actual finite-fin metric quotient admits a
midpoint satisfying hyperbolic cosh comparison against every test point. -/
theorem gluingCollarFiniteMetricGlueSpace_exists_midpoint_cosh_all_test
    {r R lam ε : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (x y : gluingCollarFiniteMetricGlueSpace r R lam ε) :
    ∃ m : gluingCollarFiniteMetricGlueSpace r R lam ε,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : gluingCollarFiniteMetricGlueSpace r R lam ε,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  refine Quotient.inductionOn x ?_
  intro px
  refine Quotient.inductionOn y ?_
  intro py
  cases px with
  | inl xl =>
    cases py with
    | inl yl =>
      exact gluingCollarFiniteMetricGlue_left_midpoint_cosh_all_test hR hlam hconv xl yl
    | inr yr =>
      exact gluingCollarFiniteMetricGlue_cross_exists_midpoint_cosh_all_test hR hlam hconv xl yr
  | inr xr =>
    cases py with
    | inl yl =>
      obtain ⟨m, hym, hmx, hcomparison⟩ :=
        gluingCollarFiniteMetricGlue_cross_exists_midpoint_cosh_all_test
          (r := r) (ε := ε) hR hlam hconv yl xr
      refine ⟨m, ?_, ?_, ?_⟩
      · change dist (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr) m =
            dist (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr)
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) / 2
        simpa only [dist_comm] using hmx
      · change dist m (Metric.toGlueL
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) =
            dist (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr)
              (Metric.toGlueL
                (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
                (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) / 2
        simpa only [dist_comm] using hym
      · intro z
        have h := hcomparison z
        change 2 * Real.cosh (dist (Metric.toGlueR
          (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
          (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr)
          (Metric.toGlueL
            (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
            (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl) / 2) *
          Real.cosh (dist z m) ≤
            Real.cosh (dist z (Metric.toGlueR
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) xr)) +
            Real.cosh (dist z (Metric.toGlueL
              (gluingCollarFiniteMetricGlueLeft_isometry r R lam ε)
              (gluingCollarFiniteMetricGlueRight_isometry r R lam ε) yl))
        simpa only [dist_comm, add_comm] using h
    | inr yr =>
      exact gluingCollarFiniteMetricGlue_right_midpoint_cosh_all_test hR hlam hconv xr yr

#print axioms gluingCollarFiniteMetricGlue_cross_exists_midpoint_cosh_all_test
#print axioms gluingCollarFiniteMetricGlueSpace_exists_midpoint_cosh_all_test

/-- Full hyperbolic comparison along any actual constant-speed segment in the
finite-fin quotient. The midpoint family is proved above for this quotient,
not supplied as an additional comparison hypothesis. -/
theorem gluingCollarFiniteMetricGlueSpace_cosh_sinh_interpolation_along_metric_path
    {r R lam ε D : ℝ} (hR : 0 ≤ R) (hlam : 0 < lam)
    [Nonempty (gluingCollarFiniteUpperFin r R lam ε)]
    (hconv : ∀ a ∈ gluingCollarFiniteUpperFin r R lam ε,
      ∀ b ∈ gluingCollarFiniteUpperFin r R lam ε,
        Vendored.RiemannDynamics.geodSeg a b ⊆
          gluingCollarFiniteUpperFin r R lam ε)
    (hD : 0 < D) (γ : ℝ → gluingCollarFiniteMetricGlueSpace r R lam ε)
    (hcont : ContinuousOn γ (Icc 0 1))
    (hdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) = D * |u - v|) :
    ∀ (z : gluingCollarFiniteMetricGlueSpace r R lam ε) (t : ℝ),
      t ∈ Icc (0 : ℝ) 1 →
      Real.sinh D * Real.cosh (dist z (γ t)) ≤
        Real.sinh ((1 - t) * D) * Real.cosh (dist z (γ 0)) +
          Real.sinh (t * D) * Real.cosh (dist z (γ 1)) := by
  exact cosh_sinh_interpolation_of_metric_path hD
    (gluingCollarFiniteMetricGlueSpace_exists_midpoint_cosh_all_test hR hlam hconv)
    γ hcont hdist

#print axioms gluingCollarFiniteMetricGlueSpace_cosh_sinh_interpolation_along_metric_path

/-- The actual dyadic finite gluing models eventually satisfy all-point
midpoint comparison. Positivity, fin nonemptiness and convexity are obtained
from the model rather than imposed as further hypotheses. -/
theorem eventually_gluingCollarFiniteMetricGlueSpace_midpoint_cosh_all_test
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ hne : Nonempty (gluingCollarFiniteUpperFin r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)),
      letI := hne
      ∀ x y : gluingCollarFiniteMetricGlueSpace r R
          (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
        ∃ m : gluingCollarFiniteMetricGlueSpace r R
            (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
          dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
          ∀ z : gluingCollarFiniteMetricGlueSpace r R
              (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n),
            2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
              Real.cosh (dist z x) + Real.cosh (dist z y) := by
  obtain ⟨N, hN, hconv⟩ := eventually_gluingCollarFiniteFins_geodSeg_subset hr hR
  refine ⟨N, hN, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := hN.trans hn
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn2
  have hlam : 0 < Real.sqrt (1 - (1 / 2 : ℝ) ^ n) := by
    apply Real.sqrt_pos.2
    norm_num at hpow
    nlinarith
  letI : Nonempty (gluingCollarFiniteUpperFin r R
      (Real.sqrt (1 - (1 / 2 : ℝ) ^ n)) ((1 / 2 : ℝ) ^ n)) :=
    gluingCollarFiniteUpperFin_nonempty hR hlam
  refine ⟨inferInstance, ?_⟩
  intro x y
  exact gluingCollarFiniteMetricGlueSpace_exists_midpoint_cosh_all_test hR hlam
    (fun a ha b hb => (hconv n hn).1 a b ha hb) x y

#print axioms eventually_gluingCollarFiniteMetricGlueSpace_midpoint_cosh_all_test

end SystolicGrowth
