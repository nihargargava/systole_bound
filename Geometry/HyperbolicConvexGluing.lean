module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainCAT
public import Geometry.MetricGluingGeodesics

@[expose] public section

/-!
# Comparison for two hyperbolic planes glued along a complete convex seam

This generalizes the checked hyperbolic distance-support argument, not the
gluing theorem for arbitrary comparison spaces. The two-plane model is the
comparison target needed for triangle inheritance. Its actual metric quotient
and genuine minimizing segments are retained throughout.
-/

open Set

namespace SystolicGrowth.HyperbolicConvexGlue

abbrev Carrier (S : Set UpperHalfPlane) [Nonempty S] :=
  Metric.GlueSpace (isometry_subtype_coe : Isometry (Subtype.val : S → UpperHalfPlane))
    (isometry_subtype_coe : Isometry (Subtype.val : S → UpperHalfPlane))

noncomputable abbrev left (S : Set UpperHalfPlane) [Nonempty S] : UpperHalfPlane → Carrier S :=
  Metric.toGlueL isometry_subtype_coe isometry_subtype_coe

noncomputable abbrev right (S : Set UpperHalfPlane) [Nonempty S] : UpperHalfPlane → Carrier S :=
  Metric.toGlueR isometry_subtype_coe isometry_subtype_coe

variable {S : Set UpperHalfPlane} [Nonempty S]

theorem left_isometry : Isometry (left S) :=
  Metric.toGlueL_isometry isometry_subtype_coe isometry_subtype_coe

theorem right_isometry : Isometry (right S) :=
  Metric.toGlueR_isometry isometry_subtype_coe isometry_subtype_coe

theorem commute (q : S) : left S q.1 = right S q.1 :=
  congrFun (Metric.toGlue_commute isometry_subtype_coe isometry_subtype_coe) q

theorem cross_dist (x y : UpperHalfPlane) :
    dist (left S x) (right S y) = ⨅ q : S, dist x q.1 + dist y q.1 :=
  metricGlue_cross_dist_eq_iInf isometry_subtype_coe isometry_subtype_coe x y

theorem cross_dist_swap (x y : UpperHalfPlane) :
    dist (left S x) (right S y) = dist (left S y) (right S x) := by
  rw [cross_dist, cross_dist]
  congr 1
  funext q
  exact add_comm _ _

variable [CompleteSpace S]

/-- Actual minimizing seam routes give an ambient lower distance support,
exact at the specified point of the left plane. -/
theorem exists_left_distance_support
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x y : UpperHalfPlane) :
    ∃ v : UpperHalfPlane, dist v x = dist (left S x) (right S y) ∧
      ∀ w : UpperHalfPlane, dist v w ≤ dist (left S w) (right S y) := by
  obtain ⟨q, hq⟩ := metricGlue_cross_dist_attained
    (isometry_subtype_coe : Isometry (Subtype.val : S → UpperHalfPlane))
    isometry_subtype_coe x y
  change dist (left S x) (right S y) = dist x q.1 + dist q.1 y at hq
  have hvariation : ∀ w ∈ S,
      0 ≤ geodInterpDistanceForwardDerivative q.1 w x +
        geodInterpDistanceForwardDerivative q.1 w y := by
    intro w hw
    apply geodInterp_distance_forward_derivative_sum_nonneg_of_minimizing
    intro t ht
    let p : S := ⟨Vendored.RiemannDynamics.geodInterp q.1 w t,
      hconv q.1 q.2 w hw (Vendored.RiemannDynamics.geodInterp_mem_geodSeg _ _ ht)⟩
    have htri := dist_triangle (left S x) (left S p.1) (right S y)
    rw [left_isometry.dist_eq, commute p, right_isometry.dist_eq, hq] at htri
    simpa only [p, dist_comm q.1 y, dist_comm (Vendored.RiemannDynamics.geodInterp q.1 w t) y]
      using htri
  obtain ⟨v, hv, hsupport⟩ :=
    exists_hyperbolic_broken_geodesic_distance_support S q.1 x y hvariation
  refine ⟨v, ?_, ?_⟩
  · rw [hq]
    simpa only [dist_comm q.1 x] using hv
  · intro w
    rw [cross_dist]
    apply le_ciInf
    intro p
    calc
      dist v w ≤ dist v p.1 + dist p.1 w := dist_triangle _ _ _
      _ ≤ dist y p.1 + dist p.1 w := add_le_add (hsupport p.1 p.2) le_rfl
      _ = dist w p.1 + dist y p.1 := by rw [dist_comm p.1 w, add_comm]

private theorem support_left_all
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x : UpperHalfPlane) (z : Carrier S) :
    ∃ v : UpperHalfPlane, dist v x = dist (left S x) z ∧
      ∀ w : UpperHalfPlane, dist v w ≤ dist (left S w) z := by
  induction z using Quotient.inductionOn with
  | h z =>
    cases z with
    | inl y =>
      refine ⟨y, ?_, ?_⟩
      · change dist y x = dist (left S x) (left S y)
        rw [left_isometry.dist_eq, dist_comm]
      · intro w
        change dist y w ≤ dist (left S w) (left S y)
        rw [left_isometry.dist_eq, dist_comm]
    | inr y => exact exists_left_distance_support hconv x y

private theorem support_right_all
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x : UpperHalfPlane) (z : Carrier S) :
    ∃ v : UpperHalfPlane, dist v x = dist (right S x) z ∧
      ∀ w : UpperHalfPlane, dist v w ≤ dist (right S w) z := by
  induction z using Quotient.inductionOn with
  | h z =>
    cases z with
    | inl y =>
      obtain ⟨v, hv, hbound⟩ := exists_left_distance_support hconv x y
      refine ⟨v, ?_, ?_⟩
      · change dist v x = dist (right S x) (left S y)
        rw [dist_comm (right S x) (left S y), cross_dist_swap y x]
        exact hv
      · intro w
        change dist v w ≤ dist (right S w) (left S y)
        rw [dist_comm (right S w) (left S y), cross_dist_swap y w]
        exact hbound w
    | inr y =>
      refine ⟨y, ?_, ?_⟩
      · change dist y x = dist (right S x) (right S y)
        rw [right_isometry.dist_eq, dist_comm]
      · intro w
        change dist y w ≤ dist (right S w) (right S y)
        rw [right_isometry.dist_eq, dist_comm]

private theorem plane_midpoint_of_support
    {M : Type*} [MetricSpace M] (F : UpperHalfPlane → M) (hF : Isometry F)
    (hsupport : ∀ x z, ∃ v : UpperHalfPlane, dist v x = dist (F x) z ∧
      ∀ w : UpperHalfPlane, dist v w ≤ dist (F w) z)
    (x y : UpperHalfPlane) :
    ∃ m : M, dist (F x) m = dist (F x) (F y) / 2 ∧
      dist m (F y) = dist (F x) (F y) / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist (F x) (F y) / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z (F x)) + Real.cosh (dist z (F y)) := by
  obtain ⟨p, hxp, hpy, hp⟩ := exists_hyperbolic_midpoint_cosh x y
  refine ⟨F p, ?_, ?_, ?_⟩
  · simpa only [hF.dist_eq] using hxp
  · simpa only [hF.dist_eq] using hpy
  · intro z
    obtain ⟨v, hvp, hbound⟩ := hsupport p z
    have hcosh (w : UpperHalfPlane) :
        Real.cosh (dist v w) ≤ Real.cosh (dist z (F w)) := by
      apply Real.cosh_le_cosh.mpr
      simpa only [abs_of_nonneg dist_nonneg, dist_comm (F w) z] using hbound w
    rw [hF.dist_eq, dist_comm z (F p), ← hvp]
    exact (hp v).le.trans (add_le_add (hcosh x) (hcosh y))

private theorem plane_cross_midpoint_copy_test
    {M : Type*} [MetricSpace M] (F : UpperHalfPlane → M) (hF : Isometry F)
    (x p : UpperHalfPlane) (y : M)
    (hsupport : ∃ v : UpperHalfPlane, dist v x = dist (F x) y ∧
      ∀ w : UpperHalfPlane, dist v w ≤ dist (F w) y)
    (hxp : dist (F x) (F p) = dist (F x) y / 2)
    (hpy : dist (F p) y = dist (F x) y / 2) :
    ∀ z : UpperHalfPlane,
      2 * Real.cosh (dist (F x) y / 2) * Real.cosh (dist (F z) (F p)) ≤
        Real.cosh (dist (F z) (F x)) + Real.cosh (dist (F z) y) := by
  obtain ⟨v, hvx, hbound⟩ := hsupport
  have hxp' : dist x p = dist (F x) y / 2 := by simpa only [hF.dist_eq] using hxp
  have hvp_le : dist v p ≤ dist (F x) y / 2 := (hbound p).trans hpy.le
  have hvp_ge : dist (F x) y / 2 ≤ dist v p := by
    have htri := dist_triangle v p x
    rw [hvx, dist_comm p x, hxp'] at htri
    linarith only [htri]
  have hpv : dist p v = dist x v / 2 := by
    rw [dist_comm p v, dist_comm x v, hvx]
    exact le_antisymm hvp_le hvp_ge
  have hxp_model : dist x p = dist x v / 2 := by rw [dist_comm x v, hvx]; exact hxp'
  intro z
  have hcosh : Real.cosh (dist z v) ≤ Real.cosh (dist (F z) y) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, dist_comm z v] using hbound z
  rw [hF.dist_eq, hF.dist_eq]
  calc
    _ = Real.cosh (dist z x) + Real.cosh (dist z v) := by
      have h := hyperbolic_midpoint_cosh hxp_model hpv z
      rw [dist_comm x v, hvx] at h
      exact h
    _ ≤ _ := add_le_add le_rfl hcosh

/-- Same-copy endpoint pairs satisfy comparison against all quotient tests. -/
theorem left_midpoint_cosh_all_test
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x y : UpperHalfPlane) :
    ∃ m : Carrier S, dist (left S x) m = dist (left S x) (left S y) / 2 ∧
      dist m (left S y) = dist (left S x) (left S y) / 2 ∧
      ∀ z : Carrier S, 2 * Real.cosh (dist (left S x) (left S y) / 2) *
        Real.cosh (dist z m) ≤
          Real.cosh (dist z (left S x)) + Real.cosh (dist z (left S y)) :=
  plane_midpoint_of_support (left S) left_isometry (support_left_all hconv) x y

theorem right_midpoint_cosh_all_test
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x y : UpperHalfPlane) :
    ∃ m : Carrier S, dist (right S x) m = dist (right S x) (right S y) / 2 ∧
      dist m (right S y) = dist (right S x) (right S y) / 2 ∧
      ∀ z : Carrier S, 2 * Real.cosh (dist (right S x) (right S y) / 2) *
        Real.cosh (dist z m) ≤
          Real.cosh (dist z (right S x)) + Real.cosh (dist z (right S y)) :=
  plane_midpoint_of_support (right S) right_isometry (support_right_all hconv) x y

/-- A midpoint in the common seam is represented in both planes, giving
comparison against every test in either plane. -/
theorem common_seam_midpoint_cosh
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x y : UpperHalfPlane) (q : S)
    (hxq : dist (left S x) (left S q.1) = dist (left S x) (right S y) / 2)
    (hqy : dist (left S q.1) (right S y) = dist (left S x) (right S y) / 2) :
    ∀ z : Carrier S,
      2 * Real.cosh (dist (left S x) (right S y) / 2) *
        Real.cosh (dist z (left S q.1)) ≤
          Real.cosh (dist z (left S x)) + Real.cosh (dist z (right S y)) := by
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
    cases z with
    | inl w =>
      exact plane_cross_midpoint_copy_test (left S) left_isometry x q.1 (right S y)
        (support_left_all hconv x _) hxq hqy w
    | inr w =>
      have hyq : dist (right S y) (right S q.1) = dist (right S y) (left S x) / 2 := by
        rw [← commute q, dist_comm (right S y) (left S q.1), dist_comm (right S y) (left S x)]
        exact hqy
      have hqx : dist (right S q.1) (left S x) = dist (right S y) (left S x) / 2 := by
        rw [← commute q, dist_comm (left S q.1) (left S x), dist_comm (right S y) (left S x)]
        exact hxq
      have h := plane_cross_midpoint_copy_test (right S) right_isometry y q.1 (left S x)
        (support_right_all hconv y _) hyq hqx w
      rw [← commute q, dist_comm (right S y) (left S x), add_comm] at h
      exact h

private theorem plane_segments (x y : UpperHalfPlane) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → UpperHalfPlane,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
        σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  let m : UpperHalfPlane → UpperHalfPlane → UpperHalfPlane :=
    fun a b => (exists_hyperbolic_midpoint_cosh a b).choose
  have hm : ∀ a b, dist a (m a b) = dist a b / 2 ∧
      dist (m a b) b = dist a b / 2 := by
    intro a b
    exact ⟨(exists_hyperbolic_midpoint_cosh a b).choose_spec.1,
      (exists_hyperbolic_midpoint_cosh a b).choose_spec.2.1⟩
  obtain ⟨γ, hγ⟩ := exists_midpoint_metric_path m hm x y
  exact metric_path_exists_isometric_interval γ hγ

/-- Cross-copy endpoints have an actual all-test comparison midpoint.
Local comparison on both copied legs and at their common join propagates
along the same attained minimizing interval. -/
theorem cross_exists_midpoint_cosh_all_test
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x y : UpperHalfPlane) :
    ∃ m : Carrier S, dist (left S x) m = dist (left S x) (right S y) / 2 ∧
      dist m (right S y) = dist (left S x) (right S y) / 2 ∧
      ∀ z : Carrier S, 2 * Real.cosh (dist (left S x) (right S y) / 2) *
        Real.cosh (dist z m) ≤
          Real.cosh (dist z (left S x)) + Real.cosh (dist z (right S y)) := by
  let d := dist (left S x) (right S y)
  by_cases hd0 : d = 0
  · have hxy : left S x = right S y := dist_eq_zero.mp hd0
    refine ⟨left S x, ?_, ?_, ?_⟩
    · change dist (left S x) (left S x) = d / 2
      simp [hd0]
    · change dist (left S x) (right S y) = d / 2
      simp [hxy, d]
    · intro z
      change 2 * Real.cosh (d / 2) * Real.cosh (dist z (left S x)) ≤ _
      rw [hd0, hxy]
      simp only [zero_div, Real.cosh_zero, mul_one]
      exact (two_mul _).le
  · have hd : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd0)
    obtain ⟨q, _, τ, σ, hσ, hσ0, hσ1, _, hσjoin, hσleft, hσright⟩ :=
      metricGlue_cross_exists_twoLeg_isometric_segment
        (isometry_subtype_coe : Isometry (Subtype.val : S → UpperHalfPlane))
        isometry_subtype_coe plane_segments plane_segments x y
    obtain ⟨γ, hcont, hγon, hdist, hγ0, hγ1, hγjoin⟩ :=
      exists_unit_parameter_path_of_isometric_interval hd σ hσ τ
    let s := τ.1 / d
    have hs : s ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg τ.2.1 hd.le, (div_le_one hd).mpr τ.2.2⟩
    have hstart : γ 0 = left S x := hγ0.trans hσ0
    have hfinish : γ 1 = right S y := hγ1.trans hσ1
    have hjoinpoint : γ s = left S q.1 := hγjoin.trans hσjoin
    have hleft : ∀ t ∈ Icc (0 : ℝ) s, γ t ∈ range (left S) := by
      intro t ht
      rw [hγon t ⟨ht.1, ht.2.trans hs.2⟩]
      apply hσleft
      have hts : t ≤ τ.1 / d := ht.2
      simpa only [mul_comm] using (le_div_iff₀ hd).mp hts
    have hright : ∀ t ∈ Icc s (1 : ℝ), γ t ∈ range (right S) := by
      intro t ht
      rw [hγon t ⟨hs.1.trans ht.1, ht.2⟩]
      apply hσright
      have hst : τ.1 / d ≤ t := ht.1
      simpa only [mul_comm] using (div_le_iff₀ hd).mp hst
    have hA : ∀ a ∈ range (left S), ∀ b ∈ range (left S),
        ∃ m : Carrier S, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
          ∀ z : Carrier S, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist z m) ≤
            Real.cosh (dist z a) + Real.cosh (dist z b) := by
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
      exact left_midpoint_cosh_all_test hconv a' b'
    have hB : ∀ a ∈ range (right S), ∀ b ∈ range (right S),
        ∃ m : Carrier S, dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
          ∀ z : Carrier S, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist z m) ≤
            Real.cosh (dist z a) + Real.cosh (dist z b) := by
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩
      exact right_midpoint_cosh_all_test hconv a' b'
    have hjoin : ∀ a ∈ range (left S), ∀ b ∈ range (right S),
        dist a (γ s) = dist a b / 2 → dist (γ s) b = dist a b / 2 →
        ∀ z : Carrier S, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist z (γ s)) ≤
          Real.cosh (dist z a) + Real.cosh (dist z b) := by
      rintro a ⟨a', rfl⟩ b ⟨b', rfl⟩ ham hmb
      rw [hjoinpoint] at ham hmb ⊢
      exact common_seam_midpoint_cosh hconv a' b' q ham hmb
    have hcomparison := cosh_midpoint_comparison_of_split_metric_path
      hd γ hcont.continuousOn hdist hs (range (left S)) (range (right S))
        hleft hright hA hB hjoin
    have hxm : dist (left S x) (γ (1 / 2)) = d / 2 := by
      rw [← hstart, hdist 0 (by norm_num) (1 / 2) (by norm_num)]
      norm_num
      ring
    have hmy : dist (γ (1 / 2)) (right S y) = d / 2 := by
      rw [← hfinish, hdist (1 / 2) (by norm_num) 1 (by norm_num)]
      norm_num
      ring
    refine ⟨γ (1 / 2), hxm, hmy, ?_⟩
    intro z
    have h := hcomparison z
    rw [hstart, hfinish] at h
    exact h

/-- The genuine two-plane convex-seam model satisfies comparison for all
endpoint pairs and all tests. This is not gluing arbitrary CAT pieces. -/
theorem exists_midpoint_cosh_all_test
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (x y : Carrier S) :
    ∃ m : Carrier S, dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : Carrier S, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y) := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      cases x with
      | inl x =>
        cases y with
        | inl y => exact left_midpoint_cosh_all_test hconv x y
        | inr y => exact cross_exists_midpoint_cosh_all_test hconv x y
      | inr x =>
        cases y with
        | inl y =>
          obtain ⟨m, hym, hmx, hcomp⟩ := cross_exists_midpoint_cosh_all_test hconv y x
          change ∃ m : Carrier S,
            dist (right S x) m = dist (right S x) (left S y) / 2 ∧
            dist m (left S y) = dist (right S x) (left S y) / 2 ∧
            ∀ z : Carrier S, 2 * Real.cosh (dist (right S x) (left S y) / 2) *
              Real.cosh (dist z m) ≤
                Real.cosh (dist z (right S x)) + Real.cosh (dist z (left S y))
          refine ⟨m, ?_, ?_, ?_⟩
          · simpa only [dist_comm m (right S x), dist_comm (left S y) (right S x)] using hmx
          · simpa only [dist_comm (left S y) m, dist_comm (left S y) (right S x)] using hym
          · intro z
            simpa only [dist_comm (right S x) (left S y), add_comm] using hcomp z
        | inr y => exact right_midpoint_cosh_all_test hconv x y

#print axioms exists_left_distance_support
#print axioms left_midpoint_cosh_all_test
#print axioms right_midpoint_cosh_all_test
#print axioms common_seam_midpoint_cosh
#print axioms exists_midpoint_cosh_all_test

end SystolicGrowth.HyperbolicConvexGlue
