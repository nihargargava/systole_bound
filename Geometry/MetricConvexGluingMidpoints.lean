module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricConvexGluingModels
public import Geometry.MetricGluingSymmetry

@[expose] public section

/-!
# All-test midpoint comparison in general convex metric gluing

The two mixed-triangle inheritance steps bound the actual midpoint of a
fixed native side. The endpoint pair fixes that midpoint before any test
point is chosen; comparison triangles are used only to estimate distances.
-/

open Set

namespace SystolicGrowth

/-- Completeness and constructed exact midpoints give native geodesic
intervals. This uses the existing coherent dyadic-grid construction. -/
theorem metricMidpointCosh_exists_isometric_interval
    {M : Type*} [MetricSpace M] [CompleteSpace M]
    (hmid : ∀ x y : M, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y)) (x y : M) :
    ∃ α : Icc (0 : ℝ) (dist x y) → M, Isometry α ∧
      α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  let m : M → M → M := fun a b => (hmid a b).choose
  have hm : ∀ a b, dist a (m a b) = dist a b / 2 ∧
      dist (m a b) b = dist a b / 2 := fun a b =>
    ⟨(hmid a b).choose_spec.1, (hmid a b).choose_spec.2.1⟩
  obtain ⟨γ, hγ⟩ := exists_midpoint_metric_path m hm x y
  exact metric_path_exists_isometric_interval γ hγ

private theorem cosh_midpoint_le_of_model_bound
    {M : Type*} [MetricSpace M] (x y z m : M) (X Y Z : UpperHalfPlane)
    (hXY : dist X Y = dist x y) (hZX : dist Z X = dist z x)
    (hZY : dist Z Y = dist z y)
    (hbound : dist z m ≤
      dist Z (Vendored.RiemannDynamics.geodInterp X Y (1 / 2))) :
    2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
      Real.cosh (dist z x) + Real.cosh (dist z y) := by
  have hc : Real.cosh (dist z m) ≤
      Real.cosh (dist Z (Vendored.RiemannDynamics.geodInterp X Y (1 / 2))) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg] using hbound
  calc
    _ ≤ 2 * Real.cosh (dist x y / 2) *
        Real.cosh (dist Z (Vendored.RiemannDynamics.geodInterp X Y (1 / 2))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = Real.cosh (dist z x) + Real.cosh (dist z y) := by
      rw [← hXY, geodInterp_midpoint_cosh, hZX, hZY]

/-- Both sides of an actual mixed triangle have midpoint comparison against
its opposite vertex. The crossed midpoint is fixed by the supplied two legs;
the same-piece midpoint is fixed by the supplied original piece interval. -/
theorem metricGlue_mixed_triangle_midpoint_bounds
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [CompleteSpace A] [CompleteSpace B]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hB : ∀ x y : B, ∃ m : B,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hS : ∀ p q : S, ∃ σ : Icc (0 : ℝ) (dist p q) → S,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
        σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q)
    (p q : S) (x : A) (y z : B)
    (hmin : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y)
    (hminZ : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ z) =
      dist x (Φ p) + dist (Ψ p) z)
    (βA : Icc (0 : ℝ) (dist x (Φ q)) → A)
    (βB : Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (αZ : Icc (0 : ℝ) (dist y z) → B)
    (hβA : Isometry βA) (hβB : Isometry βB) (hαZ : Isometry αZ)
    (hβA0 : βA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hβA1 : βA ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩ = Φ q)
    (hβB0 : βB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ q)
    (hβB1 : βB ⟨dist (Ψ q) y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hαZ0 : αZ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = y)
    (hαZ1 : αZ ⟨dist y z, ⟨dist_nonneg, le_rfl⟩⟩ = z) :
    let L := Metric.toGlueL hΦ hΨ
    let R := Metric.toGlueR hΦ hΨ
    let m := metricTwoLegUnitPoint dist_nonneg dist_nonneg
      (L ∘ βA) (R ∘ βB) ⟨1 / 2, by norm_num⟩
    let n := R (αZ ⟨dist y z * (1 / 2), by constructor <;> linarith [dist_nonneg (x := y) (y := z)]⟩)
    (2 * Real.cosh (dist (L x) (R y) / 2) * Real.cosh (dist (R z) m) ≤
      Real.cosh (dist (R z) (L x)) + Real.cosh (dist (R z) (R y))) ∧
    (2 * Real.cosh (dist (R y) (R z) / 2) * Real.cosh (dist (L x) n) ≤
      Real.cosh (dist (L x) (R y)) + Real.cosh (dist (L x) (R z))) := by
  dsimp only
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hR : Isometry R := Metric.toGlueR_isometry hΦ hΨ
  obtain ⟨αA, hαA, hαA0, hαA1⟩ := metricMidpointCosh_exists_isometric_interval hA (Φ p) x
  obtain ⟨αB, hαB, hαB0, hαB1⟩ := metricMidpointCosh_exists_isometric_interval hB (Ψ p) y
  obtain ⟨βZ, hβZ, hβZ0, hβZ1⟩ := metricMidpointCosh_exists_isometric_interval hB (Ψ p) z
  obtain ⟨σ, hσ, hσ0, hσ1⟩ := hS p q
  obtain ⟨p', q', x', y', P, X, Y, Z, U, V, W, hpq, hpx, hxq, hpy, hqy,
      hPX, hPY, hXY, hYZ, hPZ, hUV, hUW, hVW⟩ :=
    exists_metricGlue_mixed_triangle_models hΦ hΨ p q x y z hmin hminZ
  let F := Sum.elim
    (L ∘ metricSplitLeftArcBoundary (Φ p) x (Φ q) x' q' hxq αA βA)
    (R ∘ metricSplitRightArcBoundary (Ψ p) (Ψ q) y q' y' hqy αB βB)
  let f := metricInheritedLeftBoundary q' x' y' P X F
  let g := R ∘ metricSplitRightArcBoundary y (Ψ p) z P Z hPZ αZ βZ
  have hb : ∀ u v, dist (Sum.elim f g u) (Sum.elim f g v) ≤
      dist (splitBoundaryParentModel P X Z U V W u)
        (splitBoundaryParentModel P X Z U V W v) :=
    metricGlue_mixed_triangle_boundary_comparison hΦ hΨ hA hB p q x y
      p' q' x' y' hpq hpx hxq hpy hqy αA βA αB βB σ
      hαA hβA hαB hβB hσ hαA0 hαA1 hβA0 hβA1 hαB0 hαB1 hβB0 hβB1
      hσ0 hσ1 hmin P X Y hPX hPY hXY z Z hYZ hPZ αZ βZ hαZ hβZ
      hαZ0 hαZ1 hβZ0 hβZ1 hminZ U V W hUV hUW hVW
  have hfhalf : f (.inl ⟨1 / 2, by norm_num⟩) =
      metricTwoLegUnitPoint dist_nonneg dist_nonneg (L ∘ βA) (R ∘ βB)
        ⟨1 / 2, by norm_num⟩ := by
    have hh := metricInheritedLeftBoundary_outer_eq_twoLeg hΦ hΨ p q x y
      q' x' y' P X hxq hqy αA βA αB βB ⟨1 / 2, by norm_num⟩
    have hre : metricBoundaryReverseUnit ⟨(1 / 2 : ℝ), by norm_num⟩ =
        ⟨1 / 2, by norm_num⟩ := Subtype.ext (by norm_num [metricBoundaryReverseUnit])
    simpa only [hre] using hh
  have hfend : f (.inl ⟨1, by norm_num⟩) = L x := by
    simp only [f, metricInheritedLeftBoundary, Sum.elim_inl, metricBoundaryReverseUnit,
      sub_self, splitBoundaryParentXYIndex_zero, F, Function.comp_apply,
      metricSplitLeftArcBoundary, Sum.elim_inr, hβA0]
  have hghalf : g (.inl ⟨1 / 2, by norm_num⟩) =
      R (αZ ⟨dist y z * (1 / 2), by constructor <;> linarith [dist_nonneg (x := y) (y := z)]⟩) := rfl
  have hgend : g (.inl ⟨1, by norm_num⟩) = R z := by
    dsimp only [g, Function.comp_apply, metricSplitRightArcBoundary, Sum.elim_inl]
    simpa only [mul_one] using congrArg R hαZ1
  have hUV' : dist U V = dist (L x) (R y) := by
    rw [hUV, dist_comm Y X, hXY, hxq, hqy]
    exact hmin.symm
  have hUW' : dist U W = dist (R y) (R z) := by rw [hUW, hYZ, hR.dist_eq]
  have hVW' : dist V W = dist (L x) (R z) := by
    rw [hVW, dist_comm X P, hPX, hpx, hPZ, dist_comm (Φ p) x]
    exact hminZ.symm
  constructor
  · apply cosh_midpoint_le_of_model_bound (L x) (R y) (R z) _ V U W
      (by rw [dist_comm V U]; exact hUV')
      (by rw [dist_comm W V]; exact hVW')
      (by rw [dist_comm W U, dist_comm (R z) (R y)]; exact hUW')
    have h := hb (.inr (.inl ⟨1, by norm_num⟩)) (.inl (.inl ⟨1 / 2, by norm_num⟩))
    simp only [Sum.elim_inl, Sum.elim_inr, hgend, hfhalf, splitBoundaryParentModel,
      Vendored.RiemannDynamics.geodInterp_one] at h
    have hrev : Vendored.RiemannDynamics.geodInterp V U (1 / 2) =
        Vendored.RiemannDynamics.geodInterp U V (1 / 2) := by
      simpa only [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num] using
        metricBoundaryGeodInterp_reverse_of_mem_Icc U V
          (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
    simpa only [hrev] using h
  · apply cosh_midpoint_le_of_model_bound (R y) (R z) (L x) _ U W V hUW'
      (by rw [dist_comm V U]; exact hUV') hVW'
    have h := hb (.inl (.inl ⟨1, by norm_num⟩)) (.inr (.inl ⟨1 / 2, by norm_num⟩))
    simpa only [Sum.elim_inl, Sum.elim_inr, hfend, hghalf, splitBoundaryParentModel,
      Vendored.RiemannDynamics.geodInterp_one] using h

private theorem isometric_interval_midpoint_distances
    {M : Type*} [MetricSpace M] (x y : M)
    (α : Icc (0 : ℝ) (dist x y) → M) (hα : Isometry α)
    (hα0 : α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hα1 : α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    let m := α ⟨dist x y * (1 / 2), by constructor <;> linarith [dist_nonneg (x := x) (y := y)]⟩
    dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 := by
  dsimp only
  constructor
  · have h := hα.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩
      ⟨dist x y * (1 / 2), by constructor <;> linarith [dist_nonneg (x := x) (y := y)]⟩
    rw [hα0] at h
    simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, mul_one_div,
      abs_of_nonneg (by positivity : 0 ≤ dist x y / 2)] using h
  · have h := hα.dist_eq
      ⟨dist x y * (1 / 2), by constructor <;> linarith [dist_nonneg (x := x) (y := y)]⟩
      ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩
    rw [hα1] at h
    simp only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (by linarith [dist_nonneg (x := x) (y := y)] :
        dist x y * (1 / 2) - dist x y ≤ 0)] at h
    convert h using 1
    ring

/-- Endpoints in the right original piece have one fixed native midpoint
against all points of the metric gluing, including the opposite copy. -/
theorem metricGlue_right_exists_midpoint_cosh_all_test
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [ProperSpace A] [CompleteSpace B] [CompleteSpace S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hB : ∀ x y : B, ∃ m : B,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hS : ∀ p q : S, ∃ σ : Icc (0 : ℝ) (dist p q) → S,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
        σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q)
    (y z : B) :
    ∃ m : Metric.GlueSpace hΦ hΨ,
      dist (Metric.toGlueR hΦ hΨ y) m =
        dist (Metric.toGlueR hΦ hΨ y) (Metric.toGlueR hΦ hΨ z) / 2 ∧
      dist m (Metric.toGlueR hΦ hΨ z) =
        dist (Metric.toGlueR hΦ hΨ y) (Metric.toGlueR hΦ hΨ z) / 2 ∧
      ∀ w : Metric.GlueSpace hΦ hΨ,
        2 * Real.cosh (dist (Metric.toGlueR hΦ hΨ y) (Metric.toGlueR hΦ hΨ z) / 2) *
          Real.cosh (dist w m) ≤ Real.cosh (dist w (Metric.toGlueR hΦ hΨ y)) +
            Real.cosh (dist w (Metric.toGlueR hΦ hΨ z)) := by
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hR : Isometry R := Metric.toGlueR_isometry hΦ hΨ
  obtain ⟨α, hα, hα0, hα1⟩ := metricMidpointCosh_exists_isometric_interval hB y z
  let n := α ⟨dist y z * (1 / 2), by constructor <;> linarith [dist_nonneg (x := y) (y := z)]⟩
  obtain ⟨hyn, hnz⟩ := isometric_interval_midpoint_distances y z α hα hα0 hα1
  refine ⟨R n, ?_, ?_, ?_⟩
  · change dist (R y) (R n) = dist (R y) (R z) / 2
    simpa only [hR.dist_eq] using hyn
  · change dist (R n) (R z) = dist (R y) (R z) / 2
    simpa only [hR.dist_eq] using hnz
  ·
    intro w
    induction w using Quotient.inductionOn with
    | h w =>
      cases w with
      | inl x =>
        obtain ⟨q, hq⟩ := metricGlue_cross_dist_attained hΦ hΨ x y
        obtain ⟨p, hp⟩ := metricGlue_cross_dist_attained hΦ hΨ x z
        obtain ⟨βA, hβA, hβA0, hβA1⟩ := metricMidpointCosh_exists_isometric_interval hA x (Φ q)
        obtain ⟨βB, hβB, hβB0, hβB1⟩ := metricMidpointCosh_exists_isometric_interval hB (Ψ q) y
        exact (metricGlue_mixed_triangle_midpoint_bounds hΦ hΨ hA hB hS p q x y z hq hp
          βA βB α hβA hβB hα hβA0 hβA1 hβB0 hβB1 hα0 hα1).2
      | inr v =>
        change 2 * Real.cosh (dist (R y) (R z) / 2) * Real.cosh (dist (R v) (R n)) ≤
          Real.cosh (dist (R v) (R y)) + Real.cosh (dist (R v) (R z))
        have hc := cosh_comparison_at_specified_midpoint (hB y z) hyn hnz v
        simpa only [hR.dist_eq] using hc

/-- A chosen native minimizing two-leg midpoint compares against every point
in the right original piece. The two legs are fixed before the test point. -/
theorem metricGlue_cross_midpoint_cosh_right_test
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    [ProperSpace A] [CompleteSpace B] [CompleteSpace S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hB : ∀ x y : B, ∃ m : B,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hS : ∀ p q : S, ∃ σ : Icc (0 : ℝ) (dist p q) → S,
      Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
        σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q)
    (q : S) (x : A) (y : B)
    (hmin : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y)
    (βA : Icc (0 : ℝ) (dist x (Φ q)) → A)
    (βB : Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (hβA : Isometry βA) (hβB : Isometry βB)
    (hβA0 : βA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hβA1 : βA ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩ = Φ q)
    (hβB0 : βB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ q)
    (hβB1 : βB ⟨dist (Ψ q) y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    ∀ z : B,
      2 * Real.cosh (dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) / 2) *
        Real.cosh (dist (Metric.toGlueR hΦ hΨ z)
          (metricTwoLegUnitPoint dist_nonneg dist_nonneg
            (Metric.toGlueL hΦ hΨ ∘ βA) (Metric.toGlueR hΦ hΨ ∘ βB)
            ⟨1 / 2, by norm_num⟩)) ≤
        Real.cosh (dist (Metric.toGlueR hΦ hΨ z) (Metric.toGlueL hΦ hΨ x)) +
          Real.cosh (dist (Metric.toGlueR hΦ hΨ z) (Metric.toGlueR hΦ hΨ y)) := by
  intro z
  obtain ⟨p, hp⟩ := metricGlue_cross_dist_attained hΦ hΨ x z
  obtain ⟨αZ, hαZ, hαZ0, hαZ1⟩ := metricMidpointCosh_exists_isometric_interval hB y z
  exact (metricGlue_mixed_triangle_midpoint_bounds hΦ hΨ hA hB hS p q x y z hmin hp
    βA βB αZ hβA hβB hαZ hβA0 hβA1 hβB0 hβB1 hαZ0 hαZ1).1

section GeneralGlue

variable {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
  [ProperSpace A] [ProperSpace B] [CompleteSpace S]
  {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
  (hA : ∀ x y : A, ∃ m : A,
    dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
    ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
      Real.cosh (dist z x) + Real.cosh (dist z y))
  (hB : ∀ x y : B, ∃ m : B,
    dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
    ∀ z : B, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
      Real.cosh (dist z x) + Real.cosh (dist z y))
  (hS : ∀ p q : S, ∃ σ : Icc (0 : ℝ) (dist p q) → S,
    Isometry σ ∧ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
      σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q)

omit [ProperSpace A] [ProperSpace B] [CompleteSpace S] in
/-- The explicit midpoint of minimizing native legs has the required two
half-distance equalities, including a collapsed total interval. -/
theorem metricGlue_twoLeg_midpoint_distances
    (q : S) (x : A) (y : B)
    (hmin : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y)
    (βA : Icc (0 : ℝ) (dist x (Φ q)) → A)
    (βB : Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (hβA : Isometry βA) (hβB : Isometry βB)
    (hβA0 : βA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hβA1 : βA ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩ = Φ q)
    (hβB0 : βB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ q)
    (hβB1 : βB ⟨dist (Ψ q) y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    let m := metricTwoLegUnitPoint dist_nonneg dist_nonneg
      (Metric.toGlueL hΦ hΨ ∘ βA) (Metric.toGlueR hΦ hΨ ∘ βB) ⟨1 / 2, by norm_num⟩
    dist (Metric.toGlueL hΦ hΨ x) m =
      dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) / 2 ∧
    dist m (Metric.toGlueR hΦ hΨ y) =
      dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) / 2 := by
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hjoin : (L ∘ βA) ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩ =
      (R ∘ βB) ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := by
    simp only [Function.comp_apply, hβA1, hβB0]
    exact congrFun (Metric.toGlue_commute hΦ hΨ) q
  have hends : dist ((L ∘ βA) ⟨0, ⟨le_rfl, dist_nonneg⟩⟩)
      ((R ∘ βB) ⟨dist (Ψ q) y, ⟨dist_nonneg, le_rfl⟩⟩) =
        dist x (Φ q) + dist (Ψ q) y := by
    simpa only [Function.comp_apply, hβA0, hβB1] using hmin
  obtain ⟨γ, _, hdist, hγ0, hγ1, hpoint⟩ := exists_unit_path_metricTwoLegUnitPoint
    dist_nonneg dist_nonneg (L ∘ βA) (R ∘ βB)
    ((Metric.toGlueL_isometry hΦ hΨ).comp hβA)
    ((Metric.toGlueR_isometry hΦ hΨ).comp hβB) hjoin hends
  have hstart : γ 0 = L x := by simpa only [Function.comp_apply, hβA0] using hγ0
  have hend : γ 1 = R y := by simpa only [Function.comp_apply, hβB1] using hγ1
  have hm := hpoint ⟨1 / 2, by norm_num⟩
  constructor
  · change dist (L x) _ = dist (L x) (R y) / 2
    rw [← hm, ← hstart, hdist 0 (by norm_num) (1 / 2) (by norm_num)]
    norm_num
    rw [hstart, hmin]
    ring
  · change dist _ (R y) = dist (L x) (R y) / 2
    rw [← hm, ← hend, hdist (1 / 2) (by norm_num) 1 (by norm_num)]
    norm_num
    rw [hend, hmin]
    ring

include hΦ hΨ hA hB hS

/-- The same all-test property for endpoints in the left copy, transported
by the actual quotient's summand-swap isometry. -/
theorem metricGlue_left_exists_midpoint_cosh_all_test (x y : A) :
    ∃ m : Metric.GlueSpace hΦ hΨ,
      dist (Metric.toGlueL hΦ hΨ x) m =
        dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) / 2 ∧
      dist m (Metric.toGlueL hΦ hΨ y) =
        dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) / 2 ∧
      ∀ z : Metric.GlueSpace hΦ hΨ,
        2 * Real.cosh (dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) / 2) *
          Real.cosh (dist z m) ≤ Real.cosh (dist z (Metric.toGlueL hΦ hΨ x)) +
            Real.cosh (dist z (Metric.toGlueL hΦ hΨ y)) := by
  obtain ⟨m, hxm, hmy, hc⟩ :=
    metricGlue_right_exists_midpoint_cosh_all_test hΨ hΦ hB hA hS x y
  let T := metricGlueSwap hΨ hΦ
  have hT : Isometry T := metricGlueSwap_isometry hΨ hΦ
  have hxy : dist (Metric.toGlueR hΨ hΦ x) (Metric.toGlueR hΨ hΦ y) =
      dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) := by
    simpa only [T, metricGlueSwap_right] using
      (hT.dist_eq (Metric.toGlueR hΨ hΦ x) (Metric.toGlueR hΨ hΦ y)).symm
  refine ⟨T m, ?_, ?_, ?_⟩
  · have hh := hT.dist_eq (Metric.toGlueR hΨ hΦ x) m
    simpa only [T, metricGlueSwap_right, hxm, hxy] using hh
  · have hh := hT.dist_eq m (Metric.toGlueR hΨ hΦ y)
    simpa only [T, metricGlueSwap_right, hmy, hxy] using hh
  · intro z
    have hz (w : Metric.GlueSpace hΨ hΦ) :
        dist (metricGlueSwap hΦ hΨ z) w = dist z (T w) := by
      simpa only [T, metricGlueSwap_swap] using
        (hT.dist_eq (metricGlueSwap hΦ hΨ z) w).symm
    simpa only [hxy, hz, T, metricGlueSwap_right] using hc (metricGlueSwap hΦ hΨ z)

/-- Crossed endpoints have one fixed midpoint against every glued test point.
The same two native legs are used for both copies; reversing them is an exact
pointwise identity, not a fresh choice of a comparison midpoint. -/
theorem metricGlue_cross_exists_midpoint_cosh_all_test (x : A) (y : B) :
    ∃ m : Metric.GlueSpace hΦ hΨ,
      dist (Metric.toGlueL hΦ hΨ x) m =
        dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) / 2 ∧
      dist m (Metric.toGlueR hΦ hΨ y) =
        dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) / 2 ∧
      ∀ z : Metric.GlueSpace hΦ hΨ,
        2 * Real.cosh (dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) / 2) *
          Real.cosh (dist z m) ≤ Real.cosh (dist z (Metric.toGlueL hΦ hΨ x)) +
            Real.cosh (dist z (Metric.toGlueR hΦ hΨ y)) := by
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  obtain ⟨q, hmin⟩ := metricGlue_cross_dist_attained hΦ hΨ x y
  obtain ⟨βA, hβA, hβA0, hβA1⟩ := metricMidpointCosh_exists_isometric_interval hA x (Φ q)
  obtain ⟨βB, hβB, hβB0, hβB1⟩ := metricMidpointCosh_exists_isometric_interval hB (Ψ q) y
  let m := metricTwoLegUnitPoint dist_nonneg dist_nonneg
    (L ∘ βA) (R ∘ βB) ⟨1 / 2, by norm_num⟩
  obtain ⟨hxm, hmy⟩ := metricGlue_twoLeg_midpoint_distances hΦ hΨ q x y hmin
    βA βB hβA hβB hβA0 hβA1 hβB0 hβB1
  refine ⟨m, hxm, hmy, ?_⟩
  intro z
  induction z using Quotient.inductionOn with
  | h z =>
    cases z with
    | inr v =>
      exact metricGlue_cross_midpoint_cosh_right_test hΦ hΨ hA hB hS q x y hmin
        βA βB hβA hβB hβA0 hβA1 hβB0 hβB1 v
    | inl v =>
      let L' := Metric.toGlueL hΨ hΦ
      let R' := Metric.toGlueR hΨ hΦ
      let T := metricGlueSwap hΨ hΦ
      have hT : Isometry T := metricGlueSwap_isometry hΨ hΦ
      have hxy : dist (L' y) (R' x) = dist (L x) (R y) := by
        simpa only [T, L', R', metricGlueSwap_left, metricGlueSwap_right, dist_comm]
          using (hT.dist_eq (L' y) (R' x)).symm
      have hmin' : dist (L' y) (R' x) = dist y (Ψ q) + dist (Φ q) x := by
        rw [hxy, hmin, dist_comm y (Ψ q), dist_comm (Φ q) x, add_comm]
      let α' := metricReverseDistanceInterval βB
      let β' := metricReverseDistanceInterval βA
      have hc := metricGlue_cross_midpoint_cosh_right_test hΨ hΦ hB hA hS q y x hmin'
        α' β' (metricReverseDistanceInterval_isometry βB hβB)
        (metricReverseDistanceInterval_isometry βA hβA)
        (metricReverseDistanceInterval_zero βB hβB1)
        (metricReverseDistanceInterval_end βB hβB0)
        (metricReverseDistanceInterval_zero βA hβA1)
        (metricReverseDistanceInterval_end βA hβA0) v
      let n := metricTwoLegUnitPoint dist_nonneg dist_nonneg
        (L' ∘ α') (R' ∘ β') ⟨1 / 2, by norm_num⟩
      have hjoin : L (βA ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩) =
          R (βB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩) := by
        rw [hβA1, hβB0]
        exact congrFun (Metric.toGlue_commute hΦ hΨ) q
      have hnm : T n = m := by
        have hh := metricGlueSwap_reversedTwoLeg hΦ hΨ q x y βA βB hjoin
          ⟨1 / 2, by norm_num⟩
        have hre : metricBoundaryReverseUnit ⟨(1 / 2 : ℝ), by norm_num⟩ =
            ⟨1 / 2, by norm_num⟩ := Subtype.ext (by norm_num [metricBoundaryReverseUnit])
        simpa only [hre] using hh
      have hvn : dist (R' v) n = dist (L v) m := by
        simpa only [T, R', metricGlueSwap_right, hnm] using (hT.dist_eq (R' v) n).symm
      have hvy : dist (R' v) (L' y) = dist (L v) (R y) := by
        simpa only [T, R', L', metricGlueSwap_left, metricGlueSwap_right] using
          (hT.dist_eq (R' v) (L' y)).symm
      have hvx : dist (R' v) (R' x) = dist (L v) (L x) := by
        simpa only [T, R', metricGlueSwap_right] using (hT.dist_eq (R' v) (R' x)).symm
      change 2 * Real.cosh (dist (L x) (R y) / 2) * Real.cosh (dist (L v) m) ≤
        Real.cosh (dist (L v) (L x)) + Real.cosh (dist (L v) (R y))
      change 2 * Real.cosh (dist (L' y) (R' x) / 2) * Real.cosh (dist (R' v) n) ≤
        Real.cosh (dist (R' v) (L' y)) + Real.cosh (dist (R' v) (R' x)) at hc
      simpa only [hxy, hvn, hvy, hvx, add_comm] using hc

/-- Convex gluing preserves all-test hyperbolic midpoint-cosh comparison on
the actual metric quotient. Complete seam geodesics supply the common sides;
proper original pieces supply attained cross-piece routes. -/
theorem metricGlue_exists_midpoint_cosh_all_test (x y : Metric.GlueSpace hΦ hΨ) :
    ∃ m : Metric.GlueSpace hΦ hΨ,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : Metric.GlueSpace hΦ hΨ,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      cases x with
      | inl x =>
        cases y with
        | inl y => exact metricGlue_left_exists_midpoint_cosh_all_test hΦ hΨ hA hB hS x y
        | inr y => exact metricGlue_cross_exists_midpoint_cosh_all_test hΦ hΨ hA hB hS x y
      | inr x =>
        cases y with
        | inl y =>
          obtain ⟨m, hym, hmx, hc⟩ :=
            metricGlue_cross_exists_midpoint_cosh_all_test hΦ hΨ hA hB hS y x
          refine ⟨m, ?_, ?_, ?_⟩
          · change dist (Metric.toGlueR hΦ hΨ x) m =
              dist (Metric.toGlueR hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) / 2
            rw [dist_comm (Metric.toGlueR hΦ hΨ x) m,
              dist_comm (Metric.toGlueR hΦ hΨ x) (Metric.toGlueL hΦ hΨ y)]
            exact hmx
          · change dist m (Metric.toGlueL hΦ hΨ y) =
              dist (Metric.toGlueR hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) / 2
            rw [dist_comm m (Metric.toGlueL hΦ hΨ y),
              dist_comm (Metric.toGlueR hΦ hΨ x) (Metric.toGlueL hΦ hΨ y)]
            exact hym
          · intro z
            change 2 * Real.cosh
              (dist (Metric.toGlueR hΦ hΨ x) (Metric.toGlueL hΦ hΨ y) / 2) *
                Real.cosh (dist z m) ≤
              Real.cosh (dist z (Metric.toGlueR hΦ hΨ x)) +
                Real.cosh (dist z (Metric.toGlueL hΦ hΨ y))
            rw [dist_comm (Metric.toGlueR hΦ hΨ x) (Metric.toGlueL hΦ hΨ y), add_comm]
            exact hc z
        | inr y => exact metricGlue_right_exists_midpoint_cosh_all_test hΦ hΨ hA hB hS x y

end GeneralGlue

#print axioms metricMidpointCosh_exists_isometric_interval
#print axioms metricGlue_mixed_triangle_midpoint_bounds
#print axioms metricGlue_right_exists_midpoint_cosh_all_test
#print axioms metricGlue_cross_midpoint_cosh_right_test
#print axioms metricGlue_left_exists_midpoint_cosh_all_test
#print axioms metricGlue_cross_exists_midpoint_cosh_all_test
#print axioms metricGlue_exists_midpoint_cosh_all_test

end SystolicGrowth
