module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricTriangleInheritance
public import Geometry.HyperbolicTrianglePasting
public import Geometry.MetricTriangleChildComparison
public import Geometry.MetricTriangleBoundaryReparameterization

@[expose] public section

/-!
# Native mixed triangles in general convex metric gluing

The boundary inheritance theorem is applied to genuine triangles in the
original pieces. Shared edges are copies of the same seam segment, and
cross-piece sides retain their actual minimizing seam point. No comparison
property of the original glued space is supplied as an input.
-/

open Set

namespace SystolicGrowth

noncomputable def Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    {φ : E → F} (hφ : Isometry φ) {p q : E}
    (σ : Icc (0 : ℝ) (dist p q) → E)
    (t : Icc (0 : ℝ) (dist (φ p) (φ q))) : F :=
  φ (σ ⟨t.1, by simpa only [hφ.dist_eq] using t.2⟩)

private theorem isometricIntervalCopy_isometry
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    {φ : E → F} (hφ : Isometry φ) {p q : E}
    (σ : Icc (0 : ℝ) (dist p q) → E) (hσ : Isometry σ) :
    Isometry (Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy hφ σ) := by
  apply Isometry.of_dist_eq
  intro s t
  simp only [Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy, hφ.dist_eq, hσ.dist_eq, Subtype.dist_eq]

private theorem isometricIntervalCopy_zero
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    {φ : E → F} (hφ : Isometry φ) {p q : E}
    (σ : Icc (0 : ℝ) (dist p q) → E)
    (hzero : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p) :
    Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy hφ σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = φ p := by
  simpa only [Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy] using congrArg φ hzero

private theorem isometricIntervalCopy_end
    {E F : Type*} [MetricSpace E] [MetricSpace F]
    {φ : E → F} (hφ : Isometry φ) {p q : E}
    (σ : Icc (0 : ℝ) (dist p q) → E)
    (hend : σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q) :
    Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy hφ σ ⟨dist (φ p) (φ q), ⟨dist_nonneg, le_rfl⟩⟩ = φ q := by
  dsimp only [Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy]
  have ht : (⟨dist (φ p) (φ q), by simpa only [hφ.dist_eq] using
      (show dist (φ p) (φ q) ∈ Icc (0 : ℝ) (dist (φ p) (φ q)) from
        ⟨dist_nonneg, le_rfl⟩)⟩ : Icc (0 : ℝ) (dist p q)) =
      ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ := Subtype.ext (hφ.dist_eq p q)
  rw [ht, hend]

/-- Native outer and split-leg edges, with their original arc-length maps. -/
noncomputable def metricSplitLeftArcBoundary
    {A : Type*} [MetricSpace A] (P X Q : A) (x q : UpperHalfPlane)
    (hXQ : dist x q = dist X Q)
    (α : Icc (0 : ℝ) (dist P X) → A) (β : Icc (0 : ℝ) (dist X Q) → A) :
    SplitBoundaryLeft x q → A :=
  Sum.elim (fun t => α ⟨dist P X * t.1, ⟨mul_nonneg dist_nonneg t.2.1,
    by simpa using mul_le_mul_of_nonneg_left t.2.2 dist_nonneg⟩⟩)
    (fun t => β ⟨t.1, by simpa only [hXQ] using t.2⟩)

/-- The right child's native outer and split-leg edges. -/
noncomputable def metricSplitRightArcBoundary
    {B : Type*} [MetricSpace B] (P Q Y : B) (q y : UpperHalfPlane)
    (hQY : dist q y = dist Q Y)
    (α : Icc (0 : ℝ) (dist P Y) → B) (β : Icc (0 : ℝ) (dist Q Y) → B) :
    SplitBoundaryRight q y → B :=
  Sum.elim (fun t => α ⟨dist P Y * t.1, ⟨mul_nonneg dist_nonneg t.2.1,
    by simpa using mul_le_mul_of_nonneg_left t.2.2 dist_nonneg⟩⟩)
    (fun t => β ⟨t.1, by simpa only [hQY] using t.2⟩)

/-- Actual mixed triangles with apex on the common seam inherit full boundary
comparison from the original pieces. All boundary points use the specified
native intervals; the mixed side passes through the same minimizing `q`.
This is the first inheritance step of general convex gluing. -/
theorem metricGlue_seam_apex_triangle_boundary_comparison
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hB : ∀ x y : B, ∃ m : B,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (p q : S) (x : A) (y : B)
    (p' q' x' y' : UpperHalfPlane)
    (hpq : dist p' q' = dist p q)
    (hpx : dist p' x' = dist (Φ p) x) (hxq : dist x' q' = dist x (Φ q))
    (hpy : dist p' y' = dist (Ψ p) y) (hqy : dist q' y' = dist (Ψ q) y)
    (αA : Icc (0 : ℝ) (dist (Φ p) x) → A)
    (βA : Icc (0 : ℝ) (dist x (Φ q)) → A)
    (αB : Icc (0 : ℝ) (dist (Ψ p) y) → B)
    (βB : Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (σ : Icc (0 : ℝ) (dist p q) → S)
    (hαA : Isometry αA) (hβA : Isometry βA)
    (hαB : Isometry αB) (hβB : Isometry βB) (hσ : Isometry σ)
    (hαA0 : αA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Φ p)
    (hαA1 : αA ⟨dist (Φ p) x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (hβA0 : βA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hβA1 : βA ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩ = Φ q)
    (hαB0 : αB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ p)
    (hαB1 : αB ⟨dist (Ψ p) y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hβB0 : βB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ q)
    (hβB1 : βB ⟨dist (Ψ q) y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hσ0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p)
    (hσ1 : σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q)
    (hmin : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y)
    (P X Y : UpperHalfPlane)
    (hPX : dist P X = dist p' x') (hPY : dist P Y = dist p' y')
    (hXY : dist X Y = dist x' q' + dist q' y')
    (u v : SplitBoundaryLeft x' q' ⊕ SplitBoundaryRight q' y') :
    let f := metricSplitLeftArcBoundary (Φ p) x (Φ q) x' q' hxq αA βA
    let g := metricSplitRightArcBoundary (Ψ p) (Ψ q) y q' y' hqy αB βB
    dist (Sum.elim (Metric.toGlueL hΦ hΨ ∘ f) (Metric.toGlueR hΦ hΨ ∘ g) u)
      (Sum.elim (Metric.toGlueL hΦ hΨ ∘ f) (Metric.toGlueR hΦ hΨ ∘ g) v) ≤
      dist (splitBoundaryParentModel q' x' y' P X Y u)
        (splitBoundaryParentModel q' x' y' P X Y v) := by
  dsimp only
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hL : Isometry L := Metric.toGlueL_isometry hΦ hΨ
  have hR : Isometry R := Metric.toGlueR_isometry hΦ hΨ
  let γA := Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy hΦ σ
  let γB := Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy hΨ σ
  have hpqA : dist p' q' = dist (Φ p) (Φ q) := hpq.trans (hΦ.dist_eq p q).symm
  have hpqB : dist p' q' = dist (Ψ p) (Ψ q) := hpq.trans (hΨ.dist_eq p q).symm
  obtain ⟨f, hff, hf, _, hf1, hfo, hfl⟩ :=
    metric_triangle_child_left_comparison hA (Φ p) x (Φ q) p' x' q' hpx hxq hpqA
      αA βA γA hαA hβA (isometricIntervalCopy_isometry hΦ σ hσ)
      hαA0 hαA1 hβA0 hβA1 (isometricIntervalCopy_zero hΦ σ hσ0)
      (isometricIntervalCopy_end hΦ σ hσ1)
  obtain ⟨g, hgg, hg, _, hg1, hgo, hgl⟩ :=
    metric_triangle_child_right_comparison hB (Ψ p) (Ψ q) y p' q' y' hpy hqy hpqB
      αB βB γB hαB hβB (isometricIntervalCopy_isometry hΨ σ hσ)
      hαB0 hαB1 hβB0 hβB1 (isometricIntervalCopy_zero hΨ σ hσ0)
      (isometricIntervalCopy_end hΨ σ hσ1)
  have hf' : f = metricSplitLeftArcBoundary (Φ p) x (Φ q) x' q' hxq αA βA := by
    funext t
    cases t with
    | inl t => exact hfo t
    | inr t => exact hfl t
  have hg' : g = metricSplitRightArcBoundary (Ψ p) (Ψ q) y q' y' hqy αB βB := by
    funext t
    cases t with
    | inl t => exact hgo t
    | inr t => exact hgl t
  let T := Vendored.RiemannDynamics.geodSeg p' q'
  letI : Nonempty T := hyperbolicGeodSeg_nonempty p' q'
  letI : CompleteSpace T := hyperbolicGeodSeg_completeSpace p' q'
  let δ : T → Metric.GlueSpace hΦ hΨ := L ∘ metricTriangleSharedSideMap hpqA γA
  have hδ (w : T) : δ w = R (metricTriangleSharedSideMap hpqB γB w) := by
    dsimp only [δ, Function.comp_apply, metricTriangleSharedSideMap, γA, γB,
      Internal.MetricConvexGluingComparisonHelpers.isometricIntervalCopy]
    exact congrFun (Metric.toGlue_commute hΦ hΨ) (σ ⟨dist p' w.1, by
      have hw : dist p' w.1 + dist w.1 q' = dist p' q' := w.2
      have hwle : dist p' w.1 ≤ dist p' q' := by linarith [dist_nonneg (x := w.1) (y := q')]
      exact ⟨dist_nonneg, hpq ▸ hwle⟩⟩)
  have hff' : ∀ i j, dist ((L ∘ f) i) ((L ∘ f) j) ≤
      dist (splitBoundaryLeftModel p' q' x' i) (splitBoundaryLeftModel p' q' x' j) := by
    intro i j
    simpa only [Function.comp_apply, hL.dist_eq] using hff i j
  have hgg' : ∀ i j, dist ((R ∘ g) i) ((R ∘ g) j) ≤
      dist (splitBoundaryRightModel p' q' y' i) (splitBoundaryRightModel p' q' y' j) := by
    intro i j
    simpa only [Function.comp_apply, hR.dist_eq] using hgg i j
  have hf'' : ∀ i w, dist ((L ∘ f) i) (δ w) ≤ dist (splitBoundaryLeftModel p' q' x' i) w.1 := by
    intro i w
    simpa only [Function.comp_apply, δ, hL.dist_eq] using hf i w
  have hg'' : ∀ i w, dist ((R ∘ g) i) (δ w) ≤ dist (splitBoundaryRightModel p' q' y' i) w.1 := by
    intro i w
    rw [hδ w]
    simpa only [Function.comp_apply, hR.dist_eq] using hg i w
  have hactual : dist ((L ∘ f) (.inl ⟨1, by norm_num⟩))
      ((R ∘ g) (.inl ⟨1, by norm_num⟩)) = dist x' q' + dist q' y' := by
    simp only [Function.comp_apply, hf1, hg1, hxq, hqy]
    exact hmin
  have h := metric_triangle_boundary_inheritance T (hyperbolicGeodSeg_geodSeg_subset p' q')
    p' q' x' y' (Vendored.RiemannDynamics.left_mem_geodSeg p' q')
    (Vendored.RiemannDynamics.right_mem_geodSeg p' q') (L ∘ f) (R ∘ g) δ
    hff' hgg' hf'' hg'' hactual P X Y hPX hPY hXY u v
  simpa only [hf', hg'] using h

#print axioms metricGlue_seam_apex_triangle_boundary_comparison

/-- View the first inherited triangle as the left child of the next split.
The old split side is reversed and normalized, not replaced by a new segment. -/
noncomputable def metricInheritedLeftBoundary
    {M : Type*} (q x y P X : UpperHalfPlane)
    (F : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y → M) :
    SplitBoundaryLeft X P → M :=
  Sum.elim
    (fun t => F (splitBoundaryParentXYIndex q x y (metricBoundaryReverseUnit t)))
    (fun t => F (splitBoundaryParentPXIndex q x y
      (metricBoundaryReverseUnit (metricBoundaryUnitParameter dist_nonneg t))))

/-- The very same unsplit edge supplies the second inheritance's shared side. -/
noncomputable def metricInheritedSharedSideMap
    {M : Type*} (q x y P Y : UpperHalfPlane)
    (F : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y → M) :
    Vendored.RiemannDynamics.geodSeg Y P → M := fun w =>
  F (splitBoundaryParentPYIndex q x y
    (metricBoundaryReverseUnit (metricTriangleSharedSideParameter Y P w)))

private theorem metricInheritedLeftBoundary_model (q x y P X Y : UpperHalfPlane)
    (hXY : dist X Y = dist x q + dist q y) (t : SplitBoundaryLeft X P) :
    metricInheritedLeftBoundary q x y P X (splitBoundaryParentModel q x y P X Y) t =
      splitBoundaryLeftModel Y P X t := by
  cases t with
  | inl t =>
    dsimp only [metricInheritedLeftBoundary, Sum.elim_inl]
    rw [splitBoundaryParentXYIndex_model q x y P X Y hXY]
    exact (metricBoundaryGeodInterp_reverse_of_mem_Icc X Y t.2).symm
  | inr t =>
    dsimp only [metricInheritedLeftBoundary, Sum.elim_inr]
    rw [splitBoundaryParentPXIndex_model]
    exact (metricBoundaryGeodInterp_reverse_of_mem_Icc P X
      (metricBoundaryUnitParameter dist_nonneg t).2).symm

private theorem metricInheritedSharedSideMap_model (q x y P X Y : UpperHalfPlane)
    (w : Vendored.RiemannDynamics.geodSeg Y P) :
    metricInheritedSharedSideMap q x y P Y (splitBoundaryParentModel q x y P X Y) w =
      w.1 := by
  dsimp only [metricInheritedSharedSideMap]
  rw [splitBoundaryParentPYIndex_model]
  simp only [metricBoundaryReverseUnit_val]
  rw [← metricBoundaryGeodInterp_reverse_of_mem_Icc P Y
    (metricTriangleSharedSideParameter Y P w).2]
  exact metricTriangleSharedSideParameter_interp Y P w

/-- Pull the proved first-parent comparison back to genuine inputs for the
second inheritance. No comparison of the ambient glued space is assumed. -/
theorem metric_inherited_left_child_comparison
    {M : Type*} [MetricSpace M] (q x y P X Y : UpperHalfPlane)
    (hXY : dist X Y = dist x q + dist q y)
    (F : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y → M)
    (hF : ∀ u v, dist (F u) (F v) ≤
      dist (splitBoundaryParentModel q x y P X Y u)
        (splitBoundaryParentModel q x y P X Y v)) :
    (∀ i j, dist (metricInheritedLeftBoundary q x y P X F i)
        (metricInheritedLeftBoundary q x y P X F j) ≤
      dist (splitBoundaryLeftModel Y P X i) (splitBoundaryLeftModel Y P X j)) ∧
    ∀ i w, dist (metricInheritedLeftBoundary q x y P X F i)
        (metricInheritedSharedSideMap q x y P Y F w) ≤
      dist (splitBoundaryLeftModel Y P X i) w.1 := by
  have hleft := metricInheritedLeftBoundary_model q x y P X Y hXY
  have hshared := metricInheritedSharedSideMap_model q x y P X Y
  constructor
  · intro i j
    cases i <;> cases j <;>
      simpa only [metricInheritedLeftBoundary, Sum.elim_inl, Sum.elim_inr,
        ← hleft] using hF _ _
  · intro i w
    cases i <;>
      simpa only [metricInheritedLeftBoundary, metricInheritedSharedSideMap,
        Sum.elim_inl, Sum.elim_inr, ← hleft, ← hshared] using hF _ _

#print axioms metric_inherited_left_child_comparison

noncomputable def Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval
    {M : Type*} [MetricSpace M] {a b : M}
    (σ : Icc (0 : ℝ) (dist a b) → M) : Icc (0 : ℝ) (dist b a) → M := fun t =>
  σ ⟨dist a b - t.1, ⟨by simpa only [dist_comm a b] using sub_nonneg.mpr t.2.2,
    sub_le_self _ t.2.1⟩⟩

private theorem reversedIsometricInterval_isometry
    {M : Type*} [MetricSpace M] {a b : M}
    (σ : Icc (0 : ℝ) (dist a b) → M) (hσ : Isometry σ) :
    Isometry (Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval σ) := by
  apply Isometry.of_dist_eq
  intro s t
  simp only [Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval, hσ.dist_eq, Subtype.dist_eq, Real.dist_eq]
  rw [show (dist a b - s.1) - (dist a b - t.1) = t.1 - s.1 by ring, abs_sub_comm]

private theorem reversedIsometricInterval_zero
    {M : Type*} [MetricSpace M] {a b : M}
    (σ : Icc (0 : ℝ) (dist a b) → M)
    (hend : σ ⟨dist a b, ⟨dist_nonneg, le_rfl⟩⟩ = b) :
    Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = b := by
  simpa only [Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval, sub_zero] using hend

private theorem reversedIsometricInterval_end
    {M : Type*} [MetricSpace M] {a b : M}
    (σ : Icc (0 : ℝ) (dist a b) → M)
    (hzero : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = a) :
    Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval σ ⟨dist b a, ⟨dist_nonneg, le_rfl⟩⟩ = a := by
  simpa only [Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval, dist_comm b a, sub_self] using hzero

private theorem reversed_scaled_interval_parameter {d : ℝ}
    (t : Icc (0 : ℝ) d) : d * (1 - t.1 / d) = d - t.1 := by
  by_cases h : d = 0
  · have ht : t.1 = 0 := le_antisymm (by simpa only [h] using t.2.2) t.2.1
    simp [h, ht]
  · field_simp


/-- The second inheritance for an arbitrary mixed triangle. The first crossed
side is retained pointwise; both minimizing seam points and all native piece
intervals are the specified ones. No ambient glued comparison is a premise. -/
theorem metricGlue_mixed_triangle_boundary_comparison
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (hA : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hB : ∀ x y : B, ∃ m : B,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : B, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (p q : S) (x : A) (y : B)
    (p' q' x' y' : UpperHalfPlane)
    (hpq : dist p' q' = dist p q)
    (hpx : dist p' x' = dist (Φ p) x) (hxq : dist x' q' = dist x (Φ q))
    (hpy : dist p' y' = dist (Ψ p) y) (hqy : dist q' y' = dist (Ψ q) y)
    (αA : Icc (0 : ℝ) (dist (Φ p) x) → A)
    (βA : Icc (0 : ℝ) (dist x (Φ q)) → A)
    (αB : Icc (0 : ℝ) (dist (Ψ p) y) → B)
    (βB : Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (σ : Icc (0 : ℝ) (dist p q) → S)
    (hαA : Isometry αA) (hβA : Isometry βA)
    (hαB : Isometry αB) (hβB : Isometry βB) (hσ : Isometry σ)
    (hαA0 : αA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Φ p)
    (hαA1 : αA ⟨dist (Φ p) x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (hβA0 : βA ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hβA1 : βA ⟨dist x (Φ q), ⟨dist_nonneg, le_rfl⟩⟩ = Φ q)
    (hαB0 : αB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ p)
    (hαB1 : αB ⟨dist (Ψ p) y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hβB0 : βB ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ q)
    (hβB1 : βB ⟨dist (Ψ q) y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (hσ0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p)
    (hσ1 : σ ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q)
    (hmin : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ y) =
      dist x (Φ q) + dist (Ψ q) y)
    (P X Y : UpperHalfPlane)
    (hPX : dist P X = dist p' x') (hPY : dist P Y = dist p' y')
    (hXY : dist X Y = dist x' q' + dist q' y')
    (z : B) (Z : UpperHalfPlane)
    (hYZ : dist Y Z = dist y z) (hPZ : dist P Z = dist (Ψ p) z)
    (αZ : Icc (0 : ℝ) (dist y z) → B)
    (βZ : Icc (0 : ℝ) (dist (Ψ p) z) → B)
    (hαZ : Isometry αZ) (hβZ : Isometry βZ)
    (hαZ0 : αZ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = y)
    (hαZ1 : αZ ⟨dist y z, ⟨dist_nonneg, le_rfl⟩⟩ = z)
    (hβZ0 : βZ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Ψ p)
    (hβZ1 : βZ ⟨dist (Ψ p) z, ⟨dist_nonneg, le_rfl⟩⟩ = z)
    (hminZ : dist (Metric.toGlueL hΦ hΨ x) (Metric.toGlueR hΦ hΨ z) =
      dist x (Φ p) + dist (Ψ p) z)
    (U V W : UpperHalfPlane)
    (hUV : dist U V = dist Y X) (hUW : dist U W = dist Y Z)
    (hVW : dist V W = dist X P + dist P Z)
    (u v : SplitBoundaryLeft X P ⊕ SplitBoundaryRight P Z) :
    let F := Sum.elim
      (Metric.toGlueL hΦ hΨ ∘ metricSplitLeftArcBoundary (Φ p) x (Φ q) x' q' hxq αA βA)
      (Metric.toGlueR hΦ hΨ ∘ metricSplitRightArcBoundary (Ψ p) (Ψ q) y q' y' hqy αB βB)
    let f := metricInheritedLeftBoundary q' x' y' P X F
    let g := Metric.toGlueR hΦ hΨ ∘ metricSplitRightArcBoundary y (Ψ p) z P Z hPZ αZ βZ
    dist (Sum.elim f g u) (Sum.elim f g v) ≤
      dist (splitBoundaryParentModel P X Z U V W u)
        (splitBoundaryParentModel P X Z U V W v) := by
  dsimp only
  let L := Metric.toGlueL hΦ hΨ
  let R := Metric.toGlueR hΦ hΨ
  have hR : Isometry R := Metric.toGlueR_isometry hΦ hΨ
  let F := Sum.elim
    (L ∘ metricSplitLeftArcBoundary (Φ p) x (Φ q) x' q' hxq αA βA)
    (R ∘ metricSplitRightArcBoundary (Ψ p) (Ψ q) y q' y' hqy αB βB)
  have hF : ∀ i j, dist (F i) (F j) ≤
      dist (splitBoundaryParentModel q' x' y' P X Y i)
        (splitBoundaryParentModel q' x' y' P X Y j) :=
    metricGlue_seam_apex_triangle_boundary_comparison hΦ hΨ hA hB p q x y
      p' q' x' y' hpq hpx hxq hpy hqy αA βA αB βB σ
      hαA hβA hαB hβB hσ hαA0 hαA1 hβA0 hβA1 hαB0 hαB1 hβB0 hβB1
      hσ0 hσ1 hmin P X Y hPX hPY hXY
  obtain ⟨hff, hf⟩ := metric_inherited_left_child_comparison q' x' y' P X Y hXY F hF
  let γ := Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval αB
  have hYP : dist Y P = dist y (Ψ p) := by
    rw [dist_comm Y P, hPY, hpy, dist_comm]
  have hDY : dist Y P = dist (Ψ p) y := by rw [hYP, dist_comm]
  obtain ⟨g, hgg, hg, _, hg1, hgo, hgl⟩ :=
    metric_triangle_child_right_comparison hB y (Ψ p) z Y P Z hYZ hPZ hYP
      αZ βZ γ hαZ hβZ (reversedIsometricInterval_isometry αB hαB)
      hαZ0 hαZ1 hβZ0 hβZ1
      (reversedIsometricInterval_zero αB hαB1)
      (reversedIsometricInterval_end αB hαB0)
  have hgdef : g = metricSplitRightArcBoundary y (Ψ p) z P Z hPZ αZ βZ := by
    funext t
    cases t with
    | inl t => exact hgo t
    | inr t => exact hgl t
  let T := Vendored.RiemannDynamics.geodSeg Y P
  letI : Nonempty T := hyperbolicGeodSeg_nonempty Y P
  letI : CompleteSpace T := hyperbolicGeodSeg_completeSpace Y P
  let δ := metricInheritedSharedSideMap q' x' y' P Y F
  have hδ (w : T) : δ w = R (metricTriangleSharedSideMap hYP γ w) := by
    have hw : dist Y w.1 ≤ dist (Ψ p) y := by
      have hlen : dist Y w.1 + dist w.1 P = dist Y P := w.2
      rw [hDY] at hlen
      linarith [dist_nonneg (x := w.1) (y := P)]
    dsimp only [δ, metricInheritedSharedSideMap, splitBoundaryParentPYIndex,
      metricBoundaryReverseUnit, metricTriangleSharedSideParameter, F, Sum.elim_inr,
      Sum.elim_inl, Function.comp_apply, metricSplitRightArcBoundary,
      metricTriangleSharedSideMap, γ, Internal.MetricConvexGluingComparisonHelpers.reversedIsometricInterval]
    apply congrArg R
    apply congrArg αB
    apply Subtype.ext
    dsimp only
    rw [hDY]
    exact reversed_scaled_interval_parameter
      (⟨dist Y w.1, ⟨dist_nonneg, hw⟩⟩ : Icc (0 : ℝ) (dist (Ψ p) y))
  have hgg' : ∀ i j, dist ((R ∘ g) i) ((R ∘ g) j) ≤
      dist (splitBoundaryRightModel Y P Z i) (splitBoundaryRightModel Y P Z j) := by
    intro i j
    simpa only [Function.comp_apply, hR.dist_eq] using hgg i j
  have hg' : ∀ i w, dist ((R ∘ g) i) (δ w) ≤
      dist (splitBoundaryRightModel Y P Z i) w.1 := by
    intro i w
    rw [hδ w]
    simpa only [Function.comp_apply, hR.dist_eq] using hg i w
  have hleftEnd : metricInheritedLeftBoundary q' x' y' P X F
      (.inl ⟨1, by norm_num⟩) = L x := by
    simp only [metricInheritedLeftBoundary, Sum.elim_inl, metricBoundaryReverseUnit,
      sub_self, splitBoundaryParentXYIndex_zero, F, Function.comp_apply,
      metricSplitLeftArcBoundary, Sum.elim_inr, hβA0]
  have hXP : dist X P = dist x (Φ p) := by
    rw [dist_comm X P, hPX, hpx, dist_comm]
  have hactual : dist (metricInheritedLeftBoundary q' x' y' P X F
      (.inl ⟨1, by norm_num⟩)) ((R ∘ g) (.inl ⟨1, by norm_num⟩)) =
        dist X P + dist P Z := by
    rw [hleftEnd, Function.comp_apply, hg1, hXP, hPZ]
    exact hminZ
  have h := metric_triangle_boundary_inheritance T (hyperbolicGeodSeg_geodSeg_subset Y P)
    Y P X Z (Vendored.RiemannDynamics.left_mem_geodSeg Y P)
    (Vendored.RiemannDynamics.right_mem_geodSeg Y P)
    (metricInheritedLeftBoundary q' x' y' P X F) (R ∘ g) δ
    hff hgg' hf hg' hactual U V W hUV hUW hVW u v
  simpa only [hgdef] using h

#print axioms metricGlue_mixed_triangle_boundary_comparison

/-- The inherited crossed edge is the fixed native two-leg path. In
particular this expression does not depend on the third vertex or its model. -/
theorem metricInheritedLeftBoundary_outer_eq_twoLeg
    {A B S : Type*} [MetricSpace A] [MetricSpace B] [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (p q : S) (x : A) (y : B) (q' x' y' P X : UpperHalfPlane)
    (hxq : dist x' q' = dist x (Φ q)) (hqy : dist q' y' = dist (Ψ q) y)
    (αA : Icc (0 : ℝ) (dist (Φ p) x) → A)
    (βA : Icc (0 : ℝ) (dist x (Φ q)) → A)
    (αB : Icc (0 : ℝ) (dist (Ψ p) y) → B)
    (βB : Icc (0 : ℝ) (dist (Ψ q) y) → B)
    (t : Icc (0 : ℝ) 1) :
    let F := Sum.elim
      (Metric.toGlueL hΦ hΨ ∘ metricSplitLeftArcBoundary (Φ p) x (Φ q) x' q' hxq αA βA)
      (Metric.toGlueR hΦ hΨ ∘ metricSplitRightArcBoundary (Ψ p) (Ψ q) y q' y' hqy αB βB)
    metricInheritedLeftBoundary q' x' y' P X F (.inl t) =
      metricTwoLegUnitPoint dist_nonneg dist_nonneg
        (Metric.toGlueL hΦ hΨ ∘ βA) (Metric.toGlueR hΦ hΨ ∘ βB)
        (metricBoundaryReverseUnit t) := by
  dsimp only [metricInheritedLeftBoundary, Sum.elim_inl]
  unfold splitBoundaryParentXYIndex metricTwoLegUnitPoint
  simp only [hxq, hqy]
  split_ifs <;> rfl

#print axioms metricInheritedLeftBoundary_outer_eq_twoLeg

end SystolicGrowth
