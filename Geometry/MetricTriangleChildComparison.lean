module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricTriangleInheritance
public import Geometry.HyperbolicTrianglePasting

@[expose] public section

/-!
# Actual child-triangle boundary comparison

Genuine isometric child edges and the piece's all-test midpoint inequality
produce the boundary inputs of triangle inheritance. The shared-side map is
evaluated on the original arc-length segment, so independently constructed
left and right children use precisely the same seam map. Zero-length edges
are included; no boundary comparison is assumed.
-/

open Set

namespace SystolicGrowth

theorem Internal.MetricTriangleChildComparisonHelpers.geodSeg_dist_left_le (p q : UpperHalfPlane)
    (w : Vendored.RiemannDynamics.geodSeg p q) : dist p w.1 ≤ dist p q := by
  have hw : dist p w.1 + dist w.1 q = dist p q := w.2
  linarith [dist_nonneg (x := w.1) (y := q)]

/-- The zero-safe unit parameter of an actual point on the model shared side. -/
noncomputable def metricTriangleSharedSideParameter (p q : UpperHalfPlane)
    (w : Vendored.RiemannDynamics.geodSeg p q) : Icc (0 : ℝ) 1 :=
  ⟨dist p w.1 / dist p q, by
    by_cases h : dist p q = 0
    · simp [h]
    · have hpos : 0 < dist p q := lt_of_le_of_ne dist_nonneg (Ne.symm h)
      exact ⟨div_nonneg dist_nonneg dist_nonneg,
        (div_le_one hpos).mpr (Internal.MetricTriangleChildComparisonHelpers.geodSeg_dist_left_le p q w)⟩⟩

theorem metricTriangleSharedSideParameter_interp (p q : UpperHalfPlane)
    (w : Vendored.RiemannDynamics.geodSeg p q) :
    Vendored.RiemannDynamics.geodInterp p q (metricTriangleSharedSideParameter p q w).1 =
      w.1 := by
  apply Vendored.RiemannDynamics.eq_of_mem_geodSeg_of_dist_eq
    (Vendored.RiemannDynamics.geodInterp_mem_geodSeg p q
      (metricTriangleSharedSideParameter p q w).2) w.2
  rw [Vendored.RiemannDynamics.dist_geodInterp_left_abs,
    abs_of_nonneg (metricTriangleSharedSideParameter p q w).2.1]
  change dist p w.1 / dist p q * dist p q = dist p w.1
  by_cases h : dist p q = 0
  · have hw : dist p w.1 = 0 := by
      have hle := Internal.MetricTriangleChildComparisonHelpers.geodSeg_dist_left_le p q w
      rw [h] at hle
      exact le_antisymm hle dist_nonneg
    simp [h, hw]
  · exact div_mul_cancel₀ _ h

/-- Canonical evaluation of the native shared arc-length segment.
Its definition is independent of the third vertex and the chosen outer edge. -/
noncomputable def metricTriangleSharedSideMap
    {A : Type*} [MetricSpace A] {P Q : A} {p q : UpperHalfPlane}
    (hlen : dist p q = dist P Q)
    (γ : Icc (0 : ℝ) (dist P Q) → A) :
    Vendored.RiemannDynamics.geodSeg p q → A := fun w =>
  γ ⟨dist p w.1, ⟨dist_nonneg, by
    rw [← hlen]
    exact Internal.MetricTriangleChildComparisonHelpers.geodSeg_dist_left_le p q w⟩⟩

theorem metricTriangleSharedSideMap_left
    {A : Type*} [MetricSpace A] {P Q : A} {p q : UpperHalfPlane}
    (hlen : dist p q = dist P Q) (γ : Icc (0 : ℝ) (dist P Q) → A) :
    metricTriangleSharedSideMap hlen γ
      ⟨p, Vendored.RiemannDynamics.left_mem_geodSeg p q⟩ =
        γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ := by
  apply congrArg γ
  exact Subtype.ext (dist_self p)

theorem metricTriangleSharedSideMap_right
    {A : Type*} [MetricSpace A] {P Q : A} {p q : UpperHalfPlane}
    (hlen : dist p q = dist P Q) (γ : Icc (0 : ℝ) (dist P Q) → A) :
    metricTriangleSharedSideMap hlen γ
      ⟨q, Vendored.RiemannDynamics.right_mem_geodSeg p q⟩ =
        γ ⟨dist P Q, ⟨dist_nonneg, le_rfl⟩⟩ := by
  apply congrArg γ
  exact Subtype.ext hlen

private theorem unit_path_scaled_eval
    {A : Type*} [MetricSpace A] {d : ℝ} (hd : 0 ≤ d)
    (σ : Icc (0 : ℝ) d → A) (γ : ℝ → A)
    (hdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) = d * |u - v|)
    (hzero : γ 0 = σ ⟨0, ⟨le_rfl, hd⟩⟩)
    (hparam : ∀ t : Icc (0 : ℝ) d, γ (t.1 / d) = σ t)
    (t : Icc (0 : ℝ) 1) :
    γ t.1 = σ ⟨d * t.1, ⟨mul_nonneg hd t.2.1,
      by simpa using mul_le_mul_of_nonneg_left t.2.2 hd⟩⟩ := by
  by_cases hd0 : d = 0
  · have hconst : γ t.1 = γ 0 := dist_eq_zero.mp (by
      rw [hdist t.1 t.2 0 (by norm_num), hd0, zero_mul])
    rw [hconst, hzero]
    congr 1
    apply Subtype.ext
    simp [hd0]
  · have h := hparam ⟨d * t.1, ⟨mul_nonneg hd t.2.1,
      by simpa using mul_le_mul_of_nonneg_left t.2.2 hd⟩⟩
    have hcancel : d * t.1 / d = t.1 := by field_simp
    simpa only [hcancel] using h

private theorem three_vertex_distances_match
    {A : Type*} [MetricSpace A] (P Q X : A) (p q x : UpperHalfPlane)
    (hPX : dist p x = dist P X) (hXQ : dist x q = dist X Q)
    (hPQ : dist p q = dist P Q) :
    ∀ i j : Fin 3, dist (![P, Q, X] i) (![P, Q, X] j) =
      dist (![p, q, x] i) (![p, q, x] j) := by
  have hQX : dist Q X = dist q x := by
    rw [dist_comm Q X, dist_comm q x, hXQ]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hPX, hXQ, hPQ, hQX, dist_comm]

private theorem matched_triangle_edge_family_dist_le
    {A : Type*} [MetricSpace A]
    (hmid : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (v : Fin 3 → A) (v' : Fin 3 → UpperHalfPlane)
    (hvertex : ∀ i j, dist (v i) (v j) = dist (v' i) (v' j))
    (starts ends : Fin 3 → Fin 3) (paths : Fin 3 → ℝ → A)
    (hstart : ∀ i, paths i 0 = v (starts i))
    (hend : ∀ i, paths i 1 = v (ends i))
    (hcont : ∀ i, ContinuousOn (paths i) (Icc 0 1))
    (hdist : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (paths i u) (paths i v) = dist (paths i 0) (paths i 1) * |u - v|)
    (i j : Fin 3) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (paths i s) (paths j t) ≤
      dist (Vendored.RiemannDynamics.geodInterp (v' (starts i)) (v' (ends i)) s)
        (Vendored.RiemannDynamics.geodInterp (v' (starts j)) (v' (ends j)) t) :=
  metric_boundary_family_dist_le hmid paths (v' ∘ starts) (v' ∘ ends) hcont hdist
    (fun i => by rw [hstart, hend]; exact (hvertex _ _).symm)
    (fun i j => by rw [hstart, hstart]; exact hvertex _ _)
    (fun i j => by rw [hstart, hend]; exact hvertex _ _)
    (fun i j => by rw [hend, hend]; exact hvertex _ _) i j s t hs ht

/-- Construct the left child's inheritance inputs from its genuine piece
segments and midpoint comparison, retaining the original outer and leg edges. -/
theorem metric_triangle_child_left_comparison
    {A : Type*} [MetricSpace A]
    (hmid : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (P X Q : A) (p x q : UpperHalfPlane)
    (hPX : dist p x = dist P X) (hXQ : dist x q = dist X Q)
    (hPQ : dist p q = dist P Q)
    (α : Icc (0 : ℝ) (dist P X) → A)
    (β : Icc (0 : ℝ) (dist X Q) → A)
    (γ : Icc (0 : ℝ) (dist P Q) → A)
    (hα : Isometry α) (hβ : Isometry β) (hγ : Isometry γ)
    (hα0 : α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = P)
    (hα1 : α ⟨dist P X, ⟨dist_nonneg, le_rfl⟩⟩ = X)
    (hβ0 : β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = X)
    (hβ1 : β ⟨dist X Q, ⟨dist_nonneg, le_rfl⟩⟩ = Q)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = P)
    (hγ1 : γ ⟨dist P Q, ⟨dist_nonneg, le_rfl⟩⟩ = Q) :
    ∃ f : SplitBoundaryLeft x q → A,
      (∀ i j, dist (f i) (f j) ≤
        dist (splitBoundaryLeftModel p q x i) (splitBoundaryLeftModel p q x j)) ∧
      (∀ i w, dist (f i) (metricTriangleSharedSideMap hPQ γ w) ≤
        dist (splitBoundaryLeftModel p q x i) w.1) ∧
      f (.inl ⟨0, by norm_num⟩) = P ∧ f (.inl ⟨1, by norm_num⟩) = X ∧
      (∀ t : Icc (0 : ℝ) 1,
        f (.inl t) = α ⟨dist P X * t.1, ⟨mul_nonneg dist_nonneg t.2.1,
          by simpa using mul_le_mul_of_nonneg_left t.2.2 dist_nonneg⟩⟩) ∧
      ∀ t : Icc (0 : ℝ) (dist x q),
        f (.inr t) = β ⟨t.1, by simpa only [hXQ] using t.2⟩ := by
  obtain ⟨αu, hαc, hαd, hαz, hαe, hαparam⟩ :=
    unit_path_of_isometric_interval dist_nonneg α hα
  obtain ⟨βu, hβc, hβd, hβz, hβe, hβparam⟩ :=
    unit_path_of_isometric_interval dist_nonneg β hβ
  obtain ⟨γu, hγc, hγd, hγz, hγe, hγparam⟩ :=
    unit_path_of_isometric_interval dist_nonneg γ hγ
  have hαu0 : αu 0 = P := hαz.trans hα0
  have hαu1 : αu 1 = X := hαe.trans hα1
  have hβu0 : βu 0 = X := hβz.trans hβ0
  have hβu1 : βu 1 = Q := hβe.trans hβ1
  have hγu0 : γu 0 = P := hγz.trans hγ0
  have hγu1 : γu 1 = Q := hγe.trans hγ1
  let paths : Fin 3 → ℝ → A := ![αu, βu, γu]
  let starts : Fin 3 → Fin 3 := ![0, 2, 0]
  let ends : Fin 3 → Fin 3 := ![2, 1, 1]
  have hstart : ∀ i, paths i 0 = (![P, Q, X] : Fin 3 → A) (starts i) := by
    intro i
    fin_cases i <;> simp [paths, starts, hαu0, hβu0, hγu0]
  have hend : ∀ i, paths i 1 = (![P, Q, X] : Fin 3 → A) (ends i) := by
    intro i
    fin_cases i <;> simp [paths, ends, hαu1, hβu1, hγu1]
  have hcont : ∀ i, ContinuousOn (paths i) (Icc 0 1) := by
    intro i
    fin_cases i
    · exact hαc.continuousOn
    · exact hβc.continuousOn
    · exact hγc.continuousOn
  have hdist : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (paths i u) (paths i v) = dist (paths i 0) (paths i 1) * |u - v| := by
    intro i u hu v hv
    fin_cases i
    · change dist (αu u) (αu v) = dist (αu 0) (αu 1) * |u - v|
      rw [hαu0, hαu1]
      exact hαd u hu v hv
    · change dist (βu u) (βu v) = dist (βu 0) (βu 1) * |u - v|
      rw [hβu0, hβu1]
      exact hβd u hu v hv
    · change dist (γu u) (γu v) = dist (γu 0) (γu 1) * |u - v|
      rw [hγu0, hγu1]
      exact hγd u hu v hv
  have hcompare := matched_triangle_edge_family_dist_le hmid ![P, Q, X] ![p, q, x]
    (three_vertex_distances_match P Q X p q x hPX hXQ hPQ)
    starts ends paths hstart hend hcont hdist
  let f : SplitBoundaryLeft x q → A :=
    Sum.elim (fun t => αu t.1) (fun t => β ⟨t.1, by simpa only [hXQ] using t.2⟩)
  let edge : SplitBoundaryLeft x q → Fin 3 := Sum.elim (fun _ => 0) (fun _ => 1)
  let time : SplitBoundaryLeft x q → ℝ :=
    Sum.elim Subtype.val (fun t => t.1 / dist x q)
  have htime : ∀ i, time i ∈ Icc (0 : ℝ) 1 := by
    intro i
    cases i with
    | inl t => exact t.2
    | inr t =>
      by_cases h : dist x q = 0
      · simp [time, h]
      · exact ⟨div_nonneg t.2.1 dist_nonneg,
          (div_le_one (lt_of_le_of_ne dist_nonneg (Ne.symm h))).mpr t.2.2⟩
  have hshadow : ∀ i, f i = paths (edge i) (time i) := by
    intro i
    cases i with
    | inl t => rfl
    | inr t =>
      change β ⟨t.1, _⟩ = βu (t.1 / dist x q)
      simpa only [hXQ] using
        (hβparam ⟨t.1, by simpa only [hXQ] using t.2⟩).symm
  have hmodel : ∀ i, Vendored.RiemannDynamics.geodInterp
      ((![p, q, x] : Fin 3 → UpperHalfPlane) (starts (edge i)))
      ((![p, q, x] : Fin 3 → UpperHalfPlane) (ends (edge i))) (time i) =
        splitBoundaryLeftModel p q x i := by
    intro i
    cases i <;> rfl
  have hseam : ∀ w, metricTriangleSharedSideMap hPQ γ w =
      γu (metricTriangleSharedSideParameter p q w).1 := by
    intro w
    dsimp only [metricTriangleSharedSideMap, metricTriangleSharedSideParameter]
    rw [hPQ]
    exact (hγparam _).symm
  refine ⟨f, ?_, ?_, hαu0, hαu1, ?_, fun _ => rfl⟩
  · intro i j
    rw [hshadow i, hshadow j]
    have h := hcompare (edge i) (edge j) (time i) (time j) (htime i) (htime j)
    rwa [hmodel i, hmodel j] at h
  · intro i w
    rw [hshadow i, hseam w]
    have h := hcompare (edge i) 2 (time i)
      (metricTriangleSharedSideParameter p q w).1 (htime i)
      (metricTriangleSharedSideParameter p q w).2
    change dist (paths (edge i) (time i))
      (γu (metricTriangleSharedSideParameter p q w).1) ≤
        dist (Vendored.RiemannDynamics.geodInterp
          ((![p, q, x] : Fin 3 → UpperHalfPlane) (starts (edge i)))
          ((![p, q, x] : Fin 3 → UpperHalfPlane) (ends (edge i))) (time i))
          (Vendored.RiemannDynamics.geodInterp p q
            (metricTriangleSharedSideParameter p q w).1) at h
    rwa [hmodel i, metricTriangleSharedSideParameter_interp] at h
  · exact unit_path_scaled_eval dist_nonneg α αu hαd hαz hαparam

/-- Construct the right child's inheritance inputs from the original piece
edges. Its shared-side map is the same canonical map used by the left child. -/
theorem metric_triangle_child_right_comparison
    {A : Type*} [MetricSpace A]
    (hmid : ∀ x y : A, ∃ m : A,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : A, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (P Q Y : A) (p q y : UpperHalfPlane)
    (hPY : dist p y = dist P Y) (hQY : dist q y = dist Q Y)
    (hPQ : dist p q = dist P Q)
    (α : Icc (0 : ℝ) (dist P Y) → A)
    (β : Icc (0 : ℝ) (dist Q Y) → A)
    (γ : Icc (0 : ℝ) (dist P Q) → A)
    (hα : Isometry α) (hβ : Isometry β) (hγ : Isometry γ)
    (hα0 : α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = P)
    (hα1 : α ⟨dist P Y, ⟨dist_nonneg, le_rfl⟩⟩ = Y)
    (hβ0 : β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = Q)
    (hβ1 : β ⟨dist Q Y, ⟨dist_nonneg, le_rfl⟩⟩ = Y)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = P)
    (hγ1 : γ ⟨dist P Q, ⟨dist_nonneg, le_rfl⟩⟩ = Q) :
    ∃ g : SplitBoundaryRight q y → A,
      (∀ i j, dist (g i) (g j) ≤
        dist (splitBoundaryRightModel p q y i) (splitBoundaryRightModel p q y j)) ∧
      (∀ i w, dist (g i) (metricTriangleSharedSideMap hPQ γ w) ≤
        dist (splitBoundaryRightModel p q y i) w.1) ∧
      g (.inl ⟨0, by norm_num⟩) = P ∧ g (.inl ⟨1, by norm_num⟩) = Y ∧
      (∀ t : Icc (0 : ℝ) 1,
        g (.inl t) = α ⟨dist P Y * t.1, ⟨mul_nonneg dist_nonneg t.2.1,
          by simpa using mul_le_mul_of_nonneg_left t.2.2 dist_nonneg⟩⟩) ∧
      ∀ t : Icc (0 : ℝ) (dist q y),
        g (.inr t) = β ⟨t.1, by simpa only [hQY] using t.2⟩ := by
  obtain ⟨αu, hαc, hαd, hαz, hαe, hαparam⟩ :=
    unit_path_of_isometric_interval dist_nonneg α hα
  obtain ⟨βu, hβc, hβd, hβz, hβe, hβparam⟩ :=
    unit_path_of_isometric_interval dist_nonneg β hβ
  obtain ⟨γu, hγc, hγd, hγz, hγe, hγparam⟩ :=
    unit_path_of_isometric_interval dist_nonneg γ hγ
  have hαu0 : αu 0 = P := hαz.trans hα0
  have hαu1 : αu 1 = Y := hαe.trans hα1
  have hβu0 : βu 0 = Q := hβz.trans hβ0
  have hβu1 : βu 1 = Y := hβe.trans hβ1
  have hγu0 : γu 0 = P := hγz.trans hγ0
  have hγu1 : γu 1 = Q := hγe.trans hγ1
  let paths : Fin 3 → ℝ → A := ![αu, βu, γu]
  let starts : Fin 3 → Fin 3 := ![0, 1, 0]
  let ends : Fin 3 → Fin 3 := ![2, 2, 1]
  have hstart : ∀ i, paths i 0 = (![P, Q, Y] : Fin 3 → A) (starts i) := by
    intro i
    fin_cases i <;> simp [paths, starts, hαu0, hβu0, hγu0]
  have hend : ∀ i, paths i 1 = (![P, Q, Y] : Fin 3 → A) (ends i) := by
    intro i
    fin_cases i <;> simp [paths, ends, hαu1, hβu1, hγu1]
  have hcont : ∀ i, ContinuousOn (paths i) (Icc 0 1) := by
    intro i
    fin_cases i
    · exact hαc.continuousOn
    · exact hβc.continuousOn
    · exact hγc.continuousOn
  have hdist : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (paths i u) (paths i v) = dist (paths i 0) (paths i 1) * |u - v| := by
    intro i u hu v hv
    fin_cases i
    · change dist (αu u) (αu v) = dist (αu 0) (αu 1) * |u - v|
      rw [hαu0, hαu1]
      exact hαd u hu v hv
    · change dist (βu u) (βu v) = dist (βu 0) (βu 1) * |u - v|
      rw [hβu0, hβu1]
      exact hβd u hu v hv
    · change dist (γu u) (γu v) = dist (γu 0) (γu 1) * |u - v|
      rw [hγu0, hγu1]
      exact hγd u hu v hv
  have hYQ : dist y q = dist Y Q := by simpa only [dist_comm] using hQY
  have hcompare := matched_triangle_edge_family_dist_le hmid ![P, Q, Y] ![p, q, y]
    (three_vertex_distances_match P Q Y p q y hPY hYQ hPQ)
    starts ends paths hstart hend hcont hdist
  let g : SplitBoundaryRight q y → A :=
    Sum.elim (fun t => αu t.1) (fun t => β ⟨t.1, by simpa only [hQY] using t.2⟩)
  let edge : SplitBoundaryRight q y → Fin 3 := Sum.elim (fun _ => 0) (fun _ => 1)
  let time : SplitBoundaryRight q y → ℝ :=
    Sum.elim Subtype.val (fun t => t.1 / dist q y)
  have htime : ∀ i, time i ∈ Icc (0 : ℝ) 1 := by
    intro i
    cases i with
    | inl t => exact t.2
    | inr t =>
      by_cases h : dist q y = 0
      · simp [time, h]
      · exact ⟨div_nonneg t.2.1 dist_nonneg,
          (div_le_one (lt_of_le_of_ne dist_nonneg (Ne.symm h))).mpr t.2.2⟩
  have hshadow : ∀ i, g i = paths (edge i) (time i) := by
    intro i
    cases i with
    | inl t => rfl
    | inr t =>
      change β ⟨t.1, _⟩ = βu (t.1 / dist q y)
      simpa only [hQY] using
        (hβparam ⟨t.1, by simpa only [hQY] using t.2⟩).symm
  have hmodel : ∀ i, Vendored.RiemannDynamics.geodInterp
      ((![p, q, y] : Fin 3 → UpperHalfPlane) (starts (edge i)))
      ((![p, q, y] : Fin 3 → UpperHalfPlane) (ends (edge i))) (time i) =
        splitBoundaryRightModel p q y i := by
    intro i
    cases i <;> rfl
  have hseam : ∀ w, metricTriangleSharedSideMap hPQ γ w =
      γu (metricTriangleSharedSideParameter p q w).1 := by
    intro w
    dsimp only [metricTriangleSharedSideMap, metricTriangleSharedSideParameter]
    rw [hPQ]
    exact (hγparam _).symm
  refine ⟨g, ?_, ?_, hαu0, hαu1, ?_, fun _ => rfl⟩
  · intro i j
    rw [hshadow i, hshadow j]
    have h := hcompare (edge i) (edge j) (time i) (time j) (htime i) (htime j)
    rwa [hmodel i, hmodel j] at h
  · intro i w
    rw [hshadow i, hseam w]
    have h := hcompare (edge i) 2 (time i)
      (metricTriangleSharedSideParameter p q w).1 (htime i)
      (metricTriangleSharedSideParameter p q w).2
    change dist (paths (edge i) (time i))
      (γu (metricTriangleSharedSideParameter p q w).1) ≤
        dist (Vendored.RiemannDynamics.geodInterp
          ((![p, q, y] : Fin 3 → UpperHalfPlane) (starts (edge i)))
          ((![p, q, y] : Fin 3 → UpperHalfPlane) (ends (edge i))) (time i))
          (Vendored.RiemannDynamics.geodInterp p q
            (metricTriangleSharedSideParameter p q w).1) at h
    rwa [hmodel i, metricTriangleSharedSideParameter_interp] at h
  · exact unit_path_scaled_eval dist_nonneg α αu hαd hαz hαparam

end SystolicGrowth
