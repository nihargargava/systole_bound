module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricGluingGeodesics
public import Geometry.MetricTriangleBoundaryComparison
public import Geometry.HyperbolicConvexGluing

@[expose] public section

/-!
# Boundary comparison inherited across a split triangle

The two child hyperbolic models are glued along their shared model edge.
Child boundary comparison bounds every actual cross-face distance by every
model seam route. In particular the original minimizing split remains
minimizing in this model quotient. This uses boundary maps, not solid
triangles or a comparison hypothesis on the original glued space.
-/

open Set

namespace SystolicGrowth

/-- The canonical arc-length parameterization of a hyperbolic edge. -/
noncomputable def hyperbolicArc (p q : UpperHalfPlane) :
    Icc (0 : ℝ) (dist p q) → UpperHalfPlane := fun t =>
  Vendored.RiemannDynamics.geodInterp p q (t.1 / dist p q)

theorem hyperbolicArc_isometry (p q : UpperHalfPlane) :
    Isometry (hyperbolicArc p q) := by
  apply Isometry.of_dist_eq
  intro s t
  by_cases h : dist p q = 0
  · have hs : s.1 = 0 := by linarith [s.2.1, s.2.2]
    have ht : t.1 = 0 := by linarith [t.2.1, t.2.2]
    have hst : s = t := Subtype.ext (hs.trans ht.symm)
    simp [hst]
  · simp only [hyperbolicArc, Vendored.RiemannDynamics.dist_geodInterp_pair,
      Subtype.dist_eq, Real.dist_eq]
    rw [← sub_div, abs_div, abs_of_nonneg dist_nonneg]
    field_simp

@[simp] theorem hyperbolicArc_zero (p q : UpperHalfPlane) :
    hyperbolicArc p q ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p := by
  simpa only [hyperbolicArc, zero_div] using Vendored.RiemannDynamics.geodInterp_zero p q

@[simp] theorem hyperbolicArc_end (p q : UpperHalfPlane) :
    hyperbolicArc p q ⟨dist p q, ⟨dist_nonneg, le_rfl⟩⟩ = q := by
  by_cases h : dist p q = 0
  · have hpq : p = q := dist_eq_zero.mp h
    simp only [hyperbolicArc, hpq, dist_self, div_zero,
      Vendored.RiemannDynamics.geodInterp_self]
  · simpa only [hyperbolicArc, div_self h] using Vendored.RiemannDynamics.geodInterp_one p q

/-- Child boundary domination and a common shared-edge map bound every
cross-face actual distance by the distance in the model metric quotient. -/
theorem metricGlue_boundary_dist_le
    {M A B S I J : Type*} [MetricSpace M] [MetricSpace A] [MetricSpace B]
    [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : I → M) (g : J → M) (f' : I → A) (g' : J → B) (δ : S → M)
    (hf : ∀ i q, dist (f i) (δ q) ≤ dist (f' i) (Φ q))
    (hg : ∀ j q, dist (g j) (δ q) ≤ dist (g' j) (Ψ q))
    (i : I) (j : J) :
    dist (f i) (g j) ≤
      dist (Metric.toGlueL hΦ hΨ (f' i)) (Metric.toGlueR hΦ hΨ (g' j)) := by
  rw [metricGlue_cross_dist_eq_iInf hΦ hΨ]
  apply le_ciInf
  intro q
  calc
    dist (f i) (g j) ≤ dist (f i) (δ q) + dist (δ q) (g j) := dist_triangle _ _ _
    _ ≤ dist (f' i) (Φ q) + dist (g' j) (Ψ q) := by
      exact add_le_add (hf i q) (by simpa only [dist_comm] using hg j q)

/-- Full pairwise boundary domination, including both same-child cases. -/
theorem metricGlue_boundary_sum_dist_le
    {M A B S I J : Type*} [MetricSpace M] [MetricSpace A] [MetricSpace B]
    [MetricSpace S] [Nonempty S]
    {Φ : S → A} {Ψ : S → B} (hΦ : Isometry Φ) (hΨ : Isometry Ψ)
    (f : I → M) (g : J → M) (f' : I → A) (g' : J → B) (δ : S → M)
    (hff : ∀ i j, dist (f i) (f j) ≤ dist (f' i) (f' j))
    (hgg : ∀ i j, dist (g i) (g j) ≤ dist (g' i) (g' j))
    (hf : ∀ i q, dist (f i) (δ q) ≤ dist (f' i) (Φ q))
    (hg : ∀ j q, dist (g j) (δ q) ≤ dist (g' j) (Ψ q))
    (u v : I ⊕ J) :
    dist (Sum.elim f g u) (Sum.elim f g v) ≤
      dist (Sum.elim (Metric.toGlueL hΦ hΨ ∘ f') (Metric.toGlueR hΦ hΨ ∘ g') u)
        (Sum.elim (Metric.toGlueL hΦ hΨ ∘ f') (Metric.toGlueR hΦ hΨ ∘ g') v) := by
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      simpa only [Sum.elim_inl, Function.comp_apply,
        (Metric.toGlueL_isometry hΦ hΨ).dist_eq] using hff i j
    | inr j => exact metricGlue_boundary_dist_le hΦ hΨ f g f' g' δ hf hg i j
  | inr i =>
    cases v with
    | inl j =>
      simpa only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, dist_comm]
        using metricGlue_boundary_dist_le hΦ hΨ f g f' g' δ hf hg j i
    | inr j =>
      simpa only [Sum.elim_inr, Function.comp_apply,
        (Metric.toGlueR_isometry hΦ hΨ).dist_eq] using hgg i j

/-- All pairs on a family of model-matched boundary edges satisfy comparison.
The endpoint distance matrix is matched; there need not be positive edges. -/
theorem metric_boundary_family_dist_le
    {M I : Type*} [MetricSpace M]
    (hmid : ∀ x y : M, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (γ : I → ℝ → M) (a b : I → UpperHalfPlane)
    (hcont : ∀ i, ContinuousOn (γ i) (Icc 0 1))
    (hdist : ∀ i, ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ i u) (γ i v) = dist (γ i 0) (γ i 1) * |u - v|)
    (hlen : ∀ i, dist (a i) (b i) = dist (γ i 0) (γ i 1))
    (h00 : ∀ i j, dist (γ i 0) (γ j 0) = dist (a i) (a j))
    (h01 : ∀ i j, dist (γ i 0) (γ j 1) = dist (a i) (b j))
    (h11 : ∀ i j, dist (γ i 1) (γ j 1) = dist (b i) (b j))
    (i j : I) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ i s) (γ j t) ≤
      dist (Vendored.RiemannDynamics.geodInterp (a i) (b i) s)
        (Vendored.RiemannDynamics.geodInterp (a j) (b j) t) := by
  have hleft := metric_segment_dist_le_geodInterp_of_endpoint_bounds hmid
    (γ j) (hcont j) (hdist j) (γ i 0) (a j) (b j) (a i) (hlen j)
    (h00 i j).le (h01 i j).le t ht
  have hright := metric_segment_dist_le_geodInterp_of_endpoint_bounds hmid
    (γ j) (hcont j) (hdist j) (γ i 1) (a j) (b j) (b i) (hlen j)
    (by simpa only [dist_comm] using (h01 j i).le) (h11 i j).le t ht
  have h := metric_segment_dist_le_geodInterp_of_endpoint_bounds hmid
    (γ i) (hcont i) (hdist i) (γ j t) (a i) (b i)
    (Vendored.RiemannDynamics.geodInterp (a j) (b j) t) (hlen i)
    (by simpa only [dist_comm] using hleft)
    (by simpa only [dist_comm] using hright) s hs
  simpa only [dist_comm] using h

/-- Normalize a genuine isometric interval to a continuous unit-time path,
retaining every arc-length point, including when the interval has length zero. -/
theorem unit_path_of_isometric_interval
    {M : Type*} [MetricSpace M] {d : ℝ} (hd : 0 ≤ d)
    (σ : Icc (0 : ℝ) d → M) (hσ : Isometry σ) :
    ∃ γ : ℝ → M, Continuous γ ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        dist (γ u) (γ v) = d * |u - v|) ∧
      γ 0 = σ ⟨0, ⟨le_rfl, hd⟩⟩ ∧
      γ 1 = σ ⟨d, ⟨hd, le_rfl⟩⟩ ∧
      ∀ t : Icc (0 : ℝ) d, γ (t.1 / d) = σ t := by
  let γ : ℝ → M := fun t => σ (projIcc 0 d hd (d * t))
  have hscale (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : d * t ∈ Icc (0 : ℝ) d :=
    ⟨mul_nonneg hd ht.1, by simpa using mul_le_mul_of_nonneg_left ht.2 hd⟩
  have hγon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ t = σ ⟨d * t, hscale t ht⟩ := by
    dsimp [γ]
    rw [projIcc_of_mem hd (hscale t ht)]
  refine ⟨γ, hσ.continuous.comp
    (continuous_projIcc.comp (continuous_const.mul continuous_id)), ?_, ?_, ?_, ?_⟩
  · intro u hu v hv
    rw [hγon u hu, hγon v hv, hσ.dist_eq, Subtype.dist_eq, Real.dist_eq,
      show d * u - d * v = d * (u - v) by ring, abs_mul, abs_of_nonneg hd]
  · rw [hγon 0 (by norm_num)]
    congr 1
    exact Subtype.ext (mul_zero d)
  · rw [hγon 1 (by norm_num)]
    congr 1
    exact Subtype.ext (mul_one d)
  · intro t
    by_cases hd0 : d = 0
    · have ht0 : t.1 = 0 := by linarith [t.2.1, t.2.2]
      have ht : t = ⟨0, ⟨le_rfl, hd⟩⟩ := Subtype.ext ht0
      rw [ht]
      simp only [zero_div]
      rw [hγon 0 (by norm_num)]
      congr 1
      exact Subtype.ext (mul_zero d)
    · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      have ht : t.1 / d ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg t.2.1 hd, (div_le_one hdpos).mpr t.2.2⟩
      rw [hγon _ ht]
      congr 1
      exact Subtype.ext (mul_div_cancel₀ _ hd0)

/-- The left child's outer edge and its leg of the split side. -/
abbrev SplitBoundaryLeft (x q : UpperHalfPlane) :=
  Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) (dist x q)

/-- The right child's outer edge and its leg of the split side. -/
abbrev SplitBoundaryRight (q y : UpperHalfPlane) :=
  Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) (dist q y)

noncomputable def splitBoundaryLeftModel (p q x : UpperHalfPlane) :
    SplitBoundaryLeft x q → UpperHalfPlane :=
  Sum.elim (fun t => Vendored.RiemannDynamics.geodInterp p x t.1) (hyperbolicArc x q)

noncomputable def splitBoundaryRightModel (p q y : UpperHalfPlane) :
    SplitBoundaryRight q y → UpperHalfPlane :=
  Sum.elim (fun t => Vendored.RiemannDynamics.geodInterp p y t.1) (hyperbolicArc q y)

/-- Corresponding points on the unsplit parent hyperbolic model boundary.
The split side is parameterized by the sum of its two actual leg lengths. -/
noncomputable def splitBoundaryParentModel (q x y P X Y : UpperHalfPlane) :
    SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y → UpperHalfPlane :=
  Sum.elim
    (Sum.elim (fun t => Vendored.RiemannDynamics.geodInterp P X t.1)
      (fun t => Vendored.RiemannDynamics.geodInterp X Y (t.1 / (dist x q + dist q y))))
    (Sum.elim (fun t => Vendored.RiemannDynamics.geodInterp P Y t.1)
      (fun t => Vendored.RiemannDynamics.geodInterp X Y
        ((dist x q + t.1) / (dist x q + dist q y))))

private theorem div_mem_unit_of_mem_nonneg_interval {d t : ℝ}
    (hd : 0 ≤ d) (ht : t ∈ Icc (0 : ℝ) d) : t / d ∈ Icc (0 : ℝ) 1 := by
  by_cases hd0 : d = 0
  · have ht0 : t = 0 := by rw [hd0] at ht; linarith [ht.1, ht.2]
    simp [hd0, ht0]
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    exact ⟨div_nonneg ht.1 hd, (div_le_one hdpos).mpr ht.2⟩

/-- Full boundary inheritance from the two child models. The actual child
maps are compared only with their own hyperbolic models and their common
shared-edge map. The model quotient's curvature is proved independently by
`HyperbolicConvexGlue`, not assumed for the original space. The conclusion
covers every pair on the three parent edges, including zero-length legs. -/
theorem metric_triangle_boundary_inheritance
    {M : Type*} [MetricSpace M]
    (S : Set UpperHalfPlane) [Nonempty S] [CompleteSpace S]
    (hconv : ∀ a ∈ S, ∀ b ∈ S, Vendored.RiemannDynamics.geodSeg a b ⊆ S)
    (p q x y : UpperHalfPlane) (hp : p ∈ S) (hq : q ∈ S)
    (f : SplitBoundaryLeft x q → M) (g : SplitBoundaryRight q y → M)
    (δ : S → M)
    (hff : ∀ i j, dist (f i) (f j) ≤
      dist (splitBoundaryLeftModel p q x i) (splitBoundaryLeftModel p q x j))
    (hgg : ∀ i j, dist (g i) (g j) ≤
      dist (splitBoundaryRightModel p q y i) (splitBoundaryRightModel p q y j))
    (hf : ∀ i w, dist (f i) (δ w) ≤ dist (splitBoundaryLeftModel p q x i) w.1)
    (hg : ∀ i w, dist (g i) (δ w) ≤ dist (splitBoundaryRightModel p q y i) w.1)
    (hactual : dist (f (.inl ⟨1, by norm_num⟩)) (g (.inl ⟨1, by norm_num⟩)) =
      dist x q + dist q y)
    (P X Y : UpperHalfPlane)
    (hPX : dist P X = dist p x) (hPY : dist P Y = dist p y)
    (hXY : dist X Y = dist x q + dist q y)
    (u v : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y) :
    dist (Sum.elim f g u) (Sum.elim f g v) ≤
      dist (splitBoundaryParentModel q x y P X Y u)
        (splitBoundaryParentModel q x y P X Y v) := by
  classical
  let L := HyperbolicConvexGlue.left S
  let R := HyperbolicConvexGlue.right S
  have hL : Isometry L := HyperbolicConvexGlue.left_isometry
  have hR : Isometry R := HyperbolicConvexGlue.right_isometry
  let a := dist x q
  let b := dist q y
  let d := a + b
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have hd : 0 ≤ d := add_nonneg ha hb
  have hbase : R p = L p := (HyperbolicConvexGlue.commute ⟨p, hp⟩).symm
  have hxy : dist (L x) (R y) = d := by
    apply le_antisymm
    · rw [HyperbolicConvexGlue.cross_dist]
      have hbounded : BddBelow (range (fun w : S => dist x w.1 + dist y w.1)) :=
        ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩
      have hupper := ciInf_le hbounded (⟨q, hq⟩ : S)
      simpa only [a, b, d, dist_comm y q] using hupper
    · have h := metricGlue_boundary_dist_le isometry_subtype_coe isometry_subtype_coe
        f g (splitBoundaryLeftModel p q x) (splitBoundaryRightModel p q y) δ hf hg
        (.inl ⟨1, by norm_num⟩) (.inl ⟨1, by norm_num⟩)
      simpa only [hactual, splitBoundaryLeftModel, splitBoundaryRightModel, Sum.elim_inl,
        Vendored.RiemannDynamics.geodInterp_one] using h
  let α : Icc (0 : ℝ) a → HyperbolicConvexGlue.Carrier S := L ∘ hyperbolicArc x q
  let β : Icc (0 : ℝ) b → HyperbolicConvexGlue.Carrier S := R ∘ hyperbolicArc q y
  have hα : Isometry α := HyperbolicConvexGlue.left_isometry.comp (hyperbolicArc_isometry x q)
  have hβ : Isometry β := HyperbolicConvexGlue.right_isometry.comp (hyperbolicArc_isometry q y)
  have hjoin : α ⟨a, ⟨ha, le_rfl⟩⟩ = β ⟨0, ⟨le_rfl, hb⟩⟩ := by
    simp only [α, β, Function.comp_apply, a, hyperbolicArc_end, hyperbolicArc_zero]
    exact HyperbolicConvexGlue.commute ⟨q, hq⟩
  have hends : dist (α ⟨0, ⟨le_rfl, ha⟩⟩) (β ⟨b, ⟨hb, le_rfl⟩⟩) = a + b := by
    simpa only [α, β, Function.comp_apply, b, hyperbolicArc_zero, hyperbolicArc_end]
      using hxy
  obtain ⟨σ, hσ, hleft, hright⟩ := exists_isometric_two_leg_interval ha hb α β hα hβ hjoin hends
  obtain ⟨γ, hγcont, hγdist, hγzero, hγone, hγparam⟩ := unit_path_of_isometric_interval hd σ hσ
  have hγ0 : γ 0 = L x := by
    rw [hγzero]
    simpa only [α, Function.comp_apply, hyperbolicArc_zero] using hleft ⟨0, ⟨le_rfl, ha⟩⟩
  have hγ1 : γ 1 = R y := by
    rw [hγone]
    simpa only [β, Function.comp_apply, b, hyperbolicArc_end] using hright ⟨b, ⟨hb, le_rfl⟩⟩
  let paths : Fin 3 → ℝ → HyperbolicConvexGlue.Carrier S :=
    ![fun t => L (Vendored.RiemannDynamics.geodInterp p x t),
      fun t => R (Vendored.RiemannDynamics.geodInterp p y t), γ]
  let vertices : Fin 3 → HyperbolicConvexGlue.Carrier S := ![L p, L x, R y]
  let modelVertices : Fin 3 → UpperHalfPlane := ![P, X, Y]
  let starts : Fin 3 → Fin 3 := ![0, 0, 1]
  let ends : Fin 3 → Fin 3 := ![1, 2, 2]
  have hstart : ∀ i, paths i 0 = vertices (starts i) := by
    intro i
    fin_cases i <;> simp [paths, vertices, starts, Vendored.RiemannDynamics.geodInterp_zero,
      hbase, hγ0]
  have hend : ∀ i, paths i 1 = vertices (ends i) := by
    intro i
    fin_cases i <;> simp [paths, vertices, ends, Vendored.RiemannDynamics.geodInterp_one, hγ1]
  have hvertices : ∀ i j, dist (vertices i) (vertices j) =
      dist (modelVertices i) (modelVertices j) := by
    have hpx : dist (L p) (L x) = dist P X := (hL.dist_eq p x).trans hPX.symm
    have hpy : dist (L p) (R y) = dist P Y := by
      rw [← hbase, hR.dist_eq, hPY]
    have hxy' : dist (L x) (R y) = dist X Y := hxy.trans hXY.symm
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [vertices, modelVertices, hpx, hpy, hxy', dist_comm]
  have hpathscont : ∀ i, ContinuousOn (paths i) (Icc 0 1) := by
    intro i
    have hinterp (z : UpperHalfPlane) :
        Continuous (fun t : ℝ => Vendored.RiemannDynamics.geodInterp p z t) :=
      Vendored.RiemannDynamics.continuous_geodInterp.comp
        (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    fin_cases i
    · exact (HyperbolicConvexGlue.left_isometry.continuous.comp (hinterp x)).continuousOn
    · exact (HyperbolicConvexGlue.right_isometry.continuous.comp (hinterp y)).continuousOn
    · exact hγcont.continuousOn
  have hpathsdist : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (paths i s) (paths i t) = dist (paths i 0) (paths i 1) * |s - t| := by
    intro i s hs t ht
    fin_cases i
    · change dist (L (Vendored.RiemannDynamics.geodInterp p x s))
        (L (Vendored.RiemannDynamics.geodInterp p x t)) =
          dist (L (Vendored.RiemannDynamics.geodInterp p x 0))
            (L (Vendored.RiemannDynamics.geodInterp p x 1)) * |s - t|
      simp only [hL.dist_eq,
        Vendored.RiemannDynamics.dist_geodInterp_pair, Vendored.RiemannDynamics.geodInterp_zero,
        Vendored.RiemannDynamics.geodInterp_one]
      ring
    · change dist (R (Vendored.RiemannDynamics.geodInterp p y s))
        (R (Vendored.RiemannDynamics.geodInterp p y t)) =
          dist (R (Vendored.RiemannDynamics.geodInterp p y 0))
            (R (Vendored.RiemannDynamics.geodInterp p y 1)) * |s - t|
      simp only [hR.dist_eq,
        Vendored.RiemannDynamics.dist_geodInterp_pair, Vendored.RiemannDynamics.geodInterp_zero,
        Vendored.RiemannDynamics.geodInterp_one]
      ring
    · change dist (γ s) (γ t) = dist (γ 0) (γ 1) * |s - t|
      rw [hγ0, hγ1, hxy]
      exact hγdist s hs t ht
  let edge : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y → Fin 3 :=
    Sum.elim (Sum.elim (fun _ => 0) (fun _ => 2))
      (Sum.elim (fun _ => 1) (fun _ => 2))
  let time : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y → ℝ :=
    Sum.elim (Sum.elim Subtype.val (fun t => t.1 / d))
      (Sum.elim Subtype.val (fun t => (a + t.1) / d))
  have htime : ∀ w, time w ∈ Icc (0 : ℝ) 1 := by
    intro w
    rcases w with (s | t) | (s | t)
    · exact s.2
    · exact div_mem_unit_of_mem_nonneg_interval hd
        ⟨t.2.1, t.2.2.trans (le_add_of_nonneg_right hb)⟩
    · exact s.2
    · exact div_mem_unit_of_mem_nonneg_interval hd
        ⟨add_nonneg ha t.2.1, add_le_add le_rfl t.2.2⟩
  have hshadow : ∀ w,
      Sum.elim (L ∘ splitBoundaryLeftModel p q x) (R ∘ splitBoundaryRightModel p q y) w =
        paths (edge w) (time w) := by
    intro w
    rcases w with (s | t) | (s | t)
    · rfl
    · change L (hyperbolicArc x q t) = γ (t.1 / d)
      let t' : Icc (0 : ℝ) d :=
        ⟨t.1, ⟨t.2.1, t.2.2.trans (le_add_of_nonneg_right hb)⟩⟩
      rw [hγparam t']
      exact (hleft t).symm
    · rfl
    · change R (hyperbolicArc q y t) = γ ((a + t.1) / d)
      let t' : Icc (0 : ℝ) d :=
        ⟨a + t.1, ⟨add_nonneg ha t.2.1, add_le_add le_rfl t.2.2⟩⟩
      rw [hγparam t']
      exact (hright t).symm
  have hparent : ∀ w,
      Vendored.RiemannDynamics.geodInterp (modelVertices (starts (edge w)))
        (modelVertices (ends (edge w))) (time w) = splitBoundaryParentModel q x y P X Y w := by
    intro w
    rcases w with (s | t) | (s | t) <;> rfl
  have hdom := metricGlue_boundary_sum_dist_le isometry_subtype_coe isometry_subtype_coe
    f g (splitBoundaryLeftModel p q x) (splitBoundaryRightModel p q y) δ hff hgg hf hg u v
  change dist (Sum.elim f g u) (Sum.elim f g v) ≤
    dist (Sum.elim (L ∘ splitBoundaryLeftModel p q x) (R ∘ splitBoundaryRightModel p q y) u)
      (Sum.elim (L ∘ splitBoundaryLeftModel p q x) (R ∘ splitBoundaryRightModel p q y) v) at hdom
  rw [hshadow u, hshadow v] at hdom
  have hcompare := metric_boundary_family_dist_le
    (HyperbolicConvexGlue.exists_midpoint_cosh_all_test hconv) paths
    (fun i => modelVertices (starts i)) (fun i => modelVertices (ends i))
    hpathscont hpathsdist
    (fun i => by rw [hstart, hend]; exact (hvertices _ _).symm)
    (fun i j => by rw [hstart, hstart]; exact hvertices _ _)
    (fun i j => by rw [hstart, hend]; exact hvertices _ _)
    (fun i j => by rw [hend, hend]; exact hvertices _ _)
    (edge u) (edge v) (time u) (time v) (htime u) (htime v)
  rw [hparent u, hparent v] at hcompare
  exact hdom.trans hcompare

#print axioms hyperbolicArc_isometry
#print axioms metricGlue_boundary_dist_le
#print axioms metricGlue_boundary_sum_dist_le
#print axioms metric_boundary_family_dist_le
#print axioms metric_triangle_boundary_inheritance

end SystolicGrowth
