module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricTriangleInheritance

@[expose] public section

/-!
# Reparameterizing an inherited triangle boundary

The inherited boundary retains two arc-length pieces of its split side.
These indices pull its three parent sides back to unit-time interpolation,
including zero-length sides and zero-length pieces. This lets the first
boundary inheritance serve as a child comparison in a second inheritance.
-/

open Set

namespace SystolicGrowth

/-- Normalize an arc-length parameter, using zero at a collapsed interval. -/
noncomputable def metricBoundaryUnitParameter {d : ℝ} (hd : 0 ≤ d)
    (t : Icc (0 : ℝ) d) : Icc (0 : ℝ) 1 :=
  ⟨t.1 / d, by
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
      exact ⟨div_nonneg t.2.1 hd, (div_le_one hdpos).mpr t.2.2⟩⟩

/-- Reverse a unit-time parameter without excluding either endpoint. -/
def metricBoundaryReverseUnit (t : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 :=
  ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

@[simp] theorem metricBoundaryUnitParameter_val {d : ℝ} (hd : 0 ≤ d)
    (t : Icc (0 : ℝ) d) : (metricBoundaryUnitParameter hd t).1 = t.1 / d := rfl

@[simp] theorem metricBoundaryReverseUnit_val (t : Icc (0 : ℝ) 1) :
    (metricBoundaryReverseUnit t).1 = 1 - t.1 := rfl

@[simp] theorem metricBoundaryReverseUnit_reverse (t : Icc (0 : ℝ) 1) :
    metricBoundaryReverseUnit (metricBoundaryReverseUnit t) = t := by
  apply Subtype.ext
  simp [metricBoundaryReverseUnit]

/-- Reverse an arc-length interval while retaining its original domain. -/
def metricBoundaryReverseInterval {M : Type*} {d : ℝ} (_hd : 0 ≤ d)
    (α : Icc (0 : ℝ) d → M) (t : Icc (0 : ℝ) d) : M :=
  α ⟨d - t.1, ⟨sub_nonneg.mpr t.2.2, by linarith [t.2.1]⟩⟩

theorem metricBoundaryReverseInterval_isometry
    {M : Type*} [MetricSpace M] {d : ℝ} (hd : 0 ≤ d)
    (α : Icc (0 : ℝ) d → M) (hα : Isometry α) :
    Isometry (metricBoundaryReverseInterval hd α) := by
  apply Isometry.of_dist_eq
  intro s t
  simp only [metricBoundaryReverseInterval, hα.dist_eq, Subtype.dist_eq, Real.dist_eq]
  rw [show d - s.1 - (d - t.1) = t.1 - s.1 by ring, abs_sub_comm]

@[simp] theorem metricBoundaryReverseInterval_zero
    {M : Type*} {d : ℝ} (hd : 0 ≤ d) (α : Icc (0 : ℝ) d → M) :
    metricBoundaryReverseInterval hd α ⟨0, ⟨le_rfl, hd⟩⟩ =
      α ⟨d, ⟨hd, le_rfl⟩⟩ := by
  unfold metricBoundaryReverseInterval
  congr 1
  exact Subtype.ext (sub_zero d)

@[simp] theorem metricBoundaryReverseInterval_end
    {M : Type*} {d : ℝ} (hd : 0 ≤ d) (α : Icc (0 : ℝ) d → M) :
    metricBoundaryReverseInterval hd α ⟨d, ⟨hd, le_rfl⟩⟩ =
      α ⟨0, ⟨le_rfl, hd⟩⟩ := by
  unfold metricBoundaryReverseInterval
  congr 1
  exact Subtype.ext (sub_self d)

/-- Reverse an interval whose domain is written using its ordered endpoints.
The new domain uses the reversed endpoint distance, not a new chosen segment. -/
noncomputable def metricReverseDistanceInterval
    {M : Type*} [MetricSpace M] {x y : M}
    (α : Icc (0 : ℝ) (dist x y) → M) (t : Icc (0 : ℝ) (dist y x)) : M :=
  α ⟨dist x y - t.1, ⟨by simpa only [dist_comm y x] using sub_nonneg.mpr t.2.2,
    by linarith [t.2.1]⟩⟩

/-- Reversal is the ordinary interval reversal after transporting its domain. -/
theorem metricReverseDistanceInterval_eq
    {M : Type*} [MetricSpace M] {x y : M}
    (α : Icc (0 : ℝ) (dist x y) → M) (t : Icc (0 : ℝ) (dist y x)) :
    metricReverseDistanceInterval α t =
      metricBoundaryReverseInterval dist_nonneg α
        ⟨t.1, by simpa only [dist_comm y x] using t.2⟩ := rfl

theorem metricReverseDistanceInterval_isometry
    {M : Type*} [MetricSpace M] {x y : M}
    (α : Icc (0 : ℝ) (dist x y) → M) (hα : Isometry α) :
    Isometry (metricReverseDistanceInterval α) := by
  apply Isometry.of_dist_eq
  intro s t
  simp only [metricReverseDistanceInterval, hα.dist_eq, Subtype.dist_eq, Real.dist_eq]
  rw [show dist x y - s.1 - (dist x y - t.1) = t.1 - s.1 by ring, abs_sub_comm]

@[simp] theorem metricReverseDistanceInterval_zero
    {M : Type*} [MetricSpace M] {x y : M}
    (α : Icc (0 : ℝ) (dist x y) → M)
    (hend : α ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    metricReverseDistanceInterval α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = y := by
  simpa only [metricReverseDistanceInterval, sub_zero] using hend

@[simp] theorem metricReverseDistanceInterval_end
    {M : Type*} [MetricSpace M] {x y : M}
    (α : Icc (0 : ℝ) (dist x y) → M)
    (hzero : α ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x) :
    metricReverseDistanceInterval α ⟨dist y x, ⟨dist_nonneg, le_rfl⟩⟩ = x := by
  simpa only [metricReverseDistanceInterval, dist_comm y x, sub_self] using hzero

/-- The explicit unit-time point on two consecutive arc-length intervals.
This is defined before any comparison triangle or third vertex is chosen. -/
noncomputable def metricTwoLegUnitPoint
    {M : Type*} [MetricSpace M] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (α : Icc (0 : ℝ) a → M) (β : Icc (0 : ℝ) b → M)
    (t : Icc (0 : ℝ) 1) : M :=
  if h : (a + b) * t.1 ≤ a then
    α ⟨(a + b) * t.1, ⟨mul_nonneg (add_nonneg ha hb) t.2.1, h⟩⟩
  else
    β ⟨(a + b) * t.1 - a, ⟨by linarith [not_le.mp h], by
      have := mul_le_mul_of_nonneg_left t.2.2 (add_nonneg ha hb)
      nlinarith⟩⟩

/-- Any map commutes with selecting the explicit point on a two-leg path.
No continuity, distance preservation or injectivity of the map is needed. -/
theorem metricTwoLegUnitPoint_map
    {M N : Type*} [MetricSpace M] [MetricSpace N] (F : M → N)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (α : Icc (0 : ℝ) a → M) (β : Icc (0 : ℝ) b → M)
    (t : Icc (0 : ℝ) 1) :
    F (metricTwoLegUnitPoint ha hb α β t) =
      metricTwoLegUnitPoint ha hb (F ∘ α) (F ∘ β) t := by
  unfold metricTwoLegUnitPoint
  split_ifs <;> rfl

@[simp] theorem metricTwoLegUnitPoint_zero
    {M : Type*} [MetricSpace M] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (α : Icc (0 : ℝ) a → M) (β : Icc (0 : ℝ) b → M) :
    metricTwoLegUnitPoint ha hb α β ⟨0, by norm_num⟩ =
      α ⟨0, ⟨le_rfl, ha⟩⟩ := by
  simp [metricTwoLegUnitPoint, ha]

/-- Reversing the two legs reverses their explicit unit-time point.
At the common endpoint the two selected representations agree by `hjoin`. -/
theorem metricTwoLegUnitPoint_reverse
    {M : Type*} [MetricSpace M] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (α : Icc (0 : ℝ) a → M) (β : Icc (0 : ℝ) b → M)
    (hjoin : α ⟨a, ⟨ha, le_rfl⟩⟩ = β ⟨0, ⟨le_rfl, hb⟩⟩)
    (t : Icc (0 : ℝ) 1) :
    metricTwoLegUnitPoint hb ha (metricBoundaryReverseInterval hb β)
      (metricBoundaryReverseInterval ha α) t =
        metricTwoLegUnitPoint ha hb α β (metricBoundaryReverseUnit t) := by
  unfold metricTwoLegUnitPoint metricBoundaryReverseUnit
  by_cases hr : (b + a) * t.1 ≤ b
  · rw [dif_pos hr]
    by_cases hs : (a + b) * (1 - t.1) ≤ a
    · rw [dif_pos hs]
      dsimp only [metricBoundaryReverseInterval]
      have heqr : (b + a) * t.1 = b := by nlinarith [hr, hs]
      have heqs : (a + b) * (1 - t.1) = a := by nlinarith [hr, hs]
      have hβbounds : b - (b + a) * t.1 ∈ Icc (0 : ℝ) b :=
        ⟨sub_nonneg.mpr hr, by
          have := mul_nonneg (add_nonneg hb ha) t.2.1
          linarith⟩
      have hαbounds : (a + b) * (1 - t.1) ∈ Icc (0 : ℝ) a :=
        ⟨mul_nonneg (add_nonneg ha hb) (sub_nonneg.mpr t.2.2), hs⟩
      have hβ0 :
          (⟨b - (b + a) * t.1, hβbounds⟩ : Icc (0 : ℝ) b) =
            ⟨0, ⟨le_rfl, hb⟩⟩ := Subtype.ext (by
              change b - (b + a) * t.1 = 0
              linarith [heqr])
      have hαa :
          (⟨(a + b) * (1 - t.1), hαbounds⟩ : Icc (0 : ℝ) a) =
            ⟨a, ⟨ha, le_rfl⟩⟩ := Subtype.ext heqs
      rw [hβ0, hαa]
      exact hjoin.symm
    · rw [dif_neg hs]
      dsimp only [metricBoundaryReverseInterval]
      congr 1
      apply Subtype.ext
      dsimp
      ring
  · rw [dif_neg hr]
    by_cases hs : (a + b) * (1 - t.1) ≤ a
    · rw [dif_pos hs]
      dsimp only [metricBoundaryReverseInterval]
      congr 1
      apply Subtype.ext
      dsimp
      ring
    · exfalso
      nlinarith [not_le.mp hr, not_le.mp hs]

/-- Two minimizing consecutive segments have a continuous unit-time path
through exactly the explicit two-leg points. Its midpoint is consequently
fixed independently of the point against which comparison is tested. -/
theorem exists_unit_path_metricTwoLegUnitPoint
    {M : Type*} [MetricSpace M] {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (α : Icc (0 : ℝ) a → M) (β : Icc (0 : ℝ) b → M)
    (hα : Isometry α) (hβ : Isometry β)
    (hjoin : α ⟨a, ⟨ha, le_rfl⟩⟩ = β ⟨0, ⟨le_rfl, hb⟩⟩)
    (hdist : dist (α ⟨0, ⟨le_rfl, ha⟩⟩) (β ⟨b, ⟨hb, le_rfl⟩⟩) = a + b) :
    ∃ γ : ℝ → M, Continuous γ ∧
      (∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        dist (γ u) (γ v) = (a + b) * |u - v|) ∧
      γ 0 = α ⟨0, ⟨le_rfl, ha⟩⟩ ∧
      γ 1 = β ⟨b, ⟨hb, le_rfl⟩⟩ ∧
      ∀ t : Icc (0 : ℝ) 1, γ t.1 = metricTwoLegUnitPoint ha hb α β t := by
  obtain ⟨σ, hσ, hleft, hright⟩ :=
    exists_isometric_two_leg_interval ha hb α β hα hβ hjoin hdist
  obtain ⟨γ, hcont, hmetric, hzero, hend, hparam⟩ :=
    unit_path_of_isometric_interval (add_nonneg ha hb) σ hσ
  have hscale (t : Icc (0 : ℝ) 1) : (a + b) * t.1 ∈ Icc (0 : ℝ) (a + b) :=
    ⟨mul_nonneg (add_nonneg ha hb) t.2.1, by
      simpa using mul_le_mul_of_nonneg_left t.2.2 (add_nonneg ha hb)⟩
  have hγscale (t : Icc (0 : ℝ) 1) :
      γ t.1 = σ ⟨(a + b) * t.1, hscale t⟩ := by
    by_cases hd : a + b = 0
    · have hγ0 : γ t.1 = γ 0 := dist_eq_zero.mp (by
        simpa only [hd, zero_mul] using hmetric t.1 t.2 0 (by norm_num))
      rw [hγ0, hzero]
      congr 1
      exact Subtype.ext (by simp [hd])
    · simpa only [mul_div_cancel_left₀ _ hd] using
        hparam ⟨(a + b) * t.1, hscale t⟩
  refine ⟨γ, hcont, hmetric, ?_, ?_, ?_⟩
  · exact hzero.trans (hleft ⟨0, ⟨le_rfl, ha⟩⟩)
  · exact hend.trans (hright ⟨b, ⟨hb, le_rfl⟩⟩)
  · intro t
    rw [hγscale]
    unfold metricTwoLegUnitPoint
    split_ifs with h
    · exact hleft ⟨(a + b) * t.1,
        ⟨mul_nonneg (add_nonneg ha hb) t.2.1, h⟩⟩
    · have hbounds : (a + b) * t.1 - a ∈ Icc (0 : ℝ) b :=
        ⟨by linarith [not_le.mp h], by
          have := mul_le_mul_of_nonneg_left t.2.2 (add_nonneg ha hb)
          nlinarith⟩
      have hresult := hright ⟨(a + b) * t.1 - a, hbounds⟩
      have heq :
          (⟨a + ((a + b) * t.1 - a),
            ⟨add_nonneg ha hbounds.1, add_le_add le_rfl hbounds.2⟩⟩ :
            Icc (0 : ℝ) (a + b)) = ⟨(a + b) * t.1, hscale t⟩ :=
        Subtype.ext (by dsimp; ring)
      exact heq ▸ hresult

/-- Unit-time indices on the parent's unsplit left edge. -/
def splitBoundaryParentPXIndex (q x y : UpperHalfPlane)
    (t : Icc (0 : ℝ) 1) : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y :=
  .inl (.inl t)

/-- Unit-time indices on the parent's unsplit right edge. -/
def splitBoundaryParentPYIndex (q x y : UpperHalfPlane)
    (t : Icc (0 : ℝ) 1) : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y :=
  .inr (.inl t)

/-- Unit-time indices on the parent side subdivided at the seam point.
At the seam either representation agrees metrically; we select the left one. -/
noncomputable def splitBoundaryParentXYIndex (q x y : UpperHalfPlane)
    (t : Icc (0 : ℝ) 1) : SplitBoundaryLeft x q ⊕ SplitBoundaryRight q y :=
  if h : (dist x q + dist q y) * t.1 ≤ dist x q then
    .inl (.inr ⟨(dist x q + dist q y) * t.1,
      ⟨mul_nonneg (add_nonneg dist_nonneg dist_nonneg) t.2.1, h⟩⟩)
  else
    .inr (.inr ⟨(dist x q + dist q y) * t.1 - dist x q,
      ⟨by linarith [not_le.mp h], by
        have := mul_le_mul_of_nonneg_left t.2.2
          (add_nonneg (dist_nonneg (x := x) (y := q))
            (dist_nonneg (x := q) (y := y)))
        nlinarith⟩⟩)

@[simp] theorem splitBoundaryParentXYIndex_zero (q x y : UpperHalfPlane) :
    splitBoundaryParentXYIndex q x y ⟨0, by norm_num⟩ =
      .inl (.inr ⟨0, ⟨le_rfl, dist_nonneg⟩⟩) := by
  simp [splitBoundaryParentXYIndex, dist_nonneg]

@[simp] theorem splitBoundaryParentPXIndex_model (q x y P X Y : UpperHalfPlane)
    (t : Icc (0 : ℝ) 1) :
    splitBoundaryParentModel q x y P X Y (splitBoundaryParentPXIndex q x y t) =
      Vendored.RiemannDynamics.geodInterp P X t.1 := rfl

@[simp] theorem splitBoundaryParentPYIndex_model (q x y P X Y : UpperHalfPlane)
    (t : Icc (0 : ℝ) 1) :
    splitBoundaryParentModel q x y P X Y (splitBoundaryParentPYIndex q x y t) =
      Vendored.RiemannDynamics.geodInterp P Y t.1 := rfl

/-- The normalized split-side index has exactly the parent's model point;
the length-zero case is obtained from equality of the parent endpoints. -/
theorem splitBoundaryParentXYIndex_model (q x y P X Y : UpperHalfPlane)
    (hXY : dist X Y = dist x q + dist q y) (t : Icc (0 : ℝ) 1) :
    splitBoundaryParentModel q x y P X Y (splitBoundaryParentXYIndex q x y t) =
      Vendored.RiemannDynamics.geodInterp X Y t.1 := by
  by_cases hd : dist x q + dist q y = 0
  · have h : X = Y := dist_eq_zero.mp (hXY.trans hd)
    subst Y
    simp [splitBoundaryParentXYIndex, splitBoundaryParentModel, hd, dist_nonneg,
      Vendored.RiemannDynamics.geodInterp_self]
  · unfold splitBoundaryParentXYIndex
    split_ifs with h
    · simp only [splitBoundaryParentModel, Sum.elim_inl, Sum.elim_inr]
      congr 1
      field_simp
    · simp only [splitBoundaryParentModel, Sum.elim_inr]
      congr 1
      field_simp
      ring

/-- Reversing a model edge reverses its normalized parameter.
The proof uses geodesic uniqueness and also covers coincident endpoints. -/
theorem metricBoundaryGeodInterp_reverse_of_mem_Icc
    (a b : UpperHalfPlane) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Vendored.RiemannDynamics.geodInterp b a t =
      Vendored.RiemannDynamics.geodInterp a b (1 - t) := by
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hz := Vendored.RiemannDynamics.geodInterp_mem_geodSeg b a ht
  have hw : Vendored.RiemannDynamics.geodInterp a b (1 - t) ∈
      Vendored.RiemannDynamics.geodSeg b a := by
    rw [Vendored.RiemannDynamics.geodSeg_comm]
    exact Vendored.RiemannDynamics.geodInterp_mem_geodSeg a b ht'
  apply Vendored.RiemannDynamics.eq_on_geodSeg_of_dist_eq hz hw
  rw [Vendored.RiemannDynamics.dist_geodInterp_left b a ht,
    dist_comm b (Vendored.RiemannDynamics.geodInterp a b (1 - t)),
    Vendored.RiemannDynamics.dist_geodInterp_right_abs,
    show 1 - (1 - t) = t by ring, abs_of_nonneg ht.1, dist_comm b a]

#print axioms splitBoundaryParentXYIndex_model
#print axioms metricBoundaryGeodInterp_reverse_of_mem_Icc
#print axioms exists_unit_path_metricTwoLegUnitPoint
#print axioms metricTwoLegUnitPoint_reverse
#print axioms metricBoundaryReverseInterval_isometry
#print axioms metricTwoLegUnitPoint_map
#print axioms metricReverseDistanceInterval_isometry

end SystolicGrowth
