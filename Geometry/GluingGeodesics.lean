module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingMidpoints
public import Geometry.GluingDyadicGrid
public import Geometry.GluingDyadicExtension
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Path

@[expose] public section

/-!
# Actual intrinsic-metric segments in the glued carrier

Coherent exact midpoint grids give a well-defined scaled isometry on the
concrete dyadic unit interval. Completeness extends it to a genuine path
with the exact distance law. The glued carrier supplies its already
constructed midpoints and original compactness, not an assumed geodesic
or curvature structure.
-/

open Set

namespace SystolicGrowth

private theorem gluingDyadicCoordinate_rescale (n q k : ℕ) :
    ((k * 2 ^ q : ℕ) : ℝ) / (2 : ℝ) ^ (n + q) = (k : ℝ) / (2 : ℝ) ^ n := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  field_simp

section DyadicMap

variable {M : Type*} [PseudoMetricSpace M]

/-- Passing both indices to an actual common refinement gives the exact
distance law across arbitrary grid levels. -/
theorem midpointDyadicGrid_dist_cross (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) (n p : ℕ) {i j : ℕ} (hi : i ≤ 2 ^ n) (hj : j ≤ 2 ^ p) :
    dist (midpointDyadicGrid m x y n i) (midpointDyadicGrid m x y p j) =
      dist x y * |(i : ℝ) / (2 : ℝ) ^ n - (j : ℝ) / (2 : ℝ) ^ p| := by
  have hi' : i * 2 ^ p ≤ 2 ^ (n + p) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hi
  have hj' : j * 2 ^ n ≤ 2 ^ (n + p) := by
    rw [Nat.add_comm n p, pow_add]
    exact Nat.mul_le_mul_right _ hj
  have hs : midpointDyadicGrid m x y (n + p) (j * 2 ^ n) =
      midpointDyadicGrid m x y p j := by
    simpa only [Nat.add_comm] using midpointDyadicGrid_rescale m x y p n j
  have hcj : ((j * 2 ^ n : ℕ) : ℝ) / (2 : ℝ) ^ (n + p) =
      (j : ℝ) / (2 : ℝ) ^ p := by
    simpa only [Nat.add_comm] using gluingDyadicCoordinate_rescale p n j
  calc
    dist (midpointDyadicGrid m x y n i) (midpointDyadicGrid m x y p j) =
        dist (midpointDyadicGrid m x y (n + p) (i * 2 ^ p))
          (midpointDyadicGrid m x y (n + p) (j * 2 ^ n)) := by
      rw [midpointDyadicGrid_rescale, hs]
    _ = _ := (midpointDyadicGrid_dist m hm x y (n + p) hi' hj').trans (by
      rw [gluingDyadicCoordinate_rescale, hcj])

/-- Choose a dyadic representation only to evaluate the constructed grid.
The exact cross-grid law below proves independence of that representation. -/
noncomputable def midpointDyadicUnitMap (m : M → M → M) (x y : M)
    (t : GluingDyadicUnitInterval) : M :=
  midpointDyadicGrid m x y t.property.choose t.property.choose_spec.choose

/-- The actual chosen grid map obeys the scaled distance law on the whole
dyadic domain, not only on one fixed finite grid. -/
theorem midpointDyadicUnitMap_dist (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) (s t : GluingDyadicUnitInterval) :
    dist (midpointDyadicUnitMap m x y s) (midpointDyadicUnitMap m x y t) =
      dist x y * |((s : unitInterval) : ℝ) - ((t : unitInterval) : ℝ)| := by
  have hs := s.property.choose_spec.choose_spec
  have ht := t.property.choose_spec.choose_spec
  unfold midpointDyadicUnitMap
  rw [midpointDyadicGrid_dist_cross m hm x y _ _ hs.1 ht.1, ← hs.2, ← ht.2]

end DyadicMap

section Segment

variable {M : Type*} [MetricSpace M]

/-- A representation chosen by the domain evaluates to the same actual
point as every explicit bounded grid representation. -/
theorem midpointDyadicUnitMap_point (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) (n k : ℕ) (hk : k ≤ 2 ^ n) :
    midpointDyadicUnitMap m x y (gluingDyadicUnitPoint n k hk) =
      midpointDyadicGrid m x y n k := by
  let t := gluingDyadicUnitPoint n k hk
  have ht := t.property.choose_spec.choose_spec
  apply eq_of_dist_eq_zero
  change dist (midpointDyadicGrid m x y t.property.choose t.property.choose_spec.choose)
    (midpointDyadicGrid m x y n k) = 0
  rw [midpointDyadicGrid_dist_cross m hm x y _ _ ht.1 hk, ← ht.2]
  simp only [t, gluingDyadicUnitPoint_val, sub_self, abs_zero, mul_zero]

/-- Actual exact midpoint grids and completeness give a genuine
constant-speed metric segment, including coincident endpoints. -/
theorem exists_midpoint_metric_path [CompleteSpace M] (m : M → M → M)
    (hm : ∀ a b : M, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2)
    (x y : M) :
    ∃ γ : Path x y, ∀ s t : unitInterval,
      dist (γ s) (γ t) = dist x y * |(s : ℝ) - (t : ℝ)| := by
  obtain ⟨γ, hγ, hagree, hdist⟩ := exists_gluingDyadicUnitInterval_extension
    (dist x y) dist_nonneg (midpointDyadicUnitMap m x y)
    (midpointDyadicUnitMap_dist m hm x y)
  have hz : (gluingDyadicUnitPoint 0 0 (by norm_num) : unitInterval) = 0 := by
    ext
    simp only [gluingDyadicUnitPoint_val, Nat.cast_zero, pow_zero, zero_div]
    rfl
  have ho : (gluingDyadicUnitPoint 0 1 (by norm_num) : unitInterval) = 1 := by
    ext
    simp only [gluingDyadicUnitPoint_val, Nat.cast_one, pow_zero, div_one]
    rfl
  have hγ0 : γ 0 = x := by
    rw [← hz, hagree, midpointDyadicUnitMap_point m hm]
    exact midpointDyadicGrid_zero m x y 0
  have hγ1 : γ 1 = y := by
    rw [← ho, hagree, midpointDyadicUnitMap_point m hm]
    exact midpointDyadicGrid_endpoint m x y 0
  exact ⟨⟨⟨γ, hγ⟩, hγ0, hγ1⟩, hdist⟩

/-- Reparametrizing a constructed constant-speed path gives an actual
isometry of the distance interval, including the singleton interval case. -/
theorem metric_path_exists_isometric_interval {x y : M} (γ : Path x y)
    (hγ : ∀ s t : unitInterval, dist (γ s) (γ t) = dist x y * |(s : ℝ) - (t : ℝ)|) :
    ∃ σ : Icc (0 : ℝ) (dist x y) → M, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ => x, ?_, rfl, rfl⟩
    apply Isometry.of_dist_eq
    intro s t
    have hs : (s : ℝ) = 0 := by
      have h : (0 : ℝ) ≤ s ∧ (s : ℝ) ≤ 0 := by
        simpa only [dist_self, mem_Icc] using s.property
      exact le_antisymm h.2 h.1
    have ht : (t : ℝ) = 0 := by
      have h : (0 : ℝ) ≤ t ∧ (t : ℝ) ≤ 0 := by
        simpa only [dist_self, mem_Icc] using t.property
      exact le_antisymm h.2 h.1
    change dist x x = dist (s : ℝ) (t : ℝ)
    rw [hs, ht, dist_self, dist_self]
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    let σ : Icc (0 : ℝ) (dist x y) → M := fun s =>
      γ ⟨(s : ℝ) / dist x y, ⟨div_nonneg s.property.1 hd.le,
        (div_le_one hd).2 s.property.2⟩⟩
    refine ⟨σ, ?_, ?_, ?_⟩
    · apply Isometry.of_dist_eq
      intro s t
      dsimp only [σ]
      rw [hγ]
      change dist x y * |(s : ℝ) / dist x y - (t : ℝ) / dist x y| =
        dist (s : ℝ) (t : ℝ)
      rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hd]
      field_simp
    · have h0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = γ 0 := by
        dsimp only [σ]
        congr 1
        ext
        simp
      exact h0.trans γ.source
    · have h1 : σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = γ 1 := by
        dsimp only [σ]
        congr 1
        ext
        simp [hd.ne']
      exact h1.trans γ.target

end Segment

namespace ExerciseGluingPreparation

variable {C : ℝ} {g n : ℕ} {genera : Fin n → ℕ}
  {X : ∀ i, ClosedHyperbolicSurface (genera i)}

/-- Every pair in the actual glued intrinsic metric is joined by a
constructed metric segment on the original carrier and topology. -/
theorem gluedIntrinsicMetric_exists_metric_path
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ γ : Path x y, ∀ s t : unitInterval,
      dist (γ s) (γ t) = dist x y * |(s : ℝ) - (t : ℝ)| := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  letI : CompactSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace_compact
  let m : P.GluedCarrier → P.GluedCarrier → P.GluedCarrier :=
    fun a b => (P.gluedIntrinsicMetric_midpoint a b).choose
  have hm : ∀ a b, dist a (m a b) = dist a b / 2 ∧ dist (m a b) b = dist a b / 2 :=
    fun a b => (P.gluedIntrinsicMetric_midpoint a b).choose_spec
  exact exists_midpoint_metric_path m hm x y

/-- The distance interval embeds isometrically between every pair of
actual intrinsic-metric points on the original glued carrier. -/
theorem gluedIntrinsicMetric_exists_isometric_segment
    (P : ExerciseGluingPreparation C g n genera X) (x y : P.GluedCarrier) :
    letI := P.gluedCarrierIntrinsicMetricSpace
    ∃ σ : Icc (0 : ℝ) (dist x y) → P.GluedCarrier, Isometry σ ∧
      σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      σ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  letI : MetricSpace P.GluedCarrier := P.gluedCarrierIntrinsicMetricSpace
  obtain ⟨γ, hγ⟩ := P.gluedIntrinsicMetric_exists_metric_path x y
  exact metric_path_exists_isometric_interval γ hγ

end ExerciseGluingPreparation

#print axioms midpointDyadicGrid_dist_cross
#print axioms midpointDyadicUnitMap_dist
#print axioms midpointDyadicUnitMap_point
#print axioms exists_midpoint_metric_path
#print axioms metric_path_exists_isometric_interval
#print axioms ExerciseGluingPreparation.gluedIntrinsicMetric_exists_metric_path
#print axioms ExerciseGluingPreparation.gluedIntrinsicMetric_exists_isometric_segment

end SystolicGrowth
