module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricTriangleBoundaryComparison

@[expose] public section

/-!
# Aligned hyperbolic comparison-triangle models

Prescribed metric side lengths satisfying the triangle inequalities are
realized with one fixed vertical base. Both child comparison triangles can
therefore use exactly the same base points, including a degenerate base.
These are model-realization inputs to boundary inheritance, not a proof of
triangle pasting or convex gluing.
-/

open Set

namespace SystolicGrowth

/-- The fixed vertical comparison-model point at signed distance `c` from `i`. -/
noncomputable def hyperbolicTriangleModelAxisPoint (c : ℝ) : UpperHalfPlane :=
  ⟨⟨0, Real.exp c⟩, Real.exp_pos c⟩

@[simp] theorem hyperbolicTriangleModelAxisPoint_zero :
    hyperbolicTriangleModelAxisPoint 0 = UpperHalfPlane.I := by
  apply UpperHalfPlane.ext_re_im <;> simp [hyperbolicTriangleModelAxisPoint]

theorem hyperbolicTriangleModelAxisPoint_dist (c d : ℝ) :
    dist (hyperbolicTriangleModelAxisPoint c) (hyperbolicTriangleModelAxisPoint d) =
      |c - d| := by
  rw [UpperHalfPlane.dist_of_re_eq (by rfl)]
  simp [hyperbolicTriangleModelAxisPoint, Real.dist_eq]

private theorem hyperbolic_triangle_vertical_base_positive
    {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c)
    (hba : b ≤ a + c) (hab : a ≤ b + c) (hca : c ≤ a + b) :
    ∃ x : UpperHalfPlane,
      dist UpperHalfPlane.I x = a ∧ dist (hyperbolicTriangleModelAxisPoint c) x = b := by
  let k : ℝ := (Real.cosh a * Real.cosh c - Real.cosh b) /
    (Real.sinh a * Real.sinh c)
  have hsa : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hsc : 0 < Real.sinh c := Real.sinh_pos_iff.mpr hc
  have hden : 0 < Real.sinh a * Real.sinh c := mul_pos hsa hsc
  have hupper : Real.cosh b ≤ Real.cosh (a + c) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hb, abs_of_nonneg (by positivity : 0 ≤ a + c)]
    exact hba
  have hlower : Real.cosh (a - c) ≤ Real.cosh b := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hb]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Real.cosh_add] at hupper
  rw [Real.cosh_sub] at hlower
  have hklo : -1 ≤ k := by
    dsimp [k]
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hupper]
  have hkhi : k ≤ 1 := by
    dsimp [k]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hlower]
  let D : ℝ := Real.cosh a - k * Real.sinh a
  have hD : 0 < D := by
    have hcosh : 0 < Real.cosh a - Real.sinh a := by
      rw [Real.cosh_sub_sinh]
      exact Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_right hkhi hsa.le
    dsimp [D]
    linarith only [hcosh, hmul]
  have hsquare : 0 ≤ 1 - k ^ 2 := by nlinarith only [hklo, hkhi]
  let r : ℝ := Real.sqrt (1 - k ^ 2)
  have hr : r ^ 2 = 1 - k ^ 2 := Real.sq_sqrt hsquare
  have hnum : (Real.sinh a) ^ 2 * r ^ 2 + 1 + D ^ 2 =
      2 * Real.cosh a * D := by
    have hscaled := congrArg (fun v : ℝ => Real.sinh a ^ 2 * v) hr
    dsimp [D]
    nlinarith only [hscaled, Real.cosh_sq a]
  have hk : Real.cosh b = Real.cosh a * Real.cosh c -
      Real.sinh a * Real.sinh c * k := by
    dsimp [k]
    field_simp [ne_of_gt hden]
    ring
  have he : (Real.exp c) ^ 2 - 1 = 2 * Real.exp c * Real.sinh c := by
    rw [← Real.cosh_add_sinh]
    nlinarith only [Real.cosh_sq c]
  have heinv : Real.exp c * (Real.cosh c - Real.sinh c) = 1 := by
    rw [← Real.cosh_add_sinh]
    nlinarith only [Real.cosh_sq c]
  have hnum' : Real.sinh a ^ 2 * r ^ 2 + 1 + Real.exp c ^ 2 * D ^ 2 =
      2 * Real.exp c * D * Real.cosh b := by
    dsimp [D] at hnum ⊢
    linear_combination hnum + (Real.cosh a - k * Real.sinh a) ^ 2 * he -
      2 * Real.cosh a * (Real.cosh a - k * Real.sinh a) * heinv -
      2 * Real.exp c * (Real.cosh a - k * Real.sinh a) * hk
  let x : UpperHalfPlane :=
    ⟨⟨Real.sinh a * r / D, 1 / D⟩, one_div_pos.mpr hD⟩
  have hxcosh : Real.cosh (dist UpperHalfPlane.I x) = Real.cosh a := by
    rw [UpperHalfPlane.cosh_dist']
    change ((0 - Real.sinh a * r / D) ^ 2 + 1 ^ 2 + (1 / D) ^ 2) /
      (2 * 1 * (1 / D)) = Real.cosh a
    field_simp [ne_of_gt hD]
    nlinarith only [hnum]
  have hxcosh' : Real.cosh (dist (hyperbolicTriangleModelAxisPoint c) x) =
      Real.cosh b := by
    rw [UpperHalfPlane.cosh_dist']
    change ((0 - Real.sinh a * r / D) ^ 2 + Real.exp c ^ 2 + (1 / D) ^ 2) /
      (2 * Real.exp c * (1 / D)) = Real.cosh b
    field_simp [ne_of_gt hD, (Real.exp_pos c).ne']
    nlinarith only [hnum']
  refine ⟨x, ?_, ?_⟩
  · have h := Real.cosh_le_cosh.mp hxcosh.le
    have h' := Real.cosh_le_cosh.mp hxcosh.ge
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg ha.le] at h h'
    exact le_antisymm h h'
  · have h := Real.cosh_le_cosh.mp hxcosh'.le
    have h' := Real.cosh_le_cosh.mp hxcosh'.ge
    rw [abs_of_nonneg dist_nonneg, abs_of_nonneg hb] at h h'
    exact le_antisymm h h'

/-- The common vertical base has its prescribed nonnegative length. -/
theorem hyperbolicTriangleModelAxisPoint_dist_base {c : ℝ} (hc : 0 ≤ c) :
    dist UpperHalfPlane.I (hyperbolicTriangleModelAxisPoint c) = c := by
  rw [← hyperbolicTriangleModelAxisPoint_zero, hyperbolicTriangleModelAxisPoint_dist]
  simp only [zero_sub, abs_neg, abs_of_nonneg hc]

/-- Realize metric triangle side lengths on a fixed shared vertical base.

The zero-edge cases are included. Two applications with the same `c` give
comparison triangles whose base points agree literally, rather than merely
having equal base lengths. -/
theorem exists_hyperbolic_triangle_with_vertical_base
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : a ≤ b + c) (hba : b ≤ a + c) (hca : c ≤ a + b) :
    ∃ x : UpperHalfPlane,
      dist UpperHalfPlane.I x = a ∧
        dist (hyperbolicTriangleModelAxisPoint c) x = b := by
  by_cases ha0 : a = 0
  · have hbc : b = c := by linarith
    refine ⟨UpperHalfPlane.I, ?_, ?_⟩
    · simp [ha0]
    · rw [dist_comm, hyperbolicTriangleModelAxisPoint_dist_base hc, hbc]
  by_cases hc0 : c = 0
  · have hab' : a = b := by linarith
    refine ⟨hyperbolicTriangleModelAxisPoint a,
      hyperbolicTriangleModelAxisPoint_dist_base ha, ?_⟩
    rw [hc0, hyperbolicTriangleModelAxisPoint_zero,
      hyperbolicTriangleModelAxisPoint_dist_base ha, hab']
  exact hyperbolic_triangle_vertical_base_positive (lt_of_le_of_ne ha (Ne.symm ha0))
    hb (lt_of_le_of_ne hc (Ne.symm hc0)) hba hab hca

/-- The model common side is a closed subset of the hyperbolic plane. -/
theorem hyperbolicGeodSeg_isClosed (a b : UpperHalfPlane) :
    IsClosed (Vendored.RiemannDynamics.geodSeg a b) := by
  change IsClosed {z : UpperHalfPlane | dist a z + dist z b = dist a b}
  exact isClosed_eq (by fun_prop) continuous_const

/-- A finite model side is compact, including when its endpoints coincide. -/
theorem hyperbolicGeodSeg_isCompact (a b : UpperHalfPlane) :
    IsCompact (Vendored.RiemannDynamics.geodSeg a b) := by
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp]
  exact isCompact_Icc.image
    (Vendored.RiemannDynamics.continuous_geodInterp.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id)))

/-- Completeness of the actual shared-side subtype. -/
theorem hyperbolicGeodSeg_completeSpace (a b : UpperHalfPlane) :
    CompleteSpace (Vendored.RiemannDynamics.geodSeg a b) :=
  (hyperbolicGeodSeg_isCompact a b).isComplete.completeSpace_coe

/-- The left endpoint supplies nonemptiness without a positive-length assumption. -/
theorem hyperbolicGeodSeg_nonempty (a b : UpperHalfPlane) :
    Nonempty (Vendored.RiemannDynamics.geodSeg a b) :=
  ⟨⟨a, Vendored.RiemannDynamics.left_mem_geodSeg a b⟩⟩

/-- The full model side, not just its endpoints, is geodesically convex. -/
theorem hyperbolicGeodSeg_geodSeg_subset (a b : UpperHalfPlane) :
    ∀ x ∈ Vendored.RiemannDynamics.geodSeg a b,
      ∀ y ∈ Vendored.RiemannDynamics.geodSeg a b,
        Vendored.RiemannDynamics.geodSeg x y ⊆ Vendored.RiemannDynamics.geodSeg a b := by
  have hordered (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
      (hst : s ≤ t) :
      Vendored.RiemannDynamics.geodSeg
        (Vendored.RiemannDynamics.geodInterp a b s)
        (Vendored.RiemannDynamics.geodInterp a b t) ⊆
          Vendored.RiemannDynamics.geodSeg a b := by
    intro z hz
    have hsum :
        dist a (Vendored.RiemannDynamics.geodInterp a b s) +
          dist (Vendored.RiemannDynamics.geodInterp a b s)
            (Vendored.RiemannDynamics.geodInterp a b t) +
          dist (Vendored.RiemannDynamics.geodInterp a b t) b = dist a b := by
      rw [Vendored.RiemannDynamics.dist_geodInterp_left_abs,
        Vendored.RiemannDynamics.dist_geodInterp_pair,
        Vendored.RiemannDynamics.dist_geodInterp_right_abs,
        abs_of_nonneg hs.1, abs_of_nonpos (sub_nonpos.mpr hst),
        abs_of_nonneg (sub_nonneg.mpr ht.2)]
      ring
    have hzdist :
        dist (Vendored.RiemannDynamics.geodInterp a b s) z +
          dist z (Vendored.RiemannDynamics.geodInterp a b t) =
        dist (Vendored.RiemannDynamics.geodInterp a b s)
          (Vendored.RiemannDynamics.geodInterp a b t) := hz
    change dist a z + dist z b = dist a b
    exact le_antisymm (by
      linarith [dist_triangle a (Vendored.RiemannDynamics.geodInterp a b s) z,
        dist_triangle z (Vendored.RiemannDynamics.geodInterp a b t) b])
      (dist_triangle a z b)
  intro x hx y hy
  rw [Vendored.RiemannDynamics.geodSeg_eq_image_geodInterp] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  rcases le_total s t with hst | hts
  · exact hordered s t hs ht hst
  · rw [Vendored.RiemannDynamics.geodSeg_comm]
    exact hordered t s ht hs hts

end SystolicGrowth
