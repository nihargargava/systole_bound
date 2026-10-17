module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarWarp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Regularity and minimum of the actual collar warp

The nonsmooth warp `sinh (r + |t|)` is locally Lipschitz, including at the
seam. Its minimum is attained at zero. These are actual scalar hypotheses
needed for warped curvature comparison, not a curvature conclusion.
-/

open Set Filter
open scoped Topology

namespace SystolicGrowth

/-- The lower bound is the actual value on the seam, for every radius. -/
theorem gluingCollarWarp_lower_bound (r t : ℝ) :
    Real.sinh r ≤ gluingCollarWarp r t := by
  apply Real.sinh_le_sinh.mpr
  exact le_add_of_nonneg_right (abs_nonneg t)

/-- The collar warp attains its global minimum at signed radius zero. -/
theorem gluingCollarWarp_isLeast (r : ℝ) :
    IsLeast (range (gluingCollarWarp r)) (Real.sinh r) := by
  refine ⟨⟨0, gluingCollarWarp_zero r⟩, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact gluingCollarWarp_lower_bound r t

/-- A quantitative Lipschitz bound on every bounded signed-radius interval.
The argument uses the smooth `sinh` factor and the globally Lipschitz absolute
value, so no two-sided differentiability of the seam is asserted. -/
theorem gluingCollarWarp_abs_sub_le (r : ℝ) {R s t : ℝ} (hR : 0 ≤ R)
    (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R) :
    |gluingCollarWarp r s - gluingCollarWarp r t| ≤
      Real.cosh (|r| + R) * |s - t| := by
  let L := |r| + R
  have hL : 0 ≤ L := add_nonneg (abs_nonneg r) hR
  have harg {u : ℝ} (hu : u ∈ Icc (-R) R) : r + |u| ∈ Icc (-L) L := by
    have hu' : |u| ≤ R := abs_le.mpr hu
    have hr₁ := neg_le_abs r
    have hr₂ := le_abs_self r
    have hu₀ := abs_nonneg u
    constructor <;> dsimp [L] <;> linarith
  have hbound (u : ℝ) (hu : u ∈ Icc (-L) L) : ‖Real.cosh u‖ ≤ Real.cosh L := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos u)]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hL]
    exact abs_le.mpr hu
  have h := (convex_Icc (-L) L).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (Real.hasDerivAt_sinh u).hasDerivWithinAt) hbound (harg ht) (harg hs)
  calc
    |gluingCollarWarp r s - gluingCollarWarp r t| ≤
        Real.cosh L * |(r + |s|) - (r + |t|)| := by
      simpa only [gluingCollarWarp, Real.norm_eq_abs] using h
    _ = Real.cosh L * |(|s| - |t|)| := by congr 2; ring
    _ ≤ Real.cosh L * |s - t| :=
      mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub s t) (Real.cosh_pos L).le

/-- Away from the seam, the ordinary derivative of the warp is bounded on a
bounded signed-radius interval. The excluded seam is a null set for the
absolutely-continuous speed estimates used by the strip approximation. -/
theorem gluingCollarWarp_deriv_abs_le (r : ℝ) {R t : ℝ} (hR : 0 ≤ R)
    (ht : t ∈ Icc (-R) R) (ht0 : t ≠ 0) :
    |deriv (gluingCollarWarp r) t| ≤ Real.cosh (|r| + R) := by
  have hL : 0 ≤ |r| + R := add_nonneg (abs_nonneg r) hR
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · rw [gluingCollarWarp_deriv_neg r hneg, abs_neg,
      abs_of_pos (Real.cosh_pos _)]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hL]
    apply abs_le.mpr
    rcases ht with ⟨htlo, hthi⟩
    constructor <;> nlinarith [neg_le_abs r, le_abs_self r]
  · rw [gluingCollarWarp_deriv_pos r hpos,
      abs_of_pos (Real.cosh_pos _)]
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg hL]
    apply abs_le.mpr
    rcases ht with ⟨htlo, hthi⟩
    constructor <;> nlinarith [neg_le_abs r, le_abs_self r]

/-- The warp has a genuine corner at the radial seam. Lean's totalized
ordinary derivative is zero at this nondifferentiable point. -/
theorem gluingCollarWarp_deriv_zero (r : ℝ) :
    deriv (gluingCollarWarp r) 0 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  have hright : derivWithin (gluingCollarWarp r) (Ici 0) 0 =
      deriv (gluingCollarWarp r) 0 :=
    hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  have hleft : derivWithin (gluingCollarWarp r) (Iic 0) 0 =
      deriv (gluingCollarWarp r) 0 :=
    hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 0)
  have hjump := gluingCollarWarp_deriv_jump r
  rw [hright, hleft, sub_self] at hjump
  nlinarith [Real.cosh_pos r]

/-- The derivative bound holds at every point of the closed window,
including the seam under the ordinary totalized-derivative convention. -/
theorem gluingCollarWarp_deriv_abs_le_all (r : ℝ) {R t : ℝ} (hR : 0 ≤ R)
    (ht : t ∈ Icc (-R) R) :
    |deriv (gluingCollarWarp r) t| ≤ Real.cosh (|r| + R) := by
  by_cases ht0 : t = 0
  · subst t
    simp [gluingCollarWarp_deriv_zero, (Real.cosh_pos _).le]
  · exact gluingCollarWarp_deriv_abs_le r hR ht ht0

/-- Uniform positive profile bound on a closed radial window. -/
theorem gluingCollarWarp_abs_le_window {r R t : ℝ} (hr : 0 < r)
    (ht : t ∈ Icc (-R) R) :
    |gluingCollarWarp r t| ≤ Real.sinh (r + R) := by
  rw [abs_of_pos (gluingCollarWarp_pos hr t), gluingCollarWarp]
  apply Real.sinh_le_sinh.mpr
  simpa only [add_comm] using add_le_add_left (abs_le.mpr ht) r

/-- The bounded-interval estimate in mathlib's native Lipschitz predicate. -/
theorem gluingCollarWarp_lipschitzOnWith (r : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith ⟨Real.cosh (|r| + R), (Real.cosh_pos _).le⟩
      (gluingCollarWarp r) (Icc (-R) R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  change |gluingCollarWarp r s - gluingCollarWarp r t| ≤
    Real.cosh (|r| + R) * |s - t|
  exact gluingCollarWarp_abs_sub_le r hR hs ht

/-- The exact bounded-set regularity hypothesis of warped curvature
comparison follows from the quantitative interval bound. -/
theorem gluingCollarWarp_lipschitzOn_isBounded (r : ℝ) {s : Set ℝ}
    (hs : Bornology.IsBounded s) :
    ∃ K : NNReal, LipschitzOnWith K (gluingCollarWarp r) s := by
  obtain ⟨R, hR, hbound⟩ := hs.exists_pos_norm_le
  refine ⟨_, (gluingCollarWarp_lipschitzOnWith r hR.le).mono ?_⟩
  intro t ht
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hbound t ht)

/-- The actual collar warp is locally Lipschitz even at the seam. -/
theorem gluingCollarWarp_locallyLipschitz (r : ℝ) :
    LocallyLipschitz (gluingCollarWarp r) := by
  intro t
  refine ⟨⟨Real.cosh (|r| + (|t| + 1)), (Real.cosh_pos _).le⟩,
    Icc (-(|t| + 1)) (|t| + 1), ?_, ?_⟩
  · apply Icc_mem_nhds <;> linarith [le_abs_self t, neg_le_abs t]
  · exact gluingCollarWarp_lipschitzOnWith r (by positivity)

#print axioms gluingCollarWarp_isLeast
#print axioms gluingCollarWarp_abs_sub_le
#print axioms gluingCollarWarp_deriv_abs_le
#print axioms gluingCollarWarp_deriv_zero
#print axioms gluingCollarWarp_deriv_abs_le_all
#print axioms gluingCollarWarp_abs_le_window
#print axioms gluingCollarWarp_lipschitzOnWith
#print axioms gluingCollarWarp_lipschitzOn_isBounded
#print axioms gluingCollarWarp_locallyLipschitz

end SystolicGrowth
