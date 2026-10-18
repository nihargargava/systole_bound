module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarSmoothWarp
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

/-!
# Smooth collar approximations agreeing exactly outside a thin seam strip

A genuine smooth bump equals one near the seam and zero outside a fixed
thin radial strip. Localizing the constructed smooth warp makes it agree
exactly with the original hyperbolic metric outside that strip. This is the
radial producer for global bounded-curvature smoothing, not yet its global
metric or uniform curvature-variation theorem.
-/

open Set Filter
open scoped Topology

namespace SystolicGrowth

/-- Actual radial cutoff with plateau radius half its support radius. -/
noncomputable def gluingCollarSmoothingCutoff (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : ℝ) where
  rIn := δ / 2
  rOut := δ
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The true localized radial approximation, retaining the native metric
exactly wherever the chosen smooth bump vanishes. -/
noncomputable def gluingCollarLocalizedSmoothWarp (r ε : ℝ)
    (b : ContDiffBump (0 : ℝ)) (t : ℝ) : ℝ :=
  b t * gluingCollarSmoothWarp r ε t + (1 - b t) * gluingCollarWarp r t

theorem gluingCollarLocalizedSmoothWarp_eq_native (r ε : ℝ)
    (b : ContDiffBump (0 : ℝ)) {t : ℝ} (ht : b.rOut ≤ |t|) :
    gluingCollarLocalizedSmoothWarp r ε b t = gluingCollarWarp r t := by
  have hz : b t = 0 := b.zero_of_le_dist (by simpa [Real.dist_eq] using ht)
  simp [gluingCollarLocalizedSmoothWarp, hz]

theorem gluingCollarLocalizedSmoothWarp_eq_smooth (r ε : ℝ)
    (b : ContDiffBump (0 : ℝ)) {t : ℝ} (ht : |t| ≤ b.rIn) :
    gluingCollarLocalizedSmoothWarp r ε b t = gluingCollarSmoothWarp r ε t := by
  have ho : b t = 1 := b.one_of_mem_closedBall (by simpa [Real.dist_eq] using ht)
  simp [gluingCollarLocalizedSmoothWarp, ho]

/-- The localized approximation keeps the same quantitative uniform
error, without a hidden bounded-interval or curvature premise. -/
theorem gluingCollarLocalizedSmoothWarp_sub_warp_bounds
    (r : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    0 ≤ gluingCollarLocalizedSmoothWarp r ε b t - gluingCollarWarp r t ∧
      gluingCollarLocalizedSmoothWarp r ε b t - gluingCollarWarp r t ≤ Real.cosh r * ε := by
  obtain ⟨hl, hu⟩ := gluingCollarSmoothWarp_sub_warp_bounds r hε t
  have heq : gluingCollarLocalizedSmoothWarp r ε b t - gluingCollarWarp r t =
      b t * (gluingCollarSmoothWarp r ε t - gluingCollarWarp r t) := by
    unfold gluingCollarLocalizedSmoothWarp
    ring
  rw [heq]
  refine ⟨mul_nonneg b.nonneg hl, ?_⟩
  exact (mul_le_mul_of_nonneg_right b.le_one hl).trans (by simpa using hu)

theorem gluingCollarLocalizedSmoothWarp_pos {r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    0 < gluingCollarLocalizedSmoothWarp r ε b t := by
  have h := (gluingCollarLocalizedSmoothWarp_sub_warp_bounds r hε b t).1
  linarith [gluingCollarWarp_pos hr t]

theorem gluingCollarLocalizedSmoothWarp_continuous
    (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) :
    Continuous (gluingCollarLocalizedSmoothWarp r ε b) := by
  have hF : Continuous (gluingCollarSmoothWarp r ε) := by
    unfold gluingCollarSmoothWarp
    fun_prop
  exact (b.continuous.mul hF).add
    ((continuous_const.sub b.continuous).mul (gluingCollarWarp_continuous r))

theorem gluingCollarLocalizedSmoothWarp_uniform_bound
    (r : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    |gluingCollarLocalizedSmoothWarp r ε b t - gluingCollarWarp r t| ≤ Real.cosh r * ε := by
  obtain ⟨hl, hu⟩ := gluingCollarLocalizedSmoothWarp_sub_warp_bounds r hε b t
  rwa [abs_of_nonneg hl]

theorem gluingCollarLocalizedSmoothWarp_le_smooth
    (r : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    gluingCollarLocalizedSmoothWarp r ε b t ≤ gluingCollarSmoothWarp r ε t := by
  have h := (gluingCollarSmoothWarp_sub_warp_bounds r hε t).1
  have hb : 0 ≤ 1 - b t := sub_nonneg.mpr b.le_one
  have hp := mul_nonneg hb h
  unfold gluingCollarLocalizedSmoothWarp
  nlinarith

private theorem nativeWarp_contDiffAt_nonzero (r : ℝ) {t : ℝ} (ht : t ≠ 0)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n (gluingCollarWarp r) t := by
  rcases ht.lt_or_gt with hn | hp
  · have h : ContDiffAt ℝ n (fun s : ℝ => Real.sinh (r - s)) t :=
      Real.contDiff_sinh.contDiffAt.comp t (contDiffAt_const.sub contDiffAt_id)
    apply h.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hn] with s hs
    exact gluingCollarWarp_eq_of_nonpos r hs.le
  · have h : ContDiffAt ℝ n (fun s : ℝ => Real.sinh (r + s)) t :=
      Real.contDiff_sinh.contDiffAt.comp t (contDiffAt_const.add contDiffAt_id)
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hp] with s hs
    exact gluingCollarWarp_eq_of_nonneg r hs.le

/-- This localized warp is genuinely smooth through the seam. The native
absolute value is retained only where it is already smooth. -/
theorem gluingCollarLocalizedSmoothWarp_contDiff
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContDiffBump (0 : ℝ)) (n : ℕ∞) :
    ContDiff ℝ n (gluingCollarLocalizedSmoothWarp r ε b) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply (gluingCollarSmoothWarp_contDiff r hε n).contDiffAt.congr_of_eventuallyEq
    filter_upwards [b.eventuallyEq_one] with s hs
    simp [gluingCollarLocalizedSmoothWarp, hs]
  · exact (b.contDiffAt.mul (gluingCollarSmoothWarp_contDiff r hε n).contDiffAt).add
      ((contDiffAt_const.sub b.contDiffAt).mul (nativeWarp_contDiffAt_nonzero r ht n))

/-- Radial reflection compatibility is preserved by the actual even bump. -/
theorem gluingCollarLocalizedSmoothWarp_neg (r ε : ℝ) (b : ContDiffBump (0 : ℝ)) (t : ℝ) :
    gluingCollarLocalizedSmoothWarp r ε b (-t) = gluingCollarLocalizedSmoothWarp r ε b t := by
  have heven : gluingCollarSmoothWarp r ε (-t) = gluingCollarSmoothWarp r ε t := by
    change Real.sinh r * Real.cosh (-t) + Real.cosh r * Real.sqrt (Real.sinh (-t) ^ 2 + ε ^ 2) =
      Real.sinh r * Real.cosh t + Real.cosh r * Real.sqrt (Real.sinh t ^ 2 + ε ^ 2)
    rw [Real.cosh_neg, Real.sinh_neg, neg_sq]
  simp only [gluingCollarLocalizedSmoothWarp, b.neg, heven,
    gluingCollarWarp, abs_neg]

#print axioms gluingCollarLocalizedSmoothWarp_sub_warp_bounds
#print axioms gluingCollarLocalizedSmoothWarp_contDiff
#print axioms gluingCollarLocalizedSmoothWarp_neg

end SystolicGrowth
