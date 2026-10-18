module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.HyperbolicMidpointComparison
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-!
# Cosh convexity along locally metric hyperbolic segments

A positive-speed local metric segment supplies symmetric midpoint identities
near each interior parameter. The proved scalar comparison principle passes
these identities to the whole interval, without assuming global geodesicity.
-/

open Set

namespace SystolicGrowth

/-- Every continuous positive-speed local metric segment in the hyperbolic
plane satisfies the global midpoint-cosh inequality on its full interval. -/
theorem hyperbolic_locally_metric_segment_midpoint_cosh_le
    {a b speed : ℝ} (hab : a < b) (hs : 0 < speed)
    (α : Set.Icc a b → UpperHalfPlane) (hα : Continuous α)
    (hlocal : ∀ t : Set.Icc a b, a < t.1 → t.1 < b →
      ∃ η > 0, ∀ u v : Set.Icc a b,
        dist u t < η → dist v t < η →
          dist (α u) (α v) = speed * |(u : ℝ) - (v : ℝ)|)
    (o : UpperHalfPlane) :
    2 * Real.cosh (speed * (b - a) / 2) *
        Real.cosh (dist o (α ⟨(a + b) / 2, by constructor <;> linarith⟩)) ≤
      Real.cosh (dist o (α ⟨a, le_rfl, hab.le⟩)) +
        Real.cosh (dist o (α ⟨b, hab.le, le_rfl⟩)) := by
  let L := b - a
  have hL : 0 < L := sub_pos.mpr hab
  let D := speed * L
  have hD : 0 < D := mul_pos hs hL
  let T : ℝ → ℝ := fun t => a + L * t
  have hT (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : T t ∈ Icc a b := by
    dsimp [T, L]
    constructor
    · nlinarith [ht.1]
    · nlinarith [ht.2]
  let β : ℝ → UpperHalfPlane := fun t => α (projIcc a b hab.le (T t))
  have hβcont : Continuous β := hα.comp
    (continuous_projIcc.comp (by dsimp [T]; fun_prop))
  have hβ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      β t = α ⟨T t, hT t ht⟩ := by
    dsimp [β]
    rw [projIcc_of_mem hab.le (hT t ht)]
  let F : ℝ → ℝ := fun t => Real.cosh (dist o (β t))
  have hF : Continuous F := Real.continuous_cosh.comp
    (continuous_const.dist hβcont)
  have hFLocal : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ h : ℝ, 0 < h ∧
      t - h ∈ Icc 0 1 ∧ t + h ∈ Icc 0 1 ∧
      2 * Real.cosh (D * h) * F t ≤ F (t - h) + F (t + h) := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    let τ : Icc a b := ⟨T t, hT t htI⟩
    have hτa : a < τ.1 := by
      change a < a + L * t
      nlinarith [mul_pos hL ht.1]
    have hτb : τ.1 < b := by
      change a + L * t < b
      dsimp [L] at hL ⊢
      nlinarith [ht.2]
    obtain ⟨η, hη, hnear⟩ := hlocal τ hτa hτb
    let h := min (min (t / 2) ((1 - t) / 2)) (η / (2 * L))
    have hh : 0 < h := lt_min
      (lt_min (div_pos ht.1 (by norm_num)) (by linarith [ht.2]))
      (div_pos hη (mul_pos (by norm_num) hL))
    have hht : h ≤ t / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hh1 : h ≤ (1 - t) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hhη : h ≤ η / (2 * L) := min_le_right _ _
    have hLh : L * h < η := by
      calc
        L * h ≤ L * (η / (2 * L)) := mul_le_mul_of_nonneg_left hhη hL.le
        _ = η / 2 := by field_simp
        _ < η := by linarith
    have hm : t - h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hp : t + h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hclose (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hut : |u - t| ≤ h) :
        dist (⟨T u, hT u hu⟩ : Icc a b) τ < η := by
      rw [Subtype.dist_eq, Real.dist_eq]
      change |T u - T t| < η
      rw [show T u - T t = L * (u - t) by dsimp [T]; ring,
        abs_mul, abs_of_pos hL]
      exact (mul_le_mul_of_nonneg_left hut hL.le).trans_lt hLh
    have hct : dist (⟨T t, hT t htI⟩ : Icc a b) τ < η := by
      change dist τ τ < η
      simpa only [dist_self] using hη
    have hcm : dist (⟨T (t - h), hT (t - h) hm⟩ : Icc a b) τ < η :=
      hclose _ hm (by rw [show t - h - t = -h by ring, abs_neg, abs_of_pos hh])
    have hcp : dist (⟨T (t + h), hT (t + h) hp⟩ : Icc a b) τ < η :=
      hclose _ hp (by rw [show t + h - t = h by ring, abs_of_pos hh])
    have hdist (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1)
        (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
        (hcu : dist (⟨T u, hT u hu⟩ : Icc a b) τ < η)
        (hcv : dist (⟨T v, hT v hv⟩ : Icc a b) τ < η) :
        dist (β u) (β v) = D * |u - v| := by
      rw [hβ u hu, hβ v hv, hnear _ _ hcu hcv,
        show T u - T v = L * (u - v) by dsimp [T]; ring,
        abs_mul, abs_of_pos hL]
      dsimp [D]
      ring
    have hminus : dist (β (t - h)) (β t) = D * h := by
      rw [hdist _ hm _ htI hcm hct, show t - h - t = -h by ring,
        abs_neg, abs_of_pos hh]
    have hplus : dist (β t) (β (t + h)) = D * h := by
      rw [hdist _ htI _ hp hct hcp, show t - (t + h) = -h by ring,
        abs_neg, abs_of_pos hh]
    have hspan : dist (β (t - h)) (β (t + h)) = 2 * D * h := by
      rw [hdist _ hm _ hp hcm hcp, show t - h - (t + h) = -(2 * h) by ring,
        abs_neg, abs_of_pos (by positivity : 0 < 2 * h)]
      ring
    have hmidLeft : dist (β (t - h)) (β t) =
        dist (β (t - h)) (β (t + h)) / 2 := by rw [hminus, hspan]; ring
    have hmidRight : dist (β t) (β (t + h)) =
        dist (β (t - h)) (β (t + h)) / 2 := by rw [hplus, hspan]; ring
    have hc := hyperbolic_midpoint_cosh hmidLeft hmidRight o
    rw [hspan, show 2 * D * h / 2 = D * h by ring] at hc
    exact ⟨h, hh, hm, hp, hc.le⟩
  have hc := cosh_midpoint_le_of_local_midpoint hD F hF.continuousOn hFLocal
  have hβ0 : β 0 = α ⟨a, le_rfl, hab.le⟩ := by
    rw [hβ 0 (by norm_num)]
    congr 1
    apply Subtype.ext
    simp [T]
  have hβ1 : β 1 = α ⟨b, hab.le, le_rfl⟩ := by
    rw [hβ 1 (by norm_num)]
    congr 1
    apply Subtype.ext
    dsimp [T, L]
    ring
  have hβhalf : β (1 / 2) = α ⟨(a + b) / 2, by constructor <;> linarith⟩ := by
    rw [hβ (1 / 2) (by constructor <;> norm_num)]
    congr 1
    apply Subtype.ext
    dsimp [T, L]
    ring
  simpa only [F, D, L, hβ0, hβ1, hβhalf] using hc

end SystolicGrowth
