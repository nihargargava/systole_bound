module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.GluingCollarFinChainDistance

@[expose] public section

/-!
# Cosh comparison along actual metric paths

Local comparisons are supplied by each isometric copy and the same common
join. The proved scalar local-to-global theorem yields the global midpoint
comparison. Native finite-fin gluing supplies every local premise.
-/

open Set
namespace SystolicGrowth

/-- A specified midpoint inherits a constructed all-test comparison. -/
theorem cosh_comparison_at_specified_midpoint
    {M : Type*} [MetricSpace M] {x y p : M}
    (hmid : ∃ m : M, dist x m = dist x y / 2 ∧
      dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hxp : dist x p = dist x y / 2) (hpy : dist p y = dist x y / 2) :
    ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z p) ≤
      Real.cosh (dist z x) + Real.cosh (dist z y) := by
  obtain ⟨m, _, _, hcomparison⟩ := hmid
  have heq := midpoint_eq_of_midpoint_cosh_all_test hcomparison hxp hpy
  rw [heq]
  exact hcomparison

/-- Midpoint-cosh comparisons on both legs and at their common join give
the global comparison on an actual constant-speed two-leg metric path. -/
theorem cosh_midpoint_comparison_of_split_metric_path
    {M : Type*} [MetricSpace M] {D s : ℝ} (hD : 0 < D)
    (γ : ℝ → M) (hcont : ContinuousOn γ (Icc 0 1))
    (hdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) = D * |u - v|)
    (_hs : s ∈ Icc (0 : ℝ) 1) (A B : Set M)
    (hleft : ∀ t ∈ Icc (0 : ℝ) s, γ t ∈ A)
    (hright : ∀ t ∈ Icc s (1 : ℝ), γ t ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hB : ∀ x ∈ B, ∀ y ∈ B, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (hjoin : ∀ x ∈ A, ∀ y ∈ B,
      dist x (γ s) = dist x y / 2 → dist (γ s) y = dist x y / 2 →
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z (γ s)) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y)) :
    ∀ z : M, 2 * Real.cosh (D / 2) * Real.cosh (dist z (γ (1 / 2))) ≤
      Real.cosh (dist z (γ 0)) + Real.cosh (dist z (γ 1)) := by
  intro z
  apply cosh_midpoint_le_of_local_midpoint hD (fun t => Real.cosh (dist z (γ t)))
    (Real.continuous_cosh.comp_continuousOn
      (continuous_dist.comp_continuousOn
        ((continuous_const.continuousOn : ContinuousOn (fun _ : ℝ => z) (Icc 0 1)).prodMk hcont)))
  intro t ht
  have hsmall (e : ℝ) (he : 0 < e) :
      ∃ h : ℝ, 0 < h ∧ h ≤ t / 2 ∧ h ≤ (1 - t) / 2 ∧ h ≤ e / 2 := by
    refine ⟨min (min t (1 - t)) e / 2,
      div_pos (lt_min (lt_min ht.1 (sub_pos.mpr ht.2)) he) (by norm_num), ?_, ?_, ?_⟩
    · linarith [min_le_left (min t (1 - t)) e, min_le_left t (1 - t)]
    · linarith [min_le_left (min t (1 - t)) e, min_le_right t (1 - t)]
    · linarith [min_le_right (min t (1 - t)) e]
  have hcomparison (h : ℝ) (hh : 0 < h) (hm : t - h ∈ Icc (0 : ℝ) 1)
      (hp : t + h ∈ Icc (0 : ℝ) 1)
      (hc : ∀ w : M,
        2 * Real.cosh (dist (γ (t - h)) (γ (t + h)) / 2) * Real.cosh (dist w (γ t)) ≤
          Real.cosh (dist w (γ (t - h))) + Real.cosh (dist w (γ (t + h)))) :
      2 * Real.cosh (D * h) * Real.cosh (dist z (γ t)) ≤
        Real.cosh (dist z (γ (t - h))) + Real.cosh (dist z (γ (t + h))) := by
    have hxy : dist (γ (t - h)) (γ (t + h)) = 2 * D * h := by
      rw [hdist _ hm _ hp, show t - h - (t + h) = -(2 * h) by ring,
        abs_neg, abs_of_pos (by positivity : 0 < 2 * h)]
      ring
    have hc' := hc z
    rw [hxy, show 2 * D * h / 2 = D * h by ring] at hc'
    exact hc'
  have hhalf (h : ℝ) (hh : 0 < h) (hm : t - h ∈ Icc (0 : ℝ) 1)
      (hp : t + h ∈ Icc (0 : ℝ) 1) :
      dist (γ (t - h)) (γ t) = dist (γ (t - h)) (γ (t + h)) / 2 ∧
        dist (γ t) (γ (t + h)) = dist (γ (t - h)) (γ (t + h)) / 2 := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    rw [hdist _ hm _ ht', hdist _ hm _ hp, hdist _ ht' _ hp,
      show t - h - t = -h by ring,
      show t - h - (t + h) = -(2 * h) by ring,
      show t - (t + h) = -h by ring,
      abs_neg, abs_neg, abs_of_pos hh, abs_of_pos (by positivity : 0 < 2 * h)]
    constructor <;> ring
  rcases lt_trichotomy t s with hts | rfl | hst
  · obtain ⟨h, hh, hht, hh1, hhs⟩ := hsmall (s - t) (sub_pos.mpr hts)
    have hm : t - h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hp : t + h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    obtain ⟨hxm, hmy⟩ := hhalf h hh hm hp
    refine ⟨h, hh, hm, hp, hcomparison h hh hm hp ?_⟩
    apply cosh_comparison_at_specified_midpoint
      (hA _ (hleft _ ⟨hm.1, by linarith⟩) _ (hleft _ ⟨hp.1, by linarith⟩)) hxm hmy
  · obtain ⟨h, hh, hht, hh1, _⟩ := hsmall 1 zero_lt_one
    have hm : t - h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hp : t + h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    obtain ⟨hxm, hmy⟩ := hhalf h hh hm hp
    refine ⟨h, hh, hm, hp, hcomparison h hh hm hp ?_⟩
    exact hjoin _ (hleft _ ⟨hm.1, by linarith⟩)
      _ (hright _ ⟨by linarith, hp.2⟩) hxm hmy
  · obtain ⟨h, hh, hht, hh1, hhs⟩ := hsmall (t - s) (sub_pos.mpr hst)
    have hm : t - h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have hp : t + h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    obtain ⟨hxm, hmy⟩ := hhalf h hh hm hp
    refine ⟨h, hh, hm, hp, hcomparison h hh hm hp ?_⟩
    apply cosh_comparison_at_specified_midpoint
      (hB _ (hright _ ⟨by linarith, hm.2⟩) _ (hright _ ⟨by linarith, hp.2⟩)) hxm hmy

#print axioms cosh_comparison_at_specified_midpoint
#print axioms cosh_midpoint_comparison_of_split_metric_path

/-- All-point midpoint comparison gives the full hyperbolic comparison along
every actual constant-speed metric segment, not only at its midpoint. -/
theorem cosh_sinh_interpolation_of_metric_path
    {M : Type*} [MetricSpace M] {D : ℝ} (hD : 0 < D)
    (hmid : ∀ x y : M, ∃ m : M,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (γ : ℝ → M) (hcont : ContinuousOn γ (Icc 0 1))
    (hdist : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      dist (γ u) (γ v) = D * |u - v|) :
    ∀ (z : M) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      Real.sinh D * Real.cosh (dist z (γ t)) ≤
        Real.sinh ((1 - t) * D) * Real.cosh (dist z (γ 0)) +
          Real.sinh (t * D) * Real.cosh (dist z (γ 1)) := by
  intro z
  apply sinh_interpolation_le_of_local_midpoint hD (fun t => Real.cosh (dist z (γ t)))
    (Real.continuous_cosh.comp_continuousOn
      (continuous_dist.comp_continuousOn
        ((continuous_const.continuousOn :
          ContinuousOn (fun _ : ℝ => z) (Icc 0 1)).prodMk hcont)))
  intro t ht
  let h := min t (1 - t) / 2
  have hh : 0 < h :=
    div_pos (lt_min ht.1 (sub_pos.mpr ht.2)) (by norm_num)
  have hht : h ≤ t / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hh1 : h ≤ (1 - t) / 2 :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hm : t - h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hp : t + h ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hxy : dist (γ (t - h)) (γ (t + h)) = 2 * D * h := by
    rw [hdist _ hm _ hp, show t - h - (t + h) = -(2 * h) by ring,
      abs_neg, abs_of_pos (by positivity : 0 < 2 * h)]
    ring
  have hxm : dist (γ (t - h)) (γ t) = dist (γ (t - h)) (γ (t + h)) / 2 := by
    rw [hxy, hdist _ hm _ ht', show t - h - t = -h by ring,
      abs_neg, abs_of_pos hh]
    ring
  have hmy : dist (γ t) (γ (t + h)) = dist (γ (t - h)) (γ (t + h)) / 2 := by
    rw [hxy, hdist _ ht' _ hp, show t - (t + h) = -h by ring,
      abs_neg, abs_of_pos hh]
    ring
  have hc := cosh_comparison_at_specified_midpoint (hmid _ _) hxm hmy z
  rw [hxy, show 2 * D * h / 2 = D * h by ring] at hc
  exact ⟨h, hh, hm, hp, hc⟩

#print axioms cosh_sinh_interpolation_of_metric_path
end SystolicGrowth
