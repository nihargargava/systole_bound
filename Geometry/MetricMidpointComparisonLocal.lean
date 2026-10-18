module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Midpoint comparison in a local isometric chart

The model comparison keeps its midpoint inside each metric ball. An open
partial homeomorphism then transports that midpoint into a smaller source
ball where the given native distance identity holds for every pair.
-/

open Set Metric

namespace SystolicGrowth

/-- Comparison tested at the center keeps a midpoint in the closed ball
containing both endpoints. -/
theorem midpoint_cosh_comparison_mem_closedBall
    {M : Type*} [PseudoMetricSpace M] {c a b m : M} {R : ℝ}
    (hR : 0 ≤ R) (ha : a ∈ Metric.closedBall c R) (hb : b ∈ Metric.closedBall c R)
    (hcomparison : 2 * Real.cosh (dist a b / 2) * Real.cosh (dist c m) ≤
      Real.cosh (dist c a) + Real.cosh (dist c b)) :
    m ∈ Metric.closedBall c R := by
  have hca : Real.cosh (dist c a) ≤ Real.cosh R := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, abs_of_nonneg hR, dist_comm] using
      Metric.mem_closedBall.mp ha
  have hcb : Real.cosh (dist c b) ≤ Real.cosh R := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, abs_of_nonneg hR, dist_comm] using
      Metric.mem_closedBall.mp hb
  have hfactor : 2 * Real.cosh (dist c m) ≤
      2 * Real.cosh (dist a b / 2) * Real.cosh (dist c m) := by
    nlinarith [Real.one_le_cosh (dist a b / 2), Real.cosh_pos (dist c m)]
  have hcm : Real.cosh (dist c m) ≤ Real.cosh R := by
    linarith
  have hdist : dist c m ≤ R := by
    have := Real.cosh_le_cosh.mp hcm
    simpa only [abs_of_nonneg dist_nonneg, abs_of_nonneg hR] using this
  exact Metric.mem_closedBall.mpr (by simpa only [dist_comm] using hdist)

/-- An all-test cosh comparison keeps its midpoint inside the open ball
containing both endpoints. -/
theorem midpoint_cosh_all_test_mem_ball
    {M : Type*} [PseudoMetricSpace M] {c a b m : M} {R : ℝ}
    (hR : 0 < R) (ha : a ∈ Metric.ball c R) (hb : b ∈ Metric.ball c R)
    (hcomparison : ∀ w : M,
      2 * Real.cosh (dist a b / 2) * Real.cosh (dist w m) ≤
        Real.cosh (dist w a) + Real.cosh (dist w b)) :
    m ∈ Metric.ball c R := by
  have hca : Real.cosh (dist c a) < Real.cosh R := by
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, abs_of_pos hR, dist_comm] using
      Metric.mem_ball.mp ha
  have hcb : Real.cosh (dist c b) < Real.cosh R := by
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, abs_of_pos hR, dist_comm] using
      Metric.mem_ball.mp hb
  have hfactor : 2 * Real.cosh (dist c m) ≤
      2 * Real.cosh (dist a b / 2) * Real.cosh (dist c m) := by
    nlinarith [Real.one_le_cosh (dist a b / 2), Real.cosh_pos (dist c m)]
  have hcm : Real.cosh (dist c m) < Real.cosh R := by
    linarith [hcomparison c]
  have hdist : dist c m < R := by
    have := Real.cosh_lt_cosh.mp hcm
    simpa only [abs_of_nonneg dist_nonneg, abs_of_pos hR] using this
  exact Metric.mem_ball.mpr (by simpa only [dist_comm] using hdist)

/-- Global model midpoint comparison gives genuine local comparison on the
original metric space through an open chart preserving nearby distances. -/
theorem exists_local_midpoint_cosh_all_test_of_local_isometry
    {A B : Type*} [MetricSpace A] [MetricSpace B]
    (e : OpenPartialHomeomorph A B) (x : A) (hx : x ∈ e.source)
    (hlocal : ∃ R > 0, Metric.ball x R ⊆ e.source ∧
      ∀ y ∈ Metric.ball x R, ∀ z ∈ Metric.ball x R,
        dist (e y) (e z) = dist y z)
    (hmid : ∀ a b : B, ∃ m : B,
      dist a m = dist a b / 2 ∧ dist m b = dist a b / 2 ∧
      ∀ w : B, 2 * Real.cosh (dist a b / 2) * Real.cosh (dist w m) ≤
        Real.cosh (dist w a) + Real.cosh (dist w b)) :
    ∃ ε > 0, ∀ y ∈ Metric.ball x ε, ∀ z ∈ Metric.ball x ε,
      ∃ m ∈ Metric.ball x ε,
        dist y m = dist y z / 2 ∧ dist m z = dist y z / 2 ∧
        ∀ w ∈ Metric.ball x ε,
          2 * Real.cosh (dist y z / 2) * Real.cosh (dist w m) ≤
            Real.cosh (dist w y) + Real.cosh (dist w z) := by
  obtain ⟨R, hR, hsource, hdist⟩ := hlocal
  have hxR : x ∈ Metric.ball x R := Metric.mem_ball_self hR
  have hmodelOpen : IsOpen (e.target ∩ e.symm ⁻¹' Metric.ball x R) :=
    e.isOpen_inter_preimage_symm Metric.isOpen_ball
  have hxModel : e x ∈ e.target ∩ e.symm ⁻¹' Metric.ball x R := by
    refine ⟨e.map_source hx, ?_⟩
    simpa only [mem_preimage, e.left_inv hx] using hxR
  obtain ⟨δ, hδ, hmodelBall⟩ := Metric.isOpen_iff.mp hmodelOpen (e x) hxModel
  let ε := min R δ
  have hε : 0 < ε := lt_min hR hδ
  have hεR : ε ≤ R := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hsmall : Metric.ball x ε ⊆ Metric.ball x R :=
    Metric.ball_subset_ball hεR
  have himage (v : A) (hv : v ∈ Metric.ball x ε) : e v ∈ Metric.ball (e x) ε := by
    apply Metric.mem_ball.mpr
    rw [hdist v (hsmall hv) x hxR]
    exact Metric.mem_ball.mp hv
  refine ⟨ε, hε, ?_⟩
  intro y hy z hz
  obtain ⟨q, hyq, hqz, hcomparison⟩ := hmid (e y) (e z)
  have hqSmall : q ∈ Metric.ball (e x) ε :=
    midpoint_cosh_all_test_mem_ball hε (himage y hy) (himage z hz) hcomparison
  have hqModel := hmodelBall (Metric.ball_subset_ball hεδ hqSmall)
  have hqR : e.symm q ∈ Metric.ball x R := hqModel.2
  have hqEval : e (e.symm q) = q := e.right_inv hqModel.1
  have hqε : e.symm q ∈ Metric.ball x ε := by
    apply Metric.mem_ball.mpr
    rw [← hdist (e.symm q) hqR x hxR, hqEval]
    exact Metric.mem_ball.mp hqSmall
  refine ⟨e.symm q, hqε, ?_, ?_, ?_⟩
  · rw [← hdist y (hsmall hy) (e.symm q) hqR,
      ← hdist y (hsmall hy) z (hsmall hz), hqEval]
    exact hyq
  · rw [← hdist (e.symm q) hqR z (hsmall hz),
      ← hdist y (hsmall hy) z (hsmall hz), hqEval]
    exact hqz
  · intro w hw
    rw [← hdist y (hsmall hy) z (hsmall hz),
      ← hdist w (hsmall hw) (e.symm q) hqR,
      ← hdist w (hsmall hw) y (hsmall hy),
      ← hdist w (hsmall hw) z (hsmall hz), hqEval]
    exact hcomparison (e w)

end SystolicGrowth
