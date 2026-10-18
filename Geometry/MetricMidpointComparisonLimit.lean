module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Midpoint comparison through proper metric retractions

Midpoints in the approximating spaces are retracted into one fixed proper
space. A bounded subsequence converges there. Retraction distortion bounds
give the exact native midpoint and transport comparison against every fixed
native test point along that same subsequence. No comparison on the native
space is assumed, and no uniform finite-net convergence is required.
-/

open Set Filter Metric
open scoped Topology

namespace SystolicGrowth

/-- All-test midpoint-cosh comparison passes to a proper native metric space
when forward pair distances converge, actual left-inverse retractions have
distortion tending to one, and the approximating curvature scales tend to one.
The approximating midpoint family is a prerequisite, not a native comparison
premise. -/
theorem exists_midpoint_cosh_all_test_of_proper_retract_metric_limit
    {M : Type*} [MetricSpace M] [ProperSpace M]
    {N : ℕ → Type*} [∀ n, MetricSpace (N n)]
    (F : ∀ n, M → N n) (G : ∀ n, N n → M)
    (B lam : ℕ → ℝ) (hBpos : ∀ n, 0 < B n) (hlampos : ∀ n, 0 < lam n)
    (hB : Tendsto B atTop (𝓝 1)) (hlam : Tendsto lam atTop (𝓝 1))
    (hinv : ∀ n x, G n (F n x) = x)
    (hG : ∀ n (p q : N n), dist (G n p) (G n q) ≤ B n * dist p q)
    (happrox : ∀ x y : M, Tendsto (fun n => dist (F n x) (F n y))
      atTop (𝓝 (dist x y)))
    (hmid : ∀ n (x y : N n), ∃ q : N n,
      dist x q = dist x y / 2 ∧ dist q y = dist x y / 2 ∧
      ∀ z : N n,
        2 * Real.cosh (lam n * dist x y / 2) * Real.cosh (lam n * dist z q) ≤
          Real.cosh (lam n * dist z x) + Real.cosh (lam n * dist z y))
    (x y : M) :
    ∃ m : M, dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : M, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y) := by
  classical
  choose q hqx hqy hqcomparison using fun n => hmid n (F n x) (F n y)
  let m : ℕ → M := fun n => G n (q n)
  have hupperLeft (n : ℕ) :
      dist x (m n) ≤ B n * (dist (F n x) (F n y) / 2) := by
    have h := hG n (F n x) (q n)
    rw [hinv, hqx] at h
    exact h
  have hupperRight (n : ℕ) :
      dist (m n) y ≤ B n * (dist (F n x) (F n y) / 2) := by
    have h := hG n (q n) (F n y)
    rw [hinv, hqy] at h
    exact h
  have hupperLimit : Tendsto
      (fun n => B n * (dist (F n x) (F n y) / 2)) atTop (𝓝 (dist x y / 2)) := by
    simpa only [one_mul] using hB.mul ((happrox x y).div_const 2)
  have hbounded : ∀ᶠ n in atTop, m n ∈ closedBall x (dist x y / 2 + 1) := by
    have hscalar := (tendsto_order.mp hupperLimit).2 (dist x y / 2 + 1) (by linarith)
    filter_upwards [hscalar] with n hn
    exact mem_closedBall.mpr (by
      rw [dist_comm]
      exact (hupperLeft n).trans hn.le)
  obtain ⟨p, _, φ, hφ, hp⟩ :=
    (isCompact_closedBall x (dist x y / 2 + 1)).tendsto_subseq' hbounded.frequently
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hm : Tendsto (fun n => m (φ n)) atTop (𝓝 p) := hp
  have hleftBound : dist x p ≤ dist x y / 2 :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds.dist hm)
      (hupperLimit.comp hφtop) (fun n => hupperLeft (φ n))
  have hrightBound : dist p y ≤ dist x y / 2 :=
    le_of_tendsto_of_tendsto' (hm.dist tendsto_const_nhds)
      (hupperLimit.comp hφtop) (fun n => hupperRight (φ n))
  have htriangle := dist_triangle x p y
  have hleft : dist x p = dist x y / 2 := by linarith
  have hright : dist p y = dist x y / 2 := by linarith
  refine ⟨p, hleft, hright, ?_⟩
  intro z
  have hscale (n : ℕ) :
      (lam n / B n) * dist z (m n) ≤ lam n * dist (F n z) (q n) := by
    have h := hG n (F n z) (q n)
    rw [hinv] at h
    calc
      _ ≤ (lam n / B n) * (B n * dist (F n z) (q n)) :=
        mul_le_mul_of_nonneg_left h (div_nonneg (hlampos n).le (hBpos n).le)
      _ = lam n * dist (F n z) (q n) := by
        rw [← mul_assoc, div_mul_cancel₀ _ (hBpos n).ne']
  have hcomparison (n : ℕ) :
      2 * Real.cosh (lam n * dist (F n x) (F n y) / 2) *
          Real.cosh ((lam n / B n) * dist z (m n)) ≤
        Real.cosh (lam n * dist (F n z) (F n x)) +
          Real.cosh (lam n * dist (F n z) (F n y)) := by
    have hcosh : Real.cosh ((lam n / B n) * dist z (m n)) ≤
        Real.cosh (lam n * dist (F n z) (q n)) := by
      apply Real.cosh_le_cosh.mpr
      rw [abs_of_nonneg (mul_nonneg
        (div_nonneg (hlampos n).le (hBpos n).le) dist_nonneg),
        abs_of_nonneg (mul_nonneg (hlampos n).le dist_nonneg)]
      exact hscale n
    exact (mul_le_mul_of_nonneg_left hcosh (by positivity)).trans
      (hqcomparison n (F n z))
  have hlamφ : Tendsto (fun n => lam (φ n)) atTop (𝓝 1) := hlam.comp hφtop
  have hBφ : Tendsto (fun n => B (φ n)) atTop (𝓝 1) := hB.comp hφtop
  have hratio : Tendsto (fun n => lam (φ n) / B (φ n)) atTop (𝓝 1) := by
    simpa only [Pi.div_def, div_self (by norm_num : (1 : ℝ) ≠ 0)] using
      hlamφ.div hBφ (by norm_num)
  have hxy : Tendsto (fun n => lam (φ n) * dist (F (φ n) x) (F (φ n) y) / 2)
      atTop (𝓝 (dist x y / 2)) := by
    simpa only [one_mul, Function.comp_apply] using
      (hlamφ.mul ((happrox x y).comp hφtop)).div_const 2
  have hzm : Tendsto (fun n => (lam (φ n) / B (φ n)) * dist z (m (φ n)))
      atTop (𝓝 (dist z p)) := by
    simpa only [one_mul] using hratio.mul (tendsto_const_nhds.dist hm)
  have hzx : Tendsto (fun n => lam (φ n) * dist (F (φ n) z) (F (φ n) x))
      atTop (𝓝 (dist z x)) := by
    simpa only [one_mul, Function.comp_apply] using hlamφ.mul ((happrox z x).comp hφtop)
  have hzy : Tendsto (fun n => lam (φ n) * dist (F (φ n) z) (F (φ n) y))
      atTop (𝓝 (dist z y)) := by
    simpa only [one_mul, Function.comp_apply] using hlamφ.mul ((happrox z y).comp hφtop)
  have hleftLimit := ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
    ((Real.continuous_cosh.tendsto _).comp hxy)).mul
      ((Real.continuous_cosh.tendsto _).comp hzm)
  have hrightLimit := ((Real.continuous_cosh.tendsto _).comp hzx).add
    ((Real.continuous_cosh.tendsto _).comp hzy)
  exact le_of_tendsto_of_tendsto' hleftLimit hrightLimit (fun n => hcomparison (φ n))

#print axioms exists_midpoint_cosh_all_test_of_proper_retract_metric_limit

end SystolicGrowth
