module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Geometry.MetricSplitPathCosh
public import Mathlib.Topology.MetricSpace.Gluing

@[expose] public section

/-!
# Midpoint comparison on an isometric metric inductive limit

A midpoint constructed in one finite stage remains the same midpoint in
every larger stage. Uniqueness from the all-test comparison therefore gives
comparison with every test point of the actual metric inductive limit.
This theorem does not supply the geometric comparison for any finite stage.
-/

namespace SystolicGrowth

private theorem toInductiveLimit_leRecOn
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    {f : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (f n))
    {i k : ℕ} (hik : i ≤ k) (x : X i) :
    Metric.toInductiveLimit I k (Nat.leRecOn hik (f _) x) =
      Metric.toInductiveLimit I i x := by
  induction k, hik using Nat.le_induction with
  | base => simp only [Nat.leRecOn_self]
  | succ k hik ih =>
      rw [Nat.leRecOn_succ hik]
      exact (congrFun (Metric.toInductiveLimit_commute I k)
        (Nat.leRecOn hik (f _) x)).trans ih

private theorem exists_inductiveLimit_stage
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    {f : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (f n))
    (x : Metric.InductiveLimit I) :
    ∃ n, ∃ a : X n, Metric.toInductiveLimit I n a = x := by
  obtain ⟨⟨n, a⟩, rfl⟩ := Quotient.exists_rep x
  exact ⟨n, a, rfl⟩

/-- Genuine all-test midpoint comparison in each finite stage passes to
mathlib's actual metric inductive limit of isometric inclusions. -/
theorem exists_midpoint_cosh_all_test_inductiveLimit
    {X : ℕ → Type*} [∀ n, MetricSpace (X n)]
    {f : ∀ n, X n → X (n + 1)} (I : ∀ n, Isometry (f n))
    (hmid : ∀ n, ∀ x y : X n, ∃ m : X n,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : X n, 2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
        Real.cosh (dist z x) + Real.cosh (dist z y))
    (x y : Metric.InductiveLimit I) :
    ∃ m : Metric.InductiveLimit I,
      dist x m = dist x y / 2 ∧ dist m y = dist x y / 2 ∧
      ∀ z : Metric.InductiveLimit I,
        2 * Real.cosh (dist x y / 2) * Real.cosh (dist z m) ≤
          Real.cosh (dist z x) + Real.cosh (dist z y) := by
  obtain ⟨i, a, ha⟩ := exists_inductiveLimit_stage I x
  obtain ⟨j, b, hb⟩ := exists_inductiveLimit_stage I y
  let k := max i j
  let ak : X k := Nat.leRecOn (C := X) (Nat.le_max_left i j) (f _) a
  let bk : X k := Nat.leRecOn (C := X) (Nat.le_max_right i j) (f _) b
  have hak : Metric.toInductiveLimit I k ak = x :=
    (toInductiveLimit_leRecOn I (Nat.le_max_left i j) a).trans ha
  have hbk : Metric.toInductiveLimit I k bk = y :=
    (toInductiveLimit_leRecOn I (Nat.le_max_right i j) b).trans hb
  obtain ⟨mk, ham, hmb, _⟩ := hmid k ak bk
  refine ⟨Metric.toInductiveLimit I k mk, ?_, ?_, ?_⟩
  · simpa only [← hak, ← hbk, (Metric.toInductiveLimit_isometry I k).dist_eq] using ham
  · simpa only [← hak, ← hbk, (Metric.toInductiveLimit_isometry I k).dist_eq] using hmb
  · intro z
    obtain ⟨l, c, hc⟩ := exists_inductiveLimit_stage I z
    let K := max k l
    have hkK : k ≤ K := Nat.le_max_left k l
    have hlK : l ≤ K := Nat.le_max_right k l
    let A : X K := Nat.leRecOn (C := X) hkK (f _) ak
    let B : X K := Nat.leRecOn (C := X) hkK (f _) bk
    let M : X K := Nat.leRecOn (C := X) hkK (f _) mk
    let C : X K := Nat.leRecOn (C := X) hlK (f _) c
    have hA : Metric.toInductiveLimit I K A = x :=
      (toInductiveLimit_leRecOn I hkK ak).trans hak
    have hB : Metric.toInductiveLimit I K B = y :=
      (toInductiveLimit_leRecOn I hkK bk).trans hbk
    have hM : Metric.toInductiveLimit I K M = Metric.toInductiveLimit I k mk :=
      toInductiveLimit_leRecOn I hkK mk
    have hC : Metric.toInductiveLimit I K C = z :=
      (toInductiveLimit_leRecOn I hlK c).trans hc
    have hdist (u v : X k) :
        dist (Nat.leRecOn (C := X) hkK (f _) u)
          (Nat.leRecOn (C := X) hkK (f _) v) = dist u v := by
      calc
        _ = dist (Metric.toInductiveLimit I K (Nat.leRecOn hkK (f _) u))
            (Metric.toInductiveLimit I K (Nat.leRecOn hkK (f _) v)) :=
          ((Metric.toInductiveLimit_isometry I K).dist_eq _ _).symm
        _ = dist (Metric.toInductiveLimit I k u) (Metric.toInductiveLimit I k v) := by
          rw [toInductiveLimit_leRecOn I hkK u, toInductiveLimit_leRecOn I hkK v]
        _ = dist u v := (Metric.toInductiveLimit_isometry I k).dist_eq _ _
    have hAM : dist A M = dist A B / 2 := by
      simpa only [A, M, B, hdist] using ham
    have hMB : dist M B = dist A B / 2 := by
      simpa only [A, M, B, hdist] using hmb
    have hcomparison := cosh_comparison_at_specified_midpoint (hmid K A B) hAM hMB C
    simpa only [← (Metric.toInductiveLimit_isometry I K).dist_eq, hA, hB, hM, hC]
      using hcomparison

#print axioms exists_midpoint_cosh_all_test_inductiveLimit

end SystolicGrowth
