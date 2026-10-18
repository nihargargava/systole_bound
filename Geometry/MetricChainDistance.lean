module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Exact distances in a saturated finite metric chain

The polygon inequality bounds every ordered subchain by its number of
steps times the common adjacent upper bound. If the total endpoint
distance attains that bound, the triangle inequality through both ends
of any subchain forces equality there too. The result includes repeated
indices and zero-step chains and needs no geometric hypotheses.
-/

namespace SystolicGrowth

variable {M : Type*} [PseudoMetricSpace M]

/-- The actual polygon inequality bounds every ordered part of a finite chain. -/
theorem metric_chain_dist_le (f : ℕ → M) {N : ℕ} {δ : ℝ}
    (hadj : ∀ k < N, dist (f k) (f (k + 1)) ≤ δ)
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) :
    dist (f i) (f j) ≤ ((j - i : ℕ) : ℝ) * δ := by
  have h := dist_le_Ico_sum_of_dist_le (f := f) (d := fun _ => δ) hij
    (fun {_} _ hk => hadj _ (hk.trans_le hjN))
  simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using h

/-- A chain saturating its endpoint upper bound saturates every ordered
subchain bound. In particular, no sign assumption on the step bound is needed. -/
theorem metric_chain_dist_eq (f : ℕ → M) {N : ℕ} {δ : ℝ}
    (hadj : ∀ k < N, dist (f k) (f (k + 1)) ≤ δ)
    (hend : dist (f 0) (f N) = (N : ℝ) * δ)
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) :
    dist (f i) (f j) = ((j - i : ℕ) : ℝ) * δ := by
  refine (metric_chain_dist_le f hadj hij hjN).antisymm ?_
  have hp := metric_chain_dist_le f hadj (Nat.zero_le i) (hij.trans hjN)
  have ht := metric_chain_dist_le f hadj hjN le_rfl
  have h := dist_triangle4 (f 0) (f i) (f j) (f N)
  rw [hend] at h
  simp only [Nat.sub_zero] at hp
  rw [Nat.cast_sub hjN] at ht
  rw [Nat.cast_sub hij]
  nlinarith

#print axioms metric_chain_dist_le
#print axioms metric_chain_dist_eq

end SystolicGrowth
