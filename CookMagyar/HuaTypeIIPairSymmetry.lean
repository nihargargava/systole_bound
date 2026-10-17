module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Symmetry of a real off-diagonal pair sum

Hua's mean-square expansion contains both ordered pairs `(v,w)` and `(w,v)`.
For a real-valued symmetric summand they contribute equally. This finite
identity leaves only the orientation `w < v`, where the natural cubic
difference `v³-w³` is positive and its divisor factorization applies.
-/

open Finset
open ComplexConjugate
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- The real part of a phase pair is unchanged when its two entries are
reversed. This is the symmetry used below, not a claim that the complex
products themselves are equal. -/
theorem mul_conj_re_symm (z w : ℂ) :
    (z * conj w).re = (w * conj z).re := by
  calc
    (z * conj w).re = (conj (z * conj w)).re := (Complex.conj_re _).symm
    _ = (w * conj z).re := by simp [map_mul, mul_comm]

/-- A symmetric real off-diagonal pair sum is twice its `w < v` half.
This is an exact finite identity, with no cancellation estimate. -/
theorem sum_offDiagonal_eq_two_sum_lt
    (V : Finset ℕ) (f : ℕ → ℕ → ℝ)
    (hsymm : ∀ v w, f v w = f w v) :
    (∑ v ∈ V, ∑ w ∈ V.erase v, f v w) =
      2 * ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v), f v w := by
  classical
  have hsplit (v : ℕ) :
      (∑ w ∈ V.erase v, f v w) =
        (∑ w ∈ V.filter (fun w => w < v), f v w) +
        (∑ w ∈ V.filter (fun w => v < w), f v w) := by
    have hpart := Finset.sum_filter_add_sum_filter_not (V.erase v)
      (fun w => w < v) (f v)
    have hlow : (V.erase v).filter (fun w => w < v) =
        V.filter (fun w => w < v) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hwV⟩, hlt⟩
        exact ⟨hwV, hlt⟩
      · rintro ⟨hwV, hlt⟩
        exact ⟨⟨ne_of_lt hlt, hwV⟩, hlt⟩
    have hhigh : (V.erase v).filter (fun w => ¬ w < v) =
        V.filter (fun w => v < w) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨hne, hwV⟩, hnot⟩
        exact ⟨hwV, lt_of_le_of_ne (Nat.le_of_not_lt hnot) hne.symm⟩
      · rintro ⟨hwV, hlt⟩
        exact ⟨⟨ne_of_gt hlt, hwV⟩, not_lt_of_ge hlt.le⟩
    rw [← hpart, hlow, hhigh]
  have hswap :
      (∑ v ∈ V, ∑ w ∈ V.filter (fun w => v < w), f v w) =
        ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v), f v w := by
    calc
      _ = ∑ w ∈ V, ∑ v ∈ V.filter (fun v => v < w), f v w := by
        apply Finset.sum_comm'
        intro v w
        simp only [Finset.mem_filter]
        tauto
      _ = ∑ w ∈ V, ∑ v ∈ V.filter (fun v => v < w), f w v := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro v hv
        exact hsymm v w
      _ = _ := rfl
  calc
    _ = (∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v), f v w) +
        (∑ v ∈ V, ∑ w ∈ V.filter (fun w => v < w), f v w) := by
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib]
    _ = _ := by rw [hswap]; ring

#print axioms mul_conj_re_symm
#print axioms sum_offDiagonal_eq_two_sum_lt

end SystolicGrowth.CookMagyarCircle
