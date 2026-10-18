module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaTypeIISquareExpansion
public import CookMagyar.HuaTypeIISupportCount
public import CookMagyar.GeneralCubicWeyl

@[expose] public section

/-!
# The diagonal in Hua's Type-II mean square

The proof is finite counting only. It uses the *actual* strict/weak endpoint
filter, a unit-norm cubic phase, and `D < u ≤ D' ≤ 2D`. The off-diagonal
oscillatory estimate is not asserted here.
-/

open Finset
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- The complete diagonal contribution in the exact `Q=1` cubic Type-II
block is at most `P/l`. No cancellation or assumption on `a,q,b,c,d` is
used; these parameters only specify unit-modulus phases. -/
theorem hua_typeII_diagonal_le
    (P l D D' a q : ℕ) (P' : ℝ) (V : Finset ℕ) (b c d : ℝ)
    (hl : 0 < l) (hD : 0 < D) (hD' : D' ≤ 2 * D) :
    (∑ u ∈ Finset.Icc (D + 1) D',
      ∑ v ∈ V.filter (fun v : ℕ =>
        0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
          (v : ℝ) ≤ ((P : ℝ) / l) / u),
        ‖generalCubicPhase ((a : ℝ) / q) b c d (l * u * v)‖ ^ 2) ≤
      (P : ℝ) / l := by
  classical
  let S : ℕ → Finset ℕ := fun u => V.filter (fun v : ℕ =>
    0 < v ∧ P' / (u : ℝ) < (v : ℝ) ∧
      (v : ℝ) ≤ ((P : ℝ) / l) / u)
  have hphase : ∀ u ∈ Finset.Icc (D + 1) D', ∀ v ∈ S u,
      ‖generalCubicPhase ((a : ℝ) / q) b c d (l * u * v)‖ ≤ 1 := by
    intro u hu v hv
    simp
  have hcard : ∀ u ∈ Finset.Icc (D + 1) D',
      ((S u).card : ℝ) ≤ ((P : ℝ) / l) / D := by
    intro u hu
    have hu : D < u := by
      have := (Finset.mem_Icc.mp hu).1
      omega
    simpa only [S] using card_hua_typeII_interval_support_le P l D u P' V hl hD hu
  have hdiag := diagonal_le_card_mul (Finset.Icc (D + 1) D') S
    (fun u v => generalCubicPhase ((a : ℝ) / q) b c d (l * u * v))
    (((P : ℝ) / l) / D) hphase hcard
  have hUcard : ((Finset.Icc (D + 1) D').card : ℝ) ≤ (D : ℝ) := by
    have hNat : (Finset.Icc (D + 1) D').card ≤ D := by
      simp only [Nat.card_Icc]
      omega
    exact_mod_cast hNat
  have hnonneg : 0 ≤ ((P : ℝ) / l) / D := by positivity
  calc
    _ ≤ ((Finset.Icc (D + 1) D').card : ℝ) * (((P : ℝ) / l) / D) := hdiag
    _ ≤ (D : ℝ) * (((P : ℝ) / l) / D) :=
      mul_le_mul_of_nonneg_right hUcard hnonneg
    _ = (P : ℝ) / l := by
      have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      field_simp

#print axioms hua_typeII_diagonal_le

end SystolicGrowth.CookMagyarCircle
