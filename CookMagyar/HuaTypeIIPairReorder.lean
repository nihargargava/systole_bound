module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Reordering the ordered off-diagonal pairs in Hua's Type-II sum

This is finite algebra only. A variable support `W u` sits inside one fixed
support `V` for each `u ∈ U`. The theorem moves both inner indices outside,
retaining `w ∈ (W u).erase v` as the conditions `w ≠ v` and
`v, w ∈ W u`. No symmetry of `f` or absolute-value bound is used.
The strictly oriented variant retains `w < v` instead of summing both
orientations of an off-diagonal pair.

For Hua's application, `W u` will be the fixed divisor support intersected
with the `u`-dependent interval. Thus the final filter still contains both
endpoint conditions; this lemma does not estimate the resulting inner sum.
-/

open Finset
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

/-- Reorder a finite off-diagonal triple sum by its ordered pair `(v, w)`.
The result keeps exactly those outer indices for which both entries lie in
the actual variable support. In particular, `(v, w)` is not identified with
`(w, v)`. -/
theorem sum_offDiagonal_reindex
    {ι κ α : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommMonoid α]
    (U : Finset ι) (V : Finset κ) (W : ι → Finset κ)
    (hW : ∀ u ∈ U, W u ⊆ V) (f : ι → κ → κ → α) :
    (∑ u ∈ U, ∑ v ∈ W u, ∑ w ∈ (W u).erase v, f u v w) =
      ∑ v ∈ V, ∑ w ∈ V.erase v,
        ∑ u ∈ U.filter (fun u => v ∈ W u ∧ w ∈ W u), f u v w := by
  classical
  calc
    _ = ∑ v ∈ V, ∑ u ∈ U.filter (fun u => v ∈ W u),
          ∑ w ∈ (W u).erase v, f u v w := by
      apply Finset.sum_comm'
      intro u v
      constructor
      · rintro ⟨hu, hv⟩
        exact ⟨Finset.mem_filter.mpr ⟨hu, hv⟩, hW u hu hv⟩
      · rintro ⟨hu, _⟩
        exact Finset.mem_filter.mp hu
    _ = ∑ v ∈ V, ∑ w ∈ V.erase v,
          ∑ u ∈ U.filter (fun u => v ∈ W u ∧ w ∈ W u), f u v w := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_comm'
      intro u w
      constructor
      · rintro ⟨hu, hw⟩
        rcases Finset.mem_filter.mp hu with ⟨huU, huv⟩
        rcases Finset.mem_erase.mp hw with ⟨hwne, huw⟩
        exact ⟨Finset.mem_filter.mpr ⟨huU, ⟨huv, huw⟩⟩,
          Finset.mem_erase.mpr ⟨hwne, hW u huU huw⟩⟩
      · rintro ⟨hu, hw⟩
        rcases Finset.mem_filter.mp hu with ⟨huU, ⟨huv, huw⟩⟩
        exact ⟨Finset.mem_filter.mpr ⟨huU, huv⟩,
          Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, huw⟩⟩

/-- Reorder the strictly oriented part of a variable-support triple sum.
Only `w < v` pairs occur; no reverse pair is introduced, and the summand is
unchanged. No order laws beyond the strict relation itself are needed. -/
theorem sum_lt_reindex
    {ι κ α : Type*} [DecidableEq ι] [DecidableEq κ] [LT κ] [DecidableLT κ]
    [AddCommMonoid α]
    (U : Finset ι) (V : Finset κ) (W : ι → Finset κ)
    (hW : ∀ u ∈ U, W u ⊆ V) (f : ι → κ → κ → α) :
    (∑ u ∈ U, ∑ v ∈ W u,
      ∑ w ∈ (W u).filter (fun w => w < v), f u v w) =
      ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v),
        ∑ u ∈ U.filter (fun u => v ∈ W u ∧ w ∈ W u), f u v w := by
  classical
  calc
    _ = ∑ v ∈ V, ∑ u ∈ U.filter (fun u => v ∈ W u),
          ∑ w ∈ (W u).filter (fun w => w < v), f u v w := by
      apply Finset.sum_comm'
      intro u v
      constructor
      · rintro ⟨hu, hv⟩
        exact ⟨Finset.mem_filter.mpr ⟨hu, hv⟩, hW u hu hv⟩
      · rintro ⟨hu, _⟩
        exact Finset.mem_filter.mp hu
    _ = ∑ v ∈ V, ∑ w ∈ V.filter (fun w => w < v),
          ∑ u ∈ U.filter (fun u => v ∈ W u ∧ w ∈ W u), f u v w := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_comm'
      intro u w
      constructor
      · rintro ⟨hu, hw⟩
        rcases Finset.mem_filter.mp hu with ⟨huU, huv⟩
        rcases Finset.mem_filter.mp hw with ⟨huw, hwlt⟩
        exact ⟨Finset.mem_filter.mpr ⟨huU, ⟨huv, huw⟩⟩,
          Finset.mem_filter.mpr ⟨hW u huU huw, hwlt⟩⟩
      · rintro ⟨hu, hw⟩
        rcases Finset.mem_filter.mp hu with ⟨huU, ⟨huv, huw⟩⟩
        exact ⟨Finset.mem_filter.mpr ⟨huU, huv⟩,
          Finset.mem_filter.mpr ⟨huw, (Finset.mem_filter.mp hw).2⟩⟩

#print axioms sum_offDiagonal_reindex
#print axioms sum_lt_reindex

end SystolicGrowth.CookMagyarCircle
