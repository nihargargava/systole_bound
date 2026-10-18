module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Mathlib.Topology.Subpath

@[expose] public section

/-!
# Actual path subdivision subordinate to two open sets

Pulling the two open sets back along the given continuous path gives an
open cover of the compact unit interval. Mathlib's Lebesgue-number
subdivision supplies a monotone, eventually constant mesh; its finite
restriction gives actual subpaths lying in one of the original open sets.
No assumption on the number or arrangement of contacts is needed.
-/

open Set
open scoped unitInterval

namespace SystolicGrowth

/-- Every actual continuous path has a finite, monotone subdivision whose
full subpath ranges lie in one member of a genuine two-set open cover. -/
theorem exists_monotone_subpath_range_subset_two_open_cover
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : Fin (n + 1) → unitInterval,
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ i : Fin n,
        range (p.subpath (t i.castSucc) (t i.succ)) ⊆ U ∨
          range (p.subpath (t i.castSucc) (t i.succ)) ⊆ V := by
  let c : Bool → Set unitInterval := fun b => if b then p ⁻¹' U else p ⁻¹' V
  have hcopen : ∀ b, IsOpen (c b) := by
    intro b
    cases b
    · exact hV.preimage p.continuous
    · exact hU.preimage p.continuous
  have hccover : univ ⊆ ⋃ b, c b := by
    intro s _
    have hs : p s ∈ U ∨ p s ∈ V := by
      rw [← mem_union, hcover]
      exact mem_univ _
    rcases hs with hs | hs
    · exact mem_iUnion.mpr ⟨true, hs⟩
    · exact mem_iUnion.mpr ⟨false, hs⟩
  obtain ⟨t, htzero, htmono, ⟨m, htevent⟩, htsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover
  refine ⟨m + 1, Nat.succ_pos m, fun i => t i.val, ?_, ?_, ?_, ?_⟩
  · exact htzero
  · exact htevent (m + 1) (Nat.le_succ m)
  · intro i j hij
    exact htmono hij
  · intro i
    obtain ⟨b, hb⟩ := htsub i.val
    have hle : t i.val ≤ t (i.val + 1) := htmono (Nat.le_succ i.val)
    change range (p.subpath (t i.val) (t (i.val + 1))) ⊆ U ∨
      range (p.subpath (t i.val) (t (i.val + 1))) ⊆ V
    rw [Path.range_subpath_of_le p _ _ hle]
    cases b
    · right
      exact image_subset_iff.mpr hb
    · left
      exact image_subset_iff.mpr hb

#print axioms exists_monotone_subpath_range_subset_two_open_cover

end SystolicGrowth
