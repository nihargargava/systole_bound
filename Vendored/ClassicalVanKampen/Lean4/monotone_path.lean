module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

/-
Vendored from Arthur742Ramos/classical-svk-lean:
https://github.com/Arthur742Ramos/classical-svk-lean
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Frozen path: Lean4/monotone_path.lean
Original author: Dominique Lawson; copyright (c) 2023 Dominique Lawson.
Original repository: https://github.com/Dominique-Lawson/Directed-Topology-Lean-4
Original commit: 009529606c66d37ef93b4b81b8587f71ce4d2c56
Original path: Lean4/monotone_path.lean
License: MIT; complete text in ../LICENSE-MIT (relative to Lean4).
Local modifications: imports relocated; namespace isolated under
SystolicGrowth.Vendored.ClassicalVanKampen; compatibility with Lean/mathlib
v4.33.0-rc1. Existing frozen-source comments and proofs are preserved.
-/

namespace SystolicGrowth.Vendored.ClassicalVanKampen

-- Retain the frozen proof scripts and instance names across linter versions.
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.dupNamespace false

/-
  This file contains lemmas about monotone paths in a preordered topological space
-/

open scoped unitInterval

lemma monotone_path_bounded_left {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t :=
    Eq.trans_le (id γ.source.symm) (hγ unitInterval.nonneg')

lemma monotone_path_bounded_right {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : γ t ≤ y :=
  calc
    γ t ≤ γ 1 := hγ (Subtype.coe_le_coe.mp (unitInterval.le_one t))
    _ = y := γ.target

lemma monotone_path_bounded {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) (t : I) : x ≤ γ t ∧ γ t ≤ y :=
  ⟨monotone_path_bounded_left hγ t, monotone_path_bounded_right hγ t⟩

lemma monotone_path_source_le_target {α : Type*} {x y : α} [TopologicalSpace α] [Preorder α]
  {γ : Path x y} (hγ : Monotone γ) : x ≤ y :=
  calc
    x = γ 0 := γ.source.symm
    _ ≤ γ 1 := hγ (by norm_num : (0 : I) ≤ 1)
    _ = y := γ.target

end SystolicGrowth.Vendored.ClassicalVanKampen
