module

public import Vendored.ClassicalVanKampen.Lean4.constructions

@[expose] public section

/-
Vendored from Arthur742Ramos/classical-svk-lean:
https://github.com/Arthur742Ramos/classical-svk-lean
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Frozen path: Lean4/directed_unit_interval.lean
Original author: Dominique Lawson; copyright (c) 2023 Dominique Lawson.
Original repository: https://github.com/Dominique-Lawson/Directed-Topology-Lean-4
Original commit: 009529606c66d37ef93b4b81b8587f71ce4d2c56
Original path: Lean4/directed_unit_interval.lean
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
  This file contains the definition of the directed unit interval.
  The directedness is induced by the preorder it inherits from ℝ.
-/

open scoped unitInterval

universe u

namespace DirectedUnitInterval

/--
  Construct the directed unit interval by using the preorder inherited from ℝ
-/
instance : DirectedSpace I := DirectedSpace.Preorder I

/--
  The identity on I as a path I → I.
-/
def IdentityPath : Path (0 : I) (1 : I) :=
{
  toFun := fun x => x,
  continuous_toFun := by continuity,
  source' := by simp,
  target' := by simp,
}

/-- The identity path is a directed path. -/
lemma isDipath_identityPath : IsDipath IdentityPath := fun _ _ hab => hab

/--
  If `γ` is path and the identity path on I composed with `γ` is a directed path, then `γ` is a directed path.
-/
lemma isDipath_of_isDipath_comp_id {X : Type u} [DirectedSpace X] {x y : X} {γ : Path x y}
  (h : IsDipath $ IdentityPath.map γ.continuous_toFun) : IsDipath γ := by
  have hpath : (IdentityPath.map γ.continuous_toFun).cast γ.source.symm γ.target.symm = γ := by
    apply Path.ext
    funext t
    rfl
  rw [← hpath]
  exact isDipath_cast (IdentityPath.map γ.continuous_toFun) γ.source.symm γ.target.symm h

/-- A directed map from I to I is monotone -/
lemma monotone_of_directed (f : D(I, I)) : Monotone f :=
  fun _ _ h => (f.directed_toFun IdentityPath isDipath_identityPath) h

/-- A continuous map from I to I that is monotone is directed -/
lemma directed_of_monotone (f : C(I, I)) (hf_mono : Monotone f) : DirectedMap.Directed f :=
  fun _ _ _ γ_dipath _ _ ht₀t₁ => hf_mono (γ_dipath ht₀t₁)

/-- A directed path on I is bounded by its source and target -/
lemma directed_path_bounded {t₀ t₁ : I} {γ : Path t₀ t₁} (γ_dipath : IsDipath γ) : ∀ t, t₀ ≤ γ t ∧ γ t ≤ t₁ :=
  monotone_path_bounded γ_dipath

/-- The source of a directed path on I is `≤` than its target -/
lemma directed_path_source_le_target {t₀ t₁ : I} {γ : Path t₀ t₁} (γ_dipath : IsDipath γ) : t₀ ≤ t₁ :=
  monotone_path_source_le_target γ_dipath

end DirectedUnitInterval

end SystolicGrowth.Vendored.ClassicalVanKampen
