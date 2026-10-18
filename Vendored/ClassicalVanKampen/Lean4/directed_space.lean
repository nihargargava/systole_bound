module

public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

/-
Vendored from Arthur742Ramos/classical-svk-lean:
https://github.com/Arthur742Ramos/classical-svk-lean
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Frozen path: Lean4/directed_space.lean
Original author: Dominique Lawson; copyright (c) 2023 Dominique Lawson.
Original repository: https://github.com/Dominique-Lawson/Directed-Topology-Lean-4
Original commit: 009529606c66d37ef93b4b81b8587f71ce4d2c56
Original path: Lean4/directed_space.lean
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

namespace Path

/-- Compatibility name for the unit-interval endpoint lemma used by the source port. -/
theorem extend_extends {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ.extend t = γ ⟨t, ht⟩ := by
  exact _root_.Path.extend_extends' γ ⟨t, ht⟩

end Path

/-
  # Definition of directed spaces
  This file defines the directed space, an extension of a topological space where
  some of its paths are considered directed paths.
-/

universe u

open scoped unitInterval

/-- Definition of a directed topological space.

    Dipaths are closed under:
    * Constant paths,
    * Concatenation of paths,
    * Monotone reparametrization of paths
 -/
class DirectedSpace (α : Type u) extends TopologicalSpace α where
  IsDipath : ∀ {x y : α}, Path x y → Prop
  isDipath_constant : ∀ (x : α), IsDipath (Path.refl x)
  isDipath_concat : ∀ {x y z : α} {γ₁ : Path x y} {γ₂ : Path y z}, IsDipath γ₁ → IsDipath γ₂ → IsDipath (Path.trans γ₁ γ₂)
  isDipath_reparam : ∀ {x y : α} {γ : Path x y} {t₀ t₁ : I} {f : Path t₀ t₁}, Monotone f → IsDipath γ → IsDipath (f.map (γ.continuous_toFun))

section DirectedSpace

variable {α : Type u} {x y z : α} [DirectedSpace α] {γ : Path x y}  {γ' : Path y z} {t₀ t₁ : I} {f : Path t₀ t₁}

def IsDipath : (Path x y) → Prop :=
  DirectedSpace.IsDipath

theorem isDipath_constant (x : α) : IsDipath (Path.refl x) :=
  DirectedSpace.isDipath_constant _

theorem isDipath_concat (hγ : IsDipath γ) (hγ' : IsDipath γ') : IsDipath (γ.trans γ') :=
  DirectedSpace.isDipath_concat hγ hγ'

theorem isDipath_reparam (hfmono : Monotone f) (hγ : IsDipath γ) : IsDipath (f.map γ.continuous_toFun) :=
  DirectedSpace.isDipath_reparam hfmono hγ

/-- Casting a path that is directed into another path gives another directed path -/
lemma isDipath_cast {x y x' y' : α} (γ : Path x y) (hx : x' = x) (hy : y' = y) (hγ : IsDipath γ) :
  IsDipath (γ.cast hx hy) := by
    subst_vars
    simpa only [Path.cast_rfl_rfl] using hγ

end DirectedSpace

end SystolicGrowth.Vendored.ClassicalVanKampen
