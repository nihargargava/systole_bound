module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Vendored.ClassicalVanKampen.Lean4.directed_homotopy

@[expose] public section

/-
Vendored from Arthur742Ramos/classical-svk-lean:
https://github.com/Arthur742Ramos/classical-svk-lean
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Frozen path: Lean4/trans_refl.lean
Original author: Dominique Lawson; copyright (c) 2023 Dominique Lawson.
Original repository: https://github.com/Dominique-Lawson/Directed-Topology-Lean-4
Original commit: 009529606c66d37ef93b4b81b8587f71ce4d2c56
Original path: Lean4/trans_refl.lean
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
  Auxiliary lemmas for the refl_trans and trans_refl definitions in directed_path_homotopy.lean.
  These two are definitions are dihomotopies related to a `p : Dipath x₀ x₁`:
    refl_trans : from `(refl x₀).trans p` to `p`
    trans_refl : from `p` to `p.trans (refl x₁)`

  Those for trans_refl can be based on the auxiliary lemmas found in algebraic_topology.fundamental_groupoid.basic.
  They use symmetry for refl_trans which is not possible in the directed case, so we have to define them manually.
-/

open DirectedSpace DirectedMap
open scoped unitInterval

universe u v

variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x₀ x₁ : X}

noncomputable section

namespace Dipath

namespace Dihomotopy

open Path.Homotopy

section TransRefl

lemma directed_transReflReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩,
       continuous_toFun := Continuous.subtype_mk continuous_transReflReparamAux _} : C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transReflReparamAux
  simp
  have : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · calc 2 * (x : ℝ)
      _ ≤ 2 * 2⁻¹ := (mul_le_mul_iff_of_pos_left (by norm_num)).mpr h₁
      _ = 1       := by simp
  · linarith
  · linarith

def TransReflReparamAuxMap : D(I, I) where
  toContinuousMap := ⟨fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩,
    Continuous.subtype_mk continuous_transReflReparamAux _⟩
  directed_toFun := directed_transReflReparamAux

lemma trans_refl_reparam_dipath (p : Dipath x₀ x₁) : p.trans (Dipath.refl x₁) =
    p.reparam TransReflReparamAuxMap (Subtype.ext transReflReparamAux_zero)
      (Subtype.ext transReflReparamAux_one) := by
  ext t
  have : (p.trans (Dipath.refl x₁)) t = p.toPath.trans (Path.refl x₁) t := rfl
  rw [this, Path.Homotopy.trans_refl_reparam p.toPath]
  rfl

end TransRefl

section ReflTrans

/-- Auxilliary function for `ReflTransReparam` -/
def ReflTransReparamAux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/2 then
  0
else
  2 * t - 1

@[continuity]
lemma continuous_ReflTransReparamAux : Continuous ReflTransReparamAux := by
  refine' continuous_if_le _ _ (Continuous.continuousOn _) (Continuous.continuousOn _) _ <;>
  [continuity; continuity; continuity; continuity; skip]
  intros x hx
  norm_num [hx]

lemma reflTransReparamAux_mem_I (t : I) : ReflTransReparamAux t ∈ I := by
  unfold ReflTransReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

lemma reflTransReparamAux_zero : ReflTransReparamAux 0 = 0 :=
by norm_num [ReflTransReparamAux]

lemma reflTransReparamAux_one : ReflTransReparamAux 1 = 1 :=
by norm_num [ReflTransReparamAux]


lemma directed_ReflTransReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩,
       continuous_toFun := Continuous.subtype_mk continuous_ReflTransReparamAux _} : C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold ReflTransReparamAux
  simp
  have : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · calc (0 : ℝ)
      _ = (2 : ℝ) * (2⁻¹ : ℝ) - (1 : ℝ) := by norm_num
      _ ≤ 2 * (y : ℝ) - 1 := le_of_lt $ sub_lt_sub_right ((mul_lt_mul_iff_of_pos_left (by norm_num)).mpr (lt_of_not_ge h₂)) 1
  · linarith
  · linarith

def ReflTransReparamAuxMap : D(I, I) where
  toContinuousMap := ⟨fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩,
    Continuous.subtype_mk continuous_ReflTransReparamAux _⟩
  directed_toFun := directed_ReflTransReparamAux

lemma refl_trans_reparam (p : Path x₀ x₁) :
    (Path.refl x₀).trans p =
      p.reparam (fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext
  unfold ReflTransReparamAux
  simp [Path.trans_apply, not_le, coe_to_fun, Function.comp_apply]
  split_ifs
  · simp
  · simp
  · rfl
  · rfl

lemma refl_trans_reparam_dipath (p : Dipath x₀ x₁) : (Dipath.refl x₀).trans p =
    p.reparam ReflTransReparamAuxMap
      (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext t
  have : ((Dipath.refl x₀).trans p) t =  (Path.refl x₀).trans p.toPath t := rfl
  rw [this, refl_trans_reparam p.toPath]
  rfl

end ReflTrans

end Dihomotopy

end Dipath



end

end SystolicGrowth.Vendored.ClassicalVanKampen
