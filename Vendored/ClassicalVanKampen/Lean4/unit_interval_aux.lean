module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Tactic

@[expose] public section

/-
Vendored from Arthur742Ramos/classical-svk-lean:
https://github.com/Arthur742Ramos/classical-svk-lean
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Frozen path: Lean4/unit_interval_aux.lean
Original author: Dominique Lawson; copyright (c) 2023 Dominique Lawson.
Original repository: https://github.com/Dominique-Lawson/Directed-Topology-Lean-4
Original commit: 009529606c66d37ef93b4b81b8587f71ce4d2c56
Original path: Lean4/unit_interval_aux.lean
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
  This file contains lemmas about
  * elements being contained in the unit interval.
  * relations between elements in the unit interval.
-/

open scoped unitInterval

namespace unitIAux

lemma zero_le (T : I) : ⟨0, unitInterval.zero_mem⟩ ≤ T := Subtype.coe_le_coe.mp T.2.1
lemma le_one (T : I) : T ≤ ⟨1, unitInterval.one_mem⟩:= Subtype.coe_le_coe.mp T.2.2

lemma double_pos_of_pos {T : I} (hT₀ : 0 < T) : 0 < (2 * T : ℝ) :=
  mul_pos two_pos hT₀
lemma double_sigma_pos_of_lt_one {T : I} (hT₁ : T < 1) : 0 < (2 * (1 - T) : ℝ) :=
  mul_pos two_pos (by {simp; exact hT₁})

lemma double_mem_I {t : I} (ht : ↑t ≤ (2⁻¹ : ℝ)) : 2 * (t : ℝ) ∈ I := by
  constructor
  exact mul_nonneg zero_le_two t.2.1
  calc 2 * (t : ℝ)
      _ ≤ 2 * 2⁻¹ := mul_le_mul_of_nonneg_left ht (by norm_num)
      _ = 1 := by norm_num

lemma double_sub_one_mem_I {t : I} (ht : (2⁻¹ : ℝ) ≤ ↑t) : 2 * (t : ℝ) - 1 ∈ I := by
  constructor
  calc 0 = 2 * (2⁻¹ : ℝ) - 1 := by norm_num
       _ ≤ 2 * ↑t - 1        := sub_le_sub_right (mul_le_mul_of_nonneg_left ht (by norm_num)) 1
  calc 2 * (t : ℝ) - 1
      _ ≤ 2 * 1 - 1 := sub_le_sub_right (mul_le_mul_of_nonneg_left t.2.2 (by norm_num)) 1
      _ = 1         := by norm_num

lemma interp_left_le_of_le (T : I) {a b : I} (hab : a ≤ b) : (σ T : ℝ) * ↑a + ↑T ≤ (σ T : ℝ) * ↑b + ↑T := by
  exact add_le_add_left
    (mul_le_mul_of_nonneg_left (Subtype.coe_le_coe.mp hab) (σ T).2.1) (T : ℝ)

section

noncomputable section

lemma half_mem_I : (2⁻¹ : ℝ) ∈ I :=
⟨by norm_num, by norm_num⟩

abbrev half_I : I := ⟨(2⁻¹ : ℝ), half_mem_I⟩

lemma has_T_half {t₀ t₁ : I} (γ : Path t₀ t₁) (ht₀ : ↑t₀ < (2⁻¹ : ℝ)) (ht₁ : ↑t₁ > (2⁻¹ : ℝ)) :
  ∃ (T : I),  0 < T ∧ T < 1 ∧ (γ T) = half_I := by

  have : γ.toFun 0 ≤ half_I := by rw [γ.source']; exact Subtype.coe_le_coe.mp (le_of_lt ht₀)
  have h₀ : ∃ (t : I), γ t ≤ half_I := ⟨0, this⟩
  have : half_I ≤ γ.toFun 1 := by rw [γ.target']; exact Subtype.coe_le_coe.mp (le_of_lt ht₁)
  have h₁ : ∃ (t : I), half_I ≤ γ t := ⟨1, this⟩
  have hy := Set.mem_range.mp (mem_range_of_exists_le_of_exists_ge γ.continuous_toFun h₀ h₁)

  cases' hy with T hT
  use T
  have hT₀ : 0 ≠ T := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₀ : ℝ)
    calc (t₀ : ℝ)
        _ < 2⁻¹       := ht₀
        _ = (γ 0 : ℝ) := Subtype.coe_inj.mpr hT.symm
        _ = ↑t₀       := Subtype.coe_inj.mpr γ.source'

  have hT₁ : T ≠ 1 := by
    rintro ⟨rfl⟩
    apply lt_irrefl (t₁ : ℝ)
    calc (t₁ : ℝ)
      _ = (γ 1 : ℝ) := Subtype.coe_inj.mpr γ.target'.symm
      _ = half_I    := Subtype.coe_inj.mpr hT
      _ < ↑t₁       := ht₁

  exact ⟨lt_iff_le_and_ne.mpr ⟨T.2.1, hT₀⟩, lt_iff_le_and_ne.mpr ⟨T.2.2, hT₁⟩, hT⟩
end

end

end unitIAux

end SystolicGrowth.Vendored.ClassicalVanKampen
