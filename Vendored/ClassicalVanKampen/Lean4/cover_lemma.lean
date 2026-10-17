module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UnitInterval
public import Vendored.ClassicalVanKampen.Lean4.fraction

@[expose] public section

/-
Vendored from Arthur742Ramos/classical-svk-lean:
https://github.com/Arthur742Ramos/classical-svk-lean
Frozen commit: 874680e16db88b4a41daadf56eafbac79fd2f748
Frozen path: Lean4/cover_lemma.lean
Original author: Dominique Lawson; copyright (c) 2023 Dominique Lawson.
Original repository: https://github.com/Dominique-Lawson/Directed-Topology-Lean-4
Original commit: 009529606c66d37ef93b4b81b8587f71ce4d2c56
Original path: Lean4/cover_lemma.lean
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
  This file contains two applications of the Lebesgue Number Lemma:
  One concerns the unit interval and the other concerns the unit square.
-/

universe u

open scoped unitInterval

/-! ### Auxiliary lemmas -/

/--
For any two natural numbers `i n : ℕ` with `n > 0`, we have that
`(2i+1)/(2n)` is contained in the interval `[i/n, (i+1)/n]`.
-/
lemma mid_point_Icc {i n : ℕ} (hn : n > 0) :
    (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := by
  constructor <;>
  refine' (div_le_div_iff₀ (by positivity) (by positivity)).mpr _ <;>
  linarith [show (n : ℝ) > 0 by exact Nat.cast_pos.mpr hn]

/--
For any two natural numbers `i n : ℕ` with `i < n`, we have that
`(2i+1)/(2n)` is contained in unit interval
-/
lemma mid_point_I {i n : ℕ} (hi : i < n) : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := by
  have n_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_le_of_lt (Nat.zero_le i) hi)
  have : 2 * i + 1 ≤ 2 * n := by linarith
  constructor
  · apply div_nonneg
    exact add_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg i)) (by norm_num)
    exact mul_nonneg (by norm_num) (Nat.cast_nonneg n)
  · refine' (div_le_one (mul_pos (by norm_num) n_cast_pos)).mpr _
    have : (↑(2 * i  + 1) : ℝ) ≤ ↑(2 * n) := Nat.cast_le.mpr this
    exact_mod_cast this

namespace UnitIntervalSub

open Set

lemma mem_I_of_mem_interval {t : ℝ} {n i : ℕ} (hi : i < n.succ) (h : t ∈ Icc ((i:ℝ)/↑(n.succ)) (↑(i+1)/↑(n.succ))) :
    t ∈ I := by
  constructor
  exact le_trans (div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg n.succ)) h.1
  exact le_trans h.2 ((div_le_one (show (n.succ : ℝ) > 0 by
    exact Nat.cast_pos.mpr (Nat.succ_pos n))).mpr (Nat.cast_le.mpr (Nat.succ_le_of_lt hi)))

lemma mem_I_of_mem_interval_coed {t : ℝ} {n i : ℕ} (hi : i < n.succ) (h : t ∈ Icc ((i:ℝ)/(↑n+1)) ((↑i+1)/(↑n+1))) :
    t ∈ I := by
  apply mem_I_of_mem_interval hi
  convert h <;> exact Nat.cast_succ _

end UnitIntervalSub

/-! ### Covering lemma for the unit interval -/

theorem lebesgue_number_lemma_unit_interval {ι : Sort u} {c : ι → Set ℝ}
  (hc₁ : ∀ (i : ι), IsOpen (c i)) (hc₂ : I ⊆ ⋃ (i : ι), c i) :
    ∃ (n : ℕ), (n > 0) ∧ ∀ (i : ℕ) (_h : i < n), ∃ (j : ι), Set.Icc ((i : ℝ)/n) ((i+1)/n) ⊆ c j := by
  rcases (lebesgue_number_lemma_of_metric (isCompact_Icc) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩
  rcases Real.instArchimedean.arch 2 δ_pos with ⟨n, hn⟩

  use n
  have n_pos : 0 < n := by
    by_contra
    have : n = 0 := by linarith
    rw [this] at hn
    have : (2 : ℝ) ≤ 0 := hn
    linarith
  have n_cast_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr n_pos

  constructor
  · exact n_pos

  intros i hi
  have mid_point_I : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ I := mid_point_I hi
  have mid_point_Icc : (2 * i + 1 : ℝ)/(2 * n : ℝ) ∈ Set.Icc ((i:ℝ)/(n:ℝ)) ((i+1:ℝ)/(n:ℝ)) := mid_point_Icc n_pos
  rcases (hδ ((2 * i + 1 : ℝ)/(2 * n : ℝ)) mid_point_I) with ⟨j, hj⟩
  use j
  apply subset_trans _ hj
  intros x hx
  show dist x ((2 * i + 1 : ℝ)/(2 * n : ℝ)) < δ

  have : 1/(n : ℝ) < δ := by
    apply (div_lt_iff₀ n_cast_pos).mpr
    have hn' : (2 : ℝ) ≤ (n : ℝ) * δ := by simpa [nsmul_eq_mul] using hn
    calc
      1 < 2 := by norm_num
      _ ≤ δ * (n : ℝ) := by simpa [mul_comm] using hn'

  apply lt_of_le_of_lt _ this
  apply le_trans (Real.dist_le_of_mem_Icc hx mid_point_Icc)
  rw [div_sub_div_same]
  simp

/-! ### Covering lemma for the unit square -/

def UnitSquare : Set (I × I) := Set.univ

lemma compact_unitSquare : IsCompact UnitSquare := isCompact_univ

/--
For any four natural numbers `n m i j : ℕ` such that `i < n + 1` and `j < m + 1`,
we have the rectangle `[i/(n+1), (i+1)/(n+1)] × [j/(m+1), (j+1)/(m+1)]` in the unit square.
-/
def UnitSubrectangle {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ) : Set (I × I) :=  setOf $
  fun (a : I × I) =>
    ((Fraction (Nat.succ_pos n) (le_of_lt hi)) ≤ a.1 ∧ a.1 ≤ (Fraction (Nat.succ_pos n) (Nat.succ_le_of_lt hi))) ∧
    (Fraction (Nat.succ_pos m) (le_of_lt hj)) ≤ a.2 ∧ a.2 ≤ (Fraction (Nat.succ_pos m) (Nat.succ_le_of_lt hj))

namespace UnitSubrectangle

open Set

lemma mem_unitSquare (t : I × I) : t ∈ UnitSubrectangle zero_lt_one zero_lt_one := by
  unfold UnitSubrectangle
  rw [Fraction.eq_zero, Fraction.eq_one]
  exact ⟨⟨t.1.2.1, t.1.2.2⟩, ⟨t.2.2.1, t.2.2.2⟩⟩

lemma mem_unitSubrectangle {t₀ t₁ : ℝ} {n m i j : ℕ} (hi : i < n.succ) (hj : j < m.succ)
  (ht₀ : t₀ ∈ Icc ((i : ℝ)/↑(n.succ)) (↑(i+1)/↑(n.succ))) (ht₁ : t₁ ∈ Icc ((j : ℝ)/↑(m.succ)) (↑(j+1)/↑(m.succ))) :
    ((⟨t₀, UnitIntervalSub.mem_I_of_mem_interval hi ht₀⟩ : I),
      (⟨t₁, UnitIntervalSub.mem_I_of_mem_interval hj ht₁⟩ : I)) ∈ UnitSubrectangle hi hj :=
  ⟨⟨ht₀.1, ht₀.2⟩, ⟨ht₁.1, ht₁.2⟩⟩

end UnitSubrectangle

theorem lebesgue_number_lemma_unit_square {ι : Sort u} {c : ι → Set (I × I)}
  (hc₁ : ∀ (i : ι), IsOpen (c i)) (hc₂ : UnitSquare ⊆ (⋃ (i : ι), c i)) :
    ∃ (n : ℕ), ∀ (i j : ℕ) (hi : i < n.succ) (hj : j < n.succ), ∃ (a : ι), UnitSubrectangle hi hj ⊆ c a := by
  rcases (lebesgue_number_lemma_of_metric (compact_unitSquare) hc₁ hc₂) with ⟨δ, δ_pos, hδ⟩
  rcases Real.instArchimedean.arch 2 δ_pos with ⟨n, hn⟩

  use n
  have n_pos : 0 < n.succ := Nat.succ_pos n
  have n_cast_pos : 0 < (n.succ : ℝ) := Nat.cast_pos.mpr n_pos

  intros i j hi hj
  let mp_h : ℝ := (2 * i + 1 : ℝ)/(2 * n.succ : ℝ)
  let mp_v : ℝ := (2 * j + 1 : ℝ)/(2 * n.succ : ℝ)

  have mid_point_h_Icc : mp_h ∈ Set.Icc ((i:ℝ)/n.succ) ((i+1)/n.succ) := mid_point_Icc n_pos
  have mid_point_h_I : mp_h ∈ I := mid_point_I hi
  have mid_point_v_Icc : mp_v ∈ Set.Icc ((j:ℝ)/(n.succ:ℝ)) ((j+1:ℝ)/(n.succ:ℝ)) := mid_point_Icc n_pos
  have mid_point_v_I : mp_v ∈ I := mid_point_I hj

  rcases hδ (⟨mp_h, mid_point_h_I⟩, ⟨mp_v, mid_point_v_I⟩) (Set.mem_univ _) with ⟨a, ha⟩
  use a
  apply subset_trans _ ha
  intros x hx
  show dist x _ < δ
  have : dist _ _ ≤ dist _ _ + dist _ _ := dist_triangle x (x.1, ⟨mp_v, mid_point_v_I⟩)  (⟨mp_h, mid_point_h_I⟩, ⟨mp_v, mid_point_v_I⟩)
  apply lt_of_le_of_lt this
  have : 1/(n.succ : ℝ) < δ/2 := by
    apply (div_lt_iff₀ n_cast_pos).mpr
    have hn' : (2 : ℝ) ≤ (n : ℝ) * δ := by simpa [nsmul_eq_mul] using hn
    have hsucc : (2 : ℝ) < (n.succ : ℝ) * δ := by
      rw [Nat.cast_succ]
      nlinarith [δ_pos, hn']
    calc
      1 < ((n.succ : ℝ) * δ) / 2 := by nlinarith [hsucc]
      _ = δ / 2 * (n.succ : ℝ) := by ring
  have h₁ : dist x (x.1, ⟨mp_v, mid_point_v_I⟩) < (δ/2) := by
    apply lt_of_le_of_lt _ this
    have : x = (x.1, x.2) := by ext <;> rfl
    rw [this, dist_prod_same_left]
    have hxv : (x.2 : ℝ) ∈ Set.Icc ((j : ℝ) / (n.succ : ℝ))
        (((j : ℝ) + 1) / (n.succ : ℝ)) := by
      simpa only [Fraction.Fraction_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ, Set.mem_Icc] using
        And.intro (Subtype.coe_le_coe.mpr hx.2.1) (Subtype.coe_le_coe.mpr hx.2.2)
    change dist (x.2 : ℝ) mp_v ≤ 1 / (n.succ : ℝ)
    convert Real.dist_le_of_mem_Icc hxv mid_point_v_Icc using 1
    rw [div_sub_div_same]
    congr 1
    ring

  have h₂ : dist (x.1, (⟨mp_v, mid_point_v_I⟩ : I)) ((⟨mp_h, mid_point_h_I⟩ :I), (⟨mp_v, mid_point_v_I⟩ : I)) < (δ/2) := by
    apply lt_of_le_of_lt _ this
    rw [dist_prod_same_right]
    have hxh : (x.1 : ℝ) ∈ Set.Icc ((i : ℝ) / (n.succ : ℝ))
        (((i : ℝ) + 1) / (n.succ : ℝ)) := by
      simpa only [Fraction.Fraction_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ, Set.mem_Icc] using
        And.intro (Subtype.coe_le_coe.mpr hx.1.1) (Subtype.coe_le_coe.mpr hx.1.2)
    change dist (x.1 : ℝ) mp_h ≤ 1 / (n.succ : ℝ)
    convert Real.dist_le_of_mem_Icc hxh mid_point_h_Icc using 1
    rw [div_sub_div_same]
    congr 1
    ring
  linarith

end SystolicGrowth.Vendored.ClassicalVanKampen
