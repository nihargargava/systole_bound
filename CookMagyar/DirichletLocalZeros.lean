module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.DirichletLocalGrowth
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Meromorphic.NormalForm

@[expose] public section

/-!
# Local zeros of the actual Dirichlet L-function

Jensen's inequality uses the proved growth on the radius `3/2` disk and
the actual center lower bound `1/4`. It counts zeros with multiplicity in
the concentric radius `5/4` disk, uniformly in modulus and height. No
zero-free region or zero-counting estimate is supplied as a hypothesis.
-/

open Metric MeromorphicOn Set
open scoped BigOperators

namespace SystolicGrowth.CookMagyarCircle

variable {q : ℕ} [NeZero q]

/-- Nonprincipal Dirichlet L-functions are analytic on every local disk. -/
theorem dirichlet_LFunction_analyticOnNhd_disk
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ R : ℝ) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (closedBall (2 + (τ : ℂ) * Complex.I) R) := by
  intro s _hs
  exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt s

/-- Jensen's local zero count, including multiplicities, with all analytic
inputs proved for the actual L-function. -/
theorem dirichlet_LFunction_local_sum_divisor_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    (∑ᶠ z, divisor (DirichletCharacter.LFunction χ)
      (closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)) z : ℤ) ≤
      Real.log (28 * (q : ℝ) * (|τ| + 2)) / Real.log (6 / 5 : ℝ) := by
  let c : ℂ := 2 + (τ : ℂ) * Complex.I
  let M : ℝ := 7 * (q : ℝ) * (|τ| + 2)
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hM : 1 ≤ M := by dsimp only [M]; nlinarith [abs_nonneg τ]
  have hcenter : (1 / 4 : ℝ) ≤ ‖DirichletCharacter.LFunction χ c‖ :=
    dirichlet_LFunction_center_norm_lower χ τ
  have hcenterpos : 0 < ‖DirichletCharacter.LFunction χ c‖ := by linarith
  have hne : DirichletCharacter.LFunction χ c ≠ 0 :=
    norm_pos_iff.mp hcenterpos
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (closedBall c |(3 / 2 : ℝ)|) := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] using
      dirichlet_LFunction_analyticOnNhd_disk χ hχ τ (3 / 2)
  have hJ := ha.sum_divisor_le
    (r := (5 / 4 : ℝ)) (R := (3 / 2 : ℝ)) (M := M)
    (by norm_num) (by norm_num) hM hne
    (fun z hz => dirichlet_LFunction_norm_le_shifted_disk χ hχ τ
      (sphere_subset_closedBall (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
        using hz)))
  have hratio : M / ‖DirichletCharacter.LFunction χ c‖ ≤
      28 * (q : ℝ) * (|τ| + 2) := by
    apply (div_le_iff₀ hcenterpos).mpr
    have h := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 4 * M by positivity)
    dsimp only [M] at h ⊢
    nlinarith only [h]
  have hlog : Real.log (M / ‖DirichletCharacter.LFunction χ c‖) ≤
      Real.log (28 * (q : ℝ) * (|τ| + 2)) :=
    Real.log_le_log (div_pos (lt_of_lt_of_le zero_lt_one hM) hcenterpos) hratio
  have hden : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have hbound := div_le_div_of_nonneg_right hlog hden.le
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4),
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hJ
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)] at hJ
  exact hJ.trans hbound

/-- The actual center lower bound rules out local identical vanishing at
every point, by the analytic identity theorem on the whole complex plane. -/
theorem dirichlet_LFunction_analyticOrderAt_ne_top
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  intro htop
  have hf : ∀ z, AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    fun z => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s hf).mp htop
  have hcenter := dirichlet_LFunction_center_norm_lower χ 0
  simp only [hzero, Pi.zero_apply, norm_zero] at hcenter
  norm_num at hcenter

/-- The finite set of actual zeros in the local closed disk. Its definition
uses divisor support, while its membership theorem identifies actual zeros. -/
noncomputable def dirichletLocalZeros (χ : DirichletCharacter ℂ q) (τ : ℝ) : Finset ℂ :=
  (divisor (DirichletCharacter.LFunction χ)
    (closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))).finiteSupport
      (isCompact_closedBall _ _) |>.toFinset

/-- Membership in the local finite set is exactly membership in the disk
and vanishing of the actual L-function. -/
theorem mem_dirichletLocalZeros_iff
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) (s : ℂ) :
    s ∈ dirichletLocalZeros χ τ ↔
      s ∈ closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ) ∧
        DirichletCharacter.LFunction χ s = 0 := by
  let U := closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ)
  have hf := dirichlet_LFunction_analyticOnNhd_disk χ hχ τ (5 / 4)
  have hord : ∀ u : U, meromorphicOrderAt (DirichletCharacter.LFunction χ) u ≠ ⊤ := by
    intro u
    rw [(hf u u.2).meromorphicOrderAt_eq]
    exact fun h => dirichlet_LFunction_analyticOrderAt_ne_top χ hχ u
      (ENat.map_eq_top_iff.mp h)
  have hz := hf.meromorphicNFOn.zero_set_eq_divisor_support hord
  change s ∈ ((divisor (DirichletCharacter.LFunction χ) U).finiteSupport
    (isCompact_closedBall _ _)).toFinset ↔ _
  rw [Set.Finite.mem_toFinset]
  change s ∈ Function.support (divisor (DirichletCharacter.LFunction χ)
    (closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))) ↔ _
  rw [← hz]
  rfl

/-- The number of distinct local zeros is at most the Jensen bound for
the actual multiplicity sum. -/
theorem dirichletLocalZeros_card_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (τ : ℝ) :
    ((dirichletLocalZeros χ τ).card : ℝ) ≤
      Real.log (28 * (q : ℝ) * (|τ| + 2)) / Real.log (6 / 5 : ℝ) := by
  let D := divisor (DirichletCharacter.LFunction χ)
    (closedBall (2 + (τ : ℂ) * Complex.I) (5 / 4 : ℝ))
  have hf := dirichlet_LFunction_analyticOnNhd_disk χ hχ τ (5 / 4)
  have hsum : ((dirichletLocalZeros χ τ).card : ℤ) ≤
      ∑ s ∈ dirichletLocalZeros χ τ, D s := by
    calc
      _ = ∑ s ∈ dirichletLocalZeros χ τ, (1 : ℤ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        have hne : D s ≠ 0 := by
          simpa only [dirichletLocalZeros, Set.Finite.mem_toFinset,
            Function.mem_support] using hs
        have hnonneg : 0 ≤ D s := hf.divisor_nonneg s
        omega
  have hfiniteSum : (∑ᶠ s, D s) = ∑ s ∈ dirichletLocalZeros χ τ, D s :=
    finsum_eq_sum_of_support_subset _ (by
      intro s hs
      change s ∈ dirichletLocalZeros χ τ
      simpa only [dirichletLocalZeros, Set.Finite.mem_toFinset] using hs)
  have hcast : ((dirichletLocalZeros χ τ).card : ℝ) ≤ (∑ᶠ s, D s : ℤ) := by
    rw [hfiniteSum]
    exact_mod_cast hsum
  exact hcast.trans (dirichlet_LFunction_local_sum_divisor_le χ hχ τ)

#print axioms dirichlet_LFunction_local_sum_divisor_le
#print axioms dirichlet_LFunction_analyticOrderAt_ne_top
#print axioms mem_dirichletLocalZeros_iff
#print axioms dirichletLocalZeros_card_le

end SystolicGrowth.CookMagyarCircle
