module

/-
Copyright (c) 2026 Gershon Bialer.
Released under Apache 2.0 license.

Adapted from `AnalyticNT.Vaughan.Identity` in
https://github.com/gersh/ternary-goldbach-lean.  The arithmetic-function
identity is due to that development; its application to the cubic phase
`x^3-x` is specific to this project.
-/
public import CookMagyar.CircleMethod
public import CookMagyar.HuaDivisorBound
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta

@[expose] public section

open scoped ArithmeticFunction BigOperators

namespace SystolicGrowth
namespace CookMagyarVaughan

/-! # Vaughan's identity for the cubic prime sum -/

/-- The small direct piece `Λ(n) 1[n≤V]`. -/
noncomputable def vaughanLow (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ≤ V then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- The low Mangoldt truncation is nonnegative. -/
theorem vaughanLow_nonneg (V n : ℕ) : 0 ≤ vaughanLow V n := by
  change 0 ≤ (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0)
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · norm_num

/-- The low Mangoldt truncation is bounded by `log n`. -/
theorem vaughanLow_le_log (V n : ℕ) :
    vaughanLow V n ≤ Real.log (n : ℝ) := by
  change (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) ≤
    Real.log (n : ℝ)
  split_ifs with hn
  · exact ArithmeticFunction.vonMangoldt_le_log
  · have hnpos : 1 ≤ n := by omega
    exact Real.log_nonneg (by exact_mod_cast hnpos)

/-- Above its truncation, the low Mangoldt coefficient vanishes. -/
theorem vaughanLow_eq_zero_of_gt (V n : ℕ) (hn : V < n) :
    vaughanLow V n = 0 := by
  simp [vaughanLow, not_le_of_gt hn]

/-- Möbius coefficients truncated at `U`. -/
noncomputable def muTruncated (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- Complementary Möbius tail. -/
noncomputable def muHigh (U : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if U < n then (ArithmeticFunction.moebius n : ℝ) else 0, by simp⟩

/-- Complementary von--Mangoldt tail. -/
noncomputable def lambdaHigh (V : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if V < n then ArithmeticFunction.vonMangoldt n else 0, by simp⟩

/-- First Type-I piece. -/
noncomputable def vaughanS1 (U : ℕ) : ArithmeticFunction ℝ :=
  muTruncated U * ArithmeticFunction.log

/-- Second Type-I piece. -/
noncomputable def vaughanS2 (U V : ℕ) : ArithmeticFunction ℝ :=
  muTruncated U *
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaHigh V))

/-- Type-II bilinear tail. -/
noncomputable def vaughanS3 (U V : ℕ) : ArithmeticFunction ℝ :=
  lambdaHigh V *
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))

/-- The small Mangoldt piece is the part of `Lambda` below the cutoff. -/
theorem vaughanLow_eq_lambda_sub_high (V : ℕ) :
    vaughanLow V = (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
      lambdaHigh V := by
  ext n
  change (if n ≤ V then ArithmeticFunction.vonMangoldt n else 0) =
    ArithmeticFunction.vonMangoldt n -
      (if V < n then ArithmeticFunction.vonMangoldt n else 0)
  by_cases hn : n ≤ V
  · have hnot : ¬V < n := not_lt.mpr hn
    simp [hn, hnot]
  · have hlt : V < n := lt_of_not_ge hn
    simp [hn, hlt]

/-- Truncated Möbius coefficients are bounded by one. -/
theorem abs_muTruncated_le_one (U n : ℕ) : |muTruncated U n| ≤ 1 := by
  change |(if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0)| ≤ 1
  split_ifs with hn
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · norm_num

/-- The product of a truncated Möbius coefficient with a low Mangoldt
coefficient has norm at most the logarithm of the latter variable. -/
theorem norm_muTruncated_mul_vaughanLow_le_log (U V d r : ℕ) :
    ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ ≤
      Real.log (r : ℝ) := by
  have hmu : ‖(muTruncated U d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_muTruncated_le_one U d
  have hlowNonneg := vaughanLow_nonneg V r
  have hlow : ‖(vaughanLow V r : ℂ)‖ ≤ Real.log (r : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlowNonneg]
    exact vaughanLow_le_log V r
  calc
    ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ =
        ‖(muTruncated U d : ℂ)‖ * ‖(vaughanLow V r : ℂ)‖ := norm_mul _ _
    _ ≤ 1 * Real.log (r : ℝ) :=
      mul_le_mul hmu hlow (norm_nonneg _) (by norm_num)
    _ = Real.log (r : ℝ) := one_mul _

/-- The truncated Möbius coefficient is supported exactly on squarefree
integers at or below its cutoff. -/
theorem muTruncated_ne_zero_iff (U n : ℕ) :
    muTruncated U n ≠ 0 ↔ n ≤ U ∧ Squarefree n := by
  change (if n ≤ U then (ArithmeticFunction.moebius n : ℝ) else 0) ≠ 0 ↔
    n ≤ U ∧ Squarefree n
  by_cases hn : n ≤ U
  · simp [hn, ArithmeticFunction.moebius_ne_zero_iff_squarefree]
  · simp [hn]

/-- The first Type-I coefficient `mu(d) log(m)` is bounded by `log(m)`. -/
theorem abs_vaughanS1Coefficient_le (U d m : ℕ) :
    |muTruncated U d * ArithmeticFunction.log m| ≤ Real.log (m : ℝ) := by
  rw [abs_mul, ArithmeticFunction.log_apply]
  have hlog : 0 ≤ Real.log (m : ℝ) := by
    by_cases hm : m = 0
    · simp [hm]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm))
  rw [abs_of_nonneg hlog]
  calc
    |muTruncated U d| * Real.log (m : ℝ) ≤
        1 * Real.log (m : ℝ) :=
      mul_le_mul_of_nonneg_right (abs_muTruncated_le_one U d) hlog
    _ = Real.log (m : ℝ) := one_mul _

/-- The low Mangoldt divisor sum is bounded by the full Mangoldt sum `log n`.
This is the pointwise envelope for the second Type-I coefficient. -/
theorem zeta_mul_vaughanLow_nonneg_le_log (V n : ℕ) :
    0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) n ∧
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) n ≤
        Real.log (n : ℝ) := by
  have hlow_nonneg (d : ℕ) : 0 ≤ vaughanLow V d := by
    change 0 ≤ (if d ≤ V then ArithmeticFunction.vonMangoldt d else 0)
    split_ifs
    · exact ArithmeticFunction.vonMangoldt_nonneg
    · norm_num
  have hlow_le (d : ℕ) :
      vaughanLow V d ≤ ArithmeticFunction.vonMangoldt d := by
    change (if d ≤ V then ArithmeticFunction.vonMangoldt d else 0) ≤
      ArithmeticFunction.vonMangoldt d
    split_ifs
    · exact le_rfl
    · exact ArithmeticFunction.vonMangoldt_nonneg
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  constructor
  · exact Finset.sum_nonneg fun d hd => hlow_nonneg d
  · calc
      (∑ d ∈ n.divisors, vaughanLow V d) ≤
          ∑ d ∈ n.divisors, ArithmeticFunction.vonMangoldt d := by
        apply Finset.sum_le_sum
        intro d hd
        exact hlow_le d
      _ = Real.log (n : ℝ) := ArithmeticFunction.vonMangoldt_sum

/-- The second Type-I coefficient's zeta convolution is exactly the sum of
its low Mangoldt factor over the positive-product divisor antidiagonal. This
form is convenient for expanding S₂ into progression blocks. -/
theorem zeta_mul_vaughanLow_eq_divisorsAntidiagonal_sum (V n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) n =
      ∑ ab ∈ n.divisorsAntidiagonal, vaughanLow V ab.1 := by
  rw [ArithmeticFunction.coe_zeta_mul_comm, ArithmeticFunction.mul_apply]
  by_cases hn : n = 0
  · subst n
    simp
  · apply Finset.sum_congr rfl
    intro ab hab
    have hab' := Nat.mem_divisorsAntidiagonal.mp hab
    have hright : ab.2 ≠ 0 := by
      intro hzero
      simp [hzero] at hab'
      exact hn hab'.1.symm
    simp [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hright]

/-- Pointwise Type-I coefficient envelope for the second Vaughan piece:
its truncated Möbius factor has modulus at most one, while the remaining
divisor sum is at most `log m`. -/
theorem abs_vaughanS2Coefficient_le (U V d m : ℕ) :
    |muTruncated U d *
      (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          lambdaHigh V)) m)| ≤ Real.log (m : ℝ) := by
  have hinner :
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
          lambdaHigh V)) m =
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) m := by
    rw [← vaughanLow_eq_lambda_sub_high V]
  have hbound := zeta_mul_vaughanLow_nonneg_le_log V m
  rw [abs_mul]
  calc
    |muTruncated U d| *
        |((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
            lambdaHigh V)) m| =
        |muTruncated U d| *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) m := by
      rw [hinner, abs_of_nonneg hbound.1]
    _ ≤ 1 * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) m :=
      mul_le_mul_of_nonneg_right (abs_muTruncated_le_one U d) hbound.1
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) m := one_mul _
    _ ≤ Real.log (m : ℝ) := hbound.2

/-- The truncated Möbius tail remains pointwise bounded by one. This is the
coefficient bound used when the Type-II convolution is opened. -/
theorem abs_muHigh_le_one (U n : ℕ) : |muHigh U n| ≤ 1 := by
  change |(if U < n then (ArithmeticFunction.moebius n : ℝ) else 0)| ≤ 1
  split_ifs with hn
  · exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  · norm_num

/-- The complementary Möbius coefficient is supported exactly on
squarefree integers above its cutoff. -/
theorem muHigh_ne_zero_iff (U n : ℕ) :
    muHigh U n ≠ 0 ↔ U < n ∧ Squarefree n := by
  change (if U < n then (ArithmeticFunction.moebius n : ℝ) else 0) ≠ 0 ↔
    U < n ∧ Squarefree n
  by_cases hn : U < n
  · simp [hn, ArithmeticFunction.moebius_ne_zero_iff_squarefree]
  · simp [hn]

/-- The complementary Möbius coefficient vanishes at or below its cutoff. -/
theorem muHigh_eq_zero_of_le (U n : ℕ) (hnU : n ≤ U) :
    muHigh U n = 0 := by
  simp [muHigh, not_lt.mpr hnU]

/-- The Möbius-tail/zeta convolution is bounded by the divisor count. This
isolates the standard divisor-function envelope for the Type-II coefficient
in Vaughan's identity. -/
theorem abs_muHigh_mul_zeta_le_divisorCount (U n : ℕ) :
    |(muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n| ≤
      (n.divisors.card : ℝ) := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  calc
    |∑ d ∈ n.divisors, muHigh U d| ≤
        ∑ d ∈ n.divisors, |muHigh U d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact abs_muHigh_le_one U d
    _ = (n.divisors.card : ℝ) := by simp

/-- The Möbius-tail/zeta convolution vanishes below the Möbius cutoff: every
positive divisor of `n ≤ U` is itself at most `U`. -/
theorem muHigh_mul_zeta_eq_zero_of_le (U n : ℕ) (hn0 : 0 < n)
    (hnU : n ≤ U) :
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdiv := Nat.mem_divisors.mp hd
  have hdn : d ≤ n := Nat.le_of_dvd hn0 hdiv.1
  have hdU : d ≤ U := le_trans hdn hnU
  simp [muHigh, not_lt.mpr hdU]

/-- The truncated von--Mangoldt tail is nonnegative and bounded by `log n`.
The logarithm is nonnegative at every natural-number argument. -/
theorem lambdaHigh_nonneg (V n : ℕ) : 0 ≤ lambdaHigh V n := by
  change 0 ≤ (if V < n then ArithmeticFunction.vonMangoldt n else 0)
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · norm_num

theorem lambdaHigh_le_log (V n : ℕ) :
    lambdaHigh V n ≤ Real.log (n : ℝ) := by
  change (if V < n then ArithmeticFunction.vonMangoldt n else 0) ≤
    Real.log (n : ℝ)
  split_ifs with hn
  · exact ArithmeticFunction.vonMangoldt_le_log
  · by_cases hn0 : n = 0
    · simp [hn0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
      exact Real.log_nonneg hn1

/-- The von--Mangoldt tail is supported exactly on prime powers above the
cutoff. -/
theorem lambdaHigh_ne_zero_iff (V n : ℕ) :
    lambdaHigh V n ≠ 0 ↔ V < n ∧ IsPrimePow n := by
  change (if V < n then ArithmeticFunction.vonMangoldt n else 0) ≠ 0 ↔
    V < n ∧ IsPrimePow n
  by_cases hn : V < n
  · simp [hn, ArithmeticFunction.vonMangoldt_ne_zero_iff]
  · simp [hn]

/-- Coefficientwise Type-II envelope: a Vaughan `Lambda` tail times the
Möbius/zeta convolution is bounded by `log(d)` times the divisor count of
the second variable. -/
theorem abs_vaughanS3Coefficient_le (U V d m : ℕ) :
    |lambdaHigh V d *
        ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)| ≤
      Real.log (d : ℝ) * (m.divisors.card : ℝ) := by
  rw [abs_mul]
  have hlog : 0 ≤ Real.log (d : ℝ) := by
    by_cases hd : d = 0
    · simp [hd]
    · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd))
  calc
    |lambdaHigh V d| *
        |(muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m| ≤
        Real.log (d : ℝ) *
          |(muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m| :=
      mul_le_mul_of_nonneg_right
        (by rw [abs_of_nonneg (lambdaHigh_nonneg V d)]; exact lambdaHigh_le_log V d)
        (abs_nonneg _)
    _ ≤ Real.log (d : ℝ) * (m.divisors.card : ℝ) :=
      mul_le_mul_of_nonneg_left (abs_muHigh_mul_zeta_le_divisorCount U m) hlog

/-- Absolute coefficient mass for a Type-II divisor block, using a threshold
to separate small divisor counts from the divisor-rich tail. This is only
coefficient bookkeeping; oscillatory cancellation is a separate estimate. -/
theorem sum_abs_vaughanS3Coefficient_le_of_divisorThreshold
    (U V M : ℕ) (D : Finset ℕ) (T : ℝ) (hT : 0 < T) :
    (∑ d ∈ D, ∑ m ∈ Finset.Icc 1 M,
      |lambdaHigh V d *
        ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)|) ≤
      (∑ d ∈ D, Real.log (d : ℝ)) *
        (T * M + ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2) := by
  have hdivisorMass :=
    SystolicGrowth.CookMagyarCircle.sum_divisorCount_le_threshold_split
      (M := M) T hT
  have hlogM : 0 ≤ Real.log (M : ℝ) := by
    by_cases hM : M = 0
    · simp [hM]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM)
  let E : ℝ := T * M + ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hfixed : ∀ d : ℕ,
      (∑ m ∈ Finset.Icc 1 M,
        |lambdaHigh V d *
          ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)|) ≤
        Real.log (d : ℝ) * E := by
    intro d
    have hlogd : 0 ≤ Real.log (d : ℝ) := by
      by_cases hd : d = 0
      · simp [hd]
      · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd)
    calc
      (∑ m ∈ Finset.Icc 1 M,
          |lambdaHigh V d *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)|) ≤
          ∑ m ∈ Finset.Icc 1 M,
            Real.log (d : ℝ) * (m.divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        exact abs_vaughanS3Coefficient_le U V d m
      _ = Real.log (d : ℝ) *
            (∑ m ∈ Finset.Icc 1 M, (m.divisors.card : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ Real.log (d : ℝ) * E := by
        dsimp [E]
        exact mul_le_mul_of_nonneg_left hdivisorMass hlogd
  calc
    (∑ d ∈ D, ∑ m ∈ Finset.Icc 1 M,
        |lambdaHigh V d *
          ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m)|) ≤
        ∑ d ∈ D, Real.log (d : ℝ) * E := by
          apply Finset.sum_le_sum
          intro d hd
          exact hfixed d
    _ = (∑ d ∈ D, Real.log (d : ℝ)) * E := by
      rw [Finset.sum_mul]
    _ = (∑ d ∈ D, Real.log (d : ℝ)) *
          (T * M + ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ 7) / T ^ 2) := by
      rfl

/-- Vaughan's identity at the arithmetic-function level. -/
theorem vaughan_identity (U V n : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n =
      vaughanLow V n + vaughanS1 U n - vaughanS2 U V n + vaughanS3 U V n := by
  have hmu_split :
      muTruncated U + muHigh U =
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    ext k
    change
      (if k ≤ U then (ArithmeticFunction.moebius k : ℝ) else 0) +
        (if U < k then (ArithmeticFunction.moebius k : ℝ) else 0) =
          (ArithmeticFunction.moebius k : ℝ)
    by_cases hk : k ≤ U
    · have hnot : ¬U < k := not_lt.mpr hk
      simp [hk, hnot]
    · have hlt : U < k := lt_of_not_ge hk
      simp [hk, hlt]
  have hlambda_split :
      vaughanLow V + lambdaHigh V =
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
    ext k
    change
      (if k ≤ V then ArithmeticFunction.vonMangoldt k else 0) +
        (if V < k then ArithmeticFunction.vonMangoldt k else 0) =
          ArithmeticFunction.vonMangoldt k
    by_cases hk : k ≤ V
    · have hnot : ¬V < k := not_lt.mpr hk
      simp [hk, hnot]
    · have hlt : V < k := lt_of_not_ge hk
      simp [hk, hlt]
  suffices hfun :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        vaughanLow V + vaughanS1 U - vaughanS2 U V + vaughanS3 U V by
    have h := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) hfun
    simpa only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
      sub_eq_add_neg] using h
  have hS2 :
      vaughanS2 U V =
        muTruncated U *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) := by
    unfold vaughanS2
    have hsub :
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaHigh V =
          vaughanLow V := by
      have h := hlambda_split
      have :
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaHigh V =
            (vaughanLow V + lambdaHigh V) - lambdaHigh V := by rw [h]
      simpa using this
    rw [hsub]
  have hhigh :
      lambdaHigh V = vaughanS1 U - vaughanS2 U V + vaughanS3 U V := by
    have hmuzeta :
        (muTruncated U + muHigh U) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
          (1 : ArithmeticFunction ℝ) := by
      rw [hmu_split, ArithmeticFunction.coe_moebius_mul_coe_zeta]
    have hexpand :
        lambdaHigh V = lambdaHigh V *
          ((muTruncated U + muHigh U) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
      rw [hmuzeta, mul_one]
    have hdist :
        lambdaHigh V *
            ((muTruncated U + muHigh U) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
          muTruncated U *
              ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V) +
            vaughanS3 U V := by
      unfold vaughanS3
      ring
    have hhigh_eq :
        lambdaHigh V =
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - vaughanLow V := by
      have h := hlambda_split
      have : lambdaHigh V =
          (vaughanLow V + lambdaHigh V) - vaughanLow V := by abel
      rw [this, h]
    have hfirst :
        muTruncated U *
            ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V) =
          vaughanS1 U - vaughanS2 U V := by
      rw [hhigh_eq, hS2]
      unfold vaughanS1
      have hlog :
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - vaughanLow V) =
            ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V := by
        rw [mul_sub, ArithmeticFunction.zeta_mul_vonMangoldt]
      rw [hlog, mul_sub]
    rw [hexpand, hdist, hfirst]
  have hsplit :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        vaughanLow V + lambdaHigh V := hlambda_split.symm
  rw [hsplit, hhigh]
  abel

/-- Cubic exponential sum attached to a real arithmetic function. -/
noncomputable def cubicArithmeticExpSum
    (F : ArithmeticFunction ℝ) (alpha : ℝ) (N : ℕ) : ℂ :=
  ∑ x : Fin (N + 1),
    (F x : ℂ) * CookMagyarCircle.addChar alpha (primeCubic x)

/-- The generic sum specializes to the cubic von--Mangoldt sum. -/
theorem cubicArithmeticExpSum_vonMangoldt (alpha : ℝ) (N : ℕ) :
    cubicArithmeticExpSum ArithmeticFunction.vonMangoldt alpha N =
      CookMagyarCircle.cubicVonMangoldtExpSum alpha N := by
  rfl

/-- Vaughan's identity applied term-by-term to the cubic phase. -/
theorem cubic_vaughan_exp_sum (U V N : ℕ) (alpha : ℝ) :
    CookMagyarCircle.cubicVonMangoldtExpSum alpha N =
      cubicArithmeticExpSum (vaughanLow V) alpha N +
        cubicArithmeticExpSum (vaughanS1 U) alpha N -
        cubicArithmeticExpSum (vaughanS2 U V) alpha N +
        cubicArithmeticExpSum (vaughanS3 U V) alpha N := by
  unfold CookMagyarCircle.cubicVonMangoldtExpSum cubicArithmeticExpSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  have hid := vaughan_identity U V (x : ℕ)
  have hcast :
      (ArithmeticFunction.vonMangoldt x : ℂ) =
        (vaughanLow V x : ℂ) + (vaughanS1 U x : ℂ) -
          (vaughanS2 U V x : ℂ) + (vaughanS3 U V x : ℂ) := by
    exact_mod_cast hid
  rw [hcast]
  ring

/-- Exact divisor-antidiagonal expansion of the first Type-I term.  The
outer Möbius factor is supported on divisors at most `U`. -/
theorem cubic_vaughan_typeI_first_bilinear (U N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS1 U) alpha N =
      ∑ x : Fin (N + 1),
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
          (muTruncated U ab.1 : ℂ) *
            (ArithmeticFunction.log ab.2 : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic x) := by
  unfold cubicArithmeticExpSum vaughanS1
  apply Finset.sum_congr rfl
  intro x _hx
  rw [show
      (((muTruncated U * ArithmeticFunction.log) x : ℝ) : ℂ) =
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
          (muTruncated U ab.1 : ℂ) *
            (ArithmeticFunction.log ab.2 : ℂ) by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rfl]
  rw [Finset.sum_mul]

/-- Reindex a divisor-antidiagonal sum on positive integers as the
corresponding outer-divisor / inner-quotient sum. This is the finite-domain
change of variables needed to apply the progression estimate to Vaughan's
first Type-I bilinear form. -/
theorem sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum
    (N : ℕ) (F : ℕ → ℕ → ℕ → ℂ) :
    (∑ x ∈ Finset.Icc 0 N,
      ∑ ab ∈ x.divisorsAntidiagonal, F x ab.1 ab.2) =
    ∑ d ∈ Finset.Icc 1 N,
      ∑ m ∈ Finset.Icc 1 (N / d), F (d * m) d m := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
    (fun x _ => ⟨x.2.1, x.2.2⟩)
    (fun y _ => ⟨y.1 * y.2, (y.1, y.2)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    have hx' := Finset.mem_sigma.mp hx
    have hab := Nat.mem_divisorsAntidiagonal.mp hx'.2
    have houter := Finset.mem_Icc.mp hx'.1
    have hdpos : 0 < x.2.1 := by
      by_contra h
      have hdzero : x.2.1 = 0 := by omega
      simp [hdzero] at hab
      omega
    have hmpos : 0 < x.2.2 := by
      by_contra h
      have hmzero : x.2.2 = 0 := by omega
      simp [hmzero] at hab
      omega
    have hdmle : x.2.1 * x.2.2 ≤ N := by
      rw [hab.1]
      exact houter.2
    have hdle : x.2.1 ≤ N := by
      calc
        x.2.1 ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_right _ hmpos
        _ ≤ N := hdmle
    have hmle : x.2.2 ≤ N / x.2.1 :=
      (Nat.le_div_iff_mul_le hdpos).mpr (by simpa [Nat.mul_comm] using hdmle)
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle⟩,
        Finset.mem_Icc.mpr ⟨hmpos, hmle⟩⟩
  · intro y hy
    have hy' := Finset.mem_sigma.mp hy
    have hd := Finset.mem_Icc.mp hy'.1
    have hm := Finset.mem_Icc.mp hy'.2
    have hprod : y.1 * y.2 ≤ N := by
      have h := (Nat.le_div_iff_mul_le hd.1).mp hm.2
      simpa [Nat.mul_comm] using h
    have hprodpos : 0 < y.1 * y.2 := Nat.mul_pos hd.1 hm.1
    have hanti : (y.1, y.2) ∈ (y.1 * y.2).divisorsAntidiagonal := by
      apply Nat.mem_divisorsAntidiagonal.mpr
      exact ⟨rfl, Nat.ne_of_gt hprodpos⟩
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hprod⟩, hanti⟩
  · intro x hx
    have hx' := Finset.mem_sigma.mp hx
    have hab := Nat.mem_divisorsAntidiagonal.mp hx'.2
    apply Sigma.ext
    · exact hab.1
    · rfl
  · intro y hy
    apply Sigma.ext
    · rfl
    · rfl
  · intro x hx
    have hx' := Finset.mem_sigma.mp hx
    have hab := Nat.mem_divisorsAntidiagonal.mp hx'.2
    change F x.1 x.2.1 x.2.2 = F (x.2.1 * x.2.2) x.2.1 x.2.2
    rw [hab.1]

/-- Reindex a zeta--low-Mangoldt coefficient sum into two positive product
coordinates. This is the finite-sum bridge from Vaughan's second Type-I
coefficient to progressions with step equal to the product of the two small
divisor variables. -/
theorem sum_zeta_vaughanLow_mul_eq_divisor_quotient_sum
    (V M : ℕ) (c : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M,
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          vaughanLow V) m : ℝ) : ℂ) * c m) =
      ∑ r ∈ Finset.Icc 1 M,
        ∑ j ∈ Finset.Icc 1 (M / r),
          (vaughanLow V r : ℂ) * c (r * j) := by
  classical
  let F : ℕ → ℕ → ℕ → ℂ := fun x r j =>
    (vaughanLow V r : ℂ) * c x
  have hcoef (m : ℕ) :
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          vaughanLow V) m : ℝ) : ℂ) * c m =
        ∑ ab ∈ m.divisorsAntidiagonal,
          (vaughanLow V ab.1 : ℂ) * c m := by
    rw [zeta_mul_vaughanLow_eq_divisorsAntidiagonal_sum]
    rw [Complex.ofReal_sum]
    rw [Finset.sum_mul]
  have hzero :
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          vaughanLow V) 0 : ℝ) : ℂ) * c 0 = 0 := by
    simp
  have hinterval :
      Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hpositive :
      (∑ m ∈ Finset.Icc 0 M,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            vaughanLow V) m : ℝ) : ℂ) * c m) =
      (∑ m ∈ Finset.Icc 1 M,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            vaughanLow V) m : ℝ) : ℂ) * c m) := by
    rw [hinterval, Finset.sum_insert (by simp : 0 ∉ Finset.Icc 1 M), hzero,
      zero_add]
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            vaughanLow V) m : ℝ) : ℂ) * c m) =
      ∑ m ∈ Finset.Icc 0 M,
        ∑ ab ∈ m.divisorsAntidiagonal,
          (vaughanLow V ab.1 : ℂ) * c m := by
            rw [← hpositive]
            apply Finset.sum_congr rfl
            intro m hm
            exact hcoef m
    _ = ∑ r ∈ Finset.Icc 1 M,
          ∑ j ∈ Finset.Icc 1 (M / r),
            (vaughanLow V r : ℂ) * c (r * j) := by
      simpa [F] using
        sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum M F

/-- Expand the complementary Möbius/zeta convolution along its positive
divisor/quotient coordinates. This exposes the actual Möbius coefficient
and the remaining free quotient. -/
theorem sum_muHigh_mul_zeta_mul_eq_divisor_quotient_sum
    (U M : ℕ) (c : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M,
      (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
        c m) =
      ∑ r ∈ Finset.Icc 1 M,
        ∑ j ∈ Finset.Icc 1 (M / r),
          (muHigh U r : ℂ) * c (r * j) := by
  classical
  let F : ℕ → ℕ → ℕ → ℂ := fun x r j => (muHigh U r : ℂ) * c x
  have hcoef (m : ℕ) :
      (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
        c m =
      ∑ ab ∈ m.divisorsAntidiagonal, (muHigh U ab.1 : ℂ) * c m := by
    rw [ArithmeticFunction.mul_apply]
    rw [Complex.ofReal_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' := Nat.mem_divisorsAntidiagonal.mp hab
    have hright : ab.2 ≠ 0 := by
      intro hzero
      simp [hzero] at hab'
      omega
    simp [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hright]
  have hzero :
      (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) 0 : ℝ) : ℂ) *
        c 0 = 0 := by
    simp
  have hinterval :
      Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hpositive :
      (∑ m ∈ Finset.Icc 0 M,
        (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
          c m) =
      ∑ m ∈ Finset.Icc 1 M,
        (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
          c m := by
    rw [hinterval, Finset.sum_insert (by simp : 0 ∉ Finset.Icc 1 M), hzero,
      zero_add]
  calc
    (∑ m ∈ Finset.Icc 1 M,
        (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
          c m) =
      ∑ m ∈ Finset.Icc 0 M,
        ∑ ab ∈ m.divisorsAntidiagonal, (muHigh U ab.1 : ℂ) * c m := by
          rw [← hpositive]
          apply Finset.sum_congr rfl
          intro m hm
          exact hcoef m
    _ = ∑ r ∈ Finset.Icc 1 M,
          ∑ j ∈ Finset.Icc 1 (M / r),
            (muHigh U r : ℂ) * c (r * j) := by
      simpa [F] using
        sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum M F

/-- Vaughan's first Type-I bilinear sum in outer-divisor / inner-quotient
coordinates. Each inner sequence is an affine progression with step `d` and
logarithmic weight `log m`. -/
theorem cubic_vaughan_typeI_first_divisor_quotient (U N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS1 U) alpha N =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) * (ArithmeticFunction.log m : ℂ) *
            CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
  classical
  let F : ℕ → ℕ → ℕ → ℂ := fun x d m =>
    (muTruncated U d : ℂ) * (ArithmeticFunction.log m : ℂ) *
      CookMagyarCircle.addChar alpha (primeCubic x)
  have hindex :
      (∑ x : Fin (N + 1),
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal, F x ab.1 ab.2) =
      ∑ x ∈ Finset.Icc 0 N,
        ∑ ab ∈ x.divisorsAntidiagonal, F x ab.1 ab.2 := by
    refine Finset.sum_bij (fun x _ => (x : ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    · intro x hx y hy hxy
      exact Fin.ext hxy
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      refine ⟨⟨n, by omega⟩, Finset.mem_univ _, rfl⟩
    · intro x hx
      rfl
  calc
    cubicArithmeticExpSum (vaughanS1 U) alpha N =
        ∑ x : Fin (N + 1),
          ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
            (muTruncated U ab.1 : ℂ) *
              (ArithmeticFunction.log ab.2 : ℂ) *
                CookMagyarCircle.addChar alpha (primeCubic x) :=
      cubic_vaughan_typeI_first_bilinear U N alpha
    _ = ∑ x ∈ Finset.Icc 0 N,
          ∑ ab ∈ x.divisorsAntidiagonal,
            (muTruncated U ab.1 : ℂ) *
              (ArithmeticFunction.log ab.2 : ℂ) *
                CookMagyarCircle.addChar alpha (primeCubic x) := by
      simpa [F] using hindex
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Icc 1 (N / d),
            (muTruncated U d : ℂ) * (ArithmeticFunction.log m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
      simpa [F] using
        sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum N F

/-- The positive quotient range in Vaughan's first Type-I sum is exactly the
zero-based progression range used by the logarithmically weighted minor-arc
estimate, after writing `m = k + 1`. -/
theorem sum_log_primeCubic_divisor_quotient_eq_progression
    (N d : ℕ) (alpha : ℝ) (hd : 0 < d) (hdN : d ≤ N) :
    (∑ m ∈ Finset.Icc 1 (N / d),
      (ArithmeticFunction.log m : ℂ) *
        CookMagyarCircle.addChar alpha (primeCubic (d * m))) =
      ∑ k ∈ Finset.Icc 0 ((N - d) / d),
        (Real.log ((k : ℝ) + 1) : ℂ) *
          CookMagyarCircle.addChar alpha (primeCubic (d + d * k)) := by
  classical
  have hquot : (N - d) / d = N / d - 1 := by
    simpa [one_mul] using Nat.sub_mul_div_of_le N d 1 (by omega)
  have hq : 1 ≤ N / d :=
    (Nat.le_div_iff_mul_le hd).2 (by simpa using hdN)
  rw [hquot]
  refine Finset.sum_bij (fun m _ => m - 1) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  · intro m hm n hn hmn
    simp only [Finset.mem_Icc] at hm hn
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    have hmshift : m = (m - 1) + 1 := by omega
    have hphase : d * m = d + d * (m - 1) := by
      calc
        d * m = d * ((m - 1) + 1) := congrArg (fun t : ℕ => d * t) hmshift
        _ = d * (m - 1) + d := by rw [Nat.mul_add]; simp
        _ = d + d * (m - 1) := Nat.add_comm _ _
    have hlog :
        (ArithmeticFunction.log m : ℂ) =
          (Real.log (((m - 1 : ℕ) : ℝ) + 1) : ℂ) := by
      have hcast : (m : ℝ) = ((m - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hmshift
      rw [ArithmeticFunction.log_apply, hcast]
    rw [hlog, hphase]

/-- Triangle-inequality reduction of Vaughan's first Type-I sum to the
individual logarithmically weighted progression blocks. -/
theorem norm_cubic_vaughan_typeI_first_le_weighted_block_sum
    (U N : ℕ) (alpha : ℝ) :
    ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        ‖(muTruncated U d : ℂ)‖ *
          ‖∑ m ∈ Finset.Icc 1 (N / d),
              (ArithmeticFunction.log m : ℂ) *
                CookMagyarCircle.addChar alpha (primeCubic (d * m))‖ := by
  classical
  rw [cubic_vaughan_typeI_first_divisor_quotient]
  let block : ℕ → ℂ := fun d =>
    ∑ m ∈ Finset.Icc 1 (N / d),
      (ArithmeticFunction.log m : ℂ) *
        CookMagyarCircle.addChar alpha (primeCubic (d * m))
  have hinner (d : ℕ) :
      (∑ m ∈ Finset.Icc 1 (N / d),
        (muTruncated U d : ℂ) * (ArithmeticFunction.log m : ℂ) *
          CookMagyarCircle.addChar alpha (primeCubic (d * m))) =
        (muTruncated U d : ℂ) * block d := by
    calc
      (∑ m ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) * (ArithmeticFunction.log m : ℂ) *
            CookMagyarCircle.addChar alpha (primeCubic (d * m))) =
        ∑ m ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) *
            ((ArithmeticFunction.log m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m))) := by
                apply Finset.sum_congr rfl
                intro m hm
                ring
      _ = (muTruncated U d : ℂ) * block d := by
        rw [Finset.mul_sum]
  have hfactor :
      (∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) * (ArithmeticFunction.log m : ℂ) *
            CookMagyarCircle.addChar alpha (primeCubic (d * m))) =
      ∑ d ∈ Finset.Icc 1 N, (muTruncated U d : ℂ) * block d := by
    apply Finset.sum_congr rfl
    intro d hd
    exact hinner d
  rw [hfactor]
  calc
    ‖∑ d ∈ Finset.Icc 1 N, (muTruncated U d : ℂ) * block d‖ ≤
        ∑ d ∈ Finset.Icc 1 N,
          ‖(muTruncated U d : ℂ) * block d‖ := norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 N,
          ‖(muTruncated U d : ℂ)‖ * ‖block d‖ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [norm_mul]
    _ = _ := by simp [block]

/-- The first Type-I block sum is supported only on outer divisors at most
`U`; on that support the Möbius coefficient can be discarded in norm. -/
theorem norm_cubic_vaughan_typeI_first_le_truncated_block_sum
    (U N : ℕ) (alpha : ℝ) :
    ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        if d ≤ U then
          ‖∑ m ∈ Finset.Icc 1 (N / d),
            (ArithmeticFunction.log m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m))‖
        else 0 := by
  calc
    ‖cubicArithmeticExpSum (vaughanS1 U) alpha N‖ ≤
        ∑ d ∈ Finset.Icc 1 N,
          ‖(muTruncated U d : ℂ)‖ *
            ‖∑ m ∈ Finset.Icc 1 (N / d),
                (ArithmeticFunction.log m : ℂ) *
                  CookMagyarCircle.addChar alpha (primeCubic (d * m))‖ :=
      norm_cubic_vaughan_typeI_first_le_weighted_block_sum U N alpha
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hdu : d ≤ U
      · simp only [if_pos hdu]
        have hcoeff : ‖(muTruncated U d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact abs_muTruncated_le_one U d
        exact mul_le_of_le_one_left (norm_nonneg _) hcoeff
      · have hzero : muTruncated U d = 0 := by
          simp [muTruncated, not_le_of_gt (lt_of_not_ge hdu)]
        simp [hzero, hdu]

/-- Exact divisor-antidiagonal expansion of the second Type-I term.  Its
outer Möbius factor has the same small-divisor support. -/
theorem cubic_vaughan_typeI_second_bilinear (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS2 U V) alpha N =
      ∑ x : Fin (N + 1),
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
          (muTruncated U ab.1 : ℂ) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                  lambdaHigh V)) ab.2 : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic x) := by
  unfold cubicArithmeticExpSum vaughanS2
  apply Finset.sum_congr rfl
  intro x _hx
  rw [show
      (((muTruncated U *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
              lambdaHigh V))) x : ℝ) : ℂ) =
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
          (muTruncated U ab.1 : ℂ) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                  lambdaHigh V)) ab.2 : ℂ) by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rfl]
  rw [Finset.sum_mul]

/-- Vaughan's second Type-I bilinear sum in outer-divisor / inner-quotient
coordinates. The inner coefficient is the truncated Mangoldt divisor sum;
this exact reindexing is preparatory and does not by itself give cancellation. -/
theorem cubic_vaughan_typeI_second_divisor_quotient
    (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS2 U V) alpha N =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) *
            ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                  lambdaHigh V)) m : ℝ) : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
  classical
  let F : ℕ → ℕ → ℕ → ℂ := fun x d m =>
    (muTruncated U d : ℂ) *
      ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
            lambdaHigh V)) m : ℝ) : ℂ) *
        CookMagyarCircle.addChar alpha (primeCubic x)
  have hindex :
      (∑ x : Fin (N + 1),
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal, F x ab.1 ab.2) =
      ∑ x ∈ Finset.Icc 0 N,
        ∑ ab ∈ x.divisorsAntidiagonal, F x ab.1 ab.2 := by
    refine Finset.sum_bij (fun x _ => (x : ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    · intro x hx y hy hxy
      exact Fin.ext hxy
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      refine ⟨⟨n, by omega⟩, Finset.mem_univ _, rfl⟩
    · intro x hx
      rfl
  calc
    cubicArithmeticExpSum (vaughanS2 U V) alpha N =
        ∑ x : Fin (N + 1),
          ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
            (muTruncated U ab.1 : ℂ) *
              ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                  ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                    lambdaHigh V)) ab.2 : ℝ) : ℂ) *
                CookMagyarCircle.addChar alpha (primeCubic x) :=
      cubic_vaughan_typeI_second_bilinear U V N alpha
    _ = ∑ x ∈ Finset.Icc 0 N,
          ∑ ab ∈ x.divisorsAntidiagonal,
            (muTruncated U ab.1 : ℂ) *
              ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                  ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                    lambdaHigh V)) ab.2 : ℝ) : ℂ) *
                CookMagyarCircle.addChar alpha (primeCubic x) := by
      simpa [F] using hindex
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Icc 1 (N / d),
            (muTruncated U d : ℂ) *
              ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                  ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                    lambdaHigh V)) m : ℝ) : ℂ) *
                CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
      simpa [F] using
        sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum N F

/-- Exact three-variable form of Vaughan's second Type-I sum. The low
Mangoldt variable and the truncated Möbius variable are outer; the remaining
quotient runs along a progression whose step is their product. -/
theorem cubic_vaughan_typeI_second_triple_divisor_quotient
    (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS2 U V) alpha N =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * (r * j))) := by
  rw [cubic_vaughan_typeI_second_divisor_quotient]
  apply Finset.sum_congr rfl
  intro d hd
  let c : ℕ → ℂ := fun m =>
    CookMagyarCircle.addChar alpha (primeCubic (d * m))
  calc
    (∑ m ∈ Finset.Icc 1 (N / d),
        (muTruncated U d : ℂ) *
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                lambdaHigh V)) m : ℝ) : ℂ) * c m) =
      (muTruncated U d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / d),
          ((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                lambdaHigh V)) m : ℝ) : ℂ) * c m := by
          calc
            _ = ∑ m ∈ Finset.Icc 1 (N / d),
                  (muTruncated U d : ℂ) *
                    (((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
                        ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) -
                          lambdaHigh V)) m : ℝ) : ℂ) * c m) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    ring
            _ = _ := by rw [← Finset.mul_sum]
    _ = (muTruncated U d : ℂ) *
          ∑ r ∈ Finset.Icc 1 (N / d),
            ∑ j ∈ Finset.Icc 1 ((N / d) / r),
              (vaughanLow V r : ℂ) * c (r * j) := by
          rw [← vaughanLow_eq_lambda_sub_high V]
          rw [sum_zeta_vaughanLow_mul_eq_divisor_quotient_sum]
    _ = ∑ r ∈ Finset.Icc 1 (N / d),
          ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * (r * j))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp only [c]
          ring

/-- Triangle-inequality reduction of the second Type-I sum to its unweighted
progression blocks, retaining the exact Möbius and low-Mangoldt weights. -/
theorem norm_cubic_vaughan_typeI_second_le_block_norm_sum
    (U V N : ℕ) (alpha : ℝ) :
    ‖cubicArithmeticExpSum (vaughanS2 U V) alpha N‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ *
            ‖∑ j ∈ Finset.Icc 1 ((N / d) / r),
              CookMagyarCircle.addChar alpha (primeCubic (d * (r * j)))‖ := by
  classical
  let block (d r : ℕ) : ℂ :=
    ∑ j ∈ Finset.Icc 1 ((N / d) / r),
      CookMagyarCircle.addChar alpha (primeCubic (d * (r * j)))
  have hinner (d r : ℕ) :
      (∑ j ∈ Finset.Icc 1 ((N / d) / r),
        (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) *
          CookMagyarCircle.addChar alpha (primeCubic (d * (r * j)))) =
        (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) * block d r := by
    calc
      _ = ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            ((muTruncated U d : ℂ) * (vaughanLow V r : ℂ)) *
              CookMagyarCircle.addChar alpha (primeCubic (d * (r * j))) := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
      _ = _ := by rw [Finset.mul_sum]
  have hfactor :
      (∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * (r * j)))) =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) * block d r := by
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro r hr
    exact hinner d r
  rw [cubic_vaughan_typeI_second_triple_divisor_quotient, hfactor]
  calc
    ‖∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) * block d r‖ ≤
      ∑ d ∈ Finset.Icc 1 N,
        ‖∑ r ∈ Finset.Icc 1 (N / d),
          (muTruncated U d : ℂ) * (vaughanLow V r : ℂ) * block d r‖ :=
            norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
          ∑ r ∈ Finset.Icc 1 (N / d),
            ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ) * block d r‖ := by
          apply Finset.sum_le_sum
          intro d hd
          exact norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ r ∈ Finset.Icc 1 (N / d),
            ‖(muTruncated U d : ℂ) * (vaughanLow V r : ℂ)‖ *
              ‖block d r‖ := by
          apply Finset.sum_congr rfl
          intro d hd
          apply Finset.sum_congr rfl
          intro r hr
          rw [norm_mul]
    _ = _ := by simp [block]

/-- The quotient variable in the second Type-I expansion starts at one;
shifting it to zero gives the wrapped progression with step `d*r`. -/
theorem sum_primeCubic_product_divisor_quotient_eq_progression
    (N d r : ℕ) (alpha : ℝ) (hstep : 0 < d * r) (hstepN : d * r ≤ N) :
    (∑ j ∈ Finset.Icc 1 ((N / d) / r),
      CookMagyarCircle.addChar alpha (primeCubic (d * (r * j)))) =
    ∑ k ∈ Finset.Icc 0 ((N - d * r) / (d * r)),
      CookMagyarCircle.addChar alpha (primeCubic (d * r + d * r * k)) := by
  classical
  have hdiv : (N / d) / r = N / (d * r) := by
    rw [Nat.div_div_eq_div_mul]
  have hquot : (N - d * r) / (d * r) = N / (d * r) - 1 := by
    simpa [one_mul] using Nat.sub_mul_div_of_le N (d * r) 1 (by omega)
  have hq : 1 ≤ N / (d * r) :=
    (Nat.le_div_iff_mul_le hstep).2 (by simpa using hstepN)
  rw [hdiv, hquot]
  refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj k hk hjk
    simp only [Finset.mem_Icc] at hj hk
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    have hjshift : j = (j - 1) + 1 := by omega
    have hphase : d * (r * j) = d * r + d * r * (j - 1) := by
      calc
        d * (r * j) = (d * r) * j := by ring
        _ = (d * r) * ((j - 1) + 1) := by
          exact congrArg (fun x : ℕ => (d * r) * x) hjshift
        _ = (d * r) * (j - 1) + d * r := by rw [Nat.mul_add]; simp
        _ = d * r + d * r * (j - 1) := Nat.add_comm _ _
    rw [hphase]

/-- Exact divisor-antidiagonal expansion of the Type-II term. -/
theorem cubic_vaughan_typeII_bilinear (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS3 U V) alpha N =
      ∑ x : Fin (N + 1),
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
          (lambdaHigh V ab.1 : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
              ab.2 : ℂ) *
            CookMagyarCircle.addChar alpha (primeCubic x) := by
  unfold cubicArithmeticExpSum vaughanS3
  apply Finset.sum_congr rfl
  intro x _hx
  rw [show
      (((lambdaHigh V *
          (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) x : ℝ) : ℂ) =
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
          (lambdaHigh V ab.1 : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
              ab.2 : ℂ) by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rfl]
  rw [Finset.sum_mul]

/-- The Type-II bilinear form in positive divisor/quotient coordinates.
This is the exact form needed before imposing Hua's dyadic `d`-block and
`m`-interval hypotheses. -/
theorem cubic_vaughan_typeII_divisor_quotient (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS3 U V) alpha N =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ m ∈ Finset.Icc 1 (N / d),
          (lambdaHigh V d : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
  classical
  let F : ℕ → ℕ → ℕ → ℂ := fun x d m =>
    (lambdaHigh V d : ℂ) *
      ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℂ) *
        CookMagyarCircle.addChar alpha (primeCubic x)
  have hindex :
      (∑ x : Fin (N + 1),
        ∑ ab ∈ (x : ℕ).divisorsAntidiagonal, F x ab.1 ab.2) =
      ∑ x ∈ Finset.Icc 0 N,
        ∑ ab ∈ x.divisorsAntidiagonal, F x ab.1 ab.2 := by
    refine Finset.sum_bij (fun x _ => (x : ℕ)) ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
    · intro x hx y hy hxy
      exact Fin.ext hxy
    · intro n hn
      have hn' := Finset.mem_Icc.mp hn
      refine ⟨⟨n, by omega⟩, Finset.mem_univ _, rfl⟩
    · intro x hx
      rfl
  calc
    cubicArithmeticExpSum (vaughanS3 U V) alpha N =
        ∑ x : Fin (N + 1),
          ∑ ab ∈ (x : ℕ).divisorsAntidiagonal,
            (lambdaHigh V ab.1 : ℂ) *
              ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
                ab.2 : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic x) :=
      cubic_vaughan_typeII_bilinear U V N alpha
    _ = ∑ x ∈ Finset.Icc 0 N,
          ∑ ab ∈ x.divisorsAntidiagonal,
            (lambdaHigh V ab.1 : ℂ) *
              ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
                ab.2 : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic x) := by
      simpa [F] using hindex
    _ = ∑ d ∈ Finset.Icc 1 N,
          ∑ m ∈ Finset.Icc 1 (N / d),
            (lambdaHigh V d : ℂ) *
              ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
                m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
      simpa [F] using
        sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum N F

/-- The outer Type-II variable is supported strictly above Vaughan's
Mangoldt cutoff. -/
theorem lambdaHigh_eq_zero_of_le (V d : ℕ) (hdV : d ≤ V) :
    lambdaHigh V d = 0 := by
  simp [lambdaHigh, not_lt.mpr hdV]

/-- The exact Type-II sum with both truncation supports made explicit. The
outer variable is a prime-power tail (`d>V`); the inner quotient must exceed
the Möbius cutoff (`m>U`). No cancellation estimate is used here. -/
theorem cubic_vaughan_typeII_divisor_quotient_supported
    (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS3 U V) alpha N =
      ∑ d ∈ Finset.Icc (V + 1) N,
        ∑ m ∈ Finset.Icc (U + 1) (N / d),
          (lambdaHigh V d : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m)) := by
  classical
  rw [cubic_vaughan_typeII_divisor_quotient]
  let F : ℕ → ℕ → ℂ := fun d m =>
    (lambdaHigh V d : ℂ) *
      ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℂ) *
        CookMagyarCircle.addChar alpha (primeCubic (d * m))
  have hinner (d : ℕ) :
      (∑ m ∈ Finset.Icc 1 (N / d), F d m) =
        ∑ m ∈ Finset.Icc (U + 1) (N / d), F d m := by
    symm
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Icc] at hm ⊢
      omega
    · intro m hm hnot
      have hm' := Finset.mem_Icc.mp hm
      have hmU : m ≤ U := by
        simp only [Finset.mem_Icc] at hnot
        omega
      have hconv := muHigh_mul_zeta_eq_zero_of_le U m (by omega) hmU
      change (lambdaHigh V d : ℂ) *
        ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℂ) *
          CookMagyarCircle.addChar alpha (primeCubic (d * m)) = 0
      rw [hconv]
      simp
  have houter :
      (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m) =
        ∑ d ∈ Finset.Icc (V + 1) N, ∑ m ∈ Finset.Icc (U + 1) (N / d), F d m := by
    calc
      (∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N / d), F d m) =
          ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc (U + 1) (N / d), F d m := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hinner d
      _ = ∑ d ∈ Finset.Icc (V + 1) N, ∑ m ∈ Finset.Icc (U + 1) (N / d), F d m := by
        symm
        apply Finset.sum_subset
        · intro d hd
          simp only [Finset.mem_Icc] at hd ⊢
          omega
        · intro d hd hnot
          simp only [Finset.mem_Icc] at hd hnot
          have hdV : d ≤ V := by
            omega
          have hzero : lambdaHigh V d = 0 :=
            lambdaHigh_eq_zero_of_le V d hdV
          change ∑ m ∈ Finset.Icc (U + 1) (N / d), F d m = 0
          apply Finset.sum_eq_zero
          intro m hm
          change (lambdaHigh V d : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * m)) = 0
          rw [hzero]
          simp
  simpa [F] using houter

/-- Three-variable expansion of Vaughan's Type-II term after opening the
Möbius/zeta convolution. The two displayed coefficients are now individual
truncated arithmetic-function values; the phase is evaluated at the full
product `d*r*j`. -/
theorem cubic_vaughan_typeII_triple_divisor_quotient
    (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS3 U V) alpha N =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ r ∈ Finset.Icc 1 (N / d),
          ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            (lambdaHigh V d : ℂ) * (muHigh U r : ℂ) *
              CookMagyarCircle.addChar alpha
                (primeCubic (d * (r * j))) := by
  classical
  rw [cubic_vaughan_typeII_divisor_quotient]
  apply Finset.sum_congr rfl
  intro d hd
  let c : ℕ → ℂ := fun m =>
    CookMagyarCircle.addChar alpha (primeCubic (d * m))
  have hfactor :
      (∑ m ∈ Finset.Icc 1 (N / d),
        (lambdaHigh V d : ℂ) *
          (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
            c m) =
      (lambdaHigh V d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / d),
          (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
            c m := by
    calc
      _ = ∑ m ∈ Finset.Icc 1 (N / d),
            (lambdaHigh V d : ℂ) *
              ((((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
                c m) := by
          apply Finset.sum_congr rfl
          intro m hm
          ring
      _ = _ := by rw [Finset.mul_sum]
  calc
    (∑ m ∈ Finset.Icc 1 (N / d),
        (lambdaHigh V d : ℂ) *
          (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
            c m) =
      (lambdaHigh V d : ℂ) *
        ∑ m ∈ Finset.Icc 1 (N / d),
          (((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m : ℝ) : ℂ) *
            c m := hfactor
    _ = (lambdaHigh V d : ℂ) *
          ∑ r ∈ Finset.Icc 1 (N / d),
            ∑ j ∈ Finset.Icc 1 ((N / d) / r),
              (muHigh U r : ℂ) * c (r * j) := by
        rw [sum_muHigh_mul_zeta_mul_eq_divisor_quotient_sum]
    _ = ∑ r ∈ Finset.Icc 1 (N / d),
          ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            (lambdaHigh V d : ℂ) * (muHigh U r : ℂ) *
              CookMagyarCircle.addChar alpha (primeCubic (d * (r * j))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [c]
        ring

/-- The exact three-variable Type-II expansion with both truncation cutoffs
shown in its ranges: `V<d`, `U<r`. This remains an identity, not a bound. -/
theorem cubic_vaughan_typeII_triple_divisor_quotient_supported
    (U V N : ℕ) (alpha : ℝ) :
    cubicArithmeticExpSum (vaughanS3 U V) alpha N =
      ∑ d ∈ Finset.Icc (V + 1) N,
        ∑ r ∈ Finset.Icc (U + 1) (N / d),
          ∑ j ∈ Finset.Icc 1 ((N / d) / r),
            (lambdaHigh V d : ℂ) * (muHigh U r : ℂ) *
              CookMagyarCircle.addChar alpha
                (primeCubic (d * (r * j))) := by
  classical
  rw [cubic_vaughan_typeII_triple_divisor_quotient]
  let F : ℕ → ℕ → ℂ := fun d r =>
    ∑ j ∈ Finset.Icc 1 ((N / d) / r),
      (lambdaHigh V d : ℂ) * (muHigh U r : ℂ) *
        CookMagyarCircle.addChar alpha (primeCubic (d * (r * j)))
  have hinner (d : ℕ) :
      (∑ r ∈ Finset.Icc 1 (N / d), F d r) =
        ∑ r ∈ Finset.Icc (U + 1) (N / d), F d r := by
    symm
    apply Finset.sum_subset
    · intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      omega
    · intro r hr hnot
      simp only [Finset.mem_Icc] at hr hnot
      have hrU : r ≤ U := by omega
      have hzero : muHigh U r = 0 := muHigh_eq_zero_of_le U r hrU
      change ∑ j ∈ Finset.Icc 1 ((N / d) / r),
        (lambdaHigh V d : ℂ) * (muHigh U r : ℂ) *
          CookMagyarCircle.addChar alpha (primeCubic (d * (r * j))) = 0
      apply Finset.sum_eq_zero
      intro j hj
      rw [hzero]
      simp
  have houter :
      (∑ d ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 (N / d), F d r) =
        ∑ d ∈ Finset.Icc (V + 1) N, ∑ r ∈ Finset.Icc (U + 1) (N / d), F d r := by
    calc
      (∑ d ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc 1 (N / d), F d r) =
          ∑ d ∈ Finset.Icc 1 N, ∑ r ∈ Finset.Icc (U + 1) (N / d), F d r := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hinner d
      _ = ∑ d ∈ Finset.Icc (V + 1) N,
            ∑ r ∈ Finset.Icc (U + 1) (N / d), F d r := by
        symm
        apply Finset.sum_subset
        · intro d hd
          simp only [Finset.mem_Icc] at hd ⊢
          omega
        · intro d hd hnot
          simp only [Finset.mem_Icc] at hd hnot
          have hdV : d ≤ V := by omega
          have hzero : lambdaHigh V d = 0 :=
            lambdaHigh_eq_zero_of_le V d hdV
          change ∑ r ∈ Finset.Icc (U + 1) (N / d), F d r = 0
          apply Finset.sum_eq_zero
          intro r hr
          simp [F, hzero]
  simpa [F] using houter

end CookMagyarVaughan
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarVaughan.abs_muHigh_mul_zeta_le_divisorCount
#print axioms SystolicGrowth.CookMagyarVaughan.muHigh_eq_zero_of_le
#print axioms SystolicGrowth.CookMagyarVaughan.muHigh_mul_zeta_eq_zero_of_le
#print axioms SystolicGrowth.CookMagyarVaughan.abs_vaughanS3Coefficient_le
#print axioms SystolicGrowth.CookMagyarVaughan.vaughanLow_nonneg
#print axioms SystolicGrowth.CookMagyarVaughan.vaughanLow_le_log
#print axioms SystolicGrowth.CookMagyarVaughan.vaughanLow_eq_zero_of_gt
#print axioms SystolicGrowth.CookMagyarVaughan.norm_muTruncated_mul_vaughanLow_le_log
#print axioms SystolicGrowth.CookMagyarVaughan.muHigh_ne_zero_iff
#print axioms SystolicGrowth.CookMagyarVaughan.lambdaHigh_ne_zero_iff
#print axioms SystolicGrowth.CookMagyarVaughan.muTruncated_ne_zero_iff
#print axioms SystolicGrowth.CookMagyarVaughan.vaughanLow_eq_lambda_sub_high
#print axioms SystolicGrowth.CookMagyarVaughan.zeta_mul_vaughanLow_nonneg_le_log
#print axioms SystolicGrowth.CookMagyarVaughan.zeta_mul_vaughanLow_eq_divisorsAntidiagonal_sum
#print axioms SystolicGrowth.CookMagyarVaughan.sum_zeta_vaughanLow_mul_eq_divisor_quotient_sum
#print axioms SystolicGrowth.CookMagyarVaughan.abs_vaughanS1Coefficient_le
#print axioms SystolicGrowth.CookMagyarVaughan.abs_vaughanS2Coefficient_le
#print axioms SystolicGrowth.CookMagyarVaughan.sum_divisorsAntidiagonal_Icc_eq_divisor_quotient_sum
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeI_first_divisor_quotient
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeI_second_divisor_quotient
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeI_second_triple_divisor_quotient
#print axioms SystolicGrowth.CookMagyarVaughan.norm_cubic_vaughan_typeI_second_le_block_norm_sum
#print axioms SystolicGrowth.CookMagyarVaughan.sum_primeCubic_product_divisor_quotient_eq_progression
#print axioms SystolicGrowth.CookMagyarVaughan.sum_log_primeCubic_divisor_quotient_eq_progression
#print axioms SystolicGrowth.CookMagyarVaughan.norm_cubic_vaughan_typeI_first_le_weighted_block_sum
#print axioms SystolicGrowth.CookMagyarVaughan.norm_cubic_vaughan_typeI_first_le_truncated_block_sum
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeII_divisor_quotient
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeII_divisor_quotient_supported
#print axioms SystolicGrowth.CookMagyarVaughan.sum_muHigh_mul_zeta_mul_eq_divisor_quotient_sum
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeII_triple_divisor_quotient
#print axioms SystolicGrowth.CookMagyarVaughan.cubic_vaughan_typeII_triple_divisor_quotient_supported
