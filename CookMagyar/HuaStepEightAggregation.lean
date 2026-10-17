module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.HuaStepEightSourceDivision
public import Mathlib.Data.Nat.Log

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarCircle

open CookMagyarArcs

/-! # Summing Hua's normalized repeated-prime corrections

The two outer source parameters contribute harmonic factors, not their
range lengths. Coefficients of norm at most one allow the source's constant
coefficient, as well as selection of subfamilies by zero coefficients. This
module bounds only the explicit repeated-prime correction; it asserts no
Type-II cancellation estimate. The dyadic-harmonic arithmetic below also
accounts for the finite overhead in the actual Type-II source aggregate.
-/

/-- The normalized pair-minus-divisor error with every original source
range, cutoff, progression, and parity preserved. -/
noncomputable def huaStepEightSourceError (P m Q t s parity : ℕ)
    (lambda₂ lambda₃ : ℝ) (f : ℕ → ℂ) : ℂ :=
  let H := huaStepEightSieveProduct P
  let Y := Nat.ceil (Real.rpow (Real.log P) lambda₃)
  let R := huaStepEightSourceCondition P m Q t lambda₂
  ((∑ z ∈ huaStepEightPairs H Y (P / m) s parity R,
      f (m * (z.1 * z.2))) / (s : ℂ)) -
    ∑ v ∈ huaStepEightDivisors H Y (P / m) s parity R, f (m * v)

/-- The actual outer correction sum, with both outer parameters positive. -/
noncomputable def huaStepEightAggregateError (P Q t parity : ℕ)
    (lambda₂ lambda₃ : ℝ) (M S : ℕ) (coefficient : ℕ → ℕ → ℂ) (f : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
    coefficient m s * huaStepEightSourceError P m Q t s parity lambda₂ lambda₃ f

/-- The real harmonic sum in precisely the positive outer index range. -/
theorem harmonic_real_eq_sum_inv (M : ℕ) :
    (harmonic M : ℝ) = ∑ m ∈ Finset.Icc 1 M, (m : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem harmonic_real_nonneg (M : ℕ) : 0 ≤ (harmonic M : ℝ) := by
  rw [harmonic_real_eq_sum_inv]
  exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem harmonic_real_le_nat (M : ℕ) : (harmonic M : ℝ) ≤ M := by
  rw [harmonic_real_eq_sum_inv]
  calc
    _ ≤ ∑ _m ∈ Finset.Icc 1 M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact inv_le_one_of_one_le₀ (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
    _ = _ := by simp [Nat.card_Icc]

/-- A coarse finite overhead estimate for the actual dyadic count and
the two positive harmonic source ranges. No cancellation is used. -/
theorem hua_typeII_dyadic_harmonic_overhead_le
    (P sigma3 : ℕ) (hL : 2 ≤ Real.log (P : ℝ)) :
    (((Nat.log 2 (Nat.sqrt P) + 1 : ℕ) : ℝ)) *
        (harmonic (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))) : ℝ) *
        (harmonic (Nat.floor (Real.log P)) : ℝ) ≤
      (1 / Real.log 2 + 1) * Real.log (P : ℝ) ^ (sigma3 + 2) := by
  let L := Real.log (P : ℝ)
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hPpos : 0 < P := by
    by_contra h
    have hzero : P = 0 := Nat.eq_zero_of_not_pos h
    norm_num [hzero] at hL
  have hlogNat : (Nat.log 2 P : ℝ) ≤ L / Real.log 2 := by
    have hpow : (2 : ℝ) ^ Nat.log 2 P ≤ P := by
      exact_mod_cast Nat.pow_log_le_self 2 hPpos.ne'
    have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ hlog2).mpr hlog
  have hcount : (((Nat.log 2 (Nat.sqrt P) + 1 : ℕ) : ℝ)) ≤
      (1 / Real.log 2 + 1) * L := by
    have hmono : (Nat.log 2 (Nat.sqrt P) : ℝ) ≤ Nat.log 2 P := by
      exact_mod_cast Nat.log_mono_right (Nat.sqrt_le_self P)
    calc
      _ ≤ L / Real.log 2 + 1 := by
        push_cast
        exact add_le_add_left (hmono.trans hlogNat) 1
      _ ≤ L / Real.log 2 + L := add_le_add le_rfl hLone
      _ = _ := by ring
  have hfirst :
      (harmonic (Nat.floor (Real.rpow L (sigma3 : ℝ))) : ℝ) ≤ L ^ sigma3 := by
    calc
      _ ≤ (Nat.floor (Real.rpow L (sigma3 : ℝ)) : ℝ) := harmonic_real_le_nat _
      _ ≤ Real.rpow L (sigma3 : ℝ) :=
        Nat.floor_le (Real.rpow_nonneg hLpos.le (sigma3 : ℝ))
      _ = _ := Real.rpow_natCast L sigma3
  have hsecond : (harmonic (Nat.floor L) : ℝ) ≤ L :=
    (harmonic_real_le_nat _).trans (Nat.floor_le hLpos.le)
  calc
    _ ≤ ((1 / Real.log 2 + 1) * L) * L ^ sigma3 * L := by
      apply mul_le_mul ?_ hsecond (harmonic_real_nonneg _) (by positivity)
      exact mul_le_mul hcount hfirst (harmonic_real_nonneg _) (by positivity)
    _ = _ := by
      change _ = (1 / Real.log 2 + 1) * L ^ (sigma3 + 2)
      rw [pow_add]
      ring

/-- Any natural exponent budget paying for the displayed finite dyadic and
harmonic overhead converts the actual Type-II harmonic rate to the desired
logarithmic rate. Only real arithmetic and `C ≥ 0` are involved. -/
theorem hua_typeII_harmonic_overhead_log_saving_le
    (P sigma3 saving decay : ℕ) (C : ℝ)
    (hL : 2 ≤ Real.log (P : ℝ)) (hC : 0 ≤ C)
    (hbudget : decay + sigma3 + 2 ≤ saving) :
    (C * (((Nat.log 2 (Nat.sqrt P) + 1 : ℕ) : ℝ)) * (P : ℝ) /
        Real.log (P : ℝ) ^ saving) *
        (harmonic (Nat.floor (Real.rpow (Real.log P) (sigma3 : ℝ))) : ℝ) *
        (harmonic (Nat.floor (Real.log P)) : ℝ) ≤
      (C * (1 / Real.log 2 + 1)) * P / Real.log (P : ℝ) ^ decay := by
  let L := Real.log (P : ℝ)
  let K := 1 / Real.log 2 + 1
  have hLone : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hK : 0 ≤ K := by
    dsimp [K]
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hpow : L ^ decay * L ^ (sigma3 + 2) ≤ L ^ saving := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hLone (by omega)
  have hratio : L ^ (sigma3 + 2) / L ^ saving ≤ 1 / L ^ decay := by
    apply (div_le_div_iff₀ (pow_pos hLpos saving) (pow_pos hLpos decay)).mpr
    simpa only [one_mul, mul_comm] using hpow
  have hoverhead := hua_typeII_dyadic_harmonic_overhead_le P sigma3 hL
  calc
    _ = (C * (P : ℝ) / L ^ saving) *
        ((((Nat.log 2 (Nat.sqrt P) + 1 : ℕ) : ℝ)) *
          (harmonic (Nat.floor (Real.rpow L (sigma3 : ℝ))) : ℝ) *
          (harmonic (Nat.floor L) : ℝ)) := by ring
    _ ≤ (C * (P : ℝ) / L ^ saving) * (K * L ^ (sigma3 + 2)) :=
      mul_le_mul_of_nonneg_left hoverhead (by positivity)
    _ = (C * K * (P : ℝ)) * (L ^ (sigma3 + 2) / L ^ saving) := by ring
    _ ≤ (C * K * (P : ℝ)) * (1 / L ^ decay) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- A weighted double sum of reciprocal corrections has the product of
the two harmonic sums as its exact finite majorant. -/
theorem norm_weighted_reciprocal_double_sum_le (M S : ℕ) (C : ℝ)
    (error coefficient : ℕ → ℕ → ℂ)
    (hcoefficient : ∀ m ∈ Finset.Icc 1 M, ∀ s ∈ Finset.Icc 1 S,
      ‖coefficient m s‖ ≤ 1)
    (herror : ∀ m ∈ Finset.Icc 1 M, ∀ s ∈ Finset.Icc 1 S,
      ‖error m s‖ ≤ C / ((s : ℝ) * m)) :
    ‖∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
      coefficient m s * error m s‖ ≤ C * (harmonic M : ℝ) * (harmonic S : ℝ) := by
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
        ‖coefficient m s * error m s‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum fun m hm => norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 S,
        C / ((s : ℝ) * m) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro s hs
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg (error m s))
        (hcoefficient m hm s hs)).trans (herror m hm s hs)
    _ = C * (harmonic M : ℝ) * (harmonic S : ℝ) := by
      simp only [harmonic_real_eq_sum_inv, div_eq_mul_inv, mul_inv_rev]
      simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Finite outer aggregation for every real cubic phase, uniformly in all
coefficients and source progression data. Both reciprocal factors remain
visible in the harmonic majorant. -/
theorem eventually_norm_huaSourceStepEight_generalCubic_aggregate_harmonic_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity M S : ℕ, ∀ coefficient : ℕ → ℕ → ℂ,
        (∀ m ∈ Finset.Icc 1 M, ∀ s ∈ Finset.Icc 1 S, ‖coefficient m s‖ ≤ 1) →
        ∀ a b c d : ℝ,
          ‖huaStepEightAggregateError P Q t parity lambda₂ lambda₃ M S coefficient
            (generalCubicPhase a b c d)‖ ≤
              ((4 : ℝ) * P / Real.rpow (Real.log P) lambda₃) *
                (harmonic M : ℝ) * (harmonic S : ℝ) := by
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_div_sub_divisors_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro Q t parity M S coefficient hcoefficient a b c d
  apply norm_weighted_reciprocal_double_sum_le M S
    ((4 : ℝ) * P / Real.rpow (Real.log P) lambda₃)
    (fun m s => huaStepEightSourceError P m Q t s parity lambda₂ lambda₃
      (generalCubicPhase a b c d)) coefficient hcoefficient
  intro m hm s hs
  have hsource := hP.2 m Q t s parity
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1)
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hs).1) a b c d
  calc
    _ ≤ (4 : ℝ) * P / ((s : ℝ) * m * Real.rpow (Real.log P) lambda₃) := hsource
    _ = ((4 : ℝ) * P / Real.rpow (Real.log P) lambda₃) / ((s : ℝ) * m) := by
      rw [div_div]
      congr 1
      ring

/-- The harmonic aggregate bound for the actual original `x³-x`
character, without a phase-norm hypothesis. -/
theorem eventually_norm_huaSourceStepEight_primeCubic_aggregate_harmonic_le
    {lambda₂ lambda₃ : ℝ} (h₃ : 0 < lambda₃) :
    ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity M S : ℕ, ∀ coefficient : ℕ → ℕ → ℂ,
        (∀ m ∈ Finset.Icc 1 M, ∀ s ∈ Finset.Icc 1 S, ‖coefficient m s‖ ≤ 1) →
        ∀ alpha : ℝ,
          ‖huaStepEightAggregateError P Q t parity lambda₂ lambda₃ M S coefficient
            (fun n => addChar alpha (primeCubic n))‖ ≤
              ((4 : ℝ) * P / Real.rpow (Real.log P) lambda₃) *
                (harmonic M : ℝ) * (harmonic S : ℝ) := by
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_aggregate_harmonic_le h₃]
    with P hP
  refine ⟨hP.1, ?_⟩
  intro Q t parity M S coefficient hcoefficient alpha
  have hphase : generalCubicPhase alpha 0 (-alpha) 0 =
      (fun n => addChar alpha (primeCubic n)) := by
    funext n
    exact (addChar_primeCubic_eq_generalCubicPhase alpha n).symm
  rw [← hphase]
  exact hP.2 Q t parity M S coefficient hcoefficient alpha 0 (-alpha) 0

/-- The floor of a logarithmic-power outer range has the expected harmonic
envelope, also when the natural floor is zero. -/
theorem harmonic_natFloor_rpow_le_one_add_log {L a : ℝ}
    (hL : 1 ≤ L) (ha : 0 ≤ a) :
    (harmonic (Nat.floor (Real.rpow L a)) : ℝ) ≤ 1 + a * Real.log L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  by_cases hM : Nat.floor (Real.rpow L a) = 0
  · simp only [hM, harmonic_zero, Rat.cast_zero]
    have hlog := Real.log_nonneg hL
    positivity
  · have hMpos : 0 < (Nat.floor (Real.rpow L a) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hM
    have hlog : Real.log (Nat.floor (Real.rpow L a) : ℝ) ≤ a * Real.log L := by
      calc
        _ ≤ Real.log (Real.rpow L a) :=
          Real.log_le_log hMpos (Nat.floor_le (Real.rpow_nonneg hLpos.le a))
        _ = a * Real.log L := Real.log_rpow hLpos a
    exact (harmonic_le_one_add_log _).trans (add_le_add le_rfl hlog)

/-- Any positive exponent slack absorbs the two harmonic outer losses.
The explicit constant is uniform in `L ≥ 1`. -/
theorem harmonic_logCutoffs_product_le_rpow {L lambda₂ epsilon : ℝ}
    (hL : 1 ≤ L) (h₂ : 0 ≤ lambda₂) (hepsilon : 0 < epsilon) :
    (harmonic (Nat.floor (Real.rpow L lambda₂)) : ℝ) *
        (harmonic (Nat.floor L) : ℝ) ≤
      ((1 + lambda₂ / epsilon) * (1 + 1 / epsilon)) * Real.rpow L (epsilon + epsilon) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hpow := Real.one_le_rpow hL hepsilon.le
  have hlog := Real.log_le_rpow_div hLpos.le hepsilon
  have hfirst : (harmonic (Nat.floor (Real.rpow L lambda₂)) : ℝ) ≤
      (1 + lambda₂ / epsilon) * Real.rpow L epsilon := by
    calc
      _ ≤ 1 + lambda₂ * Real.log L := harmonic_natFloor_rpow_le_one_add_log hL h₂
      _ ≤ Real.rpow L epsilon + lambda₂ * (Real.rpow L epsilon / epsilon) :=
        add_le_add hpow (mul_le_mul_of_nonneg_left hlog h₂)
      _ = (1 + lambda₂ / epsilon) * Real.rpow L epsilon := by ring
  have hsecond : (harmonic (Nat.floor L) : ℝ) ≤
      (1 + 1 / epsilon) * Real.rpow L epsilon := by
    calc
      _ ≤ 1 + Real.log L := by
        simpa only [Real.rpow_eq_pow, Real.rpow_one, one_mul] using
          (harmonic_natFloor_rpow_le_one_add_log (a := 1) hL (by norm_num))
      _ ≤ Real.rpow L epsilon + Real.rpow L epsilon / epsilon := add_le_add hpow hlog
      _ = (1 + 1 / epsilon) * Real.rpow L epsilon := by ring
  calc
    _ ≤ ((1 + lambda₂ / epsilon) * Real.rpow L epsilon) *
        ((1 + 1 / epsilon) * Real.rpow L epsilon) :=
      mul_le_mul hfirst hsecond (harmonic_real_nonneg _) (by positivity)
    _ = ((1 + lambda₂ / epsilon) * (1 + 1 / epsilon)) *
        Real.rpow L (epsilon + epsilon) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_add hLpos]
      ring

/-- For the actual source outer ranges `m ≤ floor((log P)^lambda₂)` and
`1 ≤ s ≤ floor(log P)`, any positive exponent slack absorbs the harmonic
losses. The constant is independent of phase, progression, parity, and
norm-bounded coefficients. -/
theorem eventually_norm_huaSourceStepEight_generalCubic_aggregate_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : rho < lambda₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ coefficient : ℕ → ℕ → ℂ,
        (∀ m ∈ Finset.Icc 1 (Nat.floor (Real.rpow (Real.log P) lambda₂)),
          ∀ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)), ‖coefficient m s‖ ≤ 1) →
        ∀ a b c d : ℝ,
          ‖huaStepEightAggregateError P Q t parity lambda₂ lambda₃
            (Nat.floor (Real.rpow (Real.log P) lambda₂)) (Nat.floor (Real.log P))
            coefficient (generalCubicPhase a b c d)‖ ≤
              K * P / Real.rpow (Real.log P) rho := by
  let epsilon := (lambda₃ - rho) / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  let K := 4 * ((1 + lambda₂ / epsilon) * (1 + 1 / epsilon))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hlog : Filter.Tendsto (fun P : ℕ => Real.log (P : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_norm_huaSourceStepEight_generalCubic_aggregate_harmonic_le h₃,
    hlog.eventually_ge_atTop 1] with P hP hL
  refine ⟨hP.1, ?_⟩
  intro Q t parity coefficient hcoefficient a b c d
  have hLpos : 0 < Real.log (P : ℝ) := lt_of_lt_of_le zero_lt_one hL
  have hsource := hP.2 Q t parity
    (Nat.floor (Real.rpow (Real.log P) lambda₂)) (Nat.floor (Real.log P))
    coefficient hcoefficient a b c d
  have hproduct := harmonic_logCutoffs_product_le_rpow hL h₂ hepsilon
  have hsum : rho + (epsilon + epsilon) = lambda₃ := by dsimp [epsilon]; ring
  have hpowers : Real.rpow (Real.log P) lambda₃ =
      Real.rpow (Real.log P) rho * Real.rpow (Real.log P) (epsilon + epsilon) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add hLpos, hsum]
  calc
    _ ≤ ((4 : ℝ) * P / Real.rpow (Real.log P) lambda₃) *
        ((harmonic (Nat.floor (Real.rpow (Real.log P) lambda₂)) : ℝ) *
          (harmonic (Nat.floor (Real.log P)) : ℝ)) := by
      simpa only [mul_assoc] using hsource
    _ ≤ ((4 : ℝ) * P / Real.rpow (Real.log P) lambda₃) *
        (((1 + lambda₂ / epsilon) * (1 + 1 / epsilon)) *
          Real.rpow (Real.log P) (epsilon + epsilon)) :=
      mul_le_mul_of_nonneg_left hproduct
        (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg P))
          (Real.rpow_nonneg hLpos.le lambda₃))
    _ = K * P / Real.rpow (Real.log P) rho := by
      dsimp only [K]
      rw [hpowers]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hLpos rho),
        ne_of_gt (Real.rpow_pos_of_pos hLpos (epsilon + epsilon))]
      ring_nf
      simp only [Real.rpow_eq_pow]
      rw [mul_inv_cancel_right₀
        (ne_of_gt (Real.rpow_pos_of_pos hLpos (epsilon * 2)))]

/-- The source repeated-prime aggregate for `x³-x` has an arbitrarily
prescribed logarithmic saving below `lambda₃`, with the positive factor-count
range and the source's actual `m` cutoff unchanged. -/
theorem eventually_norm_huaSourceStepEight_primeCubic_aggregate_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : rho < lambda₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ coefficient : ℕ → ℕ → ℂ,
        (∀ m ∈ Finset.Icc 1 (Nat.floor (Real.rpow (Real.log P) lambda₂)),
          ∀ s ∈ Finset.Icc 1 (Nat.floor (Real.log P)), ‖coefficient m s‖ ≤ 1) →
        ∀ alpha : ℝ,
          ‖huaStepEightAggregateError P Q t parity lambda₂ lambda₃
            (Nat.floor (Real.rpow (Real.log P) lambda₂)) (Nat.floor (Real.log P))
            coefficient (fun n => addChar alpha (primeCubic n))‖ ≤
              K * P / Real.rpow (Real.log P) rho := by
  obtain ⟨K, hK, hbound⟩ :=
    eventually_norm_huaSourceStepEight_generalCubic_aggregate_logSaving_le h₂ h₃ hrho
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with P hP
  refine ⟨hP.1, ?_⟩
  intro Q t parity coefficient hcoefficient alpha
  have hphase : generalCubicPhase alpha 0 (-alpha) 0 =
      (fun n => addChar alpha (primeCubic n)) := by
    funext n
    exact (addChar_primeCubic_eq_generalCubicPhase alpha n).symm
  rw [← hphase]
  exact hP.2 Q t parity coefficient hcoefficient alpha 0 (-alpha) 0

/-- Hua's actual constant-one outer coefficients require no coefficient
estimate input in the final repeated-prime correction bound. -/
theorem eventually_norm_huaSourceStepEight_primeCubic_unweighted_logSaving_le
    {lambda₂ lambda₃ rho : ℝ} (h₂ : 0 ≤ lambda₂) (h₃ : 0 < lambda₃)
    (hrho : rho < lambda₃) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ P : ℕ in Filter.atTop,
      1 < P ∧ ∀ Q t parity : ℕ, ∀ alpha : ℝ,
        ‖huaStepEightAggregateError P Q t parity lambda₂ lambda₃
          (Nat.floor (Real.rpow (Real.log P) lambda₂)) (Nat.floor (Real.log P))
          (fun _ _ => 1) (fun n => addChar alpha (primeCubic n))‖ ≤
            K * P / Real.rpow (Real.log P) rho := by
  obtain ⟨K, hK, hbound⟩ :=
    eventually_norm_huaSourceStepEight_primeCubic_aggregate_logSaving_le h₂ h₃ hrho
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with P hP
  refine ⟨hP.1, ?_⟩
  intro Q t parity alpha
  exact hP.2 Q t parity (fun _ _ => 1) (by intro m hm s hs; simp) alpha

end CookMagyarCircle
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarCircle.norm_weighted_reciprocal_double_sum_le
#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_dyadic_harmonic_overhead_le
#print axioms SystolicGrowth.CookMagyarCircle.hua_typeII_harmonic_overhead_log_saving_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_generalCubic_aggregate_harmonic_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_primeCubic_aggregate_harmonic_le
#print axioms SystolicGrowth.CookMagyarCircle.harmonic_logCutoffs_product_le_rpow
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_generalCubic_aggregate_logSaving_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_primeCubic_aggregate_logSaving_le
#print axioms SystolicGrowth.CookMagyarCircle.eventually_norm_huaSourceStepEight_primeCubic_unweighted_logSaving_le
