module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Large-prime finite-field estimates for the local cubic factor

This file starts the analytic treatment of the large-prime Euler factors.
Everything here is finite and exact.  The main ingredient is one Weyl
difference: the square of a complete cubic sum is a sum of complete
quadratic sums.  Quadratic sums are evaluated using only additive-character
orthogonality.

The final theorem gives a target-uniform `O_n(p⁻⁷)` bound for the
prime-modulus coefficient `B(T,p)`.  It deliberately does **not** identify
that coefficient with the whole local factor
`1 + ∑_{k≥1} B(T,p^k)`: controlling the terms with `k ≥ 2` requires a
prime-power stationary-phase estimate which is not proved here.
-/

variable {p : ℕ} [NeZero p]

/-- The complete (unrestricted) cubic exponential sum over `ZMod p`. -/
noncomputable def fullCubicExponentialSum (a : ZMod p) : ℂ :=
  ∑ x : ZMod p,
    standardAdditiveCharacter (a * cubicResidue x)

/-- A complete quadratic exponential sum. -/
noncomputable def quadraticExponentialSum
    (A B C : ZMod p) : ℂ :=
  ∑ x : ZMod p,
    standardAdditiveCharacter (A * x ^ 2 + B * x + C)

omit [NeZero p] in
private theorem quadratic_difference (A B C h y : ZMod p) :
    (A * (y + h) ^ 2 + B * (y + h) + C) -
        (A * y ^ 2 + B * y + C) =
      (2 * A * h) * y + (A * h ^ 2 + B * h) := by
  ring

private theorem sum_standardAdditiveCharacter_affine
    (D E : ZMod p) :
    (∑ y : ZMod p, standardAdditiveCharacter (D * y + E)) =
      standardAdditiveCharacter E *
        (if D = 0 then (p : ℂ) else 0) := by
  calc
    (∑ y : ZMod p, standardAdditiveCharacter (D * y + E)) =
        ∑ y : ZMod p,
          standardAdditiveCharacter (D * y) *
            standardAdditiveCharacter E := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [AddChar.map_add_eq_mul]
    _ = standardAdditiveCharacter E *
          ∑ y : ZMod p, standardAdditiveCharacter (y * D) := by
          rw [← Finset.sum_mul, mul_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro y _hy
          rw [mul_comm D y]
    _ = standardAdditiveCharacter E *
          (if D = 0 then (p : ℂ) else 0) := by
          rw [sum_standardAdditiveCharacter_mul]

private theorem quadraticExponentialSum_mul_conj
    (A B C : ZMod p) :
    quadraticExponentialSum A B C *
        conj (quadraticExponentialSum A B C) =
      ∑ h : ZMod p,
        standardAdditiveCharacter (A * h ^ 2 + B * h) *
          (if 2 * A * h = 0 then (p : ℂ) else 0) := by
  classical
  unfold quadraticExponentialSum
  rw [map_sum, Finset.sum_mul_sum]
  calc
    (∑ x : ZMod p, ∑ y : ZMod p,
        standardAdditiveCharacter (A * x ^ 2 + B * x + C) *
          conj (standardAdditiveCharacter (A * y ^ 2 + B * y + C))) =
        ∑ y : ZMod p, ∑ h : ZMod p,
          standardAdditiveCharacter
            ((A * (y + h) ^ 2 + B * (y + h) + C) -
              (A * y ^ 2 + B * y + C)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _hy
          exact (Fintype.sum_bijective (fun h : ZMod p ↦ y + h)
            ⟨add_right_injective y, add_left_surjective y⟩
            (fun h ↦ standardAdditiveCharacter
              ((A * (y + h) ^ 2 + B * (y + h) + C) -
                (A * y ^ 2 + B * y + C)))
            (fun x ↦ standardAdditiveCharacter
                (A * x ^ 2 + B * x + C) *
              conj (standardAdditiveCharacter
                (A * y ^ 2 + B * y + C)))
            (fun h ↦ by
              simp only [← AddChar.map_neg_eq_conj,
                ← AddChar.map_add_eq_mul]
              congr 1
              ring)).symm
    _ = ∑ h : ZMod p, ∑ y : ZMod p,
          standardAdditiveCharacter
            ((2 * A * h) * y + (A * h ^ 2 + B * h)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _hh
          apply Finset.sum_congr rfl
          intro y _hy
          rw [quadratic_difference]
    _ = ∑ h : ZMod p,
        standardAdditiveCharacter (A * h ^ 2 + B * h) *
          (if 2 * A * h = 0 then (p : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro h _hh
          exact sum_standardAdditiveCharacter_affine _ _

/-- A complete quadratic sum with nonzero quadratic coefficient has squared
norm exactly `p`, for odd prime `p`. -/
theorem norm_quadraticExponentialSum_sq
    (hp : p.Prime) (hp2 : p ≠ 2) {A : ZMod p} (hA : A ≠ 0)
    (B C : ZMod p) :
    ‖quadraticExponentialSum A B C‖ ^ 2 = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hge : 2 ≤ p := hp.two_le
    exact hp2 (Nat.le_antisymm hle hge)
  have hprod : quadraticExponentialSum A B C *
        conj (quadraticExponentialSum A B C) = (p : ℂ) := by
    rw [quadraticExponentialSum_mul_conj]
    calc
      (∑ h : ZMod p,
          standardAdditiveCharacter (A * h ^ 2 + B * h) *
            (if 2 * A * h = 0 then (p : ℂ) else 0)) =
          ∑ h : ZMod p, if h = 0 then (p : ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro h _hh
            have hiff : 2 * A * h = 0 ↔ h = 0 := by
              constructor
              · intro hz
                exact (mul_eq_zero.mp hz).resolve_left
                  (mul_ne_zero htwo hA)
              · rintro rfl
                simp
            rw [if_congr hiff rfl rfl]
            split_ifs with hh
            · subst h
              simp
            · simp
      _ = (p : ℂ) := by simp
  have hre := congrArg Complex.re hprod
  rw [RCLike.mul_conj] at hre
  calc
    ‖quadraticExponentialSum A B C‖ ^ 2 =
        ((↑‖quadraticExponentialSum A B C‖ : ℂ) ^ 2).re := by
          exact (RCLike.re_ofReal_pow
            (K := ℂ) ‖quadraticExponentialSum A B C‖ 2).symm
    _ = (p : ℝ) := by simpa using hre

omit [NeZero p] in
private theorem cubic_difference (a h y : ZMod p) :
    a * (cubicResidue (y + h) - cubicResidue y) =
      (3 * a * h) * y ^ 2 + (3 * a * h ^ 2) * y +
        a * (h ^ 3 - h) := by
  simp only [cubicResidue]
  ring

/-- The exact one-step Weyl-differencing identity for the complete cubic
sum. -/
theorem fullCubicExponentialSum_mul_conj (a : ZMod p) :
    fullCubicExponentialSum a * conj (fullCubicExponentialSum a) =
      ∑ h : ZMod p,
        quadraticExponentialSum
          (3 * a * h) (3 * a * h ^ 2) (a * (h ^ 3 - h)) := by
  classical
  unfold fullCubicExponentialSum quadraticExponentialSum
  rw [map_sum, Finset.sum_mul_sum]
  calc
    (∑ x : ZMod p, ∑ y : ZMod p,
        standardAdditiveCharacter (a * cubicResidue x) *
          conj (standardAdditiveCharacter (a * cubicResidue y))) =
        ∑ y : ZMod p, ∑ h : ZMod p,
          standardAdditiveCharacter
            (a * (cubicResidue (y + h) - cubicResidue y)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _hy
          exact (Fintype.sum_bijective (fun h : ZMod p ↦ y + h)
            ⟨add_right_injective y, add_left_surjective y⟩
            (fun h ↦ standardAdditiveCharacter
              (a * (cubicResidue (y + h) - cubicResidue y)))
            (fun x ↦ standardAdditiveCharacter (a * cubicResidue x) *
              conj (standardAdditiveCharacter (a * cubicResidue y)))
            (fun h ↦ by
              simp only [← AddChar.map_neg_eq_conj,
                ← AddChar.map_add_eq_mul]
              congr 1
              ring)).symm
    _ = ∑ h : ZMod p, ∑ y : ZMod p,
        standardAdditiveCharacter
          ((3 * a * h) * y ^ 2 + (3 * a * h ^ 2) * y +
            a * (h ^ 3 - h)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h _hh
          apply Finset.sum_congr rfl
          intro y _hy
          rw [cubic_difference]

/-- The norm of a nondegenerate quadratic complete sum is `sqrt p`. -/
theorem norm_quadraticExponentialSum
    (hp : p.Prime) (hp2 : p ≠ 2) {A : ZMod p} (hA : A ≠ 0)
    (B C : ZMod p) :
    ‖quadraticExponentialSum A B C‖ = Real.sqrt p := by
  have hsquare := norm_quadraticExponentialSum_sq hp hp2 hA B C
  have hsqrt_square : Real.sqrt (p : ℝ) ^ 2 = p :=
    Real.sq_sqrt (Nat.cast_nonneg p)
  nlinarith [norm_nonneg (quadraticExponentialSum A B C),
    Real.sqrt_nonneg (p : ℝ)]

/-- A complete quadratic sum with all coefficients zero is the cardinality
of the field. -/
@[simp] theorem quadraticExponentialSum_zero :
    quadraticExponentialSum (0 : ZMod p) 0 0 = p := by
  simp [quadraticExponentialSum, ZMod.card]

/-- One Weyl difference gives the explicit square-norm bound
`|S_p(a)|² ≤ p + p√p` for every nonzero frequency at a prime `p ≥ 5`. -/
theorem norm_fullCubicExponentialSum_sq_le
    (hp : p.Prime) (hp5 : 5 ≤ p) {a : ZMod p} (ha : a ≠ 0) :
    ‖fullCubicExponentialSum a‖ ^ 2 ≤
      (p : ℝ) + p * Real.sqrt p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hpoint (h : ZMod p) :
      ‖quadraticExponentialSum
          (3 * a * h) (3 * a * h ^ 2) (a * (h ^ 3 - h))‖ ≤
        Real.sqrt p + if h = 0 then p else 0 := by
    by_cases hh : h = 0
    · subst h
      simp [quadraticExponentialSum_zero, Real.sqrt_nonneg]
    · have hA : 3 * a * h ≠ 0 :=
        mul_ne_zero (mul_ne_zero hthree ha) hh
      rw [norm_quadraticExponentialSum hp hp2 hA]
      simp [hh]
  calc
    ‖fullCubicExponentialSum a‖ ^ 2 =
        ‖fullCubicExponentialSum a *
          conj (fullCubicExponentialSum a)‖ := by
            rw [norm_mul]
            have hc : ‖conj (fullCubicExponentialSum a)‖ =
                ‖fullCubicExponentialSum a‖ := by
              change ‖star (fullCubicExponentialSum a)‖ =
                ‖fullCubicExponentialSum a‖
              exact norm_star _
            rw [hc, pow_two]
    _ = ‖∑ h : ZMod p,
        quadraticExponentialSum
          (3 * a * h) (3 * a * h ^ 2) (a * (h ^ 3 - h))‖ := by
            rw [fullCubicExponentialSum_mul_conj]
    _ ≤ ∑ h : ZMod p,
        ‖quadraticExponentialSum
          (3 * a * h) (3 * a * h ^ 2) (a * (h ^ 3 - h))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ h : ZMod p,
        (Real.sqrt p + if h = 0 then p else 0) := by
          exact Finset.sum_le_sum fun h _hh ↦ hpoint h
    _ = (p : ℝ) + p * Real.sqrt p := by
          rw [Finset.sum_add_distrib]
          simp [ZMod.card, add_comm]

/-- A denominator-free fourth-power form of the cubic Weyl bound. -/
theorem norm_fullCubicExponentialSum_pow_four_le
    (hp : p.Prime) (hp5 : 5 ≤ p) {a : ZMod p} (ha : a ≠ 0) :
    ‖fullCubicExponentialSum a‖ ^ 4 ≤ 4 * (p : ℝ) ^ 3 := by
  have hsq := norm_fullCubicExponentialSum_sq_le hp hp5 ha
  have hsqrt_sq : Real.sqrt (p : ℝ) ^ 2 = p :=
    Real.sq_sqrt (Nat.cast_nonneg p)
  have hp_real : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hsqrt_one : (1 : ℝ) ≤ Real.sqrt p := by
    nlinarith [Real.sqrt_nonneg (p : ℝ)]
  have hsq' : ‖fullCubicExponentialSum a‖ ^ 2 ≤
      2 * p * Real.sqrt p := by
    nlinarith
  have hpow := pow_le_pow_left₀ (sq_nonneg ‖fullCubicExponentialSum a‖)
    hsq' 2
  calc
    ‖fullCubicExponentialSum a‖ ^ 4 =
        (‖fullCubicExponentialSum a‖ ^ 2) ^ 2 := by ring
    _ ≤ (2 * (p : ℝ) * Real.sqrt p) ^ 2 := hpow
    _ = 4 * (p : ℝ) ^ 3 := by rw [mul_pow, mul_pow, hsqrt_sq]; ring

/-- Over a prime field, removing the zero summand from the full complete
sum leaves exactly the complete sum over the units. -/
theorem fullCubicExponentialSum_eq_one_add_unit
    (hp : p.Prime) (a : ZMod p) :
    fullCubicExponentialSum a =
      1 + unitCubicExponentialSum a := by
  letI : Fact p.Prime := ⟨hp⟩
  let g : ZMod p → ℂ := fun x ↦
    standardAdditiveCharacter (a * cubicResidue x)
  have hunits : (∑ u : (ZMod p)ˣ, g u) =
      ∑ x : {x : ZMod p // x ≠ 0}, g x := by
    simpa [g] using
      (Equiv.sum_comp unitsEquivNeZero
        (fun x : {x : ZMod p // x ≠ 0} ↦ g x))
  have hpartition :=
    Fintype.sum_subtype_add_sum_subtype (fun x : ZMod p ↦ x ≠ 0) g
  have hzero : (∑ x : {x : ZMod p // ¬ x ≠ 0}, g x) = 1 := by
    letI : Unique {x : ZMod p // ¬ x ≠ 0} := {
      default := ⟨0, by simp⟩
      uniq := fun x ↦ Subtype.ext (not_ne_iff.mp x.property)
    }
    rw [Fintype.sum_unique]
    have hdefault :
        ((default : {x : ZMod p // ¬ x ≠ 0}) : ZMod p) = 0 :=
      not_ne_iff.mp (default : {x : ZMod p // ¬ x ≠ 0}).property
    rw [hdefault]
    simp [g, cubicResidue]
  unfold fullCubicExponentialSum unitCubicExponentialSum
  change (∑ x : ZMod p, g x) = 1 + ∑ u : (ZMod p)ˣ, g u
  rw [hunits, add_comm, ← hzero]
  exact hpartition.symm

/-- Consequently the unit-restricted cubic sum differs from the full sum
by exactly the zero contribution. -/
theorem unitCubicExponentialSum_eq_full_sub_one
    (hp : p.Prime) (a : ZMod p) :
    unitCubicExponentialSum a = fullCubicExponentialSum a - 1 := by
  rw [fullCubicExponentialSum_eq_one_add_unit hp]
  ring

/-- The zero-frequency unit sum is Euler's totient. -/
@[simp] theorem unitCubicExponentialSum_zero :
    unitCubicExponentialSum (0 : ZMod p) = Nat.totient p := by
  simp [unitCubicExponentialSum, ZMod.card_units_eq_totient]

/-- Exact nonzero-frequency formula for the deviation of the normalized
prime-level count from `1`. -/
theorem complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum
    (hp : p.Prime) (hp5 : 5 ≤ p) (n T : ℕ) :
    complexNormalizedUnitCubicCount p n T hp.ne_zero - 1 =
      (∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod p)))) /
        (Nat.totient p : ℂ) ^ n := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold complexNormalizedUnitCubicCount
  rw [← frequencySum_eq_modulus_mul_unitCubicSolutionCount]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  simp only [unitCubicExponentialSum_zero, zero_mul, neg_zero,
    AddChar.map_zero_eq_one, mul_one]
  have hphi_nat : Nat.totient p ≠ 0 :=
    Nat.ne_of_gt (Nat.totient_pos.mpr (by omega))
  have hphi : (Nat.totient p : ℂ) ^ n ≠ 0 :=
    pow_ne_zero n (by exact_mod_cast hphi_nat)
  field_simp
  simp [AddChar.map_zero_eq_one, mul_comm]

/-- The trivial bound for the unit-restricted complete sum. -/
theorem norm_unitCubicExponentialSum_le_totient (a : ZMod p) :
    ‖unitCubicExponentialSum a‖ ≤ Nat.totient p := by
  calc
    ‖unitCubicExponentialSum a‖ ≤
        ∑ u : (ZMod p)ˣ,
          ‖standardAdditiveCharacter
            (a * cubicResidue (u : ZMod p))‖ := by
              exact norm_sum_le _ _
    _ = ∑ _u : (ZMod p)ˣ, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro u _hu
          rw [AddChar.norm_apply]
    _ = Nat.totient p := by
          simp [ZMod.card_units_eq_totient]

/-- The fourth-power Weyl bound after restricting the variable to units.
The numerical constant is deliberately elementary; the exponent saving is
what is used by the many-variable local-factor argument. -/
theorem norm_unitCubicExponentialSum_pow_four_le
    (hp : p.Prime) (hp5 : 5 ≤ p) {a : ZMod p} (ha : a ≠ 0) :
    ‖unitCubicExponentialSum a‖ ^ 4 ≤ 40 * (p : ℝ) ^ 3 := by
  have hfull := norm_fullCubicExponentialSum_pow_four_le hp hp5 ha
  have htriangle : ‖unitCubicExponentialSum a‖ ≤
      ‖fullCubicExponentialSum a‖ + 1 := by
    rw [unitCubicExponentialSum_eq_full_sub_one hp]
    simpa using norm_sub_le (fullCubicExponentialSum a) 1
  have hpow := pow_le_pow_left₀ (norm_nonneg (unitCubicExponentialSum a))
    htriangle 4
  have haux (x : ℝ) (hx : 0 ≤ x) :
      (x + 1) ^ 4 ≤ 8 * (x ^ 4 + 1) := by
    have hfactor : 0 ≤ (x - 1) ^ 2 * (7 * x ^ 2 + 10 * x + 7) := by
      positivity
    nlinarith
  have hp_real : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have hp_cube : (1 : ℝ) ≤ (p : ℝ) ^ 3 := one_le_pow₀ hp_real
  calc
    ‖unitCubicExponentialSum a‖ ^ 4 ≤
        (‖fullCubicExponentialSum a‖ + 1) ^ 4 := hpow
    _ ≤ 8 * (‖fullCubicExponentialSum a‖ ^ 4 + 1) :=
      haux _ (norm_nonneg _)
    _ ≤ 8 * (4 * (p : ℝ) ^ 3 + 1) := by nlinarith
    _ ≤ 40 * (p : ℝ) ^ 3 := by nlinarith

/-- For at least 32 variables, the fourth-power Weyl estimate can be used
eight times and the remaining powers can be bounded trivially. -/
theorem norm_unitCubicExponentialSum_pow_le
    (hp : p.Prime) (hp5 : 5 ≤ p) {a : ZMod p} (ha : a ≠ 0)
    {n : ℕ} (hn : 32 ≤ n) :
    ‖unitCubicExponentialSum a‖ ^ n ≤
      (40 * (p : ℝ) ^ 3) ^ 8 * (p : ℝ) ^ (n - 32) := by
  have hfour := norm_unitCubicExponentialSum_pow_four_le hp hp5 ha
  have h32 : ‖unitCubicExponentialSum a‖ ^ 32 ≤
      (40 * (p : ℝ) ^ 3) ^ 8 := by
    simpa [← pow_mul] using
      (pow_le_pow_left₀ (by positivity) hfour 8)
  have htrivial : ‖unitCubicExponentialSum a‖ ≤ (p : ℝ) := by
    refine (norm_unitCubicExponentialSum_le_totient a).trans ?_
    exact_mod_cast Nat.totient_le p
  have hrest := pow_le_pow_left₀ (norm_nonneg (unitCubicExponentialSum a))
    htrivial (n - 32)
  calc
    ‖unitCubicExponentialSum a‖ ^ n =
        ‖unitCubicExponentialSum a‖ ^ 32 *
          ‖unitCubicExponentialSum a‖ ^ (n - 32) := by
            rw [← pow_add, Nat.add_sub_of_le hn]
    _ ≤ (40 * (p : ℝ) ^ 3) ^ 8 *
        (p : ℝ) ^ (n - 32) := mul_le_mul h32 hrest
      (by positivity) (by positivity)

/-- Summing the pointwise estimate over all nonzero frequencies costs at
most one factor of `p`. -/
theorem norm_nonzeroFrequencySum_le
    (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : 32 ≤ n) (T : ℕ) :
    ‖∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod p)))‖ ≤
      (p : ℝ) * (40 * (p : ℝ) ^ 3) ^ 8 *
        (p : ℝ) ^ (n - 32) := by
  let B : ℝ := (40 * (p : ℝ) ^ 3) ^ 8 * (p : ℝ) ^ (n - 32)
  have hpoint (a : ZMod p)
      (ha : a ∈ (Finset.univ : Finset (ZMod p)).erase 0) :
      ‖unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod p)))‖ ≤ B := by
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    simpa [B, norm_mul, norm_pow, AddChar.norm_apply] using
      norm_unitCubicExponentialSum_pow_le hp hp5 ha0 hn
  calc
    ‖∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod p)))‖ ≤
        ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
          ‖unitCubicExponentialSum a ^ n *
            standardAdditiveCharacter (-(a * (T : ZMod p)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _a ∈ (Finset.univ : Finset (ZMod p)).erase 0, B := by
      exact Finset.sum_le_sum fun a ha ↦ hpoint a ha
    _ ≤ (p : ℝ) * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by
          have hcard :
              ((Finset.univ : Finset (ZMod p)).erase 0).card ≤ p := by
            exact (Finset.card_le_card
              (Finset.erase_subset 0 (Finset.univ : Finset (ZMod p)))).trans_eq
                (ZMod.card p)
          exact_mod_cast hcard)
        (by positivity)
    _ = (p : ℝ) * (40 * (p : ℝ) ^ 3) ^ 8 *
        (p : ℝ) ^ (n - 32) := by simp [B, mul_assoc]

/-- Quantitative level-one local-density estimate.  Its right-hand side is
`O_n(p⁻⁷)` for `n ≥ 32`; the following theorem is entirely uniform in
the target `T`. -/
theorem norm_complexNormalizedUnitCubicCount_sub_one_le
    (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : 32 ≤ n) (T : ℕ) :
    ‖complexNormalizedUnitCubicCount p n T hp.ne_zero - 1‖ ≤
      ((p : ℝ) * (40 * (p : ℝ) ^ 3) ^ 8 *
        (p : ℝ) ^ (n - 32)) / (Nat.totient p : ℝ) ^ n := by
  rw [complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum hp hp5]
  rw [norm_div, norm_pow]
  simpa using div_le_div_of_nonneg_right
    (norm_nonzeroFrequencySum_le hp hp5 hn T)
    (norm_nonneg ((Nat.totient p : ℂ) ^ n))

/-- The same estimate with the prime totient written concretely as `p-1`. -/
theorem norm_complexNormalizedUnitCubicCount_sub_one_le_prime
    (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : 32 ≤ n) (T : ℕ) :
    ‖complexNormalizedUnitCubicCount p n T hp.ne_zero - 1‖ ≤
      ((p : ℝ) * (40 * (p : ℝ) ^ 3) ^ 8 *
        (p : ℝ) ^ (n - 32)) / ((p - 1 : ℕ) : ℝ) ^ n := by
  simpa [Nat.totient_prime hp] using
    norm_complexNormalizedUnitCubicCount_sub_one_le hp hp5 hn T

/-- A conventional power-saving form of the level-one estimate.  The
constant depends only on the fixed number of variables and the exponent
`7` is uniform in both `p` and the target. -/
theorem norm_complexNormalizedUnitCubicCount_sub_one_le_inv_pow
    (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : 32 ≤ n) (T : ℕ) :
    ‖complexNormalizedUnitCubicCount p n T hp.ne_zero - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 := by
  have hbase :=
    norm_complexNormalizedUnitCubicCount_sub_one_le_prime hp hp5 hn T
  have hp_pos : (0 : ℝ) < p := by positivity
  have hp_sub_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < p - 1 by omega)
  have hcast_sub : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  have hratio : (p : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ (5 : ℝ) / 4 := by
    rw [div_le_iff₀ hp_sub_pos]
    rw [hcast_sub]
    have hp5_real : (5 : ℝ) ≤ p := by exact_mod_cast hp5
    have hfour : (p : ℝ) * 4 ≤ 5 * ((p : ℝ) - 1) := by
      linarith
    calc
      (p : ℝ) ≤ (5 * ((p : ℝ) - 1)) / 4 :=
        (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2 hfour
      _ = (5 : ℝ) / 4 * ((p : ℝ) - 1) := by ring
  have hratio_pow := pow_le_pow_left₀ (by positivity :
      0 ≤ (p : ℝ) / ((p - 1 : ℕ) : ℝ)) hratio n
  have hp_pow : (p : ℝ) ^ n =
      (p : ℝ) ^ 32 * (p : ℝ) ^ (n - 32) := by
    rw [← pow_add, Nat.add_sub_of_le hn]
  have hrearrange :
      ((p : ℝ) * (40 * (p : ℝ) ^ 3) ^ 8 *
          (p : ℝ) ^ (n - 32)) /
          ((p - 1 : ℕ) : ℝ) ^ n =
        (40 : ℝ) ^ 8 *
          ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ n /
            (p : ℝ) ^ 7 := by
    rw [div_pow, hp_pow]
    field_simp
  calc
    ‖complexNormalizedUnitCubicCount p n T hp.ne_zero - 1‖ ≤
        ((p : ℝ) * (40 * (p : ℝ) ^ 3) ^ 8 *
          (p : ℝ) ^ (n - 32)) /
          ((p - 1 : ℕ) : ℝ) ^ n := hbase
    _ = (40 : ℝ) ^ 8 *
          ((p : ℝ) / ((p - 1 : ℕ) : ℝ)) ^ n /
            (p : ℝ) ^ 7 := hrearrange
    _ ≤ (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n /
          (p : ℝ) ^ 7 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio_pow (by positivity)) (by positivity)

/-- Real-valued version of the power-saving estimate for the normalized
finite congruence count. -/
theorem abs_normalizedUnitCubicCount_sub_one_le_inv_pow
    (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : 32 ≤ n) (T : ℕ) :
    |normalizedUnitCubicCount n (T : ZMod p) - 1| ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 := by
  have h := norm_complexNormalizedUnitCubicCount_sub_one_le_inv_pow
    hp hp5 hn T
  rw [complexNormalizedUnitCubicCount_of_real] at h
  simpa [← Complex.ofReal_one, ← Complex.ofReal_sub, Real.norm_eq_abs] using h

/-- At a prime modulus, the first singular-series coefficient is exactly
the deviation of the normalized congruence count from `1`. -/
theorem singularSeriesCoefficient_prime_eq_normalized_sub_one
    (hp : p.Prime) (hp5 : 5 ≤ p) (n T : ℕ) :
    singularSeriesCoefficient p n T hp.ne_zero =
      complexNormalizedUnitCubicCount p n T hp.ne_zero - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum hp hp5]
  let g : ZMod p → ℂ := fun a ↦
    unitCubicExponentialSum a ^ n *
      standardAdditiveCharacter (-(a * (T : ZMod p)))
  have hunits : (∑ a : (ZMod p)ˣ, g a) =
      ∑ a : {a : ZMod p // a ≠ 0}, g a := by
    simpa [g] using
      (Equiv.sum_comp unitsEquivNeZero
        (fun a : {a : ZMod p // a ≠ 0} ↦ g a))
  have hnonzero : (∑ a : {a : ZMod p // a ≠ 0}, g a) =
      ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0, g a := by
    simpa [Finset.filter_ne'] using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (ZMod p))) g (p := fun a ↦ a ≠ 0))
  unfold singularSeriesCoefficient
  change ((Nat.totient p : ℂ)⁻¹) ^ n * (∑ a : (ZMod p)ˣ, g a) =
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0, g a) /
      (Nat.totient p : ℂ) ^ n
  rw [hunits, hnonzero, inv_pow]
  simp [div_eq_mul_inv, mul_comm]

/-- Thus the first prime coefficient itself has a target-uniform
`p⁻⁷` bound once `n ≥ 32`. -/
theorem norm_singularSeriesTerm_prime_le_inv_pow
    (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ} (hn : 32 ≤ n) (T : ℕ) :
    ‖singularSeriesTerm n T p‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 := by
  rw [singularSeriesTerm_of_pos n T hp.pos]
  rw [singularSeriesCoefficient_prime_eq_normalized_sub_one hp hp5]
  exact norm_complexNormalizedUnitCubicCount_sub_one_le_inv_pow hp hp5 hn T

end CookMagyarFiniteFourier
end SystolicGrowth
