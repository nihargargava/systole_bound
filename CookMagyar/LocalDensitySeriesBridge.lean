module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.SingularSeries
public import CookMagyar.LocalCount
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

open scoped BigOperators
open Filter

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! ## Generic finite conductor partitions -/

theorem sum_over_pairwise_disjoint_conductor_blocks
    {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]
    (S : Finset ι) (K : ℕ) (block : ℕ → Finset ι) (f : ι → M)
    (hdisj : (↑(Finset.range K) : Set ℕ).PairwiseDisjoint block)
    (hcover : S = (Finset.range K).biUnion block) :
    (∑ x ∈ S, f x) = ∑ j ∈ Finset.range K, ∑ x ∈ block j, f x := by
  rw [hcover]
  exact Finset.sum_biUnion hdisj

/-! ## Explicit interface for the exact 2-adic conductor decomposition -/

/-- Data for the missing exact-conductor partition of nonzero frequencies
modulo `2^K`.  The arithmetic definition of `block` and its evaluation are
kept separate from the finite partition bookkeeping. -/
structure TwoAdicConductorBlockData (K : ℕ) [NeZero (2 ^ K)] where
  block : ℕ → Finset (ZMod (2 ^ K))
  pairwiseDisjoint :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint block
  cover_nonzero :
    (Finset.univ : Finset (ZMod (2 ^ K))).erase 0 =
      (Finset.range K).biUnion block

/-- The zero-level conductor partition is empty, since `ZMod 1` has no
nonzero frequency. -/
noncomputable def twoAdicConductorBlockData_zero : TwoAdicConductorBlockData 0 where
  block := fun _ ↦ ∅
  pairwiseDisjoint := by simp
  cover_nonzero := by
    ext x
    have hxlt := ZMod.val_lt x
    have hxlt' : x.val < 1 := by simpa [pow_zero] using hxlt
    have hxval : x.val = 0 := by omega
    have hx : x = 0 := (ZMod.val_eq_zero x).mp hxval
    simp [hx]

theorem sum_nonzero_frequencies_twoAdic_zero
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ 0) → M) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ 0))).erase 0), f a) = 0 := by
  have hzero : (Finset.univ : Finset (ZMod (2 ^ 0))).erase 0 = ∅ := by
    ext x
    have hxlt := ZMod.val_lt x
    have hxlt' : x.val < 1 := by simpa [pow_zero] using hxlt
    have hxval : x.val = 0 := by omega
    have hx : x = 0 := (ZMod.val_eq_zero x).mp hxval
    simp [hx]
  rw [hzero]
  simp

/-- The first nontrivial level has one conductor block, consisting of the
unique nonzero element of `ZMod 2`. -/
noncomputable def twoAdicConductorBlockData_one : TwoAdicConductorBlockData 1 where
  block := fun j ↦ if j = 0 then {1} else ∅
  pairwiseDisjoint := by
    intro i hi j hj hij
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    exfalso
    apply hij
    exact hi0.trans hj0.symm
  cover_nonzero := by
    ext x
    constructor
    · intro hx
      have hxne : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have hxlt := ZMod.val_lt x
      norm_num [pow_one] at hxlt
      have hxval0 : x.val ≠ 0 := by
        intro hxval
        apply hxne
        exact (ZMod.val_eq_zero x).mp hxval
      have hxval : x.val = 1 := by omega
      have hxone : x = 1 :=
        (ZMod.val_eq_one (n := 2) (by norm_num) x).mp hxval
      simp [hxone]
    · intro hx
      have hxone : x = 1 := by simpa using hx
      subst x
      simp

/-- Any exact 2-adic conductor block data decomposes the nonzero Fourier sum
without further assumptions. -/
theorem sum_nonzero_frequencies_by_twoAdic_conductor_blocks
    {K : ℕ} [NeZero (2 ^ K)] (D : TwoAdicConductorBlockData K)
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ K) → M) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0), f a) =
      ∑ j ∈ Finset.range K, ∑ a ∈ D.block j, f a := by
  exact sum_over_pairwise_disjoint_conductor_blocks
    ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0) K D.block f
    D.pairwiseDisjoint D.cover_nonzero

theorem sum_nonzero_frequencies_twoAdic_one
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ 1) → M) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ 1))).erase 0), f a) = f 1 := by
  have h := sum_nonzero_frequencies_by_twoAdic_conductor_blocks
    twoAdicConductorBlockData_one f
  simpa [twoAdicConductorBlockData_one] using h

/-- The second finite level has the two expected 2-adic conductor blocks:
frequency `2` and the odd frequencies `1, 3`. -/
noncomputable def twoAdicConductorBlockData_two : TwoAdicConductorBlockData 2 where
  block := fun j ↦ if j = 0 then {2} else if j = 1 then {1, 3} else ∅
  pairwiseDisjoint := by
    intro i hi j hj hij
    have hi_le : i ≤ 1 := by simpa using hi
    have hj_le : j ≤ 1 := by simpa using hj
    have hi' : i = 0 ∨ i = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hi_le
    have hj' : j = 0 ∨ j = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hj_le
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp_all [Function.onFun] <;> decide
  cover_nonzero := by
    decide

theorem sum_nonzero_frequencies_twoAdic_two
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ 2) → M) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ 2))).erase 0), f a) =
      f 2 + ∑ a ∈ ({1, 3} : Finset (ZMod (2 ^ 2))), f a := by
  have h := sum_nonzero_frequencies_by_twoAdic_conductor_blocks
    twoAdicConductorBlockData_two f
  simpa [twoAdicConductorBlockData_two, Finset.sum_range_succ] using h

/-! The third finite level provides the next concrete induction check: the
frequency classes split into `4`, the even nonmultiples `{2, 6}`, and the odd
class `{1, 3, 5, 7}` modulo `8`. -/

noncomputable def twoAdicConductorBlockData_three : TwoAdicConductorBlockData 3 where
  block := fun j ↦
    if j = 0 then {4} else if j = 1 then {2, 6} else if j = 2 then {1, 3, 5, 7} else ∅
  pairwiseDisjoint := by
    intro i hi j hj hij
    have hi_lt : i < 3 := by simpa using hi
    have hj_lt : j < 3 := by simpa using hj
    have hi_le : i ≤ 2 := by omega
    have hj_le : j ≤ 2 := by omega
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi' with rfl | rfl | rfl <;>
      rcases hj' with rfl | rfl | rfl <;>
        simp_all [Function.onFun] <;> decide
  cover_nonzero := by
    decide

theorem sum_nonzero_frequencies_twoAdic_three
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ 3) → M) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ 3))).erase 0), f a) =
      f 4 + (∑ a ∈ ({2, 6} : Finset (ZMod (2 ^ 3))), f a) +
        ∑ a ∈ ({1, 3, 5, 7} : Finset (ZMod (2 ^ 3))), f a := by
  have h := sum_nonzero_frequencies_by_twoAdic_conductor_blocks
    twoAdicConductorBlockData_three f
  simpa [twoAdicConductorBlockData_three, Finset.sum_range_succ] using h

/-! ## General exact-order conductor blocks -/

/-- The canonical `j`-th conductor block consists of frequencies whose
additive order is exactly `2^(j+1)`.  This definition is independent of any
choice of representatives in `ZMod (2^K)`. -/
noncomputable def exactTwoAdicConductorBlock (K j : ℕ) [NeZero (2 ^ K)] :
    Finset (ZMod (2 ^ K)) :=
  Finset.filter (fun a => addOrderOf a = 2 ^ (j + 1)) Finset.univ

theorem exactTwoAdicConductorBlock_mem_iff
    {K j : ℕ} [NeZero (2 ^ K)] (a : ZMod (2 ^ K)) :
    a ∈ exactTwoAdicConductorBlock K j ↔ addOrderOf a = 2 ^ (j + 1) := by
    simp [exactTwoAdicConductorBlock]

/-! The exact-order filter has the expected number of frequencies.  This is
the first arithmetic input needed when a block sum is evaluated by a
primitive-character parametrization. -/

theorem exactTwoAdicConductorBlock_card
    {K j : ℕ} [NeZero (2 ^ K)] (hj : j < K) :
    (exactTwoAdicConductorBlock K j).card = Nat.totient (2 ^ (j + 1)) := by
  classical
  rw [show exactTwoAdicConductorBlock K j =
      Finset.filter (fun a : ZMod (2 ^ K) => addOrderOf a = 2 ^ (j + 1))
        Finset.univ by rfl]
  have hpow : 2 ^ (j + 1) ∣ 2 ^ K := Nat.pow_dvd_pow 2 (by omega)
  simpa using
    (IsAddCyclic.card_addOrderOf_eq_totient
      (α := ZMod (2 ^ K)) (d := 2 ^ (j + 1))
      (by simpa [ZMod.card] using hpow))

/-- The primitive-frequency multiplicity at 2-adic conductor `j + 1` is
exactly `2^j`. -/
theorem totient_two_pow_succ (j : ℕ) :
    Nat.totient (2 ^ (j + 1)) = 2 ^ j := by
  simpa using (Nat.totient_prime_pow_succ Nat.prime_two j)

/-- The `j`-th exact 2-adic conductor block has `2^j` frequencies. -/
theorem exactTwoAdicConductorBlock_card_eq_pow
    {K j : ℕ} [NeZero (2 ^ K)] (hj : j < K) :
    (exactTwoAdicConductorBlock K j).card = 2 ^ j := by
  rw [exactTwoAdicConductorBlock_card hj, totient_two_pow_succ]

/-- A block on which a finite Fourier summand is constant contributes its
primitive-frequency multiplicity times that common value.  This is the
coefficient-evaluation interface: analytic or stationary-phase work need
only establish the displayed constancy hypothesis for a given conductor. -/
theorem sum_exactTwoAdicConductorBlock_eq_totient_nsmul
    {K j : ℕ} [NeZero (2 ^ K)] {M : Type*} [AddCommMonoid M]
    (hj : j < K) (f : ZMod (2 ^ K) → M) (c : M)
    (hconst : ∀ a ∈ exactTwoAdicConductorBlock K j, f a = c) :
    (∑ a ∈ exactTwoAdicConductorBlock K j, f a) =
      Nat.totient (2 ^ (j + 1)) • c := by
  calc
    (∑ a ∈ exactTwoAdicConductorBlock K j, f a) =
        ∑ _a ∈ exactTwoAdicConductorBlock K j, c := by
          exact Finset.sum_congr rfl (fun a ha ↦ hconst a ha)
    _ = (exactTwoAdicConductorBlock K j).card • c := by simp
    _ = Nat.totient (2 ^ (j + 1)) • c := by
      rw [exactTwoAdicConductorBlock_card hj]

/-- The 2-adic specialization of
`sum_exactTwoAdicConductorBlock_eq_totient_nsmul`, with the multiplicity
written as the explicit power `2^j`. -/
theorem sum_exactTwoAdicConductorBlock_eq_pow_nsmul
    {K j : ℕ} [NeZero (2 ^ K)] {M : Type*} [AddCommMonoid M]
    (hj : j < K) (f : ZMod (2 ^ K) → M) (c : M)
    (hconst : ∀ a ∈ exactTwoAdicConductorBlock K j, f a = c) :
    (∑ a ∈ exactTwoAdicConductorBlock K j, f a) = 2 ^ j • c := by
  rw [sum_exactTwoAdicConductorBlock_eq_totient_nsmul hj f c hconst,
    totient_two_pow_succ]

/-- The normalized exact-order block coefficient.  Unlike a stationary-phase
formula, this is defined unconditionally from the finite Fourier summand;
the preceding theorems identify it with any subsequently proved common
block value. -/
noncomputable def exactTwoAdicConductorCoefficient
    (K j : ℕ) [NeZero (2 ^ K)] (f : ZMod (2 ^ K) → ℂ) : ℂ :=
  ((2 ^ j : ℕ) : ℂ)⁻¹ *
    ∑ a ∈ exactTwoAdicConductorBlock K j, f a

/-- Each exact-order block is its cardinality times its normalized
coefficient. -/
theorem sum_exactTwoAdicConductorBlock_eq_pow_mul_coefficient
    {K j : ℕ} [NeZero (2 ^ K)] (f : ZMod (2 ^ K) → ℂ) :
    (∑ a ∈ exactTwoAdicConductorBlock K j, f a) =
      ((2 ^ j : ℕ) : ℂ) * exactTwoAdicConductorCoefficient K j f := by
  have hpow : ((2 ^ j : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero j (by norm_num : (2 : ℕ) ≠ 0)
  rw [exactTwoAdicConductorCoefficient, ← mul_assoc, mul_inv_cancel₀ hpow, one_mul]

theorem exactTwoAdicConductorBlock_pairwiseDisjoint
    (K : ℕ) [NeZero (2 ^ K)] :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint
      (fun j => exactTwoAdicConductorBlock K j) := by
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr ?_
  intro a hai haj
  have hai' := (exactTwoAdicConductorBlock_mem_iff a).mp hai
  have haj' := (exactTwoAdicConductorBlock_mem_iff a).mp haj
  apply hij
  have heq : i + 1 = j + 1 :=
    (Nat.pow_right_injective (by decide : 2 ≤ 2)) (hai'.symm.trans haj')
  omega

theorem exactTwoAdicConductorBlock_cover
    (K : ℕ) [NeZero (2 ^ K)] :
    (Finset.univ : Finset (ZMod (2 ^ K))).erase 0 =
      (Finset.range K).biUnion (fun j => exactTwoAdicConductorBlock K j) := by
  ext a
  constructor
  · intro ha
    have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hdiv : addOrderOf a ∣ 2 ^ K := by
      simpa using (addOrderOf_dvd_card (x := a))
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    have hk_pos : 0 < k := by
      by_contra hk0
      have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk0
      apply hane
      have horder_one : addOrderOf (0 : ZMod (2 ^ K)) = 1 :=
        AddMonoid.addOrderOf_eq_one_iff.mpr rfl
      have hzeroeq : addOrderOf a = 1 := by simpa [hk_zero] using hk_eq
      have : a = 0 := AddMonoid.addOrderOf_eq_one_iff.mp hzeroeq
      exact this
    let j := k - 1
    have hjK : j < K := by omega
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjK, ?_⟩
    apply (exactTwoAdicConductorBlock_mem_iff a).mpr
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk_pos)), hk_eq]
  · intro ha
    obtain ⟨j, hj, hja⟩ := Finset.mem_biUnion.mp ha
    have horder := (exactTwoAdicConductorBlock_mem_iff a).mp hja
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hzero
    have horder_one : addOrderOf (0 : ZMod (2 ^ K)) = 1 :=
      AddMonoid.addOrderOf_eq_one_iff.mpr rfl
    have hbad : (1 : ℕ) = 2 ^ (j + 1) := by
      simpa [hzero, horder_one] using horder
    have hpow : 1 < (2 : ℕ) ^ (j + 1) :=
      Nat.one_lt_pow (by omega) (by omega)
    omega

/-- Exact-order blocks form the canonical assumption-free conductor data at
every nonzero 2-power modulus. -/
noncomputable def exactTwoAdicConductorBlockData (K : ℕ) [NeZero (2 ^ K)] :
    TwoAdicConductorBlockData K where
  block := fun j => exactTwoAdicConductorBlock K j
  pairwiseDisjoint := exactTwoAdicConductorBlock_pairwiseDisjoint K
  cover_nonzero := exactTwoAdicConductorBlock_cover K

theorem sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks
    {K : ℕ} [NeZero (2 ^ K)]
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ K) → M) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0), f a) =
      ∑ j ∈ Finset.range K,
        ∑ a ∈ exactTwoAdicConductorBlock K j, f a := by
  exact sum_nonzero_frequencies_by_twoAdic_conductor_blocks
    (exactTwoAdicConductorBlockData K) f

/-- Once the finite Fourier summand has a conductor-wise evaluation, the
entire nonzero frequency sum is a totient-weighted finite coefficient sum.
This separates the universal exact-order bookkeeping from the remaining
analytic evaluation of the common block values. -/
theorem sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks_eq_totient_coefficients
    {K : ℕ} [NeZero (2 ^ K)]
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ K) → M) (coeff : ℕ → M)
    (hcoeff : ∀ j ∈ Finset.range K,
      ∀ a ∈ exactTwoAdicConductorBlock K j, f a = coeff j) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0), f a) =
      ∑ j ∈ Finset.range K, Nat.totient (2 ^ (j + 1)) • coeff j := by
  rw [sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks f]
  refine Finset.sum_congr rfl ?_
  intro j hj
  exact sum_exactTwoAdicConductorBlock_eq_totient_nsmul
    (Finset.mem_range.mp hj) f (coeff j) (hcoeff j hj)

/-- The same conductor-wise coefficient evaluation with the 2-adic
multiplicities simplified to powers of two. -/
theorem sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks_eq_pow_coefficients
    {K : ℕ} [NeZero (2 ^ K)]
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ K) → M) (coeff : ℕ → M)
    (hcoeff : ∀ j ∈ Finset.range K,
      ∀ a ∈ exactTwoAdicConductorBlock K j, f a = coeff j) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0), f a) =
      ∑ j ∈ Finset.range K, 2 ^ j • coeff j := by
  rw [sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks_eq_totient_coefficients
    f coeff hcoeff]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [totient_two_pow_succ]

/-- The unconditional two-adic conductor decomposition of a complex finite
Fourier sum, expressed using the normalized block coefficients above. -/
theorem sum_nonzero_frequencies_by_exact_twoAdic_conductor_coefficients
    {K : ℕ} [NeZero (2 ^ K)] (f : ZMod (2 ^ K) → ℂ) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0), f a) =
      ∑ j ∈ Finset.range K,
        ((2 ^ j : ℕ) : ℂ) * exactTwoAdicConductorCoefficient K j f := by
  rw [sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks f]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  exact sum_exactTwoAdicConductorBlock_eq_pow_mul_coefficient f

/-- If each conductor block has already been evaluated, the full nonzero
Fourier sum is the corresponding finite sum of block coefficients. -/
theorem sum_nonzero_frequencies_by_twoAdic_conductor_blocks_eq_coefficients
    {K : ℕ} [NeZero (2 ^ K)] (D : TwoAdicConductorBlockData K)
    {M : Type*} [AddCommMonoid M] (f : ZMod (2 ^ K) → M)
    (coeff : ℕ → M)
    (hcoeff : ∀ j ∈ Finset.range K,
      (∑ a ∈ D.block j, f a) = coeff j) :
    (∑ a ∈ ((Finset.univ : Finset (ZMod (2 ^ K))).erase 0), f a) =
      ∑ j ∈ Finset.range K, coeff j := by
  rw [sum_nonzero_frequencies_by_twoAdic_conductor_blocks D f]
  exact Finset.sum_congr rfl (fun j hj ↦ hcoeff j hj)

/-! ## All-frequency form of the finite Fourier identity -/

theorem complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum_all_moduli
    {q : ℕ} [NeZero q] (n T : ℕ) :
    complexNormalizedUnitCubicCount q n T (NeZero.ne q) - 1 =
      (∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod q)))) /
        (Nat.totient q : ℂ) ^ n := by
  unfold complexNormalizedUnitCubicCount
  rw [← frequencySum_eq_modulus_mul_unitCubicSolutionCount]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))]
  have hzero : unitCubicExponentialSum (0 : ZMod q) = Nat.totient q := by
    simp [unitCubicExponentialSum, ZMod.card_units_eq_totient]
  rw [hzero]
  simp [AddChar.map_zero_eq_one]
  have hphi_nat : Nat.totient q ≠ 0 :=
    Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q)))
  have hphi : (Nat.totient q : ℂ) ^ n ≠ 0 :=
    pow_ne_zero n (by exact_mod_cast hphi_nat)
  field_simp
  simp

/-- A conductor-wise stationary-phase evaluation at a two-power modulus
turns the normalized finite cubic count into an explicit finite sum with
weights `2^j`.  The only remaining input is the common value of the actual
Fourier summand on each exact-order block. -/
theorem complexNormalizedUnitCubicCount_sub_one_eq_twoAdic_conductor_coefficients
    {K : ℕ} [NeZero (2 ^ K)] (n T : ℕ) (coeff : ℕ → ℂ)
    (hcoeff : ∀ j ∈ Finset.range K,
      ∀ a ∈ exactTwoAdicConductorBlock K j,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod (2 ^ K)))) = coeff j) :
    complexNormalizedUnitCubicCount (2 ^ K) n T (NeZero.ne (2 ^ K)) - 1 =
      (∑ j ∈ Finset.range K, 2 ^ j • coeff j) /
        (Nat.totient (2 ^ K) : ℂ) ^ n := by
  rw [complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum_all_moduli n T]
  rw [sum_nonzero_frequencies_by_exact_twoAdic_conductor_blocks_eq_pow_coefficients
    (fun a ↦ unitCubicExponentialSum a ^ n *
      standardAdditiveCharacter (-(a * (T : ZMod (2 ^ K))))) coeff hcoeff]

/-- The same normalized finite-count identity without an evaluation
hypothesis: the exact 2-adic block coefficients package all frequency
dependence into explicit conductor-indexed complex numbers. -/
theorem complexNormalizedUnitCubicCount_sub_one_eq_twoAdic_conductor_coefficient_sum
    {K : ℕ} [NeZero (2 ^ K)] (n T : ℕ) :
    complexNormalizedUnitCubicCount (2 ^ K) n T (NeZero.ne (2 ^ K)) - 1 =
      (∑ j ∈ Finset.range K,
        ((2 ^ j : ℕ) : ℂ) * exactTwoAdicConductorCoefficient K j
          (fun a ↦ unitCubicExponentialSum a ^ n *
            standardAdditiveCharacter (-(a * (T : ZMod (2 ^ K)))))) /
        (Nat.totient (2 ^ K) : ℂ) ^ n := by
  rw [complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum_all_moduli n T]
  rw [sum_nonzero_frequencies_by_exact_twoAdic_conductor_coefficients]

/-! # Convergence interface for local factors

The formal local factor is a sum of prime-power coefficients.  Once finite
prime-power counts are shown to equal its partial sums, the following lemma
identifies their limiting density with the local factor.  It isolates the
analytic convergence step from the missing finite Fourier partition.
-/

theorem primeLocalFactor_eq_limit_of_partial_sums
    {p n T : ℕ} {mu : ℂ}
    (hsum : Summable (fun k : ℕ ↦ singularSeriesTerm n T (p ^ (k + 1))))
    (hpartial : Tendsto
      (fun K : ℕ ↦
        (1 : ℂ) + ∑ k ∈ Finset.range K,
          singularSeriesTerm n T (p ^ (k + 1)))
      Filter.atTop (nhds mu)) :
    primeLocalFactor p n T = mu := by
  have hseries : Tendsto
      (fun K : ℕ ↦ ∑ k ∈ Finset.range K,
        singularSeriesTerm n T (p ^ (k + 1)))
      Filter.atTop (nhds (∑' k : ℕ,
        singularSeriesTerm n T (p ^ (k + 1)))) := by
    exact hsum.hasSum.tendsto_sum_nat
  have hcanonical : Tendsto
      (fun K : ℕ ↦
        (1 : ℂ) + ∑ k ∈ Finset.range K,
          singularSeriesTerm n T (p ^ (k + 1)))
      Filter.atTop
      (nhds ((1 : ℂ) + ∑' k : ℕ,
        singularSeriesTerm n T (p ^ (k + 1)))) := by
    simpa using
      (tendsto_const_nhds.add hseries)
  have hlim : mu = (1 : ℂ) + ∑' k : ℕ,
      singularSeriesTerm n T (p ^ (k + 1)) :=
    tendsto_nhds_unique hpartial hcanonical
  unfold primeLocalFactor
  rw [hlim]

end CookMagyarFiniteFourier
end SystolicGrowth
