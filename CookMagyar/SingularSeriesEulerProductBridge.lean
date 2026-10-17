module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.PrimePowerConductorFourierBridge
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.SumPrimeReciprocals

@[expose] public section

open scoped BigOperators
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Toward the Euler product for the cubic singular series

The normalized finite solution count is multiplicative by the exact CRT
equivalence.  The remaining arithmetic bridge identifies it with the divisor
sum of the primitive-frequency coefficients; Dirichlet inversion then gives
the multiplicativity required by the Euler-product theorem.
-/

/-- The normalized finite cubic count is multiplicative in coprime positive
moduli, with the same integer target reduced at both factors. -/
theorem complexNormalizedUnitCubicCount_mul_of_coprime
    {q₁ q₂ n T : ℕ} (hq₁ : q₁ ≠ 0) (hq₂ : q₂ ≠ 0)
    (hcop : q₁.Coprime q₂) :
    complexNormalizedUnitCubicCount (q₁ * q₂) n T (mul_ne_zero hq₁ hq₂) =
      complexNormalizedUnitCubicCount q₁ n T hq₁ *
        complexNormalizedUnitCubicCount q₂ n T hq₂ := by
  letI : NeZero q₁ := ⟨hq₁⟩
  letI : NeZero q₂ := ⟨hq₂⟩
  letI : NeZero (q₁ * q₂) := ⟨mul_ne_zero hq₁ hq₂⟩
  unfold complexNormalizedUnitCubicCount
  rw [unitCubicSolutionCount_mul_of_coprime_natCast n T hcop,
    Nat.totient_mul hcop]
  push_cast
  ring

/-! ## Exact conductors at an arbitrary positive modulus -/

/-- Frequencies of exact additive order `d` at modulus `q`. -/
noncomputable def exactConductorBlock (q d : ℕ) [NeZero q] :
    Finset (ZMod q) :=
  Finset.filter (fun a ↦ addOrderOf a = d) Finset.univ

@[simp] theorem mem_exactConductorBlock_iff
    {q d : ℕ} [NeZero q] (a : ZMod q) :
    a ∈ exactConductorBlock q d ↔ addOrderOf a = d := by
  simp [exactConductorBlock]

private theorem modulus_factor {q d : ℕ} (hdvd : d ∣ q) :
    q = (q / d) * d := by
  simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdvd).symm

/-- A primitive residue at conductor `d` embedded as a frequency at the
ambient modulus `q`, where `d ∣ q`. -/
noncomputable def primitiveConductorLift (q d : ℕ)
    (u : (ZMod d)ˣ) : ZMod q :=
  ((q / d * (u : ZMod d).val : ℕ) : ZMod q)

theorem addOrderOf_primitiveConductorLift
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (u : (ZMod d)ˣ) :
    addOrderOf (primitiveConductorLift q d u) = d := by
  have hq : q ≠ 0 := NeZero.ne q
  have hd : d ≠ 0 := NeZero.ne d
  have hfactor := modulus_factor hdvd
  have hscale_pos : 0 < q / d := by
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd)
      (Nat.pos_of_ne_zero hd)
  have hunit : (u : ZMod d).val.Coprime d := ZMod.val_coe_unit_coprime u
  let scale := q / d
  have hfactor' : q = scale * d := hfactor
  rw [primitiveConductorLift, ZMod.addOrderOf_coe _ hq]
  have hgcd : q.gcd (scale * (u : ZMod d).val) = scale := by
    rw [hfactor', Nat.gcd_mul_left]
    rw [Nat.gcd_comm d, hunit.gcd_eq_one, mul_one]
  rw [hgcd]
  change q / scale = d
  rw [hfactor']
  exact Nat.mul_div_right _ hscale_pos

theorem primitiveConductorLift_injective
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q) :
    Function.Injective (primitiveConductorLift q d) := by
  intro u v huv
  let scale := q / d
  have hfactor := modulus_factor hdvd
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd)
      (Nat.pos_of_ne_zero (NeZero.ne d))
  have hu_lt : scale * (u : ZMod d).val < q := by
    rw [hfactor]
    exact (Nat.mul_lt_mul_left hscale_pos).mpr (ZMod.val_lt _)
  have hv_lt : scale * (v : ZMod d).val < q := by
    rw [hfactor]
    exact (Nat.mul_lt_mul_left hscale_pos).mpr (ZMod.val_lt _)
  have hval : scale * (u : ZMod d).val = scale * (v : ZMod d).val := by
    have h := congrArg ZMod.val huv
    have huval : (primitiveConductorLift q d u).val =
        scale * (u : ZMod d).val := by
      unfold primitiveConductorLift
      exact ZMod.val_natCast_of_lt (by simpa [scale] using hu_lt)
    have hvval : (primitiveConductorLift q d v).val =
        scale * (v : ZMod d).val := by
      unfold primitiveConductorLift
      exact ZMod.val_natCast_of_lt (by simpa [scale] using hv_lt)
    exact huval.symm.trans (h.trans hvval)
  apply Units.ext
  apply ZMod.val_injective d
  exact Nat.mul_left_cancel hscale_pos hval

theorem exactConductorBlock_card
    {q d : ℕ} [NeZero q] (hdvd : d ∣ q) :
    (exactConductorBlock q d).card = Nat.totient d := by
  classical
  simpa [exactConductorBlock] using
    (IsAddCyclic.card_addOrderOf_eq_totient
      (α := ZMod q) (d := d) (by simpa [ZMod.card] using hdvd))

theorem exactConductorBlock_eq_primitive_image
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q) :
    exactConductorBlock q d =
      Finset.univ.image (primitiveConductorLift q d) := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨u, -, rfl⟩
    exact (mem_exactConductorBlock_iff _).mpr
      (addOrderOf_primitiveConductorLift hdvd u)
  · rw [exactConductorBlock_card hdvd,
      Finset.card_image_of_injective _ (primitiveConductorLift_injective hdvd),
      Finset.card_univ]
    simp [ZMod.card_units_eq_totient]

theorem sum_exactConductorBlock_eq_sum_units
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    {M : Type*} [AddCommMonoid M] (f : ZMod q → M) :
    (∑ a ∈ exactConductorBlock q d, f a) =
      ∑ u : (ZMod d)ˣ, f (primitiveConductorLift q d u) := by
  classical
  rw [exactConductorBlock_eq_primitive_image hdvd]
  exact Finset.sum_image (fun u hu v hv h ↦
    primitiveConductorLift_injective hdvd h)

private theorem stdAddChar_primitiveConductorLift
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (u : (ZMod d)ˣ) (x : ZMod q) :
    standardAdditiveCharacter (primitiveConductorLift q d u * x) =
      standardAdditiveCharacter ((u : ZMod d) * (x.cast : ZMod d)) := by
  let scale := q / d
  have hfactor : q = scale * d := modulus_factor hdvd
  have hcharacter (v : ℕ) :
      ZMod.stdAddChar ((scale * v : ℕ) : ZMod q) =
        ZMod.stdAddChar (v : ZMod d) := by
    rw [← Int.cast_natCast (scale * v), ← Int.cast_natCast v]
    rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
    congr 1
    rw [hfactor]
    push_cast
    have hs : (scale : ℂ) ≠ 0 := by
      exact_mod_cast (by
        dsimp [scale]
        exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd
          (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd)
          (Nat.pos_of_ne_zero (NeZero.ne d))))
    have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    field_simp [hs, hd]
  calc
    standardAdditiveCharacter (primitiveConductorLift q d u * x) =
        ZMod.stdAddChar
          ((scale * ((u : ZMod d).val * x.val) : ℕ) : ZMod q) := by
            congr 1
            change (((scale * (u : ZMod d).val : ℕ) : ZMod q) * x) = _
            conv_lhs => rw [← ZMod.natCast_zmod_val x]
            norm_cast
            simp only [Nat.mul_assoc]
    _ = ZMod.stdAddChar (((u : ZMod d).val * x.val : ℕ) : ZMod d) :=
      hcharacter _
    _ = standardAdditiveCharacter ((u : ZMod d) * (x.cast : ZMod d)) := by
      congr 1
      simp only [ZMod.cast_eq_val, Nat.cast_mul, ZMod.natCast_zmod_val]

def Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction {q d : ℕ} (hdvd : d ∣ q) :
    (ZMod q)ˣ →* (ZMod d)ˣ :=
  ZMod.unitsMap hdvd

def Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard {q d : ℕ} [NeZero q] [NeZero d]
    (hdvd : d ∣ q) : ℕ :=
  Fintype.card {x : (ZMod q)ˣ // Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd x = 1}

private theorem conductorUnitReduction_fiber_card
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (y : (ZMod d)ˣ) :
    Fintype.card {x : (ZMod q)ˣ // Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd x = y} =
      Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd := by
  let red := Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd
  have hsurj : Function.Surjective red := ZMod.unitsMap_surjective hdvd
  have h := MonoidHom.card_fiber_eq_of_mem_range red (hsurj y) (hsurj 1)
  simpa [Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard, Fintype.card_subtype] using h

private theorem totient_eq_totient_mul_conductorUnitFiberCard
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q) :
    Nat.totient q = Nat.totient d * Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd := by
  let red := Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd
  have htotal :
      Fintype.card ((ZMod q)ˣ) =
        Fintype.card (Σ z : (ZMod d)ˣ,
          {x : (ZMod q)ˣ // red x = z}) :=
    Fintype.card_congr (Equiv.sigmaFiberEquiv red).symm
  calc
    Nat.totient q = Fintype.card ((ZMod q)ˣ) :=
      (ZMod.card_units_eq_totient _).symm
    _ = Fintype.card (Σ z : (ZMod d)ˣ,
          {x : (ZMod q)ˣ // red x = z}) := htotal
    _ = ∑ z : (ZMod d)ˣ,
          Fintype.card {x : (ZMod q)ˣ // red x = z} := Fintype.card_sigma
    _ = ∑ _z : (ZMod d)ˣ, Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact conductorUnitReduction_fiber_card hdvd z
    _ = Nat.totient d * Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd := by
      simp [ZMod.card_units_eq_totient]

private theorem sum_conductorUnitReduction
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (f : (ZMod d)ˣ → ℂ) :
    (∑ x : (ZMod q)ˣ, f (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd x)) =
      (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) * ∑ y : (ZMod d)ˣ, f y := by
  let red := Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd
  calc
    (∑ x : (ZMod q)ˣ, f (red x)) =
        ∑ y : (ZMod d)ˣ,
          ∑ x : {x : (ZMod q)ˣ // red x = y}, f y := by
      rw [← (Equiv.sigmaFiberEquiv red).sum_comp (fun x ↦ f (red x)),
        Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x _hx
      change f (red x.val) = f y
      rw [x.property]
    _ = ∑ y : (ZMod d)ˣ,
          (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) * f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_const, Finset.card_univ,
        conductorUnitReduction_fiber_card hdvd y]
      simp only [nsmul_eq_mul]
    _ = (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) *
          ∑ y : (ZMod d)ˣ, f y := by
      rw [Finset.mul_sum]

private theorem conductorUnitReduction_cubicResidue
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (x : (ZMod q)ˣ) :
    ((cubicResidue (x : ZMod q)).cast : ZMod d) =
      cubicResidue ((Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd x : (ZMod d)ˣ) : ZMod d) := by
  let red : ZMod q →+* ZMod d := ZMod.castHom hdvd (ZMod d)
  change red (cubicResidue (x : ZMod q)) =
    cubicResidue (red (x : ZMod q))
  simp [cubicResidue]

theorem unitCubicExponentialSum_primitiveConductorLift
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (u : (ZMod d)ˣ) :
    unitCubicExponentialSum (primitiveConductorLift q d u) =
      (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) *
        unitCubicExponentialSum (u : ZMod d) := by
  calc
    unitCubicExponentialSum (primitiveConductorLift q d u) =
        ∑ x : (ZMod q)ˣ,
          standardAdditiveCharacter
            ((u : ZMod d) *
              cubicResidue ((Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitReduction hdvd x : (ZMod d)ˣ) :
                ZMod d)) := by
      unfold unitCubicExponentialSum
      apply Finset.sum_congr rfl
      intro x _hx
      rw [stdAddChar_primitiveConductorLift hdvd,
        conductorUnitReduction_cubicResidue hdvd x]
    _ = (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) *
          unitCubicExponentialSum (u : ZMod d) := by
      exact sum_conductorUnitReduction hdvd (fun y ↦
        standardAdditiveCharacter
          ((u : ZMod d) * cubicResidue (y : ZMod d)))

theorem standardAdditiveCharacter_primitiveConductorLift_target
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q)
    (u : (ZMod d)ˣ) (T : ℕ) :
    standardAdditiveCharacter
        (-(primitiveConductorLift q d u * (T : ZMod q))) =
      standardAdditiveCharacter (-((u : ZMod d) * (T : ZMod d))) := by
  rw [← mul_neg, stdAddChar_primitiveConductorLift hdvd]
  simp only [ZMod.cast_neg hdvd, ZMod.cast_natCast hdvd, mul_neg]

theorem sum_exactConductorBlock_fourier_eq_conductor_sum
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q) (n T : ℕ) :
    (∑ a ∈ exactConductorBlock q d,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod q)))) =
      (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) ^ n *
        ∑ u : (ZMod d)ˣ,
          unitCubicExponentialSum (u : ZMod d) ^ n *
            standardAdditiveCharacter (-((u : ZMod d) * (T : ZMod d))) := by
  rw [sum_exactConductorBlock_eq_sum_units hdvd]
  calc
    (∑ u : (ZMod d)ˣ,
        unitCubicExponentialSum (primitiveConductorLift q d u) ^ n *
          standardAdditiveCharacter
            (-(primitiveConductorLift q d u * (T : ZMod q)))) =
        ∑ u : (ZMod d)ˣ,
          (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) ^ n *
            (unitCubicExponentialSum (u : ZMod d) ^ n *
              standardAdditiveCharacter (-((u : ZMod d) * (T : ZMod d)))) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [unitCubicExponentialSum_primitiveConductorLift hdvd,
        standardAdditiveCharacter_primitiveConductorLift_target hdvd, mul_pow]
      ring
    _ = (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ) ^ n *
          ∑ u : (ZMod d)ˣ,
            unitCubicExponentialSum (u : ZMod d) ^ n *
              standardAdditiveCharacter (-((u : ZMod d) * (T : ZMod d))) := by
      rw [Finset.mul_sum]

/-- The exact-order block in the normalized Fourier count at `q` equals
the primitive singular-series coefficient at its conductor `d`. -/
theorem exactConductorBlock_normalized_eq_singularSeriesTerm
    {q d : ℕ} [NeZero q] [NeZero d] (hdvd : d ∣ q) (n T : ℕ) :
    (∑ a ∈ exactConductorBlock q d,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod q)))) /
      (Nat.totient q : ℂ) ^ n = singularSeriesTerm n T d := by
  rw [sum_exactConductorBlock_fourier_eq_conductor_sum hdvd n T,
    singularSeriesTerm_of_pos n T (Nat.pos_of_ne_zero (NeZero.ne d))]
  let fiber : ℂ := (Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd : ℂ)
  let phi : ℂ := (Nat.totient d : ℂ)
  let S : ℂ := ∑ u : (ZMod d)ˣ,
    unitCubicExponentialSum (u : ZMod d) ^ n *
      standardAdditiveCharacter (-((u : ZMod d) * (T : ZMod d)))
  change fiber ^ n * S / (Nat.totient q : ℂ) ^ n = phi⁻¹ ^ n * S
  have hfactor_nat := totient_eq_totient_mul_conductorUnitFiberCard hdvd
  have hfactor : (Nat.totient q : ℂ) = fiber * phi := by
    simpa [fiber, phi, mul_comm] using
      congrArg (fun m : ℕ ↦ (m : ℂ)) hfactor_nat
  have hfiber : fiber ≠ 0 := by
    dsimp [fiber]
    have hφq : 0 < Nat.totient q :=
      Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
    have hfiber_nat : Internal.SingularSeriesEulerProductBridgeHelpers.conductorUnitFiberCard hdvd ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hfactor_nat
      omega
    exact_mod_cast hfiber_nat
  rw [hfactor, mul_pow, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (fiber ^ n * (fiber ^ n)⁻¹) * ((phi ^ n)⁻¹ * S) := by ring
    _ = phi⁻¹ ^ n * S := by
      rw [mul_inv_cancel₀ (pow_ne_zero n hfiber), one_mul, inv_pow]

theorem exactConductorBlocks_pairwiseDisjoint
    (q : ℕ) [NeZero q] :
    (↑q.divisors : Set ℕ).PairwiseDisjoint
      (fun d ↦ exactConductorBlock q d) := by
  intro d₁ hd₁ d₂ hd₂ hne
  refine Finset.disjoint_left.mpr ?_
  intro a ha₁ ha₂
  exact hne ((mem_exactConductorBlock_iff a).mp ha₁ |>.symm.trans
    ((mem_exactConductorBlock_iff a).mp ha₂))

theorem exactConductorBlocks_cover
    (q : ℕ) [NeZero q] :
    (Finset.univ : Finset (ZMod q)) =
      q.divisors.biUnion (fun d ↦ exactConductorBlock q d) := by
  ext a
  constructor
  · intro _
    have hdvd : addOrderOf a ∣ q := by
      simpa [ZMod.card] using (addOrderOf_dvd_card (x := a))
    exact Finset.mem_biUnion.mpr
      ⟨addOrderOf a, Nat.mem_divisors.mpr ⟨hdvd, NeZero.ne q⟩,
        (mem_exactConductorBlock_iff a).mpr rfl⟩
  · intro _
    exact Finset.mem_univ _

/-- At every positive modulus, the normalized complete Fourier count is
the divisor sum of its primitive conductor coefficients. -/
theorem complexNormalizedUnitCubicCount_eq_sum_divisors_singularSeriesTerm
    (q n T : ℕ) (hq : q ≠ 0) :
    complexNormalizedUnitCubicCount q n T hq =
      ∑ d ∈ q.divisors, singularSeriesTerm n T d := by
  classical
  letI : NeZero q := ⟨hq⟩
  calc
    complexNormalizedUnitCubicCount q n T hq =
        (∑ a : ZMod q,
          unitCubicExponentialSum a ^ n *
            standardAdditiveCharacter (-(a * (T : ZMod q)))) /
          (Nat.totient q : ℂ) ^ n := by
      unfold complexNormalizedUnitCubicCount
      rw [frequencySum_eq_modulus_mul_unitCubicSolutionCount]
    _ = (∑ d ∈ q.divisors,
          ∑ a ∈ exactConductorBlock q d,
            unitCubicExponentialSum a ^ n *
              standardAdditiveCharacter (-(a * (T : ZMod q)))) /
          (Nat.totient q : ℂ) ^ n := by
      rw [← Finset.sum_biUnion (exactConductorBlocks_pairwiseDisjoint q),
        ← exactConductorBlocks_cover q]
    _ = ∑ d ∈ q.divisors, singularSeriesTerm n T d := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.mem_divisors.mp hd).1 (Nat.pos_of_ne_zero hq)
      letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
      exact exactConductorBlock_normalized_eq_singularSeriesTerm
        (Nat.mem_divisors.mp hd).1 n T

/-! ## Dirichlet inversion and multiplicativity -/

/-- The singular-series coefficients as an arithmetic function. -/
noncomputable def cubicCoefficientArithmeticFunction (n T : ℕ) :
    ArithmeticFunction ℂ :=
  ⟨singularSeriesTerm n T, singularSeriesTerm_zero n T⟩

/-- The normalized finite count as an arithmetic function, zero at modulus
zero. -/
noncomputable def cubicFiniteCountArithmeticFunction (n T : ℕ) :
    ArithmeticFunction ℂ :=
  ⟨fun q ↦ if hq : q = 0 then 0 else
      complexNormalizedUnitCubicCount q n T hq,
    by simp⟩

@[simp] theorem cubicCoefficientArithmeticFunction_apply
    (n T q : ℕ) :
    cubicCoefficientArithmeticFunction n T q = singularSeriesTerm n T q := rfl

@[simp] theorem cubicFiniteCountArithmeticFunction_apply_of_pos
    (n T : ℕ) {q : ℕ} (hq : 0 < q) :
    cubicFiniteCountArithmeticFunction n T q =
      complexNormalizedUnitCubicCount q n T hq.ne' := by
  simp [cubicFiniteCountArithmeticFunction, hq.ne']

theorem complexNormalizedUnitCubicCount_one (n T : ℕ) :
    complexNormalizedUnitCubicCount 1 n T (by decide) = 1 := by
  have h : ∀ x : Fin n → (ZMod 1)ˣ,
      unitCubicSum x = (T : ZMod 1) := fun _ ↦ Subsingleton.elim _ _
  simp [complexNormalizedUnitCubicCount, unitCubicSolutionCount, h]

/-- The finite normalized count is the Dirichlet convolution of the
primitive conductor coefficient with the constant-one function. -/
theorem cubicFiniteCount_eq_zeta_mul_coefficient (n T : ℕ) :
    cubicFiniteCountArithmeticFunction n T =
      (ζ : ArithmeticFunction ℂ) * cubicCoefficientArithmeticFunction n T := by
  ext q
  by_cases hq : q = 0
  · subst q
    simp [cubicFiniteCountArithmeticFunction]
  · rw [ArithmeticFunction.coe_zeta_mul_apply]
    rw [cubicFiniteCountArithmeticFunction_apply_of_pos n T
      (Nat.pos_of_ne_zero hq)]
    simpa only [cubicCoefficientArithmeticFunction_apply] using
      complexNormalizedUnitCubicCount_eq_sum_divisors_singularSeriesTerm
        q n T hq

theorem cubicFiniteCountArithmeticFunction_isMultiplicative
    (n T : ℕ) :
    (cubicFiniteCountArithmeticFunction n T).IsMultiplicative := by
  constructor
  · rw [cubicFiniteCountArithmeticFunction_apply_of_pos n T (by omega : 0 < 1)]
    exact complexNormalizedUnitCubicCount_one n T
  · intro q₁ q₂ hcop
    by_cases hq₁ : q₁ = 0
    · subst q₁
      simp [cubicFiniteCountArithmeticFunction]
    by_cases hq₂ : q₂ = 0
    · subst q₂
      simp [cubicFiniteCountArithmeticFunction]
    rw [cubicFiniteCountArithmeticFunction_apply_of_pos n T
        (Nat.mul_pos (Nat.pos_of_ne_zero hq₁) (Nat.pos_of_ne_zero hq₂)),
      cubicFiniteCountArithmeticFunction_apply_of_pos n T
        (Nat.pos_of_ne_zero hq₁),
      cubicFiniteCountArithmeticFunction_apply_of_pos n T
        (Nat.pos_of_ne_zero hq₂)]
    exact complexNormalizedUnitCubicCount_mul_of_coprime hq₁ hq₂ hcop

/-- The primitive cubic singular-series coefficients are multiplicative
in coprime moduli. -/
theorem cubicCoefficientArithmeticFunction_isMultiplicative
    (n T : ℕ) :
    (cubicCoefficientArithmeticFunction n T).IsMultiplicative := by
  have hconv := cubicFiniteCount_eq_zeta_mul_coefficient n T
  have hinv :
      (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          cubicFiniteCountArithmeticFunction n T =
        cubicCoefficientArithmeticFunction n T := by
    rw [hconv, ← mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta,
      one_mul]
  rw [← hinv]
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (cubicFiniteCountArithmeticFunction_isMultiplicative n T)

/-- The exact complete-sum coefficient is multiplicative in coprime
positive moduli (and, by its zero extension, also at modulus zero). -/
theorem singularSeriesTerm_mul_of_coprime
    (n T : ℕ) {q₁ q₂ : ℕ} (hcop : q₁.Coprime q₂) :
    singularSeriesTerm n T (q₁ * q₂) =
      singularSeriesTerm n T q₁ * singularSeriesTerm n T q₂ := by
  simpa only [cubicCoefficientArithmeticFunction_apply] using
    (cubicCoefficientArithmeticFunction_isMultiplicative n T).map_mul_of_coprime hcop

/-- CRT form of coefficient multiplicativity: a residue modulo a coprime
product contributes the product of the coefficients at its two components.
The component targets are represented by their canonical natural values. -/
theorem singularSeriesTerm_mul_of_coprime_crt
    (n q₁ q₂ : ℕ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : q₁.Coprime q₂) (t : ZMod (q₁ * q₂)) :
    singularSeriesTerm n t.val (q₁ * q₂) =
    singularSeriesTerm n (ZMod.chineseRemainder hcop t).1.val q₁ *
        singularSeriesTerm n (ZMod.chineseRemainder hcop t).2.val q₂ := by
  letI : NeZero q₁ := ⟨hq₁.ne'⟩
  letI : NeZero q₂ := ⟨hq₂.ne'⟩
  letI : NeZero (q₁ * q₂) := ⟨(Nat.mul_pos hq₁ hq₂).ne'⟩
  let t₁ := (ZMod.chineseRemainder hcop t).1
  let t₂ := (ZMod.chineseRemainder hcop t).2
  have hcrt : ZMod.chineseRemainder hcop
      (t.val : ZMod (q₁ * q₂)) = (t₁, t₂) := by
    rw [ZMod.natCast_zmod_val]
  have hcast₁ : (t.val : ZMod q₁) = t₁ := by
    have hmap := map_natCast (ZMod.chineseRemainder hcop) t.val
    rw [hcrt] at hmap
    exact congrArg Prod.fst hmap.symm
  have hcast₂ : (t.val : ZMod q₂) = t₂ := by
    have hmap := map_natCast (ZMod.chineseRemainder hcop) t.val
    rw [hcrt] at hmap
    exact congrArg Prod.snd hmap.symm
  calc
    singularSeriesTerm n t.val (q₁ * q₂) =
        singularSeriesTerm n t.val q₁ * singularSeriesTerm n t.val q₂ :=
      singularSeriesTerm_mul_of_coprime n t.val hcop
    _ = singularSeriesTerm n t₁.val q₁ * singularSeriesTerm n t₂.val q₂ := by
      rw [singularSeriesTerm_eq_of_target_eq_mod n q₁ t.val t₁.val hq₁
            (hcast₁.trans (ZMod.natCast_zmod_val t₁).symm),
          singularSeriesTerm_eq_of_target_eq_mod n q₂ t.val t₂.val hq₂
            (hcast₂.trans (ZMod.natCast_zmod_val t₂).symm)]

/-- The coefficient norm maximum is multiplicative on coprime positive
denominators. The upper bound uses coefficient multiplicativity; the reverse
bound chooses the two maximizing residues and combines them by CRT. -/
theorem singularSeriesTermNormMaximum_mul_of_coprime
    (n q₁ q₂ : ℕ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hcop : q₁.Coprime q₂) :
    singularSeriesTermNormMaximum n (q₁ * q₂) =
      singularSeriesTermNormMaximum n q₁ * singularSeriesTermNormMaximum n q₂ := by
  classical
  letI : NeZero q₁ := ⟨hq₁.ne'⟩
  letI : NeZero q₂ := ⟨hq₂.ne'⟩
  have hprod : 0 < q₁ * q₂ := Nat.mul_pos hq₁ hq₂
  letI : NeZero (q₁ * q₂) := ⟨hprod.ne'⟩
  have hmax₁ : 0 ≤ singularSeriesTermNormMaximum n q₁ := by
    obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n q₁ hq₁
    rw [ht]
    exact norm_nonneg _
  have hmax₂ : 0 ≤ singularSeriesTermNormMaximum n q₂ := by
    obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n q₂ hq₂
    rw [ht]
    exact norm_nonneg _
  have hmax₁' : 0 ≤ Finset.univ.sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (ZMod q₁)).Nonempty)
      (fun t : ZMod q₁ => ‖singularSeriesTerm n t.val q₁‖) := by
    simp [singularSeriesTermNormMaximum, hq₁.ne'] at hmax₁ ⊢
  have hupper : singularSeriesTermNormMaximum n (q₁ * q₂) ≤
      singularSeriesTermNormMaximum n q₁ * singularSeriesTermNormMaximum n q₂ := by
    simp only [singularSeriesTermNormMaximum, dif_neg hprod.ne',
      dif_neg hq₁.ne', dif_neg hq₂.ne']
    apply Finset.sup'_le (Finset.univ_nonempty :
      (Finset.univ : Finset (ZMod (q₁ * q₂))).Nonempty) _
    intro t _ht
    rw [singularSeriesTerm_mul_of_coprime_crt n q₁ q₂ hq₁ hq₂ hcop t,
      norm_mul]
    exact mul_le_mul
      (by
        simpa [singularSeriesTermNormMaximum, hq₁.ne'] using
          norm_singularSeriesTerm_le_maximum n q₁
            (ZMod.chineseRemainder hcop t).1.val hq₁)
      (by
        simpa [singularSeriesTermNormMaximum, hq₂.ne'] using
          norm_singularSeriesTerm_le_maximum n q₂
            (ZMod.chineseRemainder hcop t).2.val hq₂)
      (norm_nonneg _) hmax₁'
  obtain ⟨t₁, ht₁⟩ := singularSeriesTermNormMaximum_attained n q₁ hq₁
  obtain ⟨t₂, ht₂⟩ := singularSeriesTermNormMaximum_attained n q₂ hq₂
  let w : ZMod (q₁ * q₂) := (ZMod.chineseRemainder hcop).symm (t₁, t₂)
  have hwcrt : ZMod.chineseRemainder hcop w = (t₁, t₂) := by
    exact Equiv.apply_symm_apply _ _
  have hcoeffNorm :
      ‖singularSeriesTerm n w.val (q₁ * q₂)‖ =
        singularSeriesTermNormMaximum n q₁ * singularSeriesTermNormMaximum n q₂ := by
    rw [singularSeriesTerm_mul_of_coprime_crt n q₁ q₂ hq₁ hq₂ hcop w,
      hwcrt, norm_mul, ← ht₁, ← ht₂]
  have hlower : singularSeriesTermNormMaximum n q₁ *
      singularSeriesTermNormMaximum n q₂ ≤
        singularSeriesTermNormMaximum n (q₁ * q₂) := by
    rw [← hcoeffNorm]
    exact norm_singularSeriesTerm_le_maximum n (q₁ * q₂) w.val hprod
  exact le_antisymm hupper hlower

@[simp] theorem singularSeriesTerm_one (n T : ℕ) :
    singularSeriesTerm n T 1 = 1 := by
  simpa only [cubicCoefficientArithmeticFunction_apply] using
    (cubicCoefficientArithmeticFunction_isMultiplicative n T).map_one

/-- The Euler-product identity once global absolute summability of the
primitive coefficients is supplied.  The coefficient multiplicativity and
the prime-power factor identification are unconditional. -/
theorem singularSeries_eq_tprod_primeLocalFactor_of_summable
    (n T : ℕ)
    (hsum : Summable (fun q : ℕ ↦ ‖singularSeriesTerm n T q‖)) :
    singularSeries n T =
      ∏' p : Nat.Primes, primeLocalFactor p n T := by
  have heuler := EulerProduct.eulerProduct_tprod
    (f := singularSeriesTerm n T)
    (singularSeriesTerm_one n T)
    (fun {_ _} hcop ↦ singularSeriesTerm_mul_of_coprime n T hcop)
    hsum (singularSeriesTerm_zero n T)
  have hlocal (p : Nat.Primes) :
      (∑' e : ℕ, singularSeriesTerm n T ((p : ℕ) ^ e)) =
        primeLocalFactor p n T := by
    have hpowNorm : Summable (fun e : ℕ ↦
        ‖singularSeriesTerm n T ((p : ℕ) ^ e)‖) := by
      exact hsum.comp_injective
        (Nat.pow_right_injective p.property.two_le)
    have hpow : Summable (fun e : ℕ ↦
        singularSeriesTerm n T ((p : ℕ) ^ e)) :=
      Summable.of_norm hpowNorm
    have hsplit := hpow.sum_add_tsum_nat_add 1
    unfold primeLocalFactor
    simpa only [Finset.sum_range_one, pow_zero, singularSeriesTerm_one,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsplit.symm
  unfold singularSeries
  rw [← heuler]
  apply tprod_congr
  intro p
  exact hlocal p

/-! ## From locally summable prime powers to a globally summable coefficient -/

/-- A nonnegative multiplicative function is summable if every prime-power
series converges and the sums of its nonconstant prime-power terms form a
summable series over the primes. -/
theorem summable_of_multiplicative_of_primePowerTails_summable
    {f : ℕ → ℝ}
    (hf₀ : f 0 = 0) (hf₁ : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n)
    (hf_nonneg : ∀ q, 0 ≤ f q)
    (hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun k : ℕ ↦ ‖f (p ^ k)‖))
    (htails : Summable (fun p : Nat.Primes ↦
      ∑' k : ℕ, f ((p : ℕ) ^ (k + 1)))) :
    Summable f := by
  classical
  let tail : ℕ → ℝ := fun p ↦ ∑' k : ℕ, f (p ^ (k + 1))
  let primeTail : ℕ → ℝ :=
    Set.indicator {p : ℕ | p.Prime} tail
  have htail_nonneg (p : ℕ) : 0 ≤ tail p := by
    exact tsum_nonneg (fun k ↦ hf_nonneg _)
  have hprime_nonneg (p : ℕ) : 0 ≤ primeTail p := by
    by_cases hp : p.Prime
    · simpa [primeTail, hp] using htail_nonneg p
    · simp [primeTail, hp]
  have hprime_summable : Summable primeTail := by
    exact (summable_subtype_iff_indicator).mp htails
  apply summable_of_sum_range_le hf_nonneg
    (c := Real.exp (∑' p : ℕ, primeTail p))
  intro N
  have hsmooth :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f) hf₁ (fun {_ _} hcop ↦ hmul hcop) hlocal N
  have hsmooth_summable : Summable
      (fun q : N.smoothNumbers ↦ f (q : ℕ)) :=
    Summable.of_norm hsmooth.1
  let smoothIndicator : ℕ → ℝ :=
    Set.indicator N.smoothNumbers f
  have hind_summable : Summable smoothIndicator :=
    (summable_subtype_iff_indicator).mp hsmooth_summable
  have hind_nonneg (q : ℕ) : 0 ≤ smoothIndicator q := by
    by_cases hq : q ∈ N.smoothNumbers
    · simpa [smoothIndicator, hq] using hf_nonneg q
    · simp [smoothIndicator, hq]
  have hpoint (q : ℕ) (hq : q ∈ Finset.range N) :
      f q = smoothIndicator q := by
    by_cases hzero : q = 0
    · subst q
      have hnot : 0 ∉ N.smoothNumbers := by
        intro hmem
        exact (Nat.ne_zero_of_mem_smoothNumbers hmem) rfl
      simp [smoothIndicator, hnot, hf₀]
    · have hmem : q ∈ N.smoothNumbers := by
        apply Nat.mem_smoothNumbers_iff_forall_le.mpr
        refine ⟨hzero, ?_⟩
        intro p hp_le _ _
        exact lt_of_le_of_lt hp_le (Finset.mem_range.mp hq)
      simp [smoothIndicator, hmem]
  have hsplit (p : ℕ) (hp : p.Prime) :
      (∑' k : ℕ, f (p ^ k)) = 1 + tail p := by
    have hpow : Summable (fun k : ℕ ↦ f (p ^ k)) :=
      Summable.of_norm (hlocal hp)
    have h := hpow.sum_add_tsum_nat_add 1
    simpa only [Finset.sum_range_one, pow_zero, hf₁,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, tail] using h.symm
  calc
    (∑ q ∈ Finset.range N, f q) =
        ∑ q ∈ Finset.range N, smoothIndicator q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hpoint q hq
    _ ≤ ∑' q : ℕ, smoothIndicator q :=
      hind_summable.sum_le_tsum (Finset.range N)
        (fun q _ ↦ hind_nonneg q)
    _ = ∑' q : N.smoothNumbers, f (q : ℕ) := by
      exact (tsum_subtype N.smoothNumbers f).symm
    _ = ∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p ^ k) :=
      hsmooth.2.tsum_eq
    _ = ∏ p ∈ N.primesBelow, (1 + tail p) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact hsplit p (Nat.prime_of_mem_primesBelow hp)
    _ ≤ Real.exp (∑ p ∈ N.primesBelow, tail p) := by
      exact Real.prod_one_add_le_exp_sum _ htail_nonneg
    _ ≤ Real.exp (∑' p : ℕ, primeTail p) := by
      apply Real.exp_le_exp.mpr
      calc
        (∑ p ∈ N.primesBelow, tail p) =
            ∑ p ∈ N.primesBelow, primeTail p := by
          apply Finset.sum_congr rfl
          intro p hp
          simp [primeTail, Nat.prime_of_mem_primesBelow hp]
        _ ≤ ∑' p : ℕ, primeTail p :=
          hprime_summable.sum_le_tsum N.primesBelow
            (fun p _ ↦ hprime_nonneg p)

/-- Absolute convergence of each fixed-prime conductor series at arity at
least thirty-three, including the stationary-phase exceptional primes. -/
theorem summable_norm_singularSeriesTerm_prime_powers
    {p n T : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    Summable (fun k : ℕ ↦ ‖singularSeriesTerm n T (p ^ k)‖) := by
  by_cases hp5 : 5 ≤ p
  · letI : NeZero p := ⟨hp.ne_zero⟩
    have htail :=
      CookMagyarPrimePower.summable_norm_singularSeriesTerm_higherPrimePower
        (T := T) hp hp5 hn
    apply (summable_nat_add_iff 2).mp
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail
  have hp2 : 2 ≤ p := hp.two_le
  have hp4 : p ≤ 4 := by omega
  interval_cases p
  · apply (summable_nat_add_iff 4).mp
    have hzero (k : ℕ) :
        singularSeriesTerm n T (2 ^ (k + 4)) = 0 := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (CookMagyarPrimePower.singularSeriesTerm_two_power_exponent_eq_zero
          (m := k + 2) (T := T) (by omega) (by omega : 0 < n))
    simpa only [hzero, norm_zero] using
      (summable_zero : Summable (fun _k : ℕ ↦ (0 : ℝ)))
  · apply (summable_nat_add_iff 2).mp
    have hzero (k : ℕ) :
        singularSeriesTerm n T (3 ^ (k + 2)) = 0 :=
      CookMagyarPrimePower.singularSeriesTerm_three_power_eq_zero
        (T := T) (by omega) (by omega : 0 < n)
    simpa only [hzero, norm_zero] using
      (summable_zero : Summable (fun _k : ℕ ↦ (0 : ℝ)))
  · norm_num at hp

/-- The finite maximum of coefficient norms is summable along every
prime-power sequence once the arity is at least thirty-three. -/
theorem summable_singularSeriesTermNormMaximum_prime_powers
    {p n : ℕ} (hp : p.Prime) (hn : 33 ≤ n) :
    Summable (fun k : ℕ ↦ singularSeriesTermNormMaximum n (p ^ k)) := by
  by_cases hp5 : 5 ≤ p
  · letI : NeZero p := ⟨hp.ne_zero⟩
    have htail :=
      CookMagyarPrimePower.summable_singularSeriesTermNormMaximum_higherPrimePower
        hp hp5 hn
    apply (summable_nat_add_iff 2).mp
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail
  have hp2 : 2 ≤ p := hp.two_le
  have hp4 : p ≤ 4 := by omega
  interval_cases p
  · apply (summable_nat_add_iff 4).mp
    have hzero (k : ℕ) :
        singularSeriesTermNormMaximum n (2 ^ (k + 4)) = 0 := by
      obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n
        (2 ^ (k + 4)) (by positivity)
      rw [ht]
      have hterm := CookMagyarPrimePower.singularSeriesTerm_two_power_exponent_eq_zero
        (m := k + 2) (n := n) (T := t.val) (by omega) (by omega)
      simpa using congrArg norm hterm
    simpa only [hzero, norm_zero] using
      (summable_zero : Summable (fun _k : ℕ ↦ (0 : ℝ)))
  · apply (summable_nat_add_iff 2).mp
    have hzero (k : ℕ) :
        singularSeriesTermNormMaximum n (3 ^ (k + 2)) = 0 := by
      obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n
        (3 ^ (k + 2)) (by positivity)
      rw [ht]
      have hterm := CookMagyarPrimePower.singularSeriesTerm_three_power_eq_zero
        (k := k + 2) (n := n) (T := t.val) (by omega) (by omega)
      simpa using congrArg norm hterm
    simpa only [hzero, norm_zero] using
      (summable_zero : Summable (fun _k : ℕ ↦ (0 : ℝ)))
  · norm_num at hp

/-- The first prime-level maximum inherits the uniform `p⁻⁷` estimate from
the normalized finite-count deviation bound. -/
theorem singularSeriesTermNormMaximum_prime_le_inv_pow
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    singularSeriesTermNormMaximum n p ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨t, ht⟩ := singularSeriesTermNormMaximum_attained n p hp.pos
  rw [ht]
  exact norm_singularSeriesTerm_prime_le_inv_pow hp hp5 (by omega) t.val

theorem higherPrimePower_ratio_le_four_div_sq
    {p n : ℕ} (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
        (1 - ((p : ℝ)⁻¹) ^ (n - 2)) ≤
      4 / (p : ℝ) ^ 2 := by
  let x : ℝ := p
  let r : ℝ := x⁻¹ ^ (n - 2)
  have hx : 5 ≤ x := by
    dsimp [x]
    exact_mod_cast hp5
  have hx_pos : 0 < x := by linarith
  have hbase : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hr : 0 ≤ r := pow_nonneg (inv_nonneg.mpr hx_pos.le) _
  have hpow3 : r ≤ (x⁻¹) ^ 3 := by
    dsimp [r]
    exact pow_le_pow_of_le_one (inv_nonneg.mpr hx_pos.le) hbase
      (by omega : 3 ≤ n - 2)
  have hsmall : x⁻¹ ≤ (1 : ℝ) / 5 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hx)
  have hrhalf : r ≤ 1 / 2 := by
    calc
      r ≤ x⁻¹ := by
        dsimp [r]
        simpa only [pow_one] using
          (pow_le_pow_of_le_one (inv_nonneg.mpr hx_pos.le) hbase
            (by omega : 1 ≤ n - 2))
      _ ≤ 1 / 5 := hsmall
      _ ≤ 1 / 2 := by norm_num
  have hden : 0 < 1 - r := by linarith
  have hrr : r * x ^ 3 ≤ 1 := by
    calc
      r * x ^ 3 ≤ (x⁻¹) ^ 3 * x ^ 3 :=
        mul_le_mul_of_nonneg_right hpow3 (pow_nonneg hx_pos.le _)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hx_pos.ne', one_pow]
  have hx2le3 : x ^ 2 ≤ x ^ 3 := by nlinarith [sq_nonneg x]
  have hr2 : r * x ^ 2 ≤ r * x ^ 3 :=
    mul_le_mul_of_nonneg_left hx2le3 hr
  have hleft : (1 + x) * r * x ^ 2 ≤ 2 := by
    nlinarith [hrr, hr2]
  change (1 + x) * r / (1 - r) ≤ 4 / x ^ 2
  apply (div_le_div_iff₀ hden (pow_pos hx_pos 2)).mpr
  nlinarith [hleft, hrhalf]

/-- Sum of the absolute values of the nonconstant conductor coefficients
at a fixed prime. -/
noncomputable def primePowerNormTail (p n T : ℕ) : ℝ :=
  ∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 1))‖

end CookMagyarFiniteFourier
end SystolicGrowth

#print axioms SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm_mul_of_coprime_crt
#print axioms SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTermNormMaximum_mul_of_coprime
#print axioms SystolicGrowth.CookMagyarFiniteFourier.summable_singularSeriesTermNormMaximum_prime_powers
