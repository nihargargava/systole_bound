module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.LocalDensitySeriesBridge
public import CookMagyar.LocalLargePrimeCounts
public import CookMagyar.LocalFactorBridge
public import CookMagyar.LocalPrimeBaseFactorBridge
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Units

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarFiniteFourier

/-! # Exact prime-power conductors in the finite cubic Fourier count -/

/-- Frequencies of exact additive order `p^(j+1)` at ambient level `p^K`. -/
noncomputable def exactPrimePowerConductorBlock
    (p K j : ℕ) [NeZero (p ^ K)] : Finset (ZMod (p ^ K)) :=
  Finset.filter (fun a ↦ addOrderOf a = p ^ (j + 1)) Finset.univ

theorem mem_exactPrimePowerConductorBlock_iff
    {p K j : ℕ} [NeZero (p ^ K)] (a : ZMod (p ^ K)) :
    a ∈ exactPrimePowerConductorBlock p K j ↔
      addOrderOf a = p ^ (j + 1) := by
  simp [exactPrimePowerConductorBlock]

private theorem primePower_modulus_factor
    {p K j : ℕ} (hj : j < K) :
    p ^ K = p ^ (K - (j + 1)) * p ^ (j + 1) := by
  rw [← pow_add]
  congr 1
  omega

/-- A primitive unit residue at conductor `p^(j+1)`, embedded as an
additive frequency at the ambient modulus `p^K`. -/
noncomputable def primePowerPrimitiveLift (p K j : ℕ)
    (u : (ZMod (p ^ (j + 1)))ˣ) : ZMod (p ^ K) :=
  ((p ^ (K - (j + 1)) * (u : ZMod (p ^ (j + 1))).val : ℕ) : ZMod (p ^ K))

theorem addOrderOf_primePowerPrimitiveLift
    {p K j : ℕ} (hp : p.Prime) (hj : j < K)
    (u : (ZMod (p ^ (j + 1)))ˣ) :
    addOrderOf (primePowerPrimitiveLift p K j u) = p ^ (j + 1) := by
  have hfactor := primePower_modulus_factor (p := p) hj
  have hpow_ne : p ^ K ≠ 0 := pow_ne_zero K hp.ne_zero
  have hscale_pos : 0 < p ^ (K - (j + 1)) := pow_pos hp.pos _
  have hunit_low : (u : ZMod (p ^ (j + 1))).val.Coprime (p ^ (j + 1)) :=
    ZMod.val_coe_unit_coprime u
  have hunit_p : (u : ZMod (p ^ (j + 1))).val.Coprime p :=
    (Nat.coprime_pow_right_iff (by omega) _ _).mp hunit_low
  have hunit_high : (u : ZMod (p ^ (j + 1))).val.Coprime (p ^ K) :=
    Nat.Coprime.pow_right K hunit_p
  have hscale_dvd : p ^ (K - (j + 1)) ∣ p ^ K := by
    rw [hfactor]
    exact dvd_mul_right _ _
  rw [primePowerPrimitiveLift, ZMod.addOrderOf_coe _ hpow_ne]
  have hgcd : (p ^ K).gcd
      (p ^ (K - (j + 1)) * (u : ZMod (p ^ (j + 1))).val) =
      p ^ (K - (j + 1)) := by
    rw [Nat.gcd_comm, Nat.mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd hunit_high hscale_dvd
  rw [hgcd, hfactor]
  exact Nat.mul_div_right _ hscale_pos

/-- Distinct primitive conductor residues remain distinct after lifting. -/
theorem primePowerPrimitiveLift_injective
    {p K j : ℕ} (hp : p.Prime) (hj : j < K) :
    Function.Injective (primePowerPrimitiveLift p K j) := by
  letI : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  intro u v huv
  let scale := p ^ (K - (j + 1))
  have hfactor := primePower_modulus_factor (p := p) hj
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact pow_pos hp.pos _
  have hu_lt : scale * (u : ZMod (p ^ (j + 1))).val < p ^ K := by
    rw [hfactor]
    exact (Nat.mul_lt_mul_left hscale_pos).mpr (ZMod.val_lt _)
  have hv_lt : scale * (v : ZMod (p ^ (j + 1))).val < p ^ K := by
    rw [hfactor]
    exact (Nat.mul_lt_mul_left hscale_pos).mpr (ZMod.val_lt _)
  have hval : scale * (u : ZMod (p ^ (j + 1))).val =
      scale * (v : ZMod (p ^ (j + 1))).val := by
    have h := congrArg ZMod.val huv
    have huval : (primePowerPrimitiveLift p K j u).val =
        scale * (u : ZMod (p ^ (j + 1))).val := by
      unfold primePowerPrimitiveLift
      exact ZMod.val_natCast_of_lt (by simpa [scale] using hu_lt)
    have hvval : (primePowerPrimitiveLift p K j v).val =
        scale * (v : ZMod (p ^ (j + 1))).val := by
      unfold primePowerPrimitiveLift
      exact ZMod.val_natCast_of_lt (by simpa [scale] using hv_lt)
    exact huval.symm.trans (h.trans hvval)
  apply Units.ext
  apply ZMod.val_injective (p ^ (j + 1))
  exact Nat.mul_left_cancel hscale_pos hval

theorem exactPrimePowerConductorBlock_card
    {p K j : ℕ} [NeZero (p ^ K)] (hj : j < K) :
    (exactPrimePowerConductorBlock p K j).card =
      Nat.totient (p ^ (j + 1)) := by
  classical
  rw [show exactPrimePowerConductorBlock p K j =
      Finset.filter (fun a : ZMod (p ^ K) ↦
        addOrderOf a = p ^ (j + 1)) Finset.univ by rfl]
  have hpow : p ^ (j + 1) ∣ p ^ K := Nat.pow_dvd_pow p (by omega)
  simpa using
    (IsAddCyclic.card_addOrderOf_eq_totient
      (α := ZMod (p ^ K)) (d := p ^ (j + 1))
      (by simpa [ZMod.card] using hpow))

/-- Primitive units exhaust the exact additive-order block. -/
theorem exactPrimePowerConductorBlock_eq_primitive_image
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K) :
    exactPrimePowerConductorBlock p K j =
      Finset.univ.image (primePowerPrimitiveLift p K j) := by
  classical
  letI : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rcases Finset.mem_image.mp ha with ⟨u, -, rfl⟩
    exact (mem_exactPrimePowerConductorBlock_iff _).mpr
      (addOrderOf_primePowerPrimitiveLift hp hj u)
  · rw [exactPrimePowerConductorBlock_card hj,
      Finset.card_image_of_injective _ (primePowerPrimitiveLift_injective hp hj),
      Finset.card_univ]
    simp [ZMod.card_units_eq_totient]

/-- Reindex one exact-conductor Fourier block by its primitive units. -/
theorem sum_exactPrimePowerConductorBlock_eq_sum_units
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K)
    {M : Type*} [AddCommMonoid M] (f : ZMod (p ^ K) → M) :
    (∑ a ∈ exactPrimePowerConductorBlock p K j, f a) =
      ∑ u : (ZMod (p ^ (j + 1)))ˣ,
        f (primePowerPrimitiveLift p K j u) := by
  classical
  letI : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [exactPrimePowerConductorBlock_eq_primitive_image hp hj]
  exact Finset.sum_image (fun u hu v hv h ↦
    primePowerPrimitiveLift_injective hp hj h)

theorem exactPrimePowerConductorBlock_pairwiseDisjoint
    (p K : ℕ) [NeZero (p ^ K)] (hp : p.Prime) :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint
      (fun j ↦ exactPrimePowerConductorBlock p K j) := by
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr ?_
  intro a hai haj
  have hai' := (mem_exactPrimePowerConductorBlock_iff a).mp hai
  have haj' := (mem_exactPrimePowerConductorBlock_iff a).mp haj
  apply hij
  have heq : i + 1 = j + 1 :=
    (Nat.pow_right_injective hp.two_le) (hai'.symm.trans haj')
  omega

theorem exactPrimePowerConductorBlock_cover
    (p K : ℕ) [NeZero (p ^ K)] (hp : p.Prime) :
    (Finset.univ : Finset (ZMod (p ^ K))).erase 0 =
      (Finset.range K).biUnion (fun j ↦ exactPrimePowerConductorBlock p K j) := by
  ext a
  constructor
  · intro ha
    have hane : a ≠ 0 := (Finset.mem_erase.mp ha).1
    have hdiv : addOrderOf a ∣ p ^ K := by
      simpa using (addOrderOf_dvd_card (x := a))
    obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hp).mp hdiv
    have hk_pos : 0 < k := by
      by_contra hk0
      have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk0
      apply hane
      have hzeroeq : addOrderOf a = 1 := by simpa [hk_zero] using hk_eq
      exact AddMonoid.addOrderOf_eq_one_iff.mp hzeroeq
    let j := k - 1
    have hjK : j < K := by omega
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjK, ?_⟩
    apply (mem_exactPrimePowerConductorBlock_iff a).mpr
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk_pos)), hk_eq]
  · intro ha
    obtain ⟨j, hj, hja⟩ := Finset.mem_biUnion.mp ha
    have horder := (mem_exactPrimePowerConductorBlock_iff a).mp hja
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hzero
    have hbad : (1 : ℕ) = p ^ (j + 1) := by
      simpa [hzero] using horder
    have hpow : 1 < p ^ (j + 1) :=
      Nat.one_lt_pow (by omega) hp.one_lt
    omega

/-- The nonzero ambient frequencies split into exact prime-power
conductor blocks. -/
theorem sum_nonzero_frequencies_by_primePower_conductor_blocks
    {p K : ℕ} [NeZero (p ^ K)] (hp : p.Prime)
    {M : Type*} [AddCommMonoid M] (f : ZMod (p ^ K) → M) :
    (∑ a ∈ (Finset.univ : Finset (ZMod (p ^ K))).erase 0, f a) =
      ∑ j ∈ Finset.range K,
        ∑ a ∈ exactPrimePowerConductorBlock p K j, f a := by
  rw [exactPrimePowerConductorBlock_cover p K hp]
  exact Finset.sum_biUnion (exactPrimePowerConductorBlock_pairwiseDisjoint p K hp)

private theorem primePower_stdAddChar_primitiveLift
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K)
    (u : (ZMod (p ^ (j + 1)))ˣ) (x : ZMod (p ^ K)) :
    standardAdditiveCharacter (primePowerPrimitiveLift p K j u * x) =
      standardAdditiveCharacter
        ((u : ZMod (p ^ (j + 1))) *
          (x.cast : ZMod (p ^ (j + 1)))) := by
  let scale := p ^ (K - (j + 1))
  have hfactor := primePower_modulus_factor (p := p) hj
  have hcharacter (v : ℕ) :
      ZMod.stdAddChar ((scale * v : ℕ) : ZMod (p ^ K)) =
        ZMod.stdAddChar (v : ZMod (p ^ (j + 1))) := by
    rw [← Int.cast_natCast (scale * v), ← Int.cast_natCast v]
    rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
    congr 1
    rw [hfactor]
    push_cast
    have hs : (scale : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero (K - (j + 1)) hp.ne_zero
    have hlow : (p ^ (j + 1) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero (j + 1) hp.ne_zero
    field_simp [hs, hlow]
    simp [scale, mul_comm,
      mul_div_cancel_right₀ (v : ℂ)
        (show (p : ℂ) ^ (K - (j + 1)) ≠ 0 by
          exact_mod_cast pow_ne_zero (K - (j + 1)) hp.ne_zero)]
  calc
    standardAdditiveCharacter (primePowerPrimitiveLift p K j u * x) =
        ZMod.stdAddChar
          ((scale * ((u : ZMod (p ^ (j + 1))).val * x.val) : ℕ) :
            ZMod (p ^ K)) := by
              congr 1
              change (((scale * (u : ZMod (p ^ (j + 1))).val : ℕ) :
                ZMod (p ^ K)) * x) = _
              conv_lhs => rw [← ZMod.natCast_zmod_val x]
              norm_cast
              simp only [Nat.mul_assoc]
    _ = ZMod.stdAddChar
          (((u : ZMod (p ^ (j + 1))).val * x.val : ℕ) :
            ZMod (p ^ (j + 1))) := hcharacter _
    _ = standardAdditiveCharacter
          ((u : ZMod (p ^ (j + 1))) *
            (x.cast : ZMod (p ^ (j + 1)))) := by
              congr 1
              simp only [ZMod.cast_eq_val, Nat.cast_mul,
                ZMod.natCast_zmod_val]

def Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction {p K j : ℕ} (hj : j < K) :
    (ZMod (p ^ K))ˣ →* (ZMod (p ^ (j + 1)))ˣ :=
  ZMod.unitsMap (Nat.pow_dvd_pow p (by omega : j + 1 ≤ K))

private theorem primePower_totient_factor
    {p K j : ℕ} (hp : p.Prime) (hj : j < K) :
    Nat.totient (p ^ K) =
      p ^ (K - (j + 1)) * Nat.totient (p ^ (j + 1)) := by
  have hK : K - 1 + 1 = K := by omega
  calc
    Nat.totient (p ^ K) = p ^ (K - 1) * (p - 1) := by
      conv_lhs => rw [← hK]
      exact Nat.totient_prime_pow_succ hp (K - 1)
    _ = p ^ (K - (j + 1)) * (p ^ j * (p - 1)) := by
      have hexp : K - (j + 1) + j = K - 1 := by omega
      rw [← hexp, pow_add, mul_assoc]
    _ = p ^ (K - (j + 1)) * Nat.totient (p ^ (j + 1)) := by
      rw [Nat.totient_prime_pow_succ hp]

private theorem primePowerUnitReduction_fiber_card
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K)
    (y : (ZMod (p ^ (j + 1)))ˣ) :
    Fintype.card {x : (ZMod (p ^ K))ˣ // Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction hj x = y} =
      p ^ (K - (j + 1)) := by
  let red := Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction (p := p) hj
  have hsurj : Function.Surjective red :=
    ZMod.unitsMap_surjective (Nat.pow_dvd_pow p (by omega : j + 1 ≤ K))
  have hfiber (z : (ZMod (p ^ (j + 1)))ˣ) :
      Fintype.card {x : (ZMod (p ^ K))ˣ // red x = z} =
        Fintype.card {x : (ZMod (p ^ K))ˣ // red x = y} := by
    have h := MonoidHom.card_fiber_eq_of_mem_range red (hsurj z) (hsurj y)
    simpa [Fintype.card_subtype] using h
  have htotal :
      Fintype.card ((ZMod (p ^ K))ˣ) =
        Fintype.card (Σ z : (ZMod (p ^ (j + 1)))ˣ,
          {x : (ZMod (p ^ K))ˣ // red x = z}) :=
    Fintype.card_congr (Equiv.sigmaFiberEquiv red).symm
  have hcard :
      Nat.totient (p ^ K) = Nat.totient (p ^ (j + 1)) *
        Fintype.card {x : (ZMod (p ^ K))ˣ // red x = y} := by
    calc
      Nat.totient (p ^ K) = Fintype.card ((ZMod (p ^ K))ˣ) :=
        (ZMod.card_units_eq_totient _).symm
      _ = Fintype.card (Σ z : (ZMod (p ^ (j + 1)))ˣ,
            {x : (ZMod (p ^ K))ˣ // red x = z}) := htotal
      _ = ∑ z : (ZMod (p ^ (j + 1)))ˣ,
            Fintype.card {x : (ZMod (p ^ K))ˣ // red x = z} :=
        Fintype.card_sigma
      _ = ∑ _z : (ZMod (p ^ (j + 1)))ˣ,
            Fintype.card {x : (ZMod (p ^ K))ˣ // red x = y} := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact hfiber z
      _ = Nat.totient (p ^ (j + 1)) *
            Fintype.card {x : (ZMod (p ^ K))ˣ // red x = y} := by
        simp [ZMod.card_units_eq_totient]
  have hφ : 0 < Nat.totient (p ^ (j + 1)) := by
    rw [Nat.totient_prime_pow_succ hp]
    have hsub : 0 < p - 1 := by have := hp.one_lt; omega
    exact Nat.mul_pos (pow_pos hp.pos _) hsub
  apply Nat.eq_of_mul_eq_mul_left hφ
  change Nat.totient (p ^ (j + 1)) *
      Fintype.card {x : (ZMod (p ^ K))ˣ // red x = y} =
        Nat.totient (p ^ (j + 1)) * p ^ (K - (j + 1))
  rw [← hcard, primePower_totient_factor hp hj, mul_comm]

private theorem sum_primePowerUnitReduction
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K)
    (f : (ZMod (p ^ (j + 1)))ˣ → ℂ) :
    (∑ x : (ZMod (p ^ K))ˣ, f (Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction hj x)) =
      (p ^ (K - (j + 1)) : ℂ) *
        ∑ y : (ZMod (p ^ (j + 1)))ˣ, f y := by
  let red := Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction (p := p) hj
  calc
    (∑ x : (ZMod (p ^ K))ˣ, f (red x)) =
        ∑ y : (ZMod (p ^ (j + 1)))ˣ,
          ∑ x : {x : (ZMod (p ^ K))ˣ // red x = y}, f y := by
      rw [← (Equiv.sigmaFiberEquiv red).sum_comp (fun x ↦ f (red x)),
        Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro y _hy
      apply Finset.sum_congr rfl
      intro x _hx
      change f (red x.val) = f y
      rw [x.property]
    _ = ∑ y : (ZMod (p ^ (j + 1)))ˣ,
          (p ^ (K - (j + 1)) : ℂ) * f y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_const, Finset.card_univ,
        primePowerUnitReduction_fiber_card hp hj y]
      simp only [nsmul_eq_mul, Nat.cast_pow]
    _ = (p ^ (K - (j + 1)) : ℂ) *
          ∑ y : (ZMod (p ^ (j + 1)))ˣ, f y := by
      rw [Finset.mul_sum]

private theorem primePowerUnitReduction_cubicResidue
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hj : j < K) (x : (ZMod (p ^ K))ˣ) :
    ((cubicResidue (x : ZMod (p ^ K))).cast : ZMod (p ^ (j + 1))) =
      cubicResidue ((Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction hj x :
        (ZMod (p ^ (j + 1)))ˣ) : ZMod (p ^ (j + 1))) := by
  let red : ZMod (p ^ K) →+* ZMod (p ^ (j + 1)) :=
    ZMod.castHom (Nat.pow_dvd_pow p (by omega : j + 1 ≤ K))
      (ZMod (p ^ (j + 1)))
  change red (cubicResidue (x : ZMod (p ^ K))) =
    cubicResidue (red (x : ZMod (p ^ K)))
  simp [cubicResidue]

/-- A primitive frequency at ambient level `p^K` has the conductor-level
cubic complete sum multiplied by the unit-reduction fiber size. -/
theorem unitCubicExponentialSum_primePowerPrimitiveLift
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K)
    (u : (ZMod (p ^ (j + 1)))ˣ) :
    unitCubicExponentialSum (primePowerPrimitiveLift p K j u) =
      (p ^ (K - (j + 1)) : ℂ) *
        unitCubicExponentialSum (u : ZMod (p ^ (j + 1))) := by
  calc
    unitCubicExponentialSum (primePowerPrimitiveLift p K j u) =
        ∑ x : (ZMod (p ^ K))ˣ,
          standardAdditiveCharacter
            ((u : ZMod (p ^ (j + 1))) *
              cubicResidue ((Internal.PrimePowerConductorFourierBridgeHelpers.primePowerUnitReduction hj x :
                (ZMod (p ^ (j + 1)))ˣ) : ZMod (p ^ (j + 1)))) := by
      unfold unitCubicExponentialSum
      apply Finset.sum_congr rfl
      intro x _hx
      rw [primePower_stdAddChar_primitiveLift hp hj,
        primePowerUnitReduction_cubicResidue hj x]
    _ = (p ^ (K - (j + 1)) : ℂ) *
          unitCubicExponentialSum (u : ZMod (p ^ (j + 1))) := by
      exact sum_primePowerUnitReduction hp hj (fun y ↦
        standardAdditiveCharacter
          ((u : ZMod (p ^ (j + 1))) * cubicResidue (y : ZMod (p ^ (j + 1)))))

/-- The target character at a primitive high-level frequency reduces to
the target character at its conductor. -/
theorem standardAdditiveCharacter_primePowerPrimitiveLift_target
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K)
    (u : (ZMod (p ^ (j + 1)))ˣ) (T : ℕ) :
    standardAdditiveCharacter
        (-(primePowerPrimitiveLift p K j u * (T : ZMod (p ^ K)))) =
      standardAdditiveCharacter
        (-((u : ZMod (p ^ (j + 1))) * (T : ZMod (p ^ (j + 1))))) := by
  rw [← mul_neg, primePower_stdAddChar_primitiveLift hp hj]
  have hdiv : p ^ (j + 1) ∣ p ^ K := Nat.pow_dvd_pow p (by omega)
  simp only [ZMod.cast_neg hdiv, ZMod.cast_natCast hdiv, mul_neg]

/-- The Fourier contribution of one exact-order block at ambient modulus
`p^K` is the primitive conductor contribution times the reduction fiber
factor to the `n`th power. -/
theorem sum_exactPrimePowerConductorBlock_fourier_eq_conductor_sum
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K) (n T : ℕ) :
    (∑ a ∈ exactPrimePowerConductorBlock p K j,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod (p ^ K))))) =
      (p ^ (K - (j + 1)) : ℂ) ^ n *
        ∑ u : (ZMod (p ^ (j + 1)))ˣ,
          unitCubicExponentialSum (u : ZMod (p ^ (j + 1))) ^ n *
            standardAdditiveCharacter
              (-((u : ZMod (p ^ (j + 1))) *
                (T : ZMod (p ^ (j + 1))))) := by
  rw [sum_exactPrimePowerConductorBlock_eq_sum_units hp hj]
  calc
    (∑ u : (ZMod (p ^ (j + 1)))ˣ,
        unitCubicExponentialSum (primePowerPrimitiveLift p K j u) ^ n *
          standardAdditiveCharacter
            (-(primePowerPrimitiveLift p K j u * (T : ZMod (p ^ K))))) =
        ∑ u : (ZMod (p ^ (j + 1)))ˣ,
          (p ^ (K - (j + 1)) : ℂ) ^ n *
            (unitCubicExponentialSum (u : ZMod (p ^ (j + 1))) ^ n *
              standardAdditiveCharacter
                (-((u : ZMod (p ^ (j + 1))) *
                  (T : ZMod (p ^ (j + 1)))))) := by
      apply Finset.sum_congr rfl
      intro u _hu
      rw [unitCubicExponentialSum_primePowerPrimitiveLift hp hj,
        standardAdditiveCharacter_primePowerPrimitiveLift_target hp hj, mul_pow]
      ring
    _ = (p ^ (K - (j + 1)) : ℂ) ^ n *
          ∑ u : (ZMod (p ^ (j + 1)))ˣ,
            unitCubicExponentialSum (u : ZMod (p ^ (j + 1))) ^ n *
              standardAdditiveCharacter
                (-((u : ZMod (p ^ (j + 1))) *
                  (T : ZMod (p ^ (j + 1))))) := by
      rw [Finset.mul_sum]

/-- An exact-conductor Fourier block, normalized at the ambient level,
equals the singular-series coefficient at that conductor. -/
theorem exactPrimePowerConductorBlock_normalized_eq_singularSeriesTerm
    {p K j : ℕ} [NeZero (p ^ K)] [NeZero (p ^ (j + 1))]
    (hp : p.Prime) (hj : j < K) (n T : ℕ) :
    (∑ a ∈ exactPrimePowerConductorBlock p K j,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod (p ^ K))))) /
      (Nat.totient (p ^ K) : ℂ) ^ n =
        singularSeriesTerm n T (p ^ (j + 1)) := by
  rw [sum_exactPrimePowerConductorBlock_fourier_eq_conductor_sum hp hj n T,
    singularSeriesTerm_of_pos n T (pow_pos hp.pos _)]
  let scale : ℂ := (p ^ (K - (j + 1)) : ℂ)
  let phi : ℂ := (Nat.totient (p ^ (j + 1)) : ℂ)
  let S : ℂ := ∑ u : (ZMod (p ^ (j + 1)))ˣ,
    unitCubicExponentialSum (u : ZMod (p ^ (j + 1))) ^ n *
      standardAdditiveCharacter
        (-((u : ZMod (p ^ (j + 1))) *
          (T : ZMod (p ^ (j + 1)))))
  change scale ^ n * S / (Nat.totient (p ^ K) : ℂ) ^ n = phi⁻¹ ^ n * S
  have hfactor : (Nat.totient (p ^ K) : ℂ) = scale * phi := by
    simpa [scale, phi] using
      congrArg (fun m : ℕ ↦ (m : ℂ)) (primePower_totient_factor hp hj)
  have hs : scale ≠ 0 := by
    dsimp [scale]
    exact_mod_cast pow_ne_zero (K - (j + 1)) hp.ne_zero
  have hphi : phi ≠ 0 := by
    dsimp [phi]
    exact_mod_cast (by
      rw [Nat.totient_prime_pow_succ hp]
      exact Nat.mul_ne_zero (pow_ne_zero j hp.ne_zero) (by
        have := hp.one_lt
        omega) : Nat.totient (p ^ (j + 1)) ≠ 0)
  rw [hfactor, mul_pow, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (scale ^ n * (scale ^ n)⁻¹) * ((phi ^ n)⁻¹ * S) := by ring
    _ = phi⁻¹ ^ n * S := by
      rw [mul_inv_cancel₀ (pow_ne_zero n hs), one_mul, inv_pow]

/-- At each prime-power modulus, the normalized finite cubic count is
exactly the singular-series partial sum through that modulus. -/
theorem complexNormalizedUnitCubicCount_prime_power_eq_singularSeries_partial_sum
    (p K n T : ℕ) (hp : p.Prime) :
    complexNormalizedUnitCubicCount (p ^ K) n T
        (pow_ne_zero K hp.ne_zero) =
      1 + ∑ j ∈ Finset.range K, singularSeriesTerm n T (p ^ (j + 1)) := by
  letI : NeZero (p ^ K) := ⟨pow_ne_zero K hp.ne_zero⟩
  calc
    complexNormalizedUnitCubicCount (p ^ K) n T (NeZero.ne (p ^ K)) =
        1 + (complexNormalizedUnitCubicCount (p ^ K) n T
          (NeZero.ne (p ^ K)) - 1) := by ring
    _ = 1 +
          (∑ a ∈ (Finset.univ : Finset (ZMod (p ^ K))).erase 0,
            unitCubicExponentialSum a ^ n *
              standardAdditiveCharacter (-(a * (T : ZMod (p ^ K))))) /
            (Nat.totient (p ^ K) : ℂ) ^ n := by
      rw [complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum_all_moduli]
    _ = 1 +
          (∑ j ∈ Finset.range K,
            ∑ a ∈ exactPrimePowerConductorBlock p K j,
              unitCubicExponentialSum a ^ n *
                standardAdditiveCharacter (-(a * (T : ZMod (p ^ K))))) /
            (Nat.totient (p ^ K) : ℂ) ^ n := by
      rw [sum_nonzero_frequencies_by_primePower_conductor_blocks hp]
    _ = 1 + ∑ j ∈ Finset.range K,
          singularSeriesTerm n T (p ^ (j + 1)) := by
      rw [Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      letI : NeZero (p ^ (j + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact exactPrimePowerConductorBlock_normalized_eq_singularSeriesTerm
        hp (Finset.mem_range.mp hj) n T

/-- The finite Fourier identity for the real prime-power density count. -/
theorem primePowerLocalDensityApproximation_eq_singularSeries_partial_sum
    (p K n T : ℕ) (hp : p.Prime) :
    (primePowerLocalDensityApproximation p K n T hp : ℂ) =
      1 + ∑ j ∈ Finset.range K, singularSeriesTerm n T (p ^ (j + 1)) := by
  rw [← complexNormalizedUnitCubicCount_prime_power_eq_singularSeries_partial_sum
    p K n T hp]
  exact (complexNormalizedUnitCubicCount_of_real (p ^ K) n T
    (pow_ne_zero K hp.ne_zero)).symm

/-- A limiting prime-power density is exactly the completed local factor
whenever the singular-series conductor terms are summable. -/
theorem primeLocalFactor_eq_localDensity_of_hasPrimeLocalDensity
    {p n T : ℕ} (hp : p.Prime) {mu : ℝ}
    (hsum : Summable (fun j : ℕ ↦
      singularSeriesTerm n T (p ^ (j + 1))))
    (hdensity : HasPrimeLocalDensity p n T hp mu) :
    primeLocalFactor p n T = (mu : ℂ) := by
  apply primeLocalFactor_eq_limit_of_partial_sums hsum
  have hcast : Filter.Tendsto
      (fun K : ℕ ↦
        (primePowerLocalDensityApproximation p K n T hp : ℂ))
      Filter.atTop (nhds (mu : ℂ)) :=
    (Complex.continuous_ofReal.tendsto mu).comp hdensity
  simpa only [primePowerLocalDensityApproximation_eq_singularSeries_partial_sum]
    using hcast

/-- At every prime at least five and arity at least thirty-three, the
prime-power conductor terms are absolutely summable. -/
theorem summable_singularSeriesTerm_prime_power_of_large_arity
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    Summable (fun j : ℕ ↦
      singularSeriesTerm n T (p ^ (j + 1))) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have htailNorm :=
    CookMagyarPrimePower.summable_norm_singularSeriesTerm_higherPrimePower
      (T := T) hp hp5 hn
  have htail : Summable (fun k : ℕ ↦
      singularSeriesTerm n T (p ^ (k + 2))) :=
    Summable.of_norm htailNorm
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- The completed factor is the limit of real normalized prime-power
counts for primes at least five and arity at least thirty-three. -/
theorem hasPrimeLocalDensity_eq_primeLocalFactor_re_of_large_arity
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    HasPrimeLocalDensity p n T hp (primeLocalFactor p n T).re := by
  have hsum := summable_singularSeriesTerm_prime_power_of_large_arity
    (T := T) hp hp5 hn
  have hseries : Filter.Tendsto
      (fun K : ℕ ↦ ∑ j ∈ Finset.range K,
        singularSeriesTerm n T (p ^ (j + 1)))
      Filter.atTop (nhds (∑' j : ℕ,
        singularSeriesTerm n T (p ^ (j + 1)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hcomplex : Filter.Tendsto
      (fun K : ℕ ↦
        (primePowerLocalDensityApproximation p K n T hp : ℂ))
      Filter.atTop (nhds (primeLocalFactor p n T)) := by
    unfold primeLocalFactor
    simpa only [primePowerLocalDensityApproximation_eq_singularSeries_partial_sum]
      using (tendsto_const_nhds.add hseries)
  have hreal : Filter.Tendsto
      (fun K : ℕ ↦
        ((primePowerLocalDensityApproximation p K n T hp : ℂ)).re)
      Filter.atTop (nhds (primeLocalFactor p n T).re) :=
    (Complex.continuous_re.tendsto _).comp hcomplex
  simpa only [HasPrimeLocalDensity, Complex.ofReal_re] using hreal

/-- At primes at least five, the completed factor is real and is the
positive limiting normalized prime-power count. -/
theorem primeLocalFactor_eq_realPart_of_large_arity
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    primeLocalFactor p n T = ((primeLocalFactor p n T).re : ℂ) := by
  apply primeLocalFactor_eq_localDensity_of_hasPrimeLocalDensity hp
    (summable_singularSeriesTerm_prime_power_of_large_arity hp hp5 hn)
  exact hasPrimeLocalDensity_eq_primeLocalFactor_re_of_large_arity hp hp5 hn

/-- The completed local factor inherits the explicit nonsingular-lift
bound, uniformly in the target. -/
theorem primeLocalFactor_re_ge_lift_bound_of_prime_ge_five
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    (p : ℝ) / ((p - 1 : ℕ) : ℝ) ^ n ≤
      (primeLocalFactor p n T).re := by
  exact primeLocalDensity_ge_lift_bound_of_hasPrimeLocalDensity
    hp hp5 (by omega)
    (hasPrimeLocalDensity_eq_primeLocalFactor_re_of_large_arity hp hp5 hn)

/-- The nonsingular modular solutions make every completed local factor at
prime `p ≥ 5` strictly positive, without a large-prime cutoff. -/
theorem primeLocalFactor_re_pos_of_prime_ge_five
    {p n T : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) :
    0 < (primeLocalFactor p n T).re := by
  exact primeLocalDensity_pos_of_hasPrimeLocalDensity hp hp5 (by omega)
    (hasPrimeLocalDensity_eq_primeLocalFactor_re_of_large_arity hp hp5 hn)

end CookMagyarFiniteFourier
end SystolicGrowth
