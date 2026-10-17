module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.LocalFactorTail
public import CookMagyar.LocalLargePrimeCounts
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarPrimePower

/-! # Prime-power stationary-phase algebra

This file develops the finite algebra behind the prime-power tail of the
Cook--Magyar singular series.  The central reindexing writes a residue
modulo `M * R` uniquely as `x + M*y`, with `x` modulo `M` and `y` modulo
`R`.  For `M = p^m`, `R = p^d`, and `d ≤ m`, the quadratic Taylor
remainder of `X³-X` vanishes modulo `p^(m+d)`.  Orthogonality in `y`
then restricts the outer sum to residues for which the derivative vanishes
modulo `p^d`.
-/

open CookMagyarFiniteFourier CookMagyarLocal

/-- The additive embedding `y ↦ M*y` from residues modulo `R` into
residues modulo `M*R`. -/
def blockKernelAddHom (M R : ℕ) [NeZero M] [NeZero R] :
    ZMod R →+ ZMod (M * R) where
  toFun y := (M * y.val : ℕ)
  map_zero' := by simp
  map_add' a b := by
    rw [← Nat.cast_add]
    apply (ZMod.natCast_eq_natCast_iff _ _ (M * R)).2
    have h : (a + b).val ≡ a.val + b.val [MOD R] := by
      apply (ZMod.natCast_eq_natCast_iff _ _ R).mp
      simp
    simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      h.mul_left' M

@[simp] theorem blockKernelAddHom_apply (M R : ℕ) [NeZero M] [NeZero R]
    (y : ZMod R) :
    blockKernelAddHom M R y = (M * y.val : ℕ) := rfl

/-- Every residue modulo `M*R` is uniquely a low digit modulo `M` plus
`M` times a high digit modulo `R`. -/
noncomputable def residueBlockEquiv (M R : ℕ) [NeZero M] [NeZero R] :
    ZMod M × ZMod R ≃ ZMod (M * R) :=
  ((ZMod.finEquiv M).symm.toEquiv.prodCongr
      (ZMod.finEquiv R).symm.toEquiv).trans <|
    Equiv.prodComm _ _ |>.trans <|
      finProdFinEquiv |>.trans (finCongr (Nat.mul_comm R M)) |>.trans
        (ZMod.finEquiv (M * R)).toEquiv

@[simp] theorem residueBlockEquiv_apply (M R : ℕ) [NeZero M] [NeZero R]
    (x : ZMod M) (y : ZMod R) :
    residueBlockEquiv M R (x, y) =
      (x.val + M * y.val : ℕ) := by
  have hsum : x.val + M * y.val < M * R := by
    calc
      x.val + M * y.val < M + M * y.val :=
        Nat.add_lt_add_right x.val_lt _
      _ = M * (y.val + 1) := by ring
      _ ≤ M * R := Nat.mul_le_mul_left M (Nat.succ_le_iff.mpr y.val_lt)
  apply ZMod.val_injective (M * R)
  rw [ZMod.val_cast_of_lt hsum]
  cases M with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ M =>
      cases R with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ R => rfl

/-- Core.Reduction from residues modulo `M*R` to residues modulo `M`. -/
def blockReduction (M R : ℕ) : ZMod (M * R) →+* ZMod M :=
  ZMod.castHom (dvd_mul_right M R) (ZMod M)

@[simp] theorem blockReduction_residueBlockEquiv
    (M R : ℕ) [NeZero M] [NeZero R]
    (x : ZMod M) (y : ZMod R) :
    blockReduction M R (residueBlockEquiv M R (x, y)) = x := by
  rw [residueBlockEquiv_apply]
  unfold blockReduction
  rw [ZMod.castHom_apply, ZMod.cast_natCast (dvd_mul_right M R)]
  push_cast
  rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- The block-kernel embedding is injective. -/
theorem blockKernelAddHom_injective (M R : ℕ) [NeZero M] [NeZero R] :
    Function.Injective (blockKernelAddHom M R) := by
  intro a b hab
  have hmod : M * a.val ≡ M * b.val [MOD M * R] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ (M * R)).mp
    exact hab
  have hM : 0 < M := NeZero.pos M
  have ha_lt : M * a.val < M * R :=
    Nat.mul_lt_mul_of_pos_left a.val_lt hM
  have hb_lt : M * b.val < M * R :=
    Nat.mul_lt_mul_of_pos_left b.val_lt hM
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod
  exact ZMod.val_injective R (Nat.eq_of_mul_eq_mul_left hM hmod)

/-- Multiplication by `M` depends only on reduction modulo `R` when the
ambient modulus is `M*R`. -/
theorem blockKernel_cast_eq_mul (M R : ℕ) [NeZero M] [NeZero R]
    (D : ZMod (M * R)) :
    blockKernelAddHom M R (D.cast : ZMod R) =
      (M : ZMod (M * R)) * D := by
  rw [← ZMod.natCast_zmod_val D]
  rw [blockKernelAddHom_apply]
  push_cast
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_natCast_iff _ _ (M * R)).2
  have hcast : ((D.cast : ZMod R).val : ZMod R) = (D.val : ZMod R) := by
    rw [ZMod.natCast_zmod_val]
    exact ZMod.cast_eq_val D
  have hmod : (D.cast : ZMod R).val ≡ D.val [MOD R] :=
    (ZMod.natCast_eq_natCast_iff _ _ R).mp hcast
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    hmod.mul_left' M

/-- Multiplication by `M` vanishes modulo `M*R` exactly when the other
factor vanishes after reduction modulo `R`. -/
theorem natCast_mul_eq_zero_iff_cast_eq_zero
    (M R : ℕ) [NeZero M] [NeZero R] (D : ZMod (M * R)) :
    (M : ZMod (M * R)) * D = 0 ↔ (D.cast : ZMod R) = 0 := by
  rw [← blockKernel_cast_eq_mul M R D]
  constructor
  · intro h
    apply blockKernelAddHom_injective M R
    simpa using h
  · intro h
    simp [h]

/-- The character in the high block produced by a fixed linear
coefficient. -/
noncomputable def blockLinearCharacter
    (M R : ℕ) [NeZero M] [NeZero R] (D : ZMod (M * R)) :
    AddChar (ZMod R) ℂ :=
  (standardAdditiveCharacter (q := M * R)).compAddMonoidHom
    ((AddMonoidHom.mulRight D).comp (blockKernelAddHom M R))

@[simp] theorem blockLinearCharacter_apply
    (M R : ℕ) [NeZero M] [NeZero R]
    (D : ZMod (M * R)) (y : ZMod R) :
    blockLinearCharacter M R D y =
      standardAdditiveCharacter
        (blockKernelAddHom M R y * D) := rfl

/-- Exact block orthogonality.  This is the stationary-phase cancellation:
the inner block sum vanishes unless the linear coefficient is zero modulo
the block modulus. -/
theorem sum_blockLinearCharacter
    (M R : ℕ) [NeZero M] [NeZero R] (D : ZMod (M * R)) :
    (∑ y : ZMod R, blockLinearCharacter M R D y) =
      if (D.cast : ZMod R) = 0 then (R : ℂ) else 0 := by
  by_cases hD : (D.cast : ZMod R) = 0
  · rw [if_pos hD]
    have hmul : (M : ZMod (M * R)) * D = 0 :=
      (natCast_mul_eq_zero_iff_cast_eq_zero M R D).2 hD
    calc
      (∑ y : ZMod R, blockLinearCharacter M R D y) =
          ∑ _y : ZMod R, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro y _hy
            rw [blockLinearCharacter_apply]
            have hy : blockKernelAddHom M R y * D = 0 := by
              rw [blockKernelAddHom_apply, Nat.cast_mul]
              change ((M : ZMod (M * R)) * (y.val : ZMod (M * R))) * D = 0
              rw [mul_assoc, mul_comm (y.val : ZMod (M * R)) D,
                ← mul_assoc, hmul, zero_mul]
            rw [hy, AddChar.map_zero_eq_one]
      _ = (R : ℂ) := by simp [ZMod.card]
  · rw [if_neg hD]
    apply AddChar.sum_eq_zero_of_ne_one
    rw [AddChar.zmod_char_ne_one_iff R]
    rw [blockLinearCharacter_apply]
    have hnonzero :
        blockKernelAddHom M R (1 : ZMod R) * D ≠ 0 := by
      rw [blockKernelAddHom_apply]
      have hR1 : R ≠ 1 := by
        intro hR
        subst R
        exact hD (Subsingleton.elim _ _)
      rw [ZMod.val_one'' hR1]
      norm_num
      change (M : ZMod (M * R)) * D ≠ 0
      exact (natCast_mul_eq_zero_iff_cast_eq_zero M R D).not.mpr hD
    exact fun hone ↦ hnonzero <|
      ((ZMod.isPrimitive_stdAddChar (M * R)).zmod_char_eq_one_iff
        (M * R) _).mp hone

/-! ## Taylor linearization on a half-size block -/

/-- The block reindexing is addition of its low representative and its
kernel correction. -/
theorem residueBlockEquiv_eq_add_kernel
    (M R : ℕ) [NeZero M] [NeZero R]
    (x : ZMod M) (y : ZMod R) :
    residueBlockEquiv M R (x, y) =
      (x.val : ZMod (M * R)) + blockKernelAddHom M R y := by
  rw [residueBlockEquiv_apply, blockKernelAddHom_apply]
  push_cast
  rfl

/-- If `R ∣ M`, every block correction has square zero modulo `M*R`. -/
theorem blockKernelAddHom_sq_eq_zero
    (M R : ℕ) [NeZero M] [NeZero R] (hRM : R ∣ M)
    (y : ZMod R) :
    (blockKernelAddHom M R y) ^ 2 = 0 := by
  rw [blockKernelAddHom_apply]
  rw [← Nat.cast_pow]
  rw [ZMod.natCast_eq_zero_iff]
  have hbase : M * R ∣ M * M := by
    simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left M hRM
  have hmul : M * R ∣ (M * M) * (y.val * y.val) :=
    dvd_mul_of_dvd_left hbase _
  simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-- Exact first-order Taylor expansion on a block whose high modulus
divides its low modulus. -/
theorem cubicResidue_residueBlockEquiv
    (M R : ℕ) [NeZero M] [NeZero R] (hRM : R ∣ M)
    (x : ZMod M) (y : ZMod R) :
    CookMagyarFiniteFourier.cubicResidue
        (residueBlockEquiv M R (x, y)) =
      CookMagyarFiniteFourier.cubicResidue (x.val : ZMod (M * R)) +
        blockKernelAddHom M R y *
          CookMagyarLocal.cubicDerivative (x.val : ZMod (M * R)) := by
  rw [residueBlockEquiv_eq_add_kernel]
  simp only [CookMagyarFiniteFourier.cubicResidue,
    CookMagyarLocal.cubicDerivative]
  have hsquare := blockKernelAddHom_sq_eq_zero M R hRM y
  calc
    ((x.val : ZMod (M * R)) + blockKernelAddHom M R y) ^ 3 -
        ((x.val : ZMod (M * R)) + blockKernelAddHom M R y) =
      (x.val : ZMod (M * R)) ^ 3 - x.val +
        blockKernelAddHom M R y *
          (3 * (x.val : ZMod (M * R)) ^ 2 - 1) +
        (blockKernelAddHom M R y) ^ 2 *
          (3 * (x.val : ZMod (M * R)) + blockKernelAddHom M R y) := by ring
    _ = (x.val : ZMod (M * R)) ^ 3 - x.val +
        blockKernelAddHom M R y *
          (3 * (x.val : ZMod (M * R)) ^ 2 - 1) := by rw [hsquare, zero_mul, add_zero]

/-- A prime-power block correction preserves whether a residue is a unit,
provided the low block has positive exponent. -/
theorem isUnit_residueBlockEquiv_primePower_iff
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hm : 1 ≤ m)
    (x : ZMod (p ^ m)) (y : ZMod (p ^ d)) :
    IsUnit (residueBlockEquiv (p ^ m) (p ^ d) (x, y)) ↔ IsUnit x := by
  rw [residueBlockEquiv_apply]
  rw [← pow_add]
  simpa only [ZMod.natCast_zmod_val] using
    (show
      IsUnit ((x.val + p ^ m * y.val : ℕ) : ZMod (p ^ (m + d))) ↔
        IsUnit ((x.val : ℕ) : ZMod (p ^ m)) by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < m + d),
        ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega : 0 < m)]
      constructor
      · contrapose!
        intro hx
        exact hx.add (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m ≠ 0)) y.val)
      · contrapose!
        intro hsum
        exact (Nat.dvd_add_iff_left
          (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m ≠ 0)) y.val)).mpr hsum)

noncomputable def Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit (q : ℕ) [NeZero q] :
    (ZMod q)ˣ ≃ {x : ZMod q // IsUnit x} where
  toFun u := ⟨u, u.isUnit⟩
  invFun x := x.property.unit
  left_inv u := by
    apply Units.ext
    exact u.isUnit.unit_spec
  right_inv x := by
    apply Subtype.ext
    exact x.property.unit_spec

private theorem unitCubicExponentialSum_eq_sum_if_isUnit
    {q : ℕ} [NeZero q] (a : ZMod q) :
    unitCubicExponentialSum a =
      ∑ x : ZMod q, if IsUnit x then
        standardAdditiveCharacter
          (a * CookMagyarFiniteFourier.cubicResidue x) else 0 := by
  classical
  let f : ZMod q → ℂ := fun x ↦
    if IsUnit x then standardAdditiveCharacter
      (a * CookMagyarFiniteFourier.cubicResidue x) else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun x : ZMod q ↦ IsUnit x) f
  have hunit : (∑ x : {x : ZMod q // IsUnit x}, f x) =
      unitCubicExponentialSum a := by
    calc
      (∑ x : {x : ZMod q // IsUnit x}, f x) =
          ∑ u : (ZMod q)ˣ, f (Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit q u) := by
            exact ((Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit q).sum_comp
              (fun x : {x : ZMod q // IsUnit x} ↦ f x)).symm
      _ = unitCubicExponentialSum a := by
        unfold unitCubicExponentialSum
        apply Finset.sum_congr rfl
        intro u _hu
        simp [f, Internal.PrimePowerStationaryPhaseHelpers.unitsEquivIsUnit]
  have hnonunit : (∑ x : {x : ZMod q // ¬ IsUnit x}, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _hx
    simp [f, x.property]
  rw [hunit, hnonunit, add_zero] at hsplit
  simpa [f] using hsplit

/-- Exact stationary-phase decomposition of a unit-restricted complete
cubic sum over a prime-power block.  Orthogonality kills every low residue
whose phase derivative is nonzero modulo the high block. -/
theorem unitCubicExponentialSum_primePower_block
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hm : 1 ≤ m) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d)) :
    unitCubicExponentialSum a =
      ∑ x : ZMod (p ^ m), if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0 := by
  classical
  let M := p ^ m
  let R := p ^ d
  let e := residueBlockEquiv M R
  let f : ZMod (M * R) → ℂ := fun z ↦
    if IsUnit z then standardAdditiveCharacter
      (a * CookMagyarFiniteFourier.cubicResidue z) else 0
  have hRM : R ∣ M := pow_dvd_pow p hdm
  rw [unitCubicExponentialSum_eq_sum_if_isUnit]
  change (∑ z : ZMod (M * R), f z) = _
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _hx
  have hunit (y : ZMod R) :
      IsUnit (e (x, y)) ↔ IsUnit x := by
    simpa [M, R, e] using
      isUnit_residueBlockEquiv_primePower_iff hp hm x y
  simp only [f]
  simp_rw [hunit]
  by_cases hxunit : IsUnit x
  · simp only [if_pos hxunit]
    have hphase (y : ZMod R) :
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue (e (x, y))) =
          standardAdditiveCharacter
              (a * CookMagyarFiniteFourier.cubicResidue
                (x.val : ZMod (M * R))) *
            blockLinearCharacter M R
              (a * cubicDerivative (x.val : ZMod (M * R))) y := by
      rw [show e (x, y) = residueBlockEquiv M R (x, y) from rfl]
      rw [cubicResidue_residueBlockEquiv M R hRM]
      rw [blockLinearCharacter_apply]
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [hphase]
    rw [← Finset.mul_sum, sum_blockLinearCharacter]
    simp [R]
  · simp only [if_neg hxunit]
    simp

/-- If the phase has no stationary unit residue in the high block, the
complete unit sum cancels exactly. -/
theorem unitCubicExponentialSum_primePower_block_eq_zero
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hm : 1 ≤ m) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d))
    (hstationary : ∀ x : ZMod (p ^ m), IsUnit x →
      (((a * cubicDerivative
        (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) ≠ 0)) :
    unitCubicExponentialSum a = 0 := by
  rw [unitCubicExponentialSum_primePower_block hp hm hdm a]
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hxunit : IsUnit x
  · rw [if_pos hxunit, if_neg (hstationary x hxunit), mul_zero]
  · rw [if_neg hxunit]

/-- At the prime `3`, every unit frequency has no stationary block, so its
complete cubic sum vanishes after any positive high block. -/
theorem unitCubicExponentialSum_three_power_block_eq_zero
    {m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hdm : d ≤ m)
    (a : ZMod (3 ^ m * 3 ^ d)) (ha : IsUnit a) :
    unitCubicExponentialSum a = 0 := by
  letI : NeZero 3 := ⟨by norm_num⟩
  letI : Nontrivial (ZMod (3 ^ d)) := ZMod.nontrivial_iff.mpr <|
    ne_of_gt (one_lt_pow₀ (by norm_num : 1 < (3 : ℕ)) (by omega))
  apply unitCubicExponentialSum_primePower_block_eq_zero
    (p := 3) (Nat.prime_three) hm hdm a
  intro x _hx
  let castP : ZMod (3 ^ m * 3 ^ d) →+* ZMod (3 ^ d) :=
    ZMod.castHom (dvd_mul_left (3 ^ d) (3 ^ m)) (ZMod (3 ^ d))
  have ha_cast : IsUnit (castP a) := ha.map castP
  have hderiv_cast : IsUnit
      (castP (cubicDerivative (x.val : ZMod (3 ^ m * 3 ^ d)))) := by
    have h := cubicDerivative_threeAdic_isUnit d
      (castP (x.val : ZMod (3 ^ m * 3 ^ d)))
    unfold cubicDerivative at h ⊢
    simpa only [map_sub, map_mul, map_pow, map_ofNat, map_one] using h
  have hproduct : IsUnit
      (castP (a * cubicDerivative
        (x.val : ZMod (3 ^ m * 3 ^ d)))) := by
    rw [map_mul]
    exact ha_cast.mul hderiv_cast
  simpa [castP, ZMod.castHom_apply] using hproduct.ne_zero

/-- Consequently every higher `3`-power block has zero singular-series
coefficient in positive arity. -/
theorem singularSeriesCoefficient_three_power_block_eq_zero
    {m d n T : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hdm : d ≤ m)
    (hn : 0 < n) :
    singularSeriesCoefficient (3 ^ m * 3 ^ d) n T (by positivity) = 0 := by
  letI : NeZero 3 := ⟨by norm_num⟩
  unfold singularSeriesCoefficient
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro a _ha
  rw [unitCubicExponentialSum_three_power_block_eq_zero
    hm hd hdm (a : ZMod (3 ^ m * 3 ^ d)) a.isUnit]
  simp [zero_pow hn.ne']

/-- The corresponding term of the singular series vanishes exactly. -/
theorem singularSeriesTerm_three_power_block_eq_zero
    {m d n T : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) (hdm : d ≤ m)
    (hn : 0 < n) :
    singularSeriesTerm n T (3 ^ m * 3 ^ d) = 0 := by
  rw [singularSeriesTerm_of_pos n T (by positivity)]
  exact singularSeriesCoefficient_three_power_block_eq_zero hm hd hdm hn

/-- Every `3^k` coefficient above prime level vanishes. -/
theorem singularSeriesTerm_three_power_eq_zero
    {k n T : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    singularSeriesTerm n T (3 ^ k) = 0 := by
  have h := singularSeriesTerm_three_power_block_eq_zero
    (m := k - 1) (d := 1) (T := T) (by omega) (by omega) (by omega) hn
  have hpow : 3 ^ (k - 1) * 3 ^ 1 = 3 ^ k := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at h
  exact h

/-- Thus the `3`-adic local factor has no tail beyond its prime-level
coefficient. -/
theorem primeLocalFactor_three_eq
    {n T : ℕ} (hn : 0 < n) :
    primeLocalFactor 3 n T = 1 + singularSeriesTerm n T 3 := by
  unfold primeLocalFactor
  congr 1
  rw [tsum_eq_single 0]
  · simp
  · intro k hk
    exact singularSeriesTerm_three_power_eq_zero (k := k + 1) (by omega) hn

/-- The prime-level normalized count differs from `1` by the sum over
nonzero frequencies.  This exact identity holds at every prime. -/
theorem complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum_prime
    {p : ℕ} [NeZero p] (hp : p.Prime) (n T : ℕ) :
    complexNormalizedUnitCubicCount p n T hp.ne_zero - 1 =
      (∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        unitCubicExponentialSum a ^ n *
          standardAdditiveCharacter (-(a * (T : ZMod p)))) /
        (Nat.totient p : ℂ) ^ n := by
  letI : Fact p.Prime := ⟨hp⟩
  unfold complexNormalizedUnitCubicCount
  rw [← frequencySum_eq_modulus_mul_unitCubicSolutionCount]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
  simp only [CookMagyarFiniteFourier.unitCubicExponentialSum_zero,
    zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hphi_nat : Nat.totient p ≠ 0 :=
    Nat.ne_of_gt (Nat.totient_pos.mpr hp.pos)
  have hphi : (Nat.totient p : ℂ) ^ n ≠ 0 :=
    pow_ne_zero n (by exact_mod_cast hphi_nat)
  field_simp
  simp [AddChar.map_zero_eq_one, mul_comm]

/-- At every prime, the first singular-series coefficient is the deviation
of the normalized congruence count from `1`. -/
theorem singularSeriesCoefficient_prime_eq_normalized_sub_one_general
    {p : ℕ} [NeZero p] (hp : p.Prime) (n T : ℕ) :
    singularSeriesCoefficient p n T hp.ne_zero =
      complexNormalizedUnitCubicCount p n T hp.ne_zero - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [complexNormalizedUnitCubicCount_sub_one_eq_nonzeroFrequencySum_prime
    hp]
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

/-- For positive arity, the full `3`-adic factor is exactly its normalized
prime-level congruence count. -/
theorem primeLocalFactor_three_eq_normalizedUnitCubicCount
    {n T : ℕ} (hn : 0 < n) :
    primeLocalFactor 3 n T =
      (normalizedUnitCubicCount n (T : ZMod 3) : ℂ) := by
  letI : NeZero 3 := ⟨by norm_num⟩
  rw [primeLocalFactor_three_eq hn]
  rw [singularSeriesTerm_of_pos n T (by norm_num : 0 < 3)]
  rw [singularSeriesCoefficient_prime_eq_normalized_sub_one_general
    Nat.prime_three]
  rw [complexNormalizedUnitCubicCount_of_real]
  ring

/-- The `3`-adic local factor is strictly positive for the admissible
Cook--Magyar targets. -/
theorem primeLocalFactor_three_re_pos
    {n T : ℕ} (hn : 1 ≤ n) (hT : 24 ∣ T) :
    0 < (primeLocalFactor 3 n T).re := by
  rw [primeLocalFactor_three_eq_normalizedUnitCubicCount (by omega)]
  rw [Complex.ofReal_re]
  apply normalizedUnitCubicCount_pos (q := 3) (by norm_num)
  simpa using unitCubicSolutionCount_pos_three_power
    (n := n) (k := 1) hn hT

/-! ### Stationary residues at primes at least five -/

/-- A residue modulo a positive prime power is a unit if its reduction
modulo the underlying prime is nonzero. -/
theorem isUnit_of_prime_cast_ne_zero
    {p d : ℕ} [NeZero p] (hp : p.Prime) (hd : 0 < d)
    (z : ZMod (p ^ d)) (hz : (z.cast : ZMod p) ≠ 0) : IsUnit z := by
  rw [← ZMod.natCast_zmod_val z]
  rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hd]
  intro hpz
  apply hz
  rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  exact hpz

/-- For `p ≥ 5`, any two roots of `3X² - 1` modulo a positive power of
`p` differ by a sign. -/
theorem cubicDerivative_root_eq_or_eq_neg
    {p d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 0 < d)
    {x y : ZMod (p ^ d)}
    (hx : cubicDerivative x = 0) (hy : cubicDerivative y = 0) :
    y = x ∨ y = -x := by
  letI : Fact p.Prime := ⟨hp⟩
  let castP : ZMod (p ^ d) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p hd.ne') (ZMod p)
  have hthree : IsUnit (3 : ZMod (p ^ d)) := by
    change IsUnit ((3 : ℕ) : ZMod (p ^ d))
    rw [ZMod.isUnit_natCast_iff_not_dvd_pow hp hd]
    intro hp3
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
    omega
  have hxunit : IsUnit x := by
    apply IsUnit.of_mul_eq_one (3 * x)
    have hx' : 3 * x ^ 2 = 1 := sub_eq_zero.mp hx
    rw [show x * (3 * x) = 3 * x ^ 2 by ring]
    exact hx'
  have hsq : x ^ 2 = y ^ 2 := by
    apply hthree.mul_left_cancel
    have hx' : 3 * x ^ 2 = 1 := sub_eq_zero.mp hx
    have hy' : 3 * y ^ 2 = 1 := sub_eq_zero.mp hy
    exact hx'.trans hy'.symm
  have hprod : (x - y) * (x + y) = 0 := by
    rw [show (x - y) * (x + y) = x ^ 2 - y ^ 2 by ring, hsq, sub_self]
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hzero
    have hp2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
    omega
  have hxcast : IsUnit (castP x) := hxunit.map castP
  by_cases hdiffcast : castP (x - y) ≠ 0
  · have hdiff : IsUnit (x - y) := by
      apply isUnit_of_prime_cast_ne_zero hp hd
      simpa [castP, ZMod.castHom_apply] using hdiffcast
    right
    have hsumzero : x + y = 0 := by
      apply hdiff.mul_left_cancel
      simpa using hprod
    exact eq_neg_of_add_eq_zero_right hsumzero
  · have hsumcast : castP (x + y) ≠ 0 := by
      intro hsumcast
      have hdiffzero : castP (x - y) = 0 := not_ne_iff.mp hdiffcast
      have h2x : (2 : ZMod p) * castP x = 0 := by
        calc
          (2 : ZMod p) * castP x = castP (x - y) + castP (x + y) := by
            simp only [map_sub, map_add]
            ring
          _ = 0 := by rw [hdiffzero, hsumcast, add_zero]
      exact hxcast.ne_zero ((mul_eq_zero.mp h2x).resolve_left htwo)
    have hsum : IsUnit (x + y) := by
      apply isUnit_of_prime_cast_ne_zero hp hd
      simpa [castP, ZMod.castHom_apply] using hsumcast
    left
    have hdiffzero : x - y = 0 := by
      apply hsum.mul_right_cancel
      simpa using hprod
    exact (sub_eq_zero.mp hdiffzero).symm

/-- Residues where the cubic phase is stationary. -/
def cubicDerivativeRootFinset (p d : ℕ) [NeZero p] :
    Finset (ZMod (p ^ d)) :=
  Finset.univ.filter fun x ↦ cubicDerivative x = 0

/-- At a prime `p ≥ 5`, the cubic derivative has at most two roots modulo
every positive power of `p`. -/
theorem card_cubicDerivativeRootFinset_le_two
    {p d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hd : 0 < d) :
    (cubicDerivativeRootFinset p d).card ≤ 2 := by
  classical
  let s := cubicDerivativeRootFinset p d
  change s.card ≤ 2
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    calc
      s.card ≤ ({x, -x} : Finset (ZMod (p ^ d))).card := by
        apply Finset.card_le_card
        intro y hy
        have hxroot : cubicDerivative x = 0 := by
          simpa [s, cubicDerivativeRootFinset] using hx
        have hyroot : cubicDerivative y = 0 := by
          simpa [s, cubicDerivativeRootFinset] using hy
        rcases cubicDerivative_root_eq_or_eq_neg hp hp5 hd hyroot hxroot with
          h | h
        · simp [h]
        · simp [h]
      _ ≤ 2 := Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

/-- Core.Reduction from `p^m` to `p^d` when `d ≤ m`. -/
def primePowerCast (p m d : ℕ) (hdm : d ≤ m) :
    ZMod (p ^ m) →+* ZMod (p ^ d) :=
  ZMod.castHom (pow_dvd_pow p hdm) (ZMod (p ^ d))

@[simp] theorem primePowerCast_apply
    (p m d : ℕ) (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    primePowerCast p m d hdm x = (x.cast : ZMod (p ^ d)) :=
  ZMod.castHom_apply x

/-- Every fiber of prime-power reduction from level `m` to level `d` has
cardinality `p^(m-d)`. -/
theorem card_primePowerCast_fiber
    {p m d : ℕ} [NeZero p] (hdm : d ≤ m) (y : ZMod (p ^ d)) :
    Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} =
      p ^ (m - d) := by
  have hsurj : Function.Surjective (primePowerCast p m d hdm) :=
    ZMod.castHom_surjective (pow_dvd_pow p hdm)
  have hfiber (z : ZMod (p ^ d)) :
      Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z} =
        Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
    have h := AddMonoidHom.card_fiber_eq_of_mem_range
      (primePowerCast p m d hdm).toAddMonoidHom
      (hsurj z) (hsurj y)
    simpa [Fintype.card_subtype] using h
  have htotal :
      Fintype.card (ZMod (p ^ m)) =
        Fintype.card (Σ z : ZMod (p ^ d),
          {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z}) :=
    Fintype.card_congr
      (Equiv.sigmaFiberEquiv (primePowerCast p m d hdm)).symm
  have hcard : p ^ m = p ^ d *
      Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
    calc
      p ^ m = Fintype.card (ZMod (p ^ m)) := (ZMod.card _).symm
      _ = Fintype.card (Σ z : ZMod (p ^ d),
          {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z}) := htotal
      _ = ∑ z : ZMod (p ^ d),
          Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = z} :=
        Fintype.card_sigma
      _ = ∑ _z : ZMod (p ^ d),
          Fintype.card {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
        apply Finset.sum_congr rfl
        intro z _hz
        exact hfiber z
      _ = p ^ d * Fintype.card
          {x : ZMod (p ^ m) // primePowerCast p m d hdm x = y} := by
        simp [ZMod.card]
  have hpow : p ^ m = p ^ d * p ^ (m - d) := by
    rw [← pow_add]
    congr 1
    omega
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (NeZero.pos p) d)
  exact hcard.symm.trans hpow

@[simp] theorem primePowerCast_cubicDerivative
    (p m d : ℕ) (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    primePowerCast p m d hdm (cubicDerivative x) =
      cubicDerivative (primePowerCast p m d hdm x) := by
  unfold cubicDerivative
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]

/-- Low residues whose cubic derivative vanishes after reduction to
`p^d`. -/
def cubicDerivativeCastRootFinset
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) :
    Finset (ZMod (p ^ m)) :=
  Finset.univ.filter fun x ↦
    primePowerCast p m d hdm (cubicDerivative x) = 0

/-- The number of stationary low residues is the number of roots modulo
`p^d` times the common reduction-fiber cardinality. -/
theorem card_cubicDerivativeCastRootFinset_eq
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) :
    (cubicDerivativeCastRootFinset p m d hdm).card =
      (cubicDerivativeRootFinset p d).card * p ^ (m - d) := by
  classical
  let castP := primePowerCast p m d hdm
  let P : ZMod (p ^ m) → Prop := fun x ↦
    castP (cubicDerivative x) = 0
  let f : ZMod (p ^ m) → ℕ := fun x ↦ if P x then 1 else 0
  have he := (Equiv.sigmaFiberEquiv castP).sum_comp f
  have hleft : (cubicDerivativeCastRootFinset p m d hdm).card =
      ∑ x : ZMod (p ^ m), f x := by
    unfold cubicDerivativeCastRootFinset
    simp [P, f, castP]
  have hright : (cubicDerivativeRootFinset p d).card =
      ∑ y : ZMod (p ^ d), if cubicDerivative y = 0 then 1 else 0 := by
    unfold cubicDerivativeRootFinset
    simp
  rw [hleft, hright]
  rw [← he, Fintype.sum_sigma, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyroot : cubicDerivative y = 0
  · simp only [hyroot, if_true, one_mul]
    calc
      (∑ x : {x : ZMod (p ^ m) // castP x = y}, f x) =
          ∑ _x : {x : ZMod (p ^ m) // castP x = y}, 1 := by
        apply Finset.sum_congr rfl
        intro x _hx
        have hxP : P x := by
          unfold P castP
          rw [primePowerCast_cubicDerivative, x.property, hyroot]
        simp [f, hxP]
      _ = Fintype.card {x : ZMod (p ^ m) // castP x = y} := by simp
      _ = p ^ (m - d) := by
        simpa [castP] using card_primePowerCast_fiber hdm y
  · simp only [hyroot, if_false, zero_mul]
    apply Finset.sum_eq_zero
    intro x _hx
    have hxnotP : ¬ P x := by
      intro hxP
      apply hyroot
      unfold P castP at hxP
      rw [primePowerCast_cubicDerivative, x.property] at hxP
      exact hxP
    simp [f, hxnotP]

/-- For `p ≥ 5`, at most `2p^(m-d)` low residues are stationary modulo
`p^d`. -/
theorem card_cubicDerivativeCastRootFinset_le
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : 0 < d) (hdm : d ≤ m) :
    (cubicDerivativeCastRootFinset p m d hdm).card ≤
      2 * p ^ (m - d) := by
  rw [card_cubicDerivativeCastRootFinset_eq]
  exact Nat.mul_le_mul_right (p ^ (m - d))
    (card_cubicDerivativeRootFinset_le_two hp hp5 hd)

private theorem cast_cubicDerivative_natCast_eq_primePowerCast
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    ZMod.castHom (dvd_mul_left (p ^ d) (p ^ m)) (ZMod (p ^ d))
        (cubicDerivative (x.val : ZMod (p ^ m * p ^ d))) =
        primePowerCast p m d hdm (cubicDerivative x) := by
  unfold cubicDerivative primePowerCast
  simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
  congr 1
  simp only [ZMod.castHom_apply]
  rw [ZMod.cast_natCast (dvd_mul_left (p ^ d) (p ^ m)) x.val,
    ZMod.cast_eq_val]

/-- At an odd residue, the derivative of `x^3 - x` is congruent to `2`
modulo `4`. Hence it cannot be stationary modulo `4`. -/
theorem primePowerCast_cubicDerivative_two_ne_zero
    {m : ℕ} (hm : 2 ≤ m) (x : ZMod (2 ^ m)) (hx : IsUnit x) :
    primePowerCast 2 m 2 hm (cubicDerivative x) ≠ 0 := by
  let y : ZMod (2 ^ 2) := primePowerCast 2 m 2 hm x
  have hy : IsUnit y := by
    exact hx.map (primePowerCast 2 m 2 hm)
  have hderiv : cubicDerivative y ≠ 0 := by
    have hylt : y.val < 4 := by simpa using ZMod.val_lt y
    interval_cases hval : y.val
    · have hyval : y = 0 := by
        apply ZMod.val_injective 4
        calc
          y.val = 0 := hval
          _ = (0 : ZMod 4).val :=
            (ZMod.val_natCast_of_lt (by norm_num : 0 < 4)).symm
      rw [hyval] at hy ⊢
      exfalso
      exact (by decide : ¬ IsUnit (0 : ZMod 4)) hy
    · have hyval : y = 1 := by
        apply ZMod.val_injective 4
        calc
          y.val = 1 := hval
          _ = (1 : ZMod 4).val :=
            (ZMod.val_natCast_of_lt (by norm_num : 1 < 4)).symm
      rw [hyval] at ⊢
      decide
    · have hyval : y = 2 := by
        apply ZMod.val_injective 4
        calc
          y.val = 2 := hval
          _ = (2 : ZMod 4).val :=
            (ZMod.val_natCast_of_lt (by norm_num : 2 < 4)).symm
      rw [hyval] at hy ⊢
      exfalso
      exact (by decide : ¬ IsUnit (2 : ZMod 4)) hy
    · have hyval : y = 3 := by
        apply ZMod.val_injective 4
        calc
          y.val = 3 := hval
          _ = (3 : ZMod 4).val :=
            (ZMod.val_natCast_of_lt (by norm_num : 3 < 4)).symm
      rw [hyval] at ⊢
      decide
  have hcast : primePowerCast 2 m 2 hm (cubicDerivative x) =
      cubicDerivative y := by
    change primePowerCast 2 m 2 hm (cubicDerivative x) =
      cubicDerivative (primePowerCast 2 m 2 hm x)
    unfold cubicDerivative
    simp only [map_sub, map_mul, map_pow, map_ofNat, map_one]
  rw [hcast]
  exact hderiv

/-- A primitive unit frequency gives exact cancellation for the unit cubic
sum modulo `2^m * 4` once `m ≥ 2`. The derivative at every unit is nonzero
in the high block `ZMod 4`, so the stationary-phase decomposition has no
stationary terms. -/
theorem unitCubicExponentialSum_two_power_block_eq_zero
    {m : ℕ} (hm : 2 ≤ m)
    (a : ZMod (2 ^ m * 2 ^ 2)) (ha : IsUnit a) :
    unitCubicExponentialSum a = 0 := by
  letI : NeZero 2 := ⟨by norm_num⟩
  apply unitCubicExponentialSum_primePower_block_eq_zero
    (p := 2) Nat.prime_two (by omega) (by omega) a
  intro x hx
  let castHigh : ZMod (2 ^ m * 2 ^ 2) →+* ZMod (2 ^ 2) :=
    ZMod.castHom (dvd_mul_left (2 ^ 2) (2 ^ m)) (ZMod (2 ^ 2))
  have haHigh : IsUnit (castHigh a) := ha.map castHigh
  have hderiv := cast_cubicDerivative_natCast_eq_primePowerCast
    2 m 2 (by omega) x
  change castHigh (cubicDerivative (x.val : ZMod (2 ^ m * 2 ^ 2))) =
      primePowerCast 2 m 2 (by omega) (cubicDerivative x) at hderiv
  have hderiv_ne := primePowerCast_cubicDerivative_two_ne_zero hm x hx
  intro hzero
  change castHigh (a * cubicDerivative
    (x.val : ZMod (2 ^ m * 2 ^ 2))) = 0 at hzero
  have hzero' : castHigh a *
      castHigh (cubicDerivative (x.val : ZMod (2 ^ m * 2 ^ 2))) = 0 := by
    simpa only [map_mul] using hzero
  have hzero_deriv : castHigh
      (cubicDerivative (x.val : ZMod (2 ^ m * 2 ^ 2))) = 0 :=
    haHigh.mul_left_cancel hzero'
  exact hderiv_ne (by rw [← hderiv]; exact hzero_deriv)

/-- Consequently every positive-arity singular-series coefficient at a
modulus `2^m * 4`, `m ≥ 2`, vanishes: each unit frequency has zero cubic
complete sum. -/
theorem singularSeriesCoefficient_two_power_block_eq_zero
    {m n T : ℕ} (hm : 2 ≤ m) (hn : 0 < n) :
    CookMagyarFiniteFourier.singularSeriesCoefficient
      (2 ^ m * 2 ^ 2) n T (by positivity) = 0 := by
  let q := 2 ^ m * 2 ^ 2
  have hq : q ≠ 0 := by dsimp [q]; positivity
  letI : NeZero q := ⟨hq⟩
  have hsum : (∑ a : (ZMod q)ˣ,
      CookMagyarFiniteFourier.unitCubicExponentialSum (a : ZMod q) ^ n *
        CookMagyarFiniteFourier.standardAdditiveCharacter
          (-((a : ZMod q) * (T : ZMod q)))) = 0 := by
    apply Finset.sum_eq_zero
    intro a _ha
    rw [unitCubicExponentialSum_two_power_block_eq_zero hm a a.isUnit]
    simp [hn.ne']
  change ((Nat.totient q : ℂ)⁻¹) ^ n *
      (∑ a : (ZMod q)ˣ,
        CookMagyarFiniteFourier.unitCubicExponentialSum (a : ZMod q) ^ n *
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod q) * (T : ZMod q)))) = 0
  rw [hsum]
  simp

/-- Exponent-indexed form of the high-conductor coefficient cancellation. -/
theorem singularSeriesCoefficient_two_power_exponent_eq_zero
    {m n T : ℕ} (hm : 2 ≤ m) (hn : 0 < n) :
    CookMagyarFiniteFourier.singularSeriesCoefficient
      (2 ^ (m + 2)) n T (by positivity) = 0 := by
  simpa [Nat.pow_add] using
    (singularSeriesCoefficient_two_power_block_eq_zero (m := m) hm hn)

/-- The corresponding singular-series terms vanish at every power of `2`
from exponent `4` onward. -/
theorem singularSeriesTerm_two_power_exponent_eq_zero
    {m n T : ℕ} (hm : 2 ≤ m) (hn : 0 < n) :
    CookMagyarFiniteFourier.singularSeriesTerm n T (2 ^ (m + 2)) = 0 := by
  have hq : 0 < 2 ^ (m + 2) := pow_pos (by norm_num : 0 < (2 : ℕ)) _
  rw [CookMagyarFiniteFourier.singularSeriesTerm_of_pos n T hq]
  exact singularSeriesCoefficient_two_power_exponent_eq_zero hm hn

/-- Thus the formal `2`-adic local factor reduces to its first three prime
powers whenever the represented arity is positive. -/
theorem primeLocalFactor_two_eq_first_three_terms
    {n T : ℕ} (hn : 0 < n) :
    CookMagyarFiniteFourier.primeLocalFactor 2 n T =
      1 + CookMagyarFiniteFourier.singularSeriesTerm n T 2 +
        CookMagyarFiniteFourier.singularSeriesTerm n T 4 +
          CookMagyarFiniteFourier.singularSeriesTerm n T 8 := by
  unfold CookMagyarFiniteFourier.primeLocalFactor
  rw [tsum_eq_sum (s := Finset.range 3) (fun k hk ↦ ?_)]
  · simp [Finset.sum_range_succ, add_assoc]
  · have hk : 3 ≤ k := by
      simpa only [Finset.mem_range, not_lt] using hk
    have hkexp : k + 1 = (k - 1) + 2 := by omega
    rw [hkexp]
    exact singularSeriesTerm_two_power_exponent_eq_zero (by omega) hn

/-- The unit cubic sum at modulus `2` is identically one. -/
theorem unitCubicExponentialSum_mod_two (a : ZMod 2) :
    CookMagyarFiniteFourier.unitCubicExponentialSum a = 1 := by
  have hzero (u : (ZMod 2)ˣ) :
      CookMagyarFiniteFourier.cubicResidue (u : ZMod 2) = 0 := by
    have huval : (u : ZMod 2).val ≠ 0 := by
      intro h
      exact u.isUnit.ne_zero ((ZMod.val_eq_zero (u : ZMod 2)).mp h)
    have huval' : (u : ZMod 2).val = 1 := by
      have hlt := ZMod.val_lt (u : ZMod 2)
      omega
    have hu : (u : ZMod 2) = 1 := by
      apply ZMod.val_injective 2
      calc
        (u : ZMod 2).val = 1 := huval'
        _ = (1 : ZMod 2).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 1 < 2)).symm
    simp [CookMagyarFiniteFourier.cubicResidue, hu]
  simp [CookMagyarFiniteFourier.unitCubicExponentialSum, hzero,
    ZMod.card_units_eq_totient]

private theorem cubicResidue_eq_zero_of_unit_mod_four
    (x : ZMod 4) (hx : IsUnit x) :
    CookMagyarFiniteFourier.cubicResidue x = 0 := by
  have hxlt : x.val < 4 := ZMod.val_lt x
  interval_cases hval : x.val
  · have hxval : x = 0 := by
      apply ZMod.val_injective 4
      calc
        x.val = 0 := hval
        _ = (0 : ZMod 4).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 0 < 4)).symm
    rw [hxval] at hx
    exfalso
    exact (by decide : ¬ IsUnit (0 : ZMod 4)) hx
  · have hxval : x = 1 := by
      apply ZMod.val_injective 4
      calc
        x.val = 1 := hval
        _ = (1 : ZMod 4).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 1 < 4)).symm
    rw [hxval]
    norm_num [CookMagyarFiniteFourier.cubicResidue]
  · have hxval : x = 2 := by
      apply ZMod.val_injective 4
      calc
        x.val = 2 := hval
        _ = (2 : ZMod 4).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 2 < 4)).symm
    rw [hxval] at hx
    exfalso
    exact (by decide : ¬ IsUnit (2 : ZMod 4)) hx
  · have hxval : x = 3 := by
      apply ZMod.val_injective 4
      calc
        x.val = 3 := hval
        _ = (3 : ZMod 4).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 3 < 4)).symm
    rw [hxval]
    decide

/-- Modulo `4`, every unit is a zero of `X^3-X`. -/
theorem unitCubicExponentialSum_mod_four (a : ZMod 4) :
    CookMagyarFiniteFourier.unitCubicExponentialSum a = 2 := by
  calc
    CookMagyarFiniteFourier.unitCubicExponentialSum a =
        ∑ u : (ZMod 4)ˣ, (1 : ℂ) := by
      unfold CookMagyarFiniteFourier.unitCubicExponentialSum
      apply Finset.sum_congr rfl
      intro u _hu
      rw [cubicResidue_eq_zero_of_unit_mod_four (u : ZMod 4) u.isUnit]
      simp
    _ = 2 := by exact_mod_cast (show Nat.totient 4 = 2 by decide)

private theorem cubicResidue_eq_zero_of_unit_mod_eight
    (x : ZMod 8) (hx : IsUnit x) :
    CookMagyarFiniteFourier.cubicResidue x = 0 := by
  have hxlt : x.val < 8 := ZMod.val_lt x
  interval_cases hval : x.val
  · have hxval : x = 0 := by
      apply ZMod.val_injective 8
      calc
        x.val = 0 := hval
        _ = (0 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 0 < 8)).symm
    rw [hxval] at hx
    exfalso
    exact (by decide : ¬ IsUnit (0 : ZMod 8)) hx
  · have hxval : x = 1 := by
      apply ZMod.val_injective 8
      calc
        x.val = 1 := hval
        _ = (1 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 1 < 8)).symm
    rw [hxval]
    decide
  · have hxval : x = 2 := by
      apply ZMod.val_injective 8
      calc
        x.val = 2 := hval
        _ = (2 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 2 < 8)).symm
    rw [hxval] at hx
    exfalso
    exact (by decide : ¬ IsUnit (2 : ZMod 8)) hx
  · have hxval : x = 3 := by
      apply ZMod.val_injective 8
      calc
        x.val = 3 := hval
        _ = (3 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 3 < 8)).symm
    rw [hxval]
    decide
  · have hxval : x = 4 := by
      apply ZMod.val_injective 8
      calc
        x.val = 4 := hval
        _ = (4 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 4 < 8)).symm
    rw [hxval] at hx
    exfalso
    exact (by decide : ¬ IsUnit (4 : ZMod 8)) hx
  · have hxval : x = 5 := by
      apply ZMod.val_injective 8
      calc
        x.val = 5 := hval
        _ = (5 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 5 < 8)).symm
    rw [hxval]
    decide
  · have hxval : x = 6 := by
      apply ZMod.val_injective 8
      calc
        x.val = 6 := hval
        _ = (6 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 6 < 8)).symm
    rw [hxval] at hx
    exfalso
    exact (by decide : ¬ IsUnit (6 : ZMod 8)) hx
  · have hxval : x = 7 := by
      apply ZMod.val_injective 8
      calc
        x.val = 7 := hval
        _ = (7 : ZMod 8).val :=
          (ZMod.val_natCast_of_lt (by norm_num : 7 < 8)).symm
    rw [hxval]
    decide

/-- Modulo `8`, every unit is a zero of `X^3-X`. -/
theorem unitCubicExponentialSum_mod_eight (a : ZMod 8) :
    CookMagyarFiniteFourier.unitCubicExponentialSum a = 4 := by
  calc
    CookMagyarFiniteFourier.unitCubicExponentialSum a =
        ∑ u : (ZMod 8)ˣ, (1 : ℂ) := by
      unfold CookMagyarFiniteFourier.unitCubicExponentialSum
      apply Finset.sum_congr rfl
      intro u _hu
      rw [cubicResidue_eq_zero_of_unit_mod_eight (u : ZMod 8) u.isUnit]
      simp
    _ = 4 := by exact_mod_cast (show Nat.totient 8 = 4 by decide)

/-- The normalized coefficient at conductor two is just its single
nontrivial additive character. -/
theorem singularSeriesCoefficient_two_eq_unit_character
    (n T : ℕ) :
    CookMagyarFiniteFourier.singularSeriesCoefficient 2 n T (by norm_num) =
      CookMagyarFiniteFourier.standardAdditiveCharacter
        (-((1 : ZMod 2) * (T : ZMod 2))) := by
  letI : NeZero 2 := ⟨by norm_num⟩
  have hunit (u : (ZMod 2)ˣ) : (u : ZMod 2) = 1 := by
    have huv : (u : ZMod 2).val ≠ 0 := by
      intro h
      exact u.isUnit.ne_zero ((ZMod.val_eq_zero (u : ZMod 2)).mp h)
    have hval : (u : ZMod 2).val = 1 := by
      have := ZMod.val_lt (u : ZMod 2)
      omega
    apply ZMod.val_injective 2
    calc
      (u : ZMod 2).val = 1 := hval
      _ = (1 : ZMod 2).val :=
        (ZMod.val_natCast_of_lt (by norm_num : 1 < 2)).symm
  have htot : (Nat.totient 2 : ℂ) = 1 := by
    exact_mod_cast (show Nat.totient 2 = 1 by decide)
  rw [CookMagyarFiniteFourier.singularSeriesCoefficient]
  simp_rw [CookMagyarPrimePower.unitCubicExponentialSum_mod_two]
  rw [htot]
  have hsum :
      (∑ u : (ZMod 2)ˣ,
        (1 : ℂ) ^ n *
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((u : ZMod 2) * (T : ZMod 2)))) =
        CookMagyarFiniteFourier.standardAdditiveCharacter
          (-((1 : ZMod 2) * (T : ZMod 2))) := by
    calc
      _ = ∑ _u : (ZMod 2)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((1 : ZMod 2) * (T : ZMod 2))) := by
          apply Finset.sum_congr rfl
          intro u _
          simp [hunit u]
      _ = _ := by
        simp [ZMod.card_units_eq_totient]
  rw [hsum]
  simp

/-- At modulus four, normalization by the number of units cancels the
constant unit cubic sum. Thus the coefficient is exactly the unit additive
character sum (the classical Ramanujan sum at conductor four). -/
theorem singularSeriesCoefficient_four_eq_unit_character_sum
    (n T : ℕ) :
    CookMagyarFiniteFourier.singularSeriesCoefficient 4 n T (by norm_num) =
      ∑ a : (ZMod 4)ˣ,
        CookMagyarFiniteFourier.standardAdditiveCharacter
          (-((a : ZMod 4) * (T : ZMod 4))) := by
  letI : NeZero 4 := ⟨by norm_num⟩
  rw [CookMagyarFiniteFourier.singularSeriesCoefficient]
  simp_rw [CookMagyarPrimePower.unitCubicExponentialSum_mod_four]
  have htot : (Nat.totient 4 : ℂ) = 2 := by
    exact_mod_cast (show Nat.totient 4 = 2 by decide)
  rw [htot]
  rw [← Finset.mul_sum]
  have hcancel : ((2 : ℂ)⁻¹) ^ n * (2 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((2 : ℂ)⁻¹) ^ n * ((2 : ℂ) ^ n *
        ∑ a : (ZMod 4)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod 4) * (T : ZMod 4)))) =
      (((2 : ℂ)⁻¹) ^ n * (2 : ℂ) ^ n) *
        ∑ a : (ZMod 4)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod 4) * (T : ZMod 4))) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- At modulus eight, normalization by the number of units cancels the
constant unit cubic sum, leaving only the target-dependent additive
character sum. -/
theorem singularSeriesCoefficient_eight_eq_unit_character_sum
    (n T : ℕ) :
    CookMagyarFiniteFourier.singularSeriesCoefficient 8 n T (by norm_num) =
      ∑ a : (ZMod 8)ˣ,
        CookMagyarFiniteFourier.standardAdditiveCharacter
          (-((a : ZMod 8) * (T : ZMod 8))) := by
  letI : NeZero 8 := ⟨by norm_num⟩
  rw [CookMagyarFiniteFourier.singularSeriesCoefficient]
  simp_rw [CookMagyarPrimePower.unitCubicExponentialSum_mod_eight]
  have htot : (Nat.totient 8 : ℂ) = 4 := by
    exact_mod_cast (show Nat.totient 8 = 4 by decide)
  rw [htot]
  rw [← Finset.mul_sum]
  have hcancel : ((4 : ℂ)⁻¹) ^ n * (4 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    ((4 : ℂ)⁻¹) ^ n * ((4 : ℂ) ^ n *
        ∑ a : (ZMod 8)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod 8) * (T : ZMod 8)))) =
      (((4 : ℂ)⁻¹) ^ n * (4 : ℂ) ^ n) *
        ∑ a : (ZMod 8)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod 8) * (T : ZMod 8))) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- The complete two-adic factor at positive arity consists of the
single-frequency conductor-two term and the two unit-character sums at
conductors four and eight. All higher conductors vanish. -/
theorem primeLocalFactor_two_eq_low_conductor_character_sums
    {n T : ℕ} (hn : 0 < n) :
    CookMagyarFiniteFourier.primeLocalFactor 2 n T =
      1 + CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((1 : ZMod 2) * (T : ZMod 2))) +
        (∑ a : (ZMod 4)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod 4) * (T : ZMod 4)))) +
        (∑ a : (ZMod 8)ˣ,
          CookMagyarFiniteFourier.standardAdditiveCharacter
            (-((a : ZMod 8) * (T : ZMod 8)))) := by
  rw [primeLocalFactor_two_eq_first_three_terms hn]
  rw [CookMagyarFiniteFourier.singularSeriesTerm_of_pos n T (by norm_num)]
  rw [CookMagyarFiniteFourier.singularSeriesTerm_of_pos n T (by norm_num)]
  rw [CookMagyarFiniteFourier.singularSeriesTerm_of_pos n T (by norm_num)]
  rw [singularSeriesCoefficient_two_eq_unit_character,
    singularSeriesCoefficient_four_eq_unit_character_sum,
    singularSeriesCoefficient_eight_eq_unit_character_sum]

/-- On every admissible 2-adic target, each surviving additive character is
one. The complete local factor is therefore exactly eight. -/
theorem primeLocalFactor_two_eq_eight_of_dvd_eight
    {n T : ℕ} (hn : 0 < n) (hT : 8 ∣ T) :
    CookMagyarFiniteFourier.primeLocalFactor 2 n T = 8 := by
  obtain ⟨u, rfl⟩ := hT
  have h2 : ((8 * u : ℕ) : ZMod 2) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (8 * u) 2).2 ⟨4 * u, by ring⟩
  have h4 : ((8 * u : ℕ) : ZMod 4) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (8 * u) 4).2 ⟨2 * u, by ring⟩
  have h8 : ((8 * u : ℕ) : ZMod 8) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (8 * u) 8).2 ⟨u, rfl⟩
  rw [primeLocalFactor_two_eq_low_conductor_character_sums hn]
  simp [h2, h4, h8, ZMod.card_units_eq_totient,
    show Nat.totient 4 = 2 by decide, show Nat.totient 8 = 4 by decide]
  norm_num

/-- In particular, the real part of the two-adic local factor is strictly
positive on Cook--Magyar's admissible targets. -/
theorem primeLocalFactor_two_re_pos_of_dvd_twentyFour
    {n T : ℕ} (hn : 0 < n) (hT : 24 ∣ T) :
    0 < (CookMagyarFiniteFourier.primeLocalFactor 2 n T).re := by
  have h8 : 8 ∣ T := dvd_trans (by norm_num : 8 ∣ 24) hT
  rw [primeLocalFactor_two_eq_eight_of_dvd_eight hn h8]
  norm_num

/-- Stationary phase gives square-root-scale cancellation for the
unit-restricted cubic sum over a balanced prime-power block. -/
theorem norm_unitCubicExponentialSum_primePower_block_le
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hd : 0 < d) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d)) (ha : IsUnit a) :
    ‖unitCubicExponentialSum a‖ ≤ 2 * (p : ℝ) ^ m := by
  classical
  let s := cubicDerivativeCastRootFinset p m d hdm
  let castHigh : ZMod (p ^ m * p ^ d) →+* ZMod (p ^ d) :=
    ZMod.castHom (dvd_mul_left (p ^ d) (p ^ m)) (ZMod (p ^ d))
  have haHigh : IsUnit (castHigh a) := ha.map castHigh
  have hcondition (x : ZMod (p ^ m)) :
      (((a * cubicDerivative
        (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0) ↔
          x ∈ s := by
    have hderiv := cast_cubicDerivative_natCast_eq_primePowerCast
      p m d hdm x
    change castHigh (cubicDerivative
      (x.val : ZMod (p ^ m * p ^ d))) =
        primePowerCast p m d hdm (cubicDerivative x) at hderiv
    change castHigh (a * cubicDerivative
      (x.val : ZMod (p ^ m * p ^ d))) = 0 ↔ x ∈ s
    rw [map_mul, hderiv]
    constructor
    · intro hzero
      have hderivzero : primePowerCast p m d hdm (cubicDerivative x) = 0 := by
        apply haHigh.mul_left_cancel
        simpa using hzero
      simpa [s, cubicDerivativeCastRootFinset] using hderivzero
    · intro hx
      have hderivzero : primePowerCast p m d hdm (cubicDerivative x) = 0 := by
        simpa [s, cubicDerivativeCastRootFinset] using hx
      rw [hderivzero, mul_zero]
  rw [unitCubicExponentialSum_primePower_block hp hm hdm a]
  calc
    ‖∑ x : ZMod (p ^ m), if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0‖ ≤
      ∑ x : ZMod (p ^ m), ‖if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod (p ^ m),
        if x ∈ s then (p ^ d : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hxs : x ∈ s
      · have hc := (hcondition x).2 hxs
        by_cases hxunit : IsUnit x
        · rw [if_pos hxunit, if_pos hc]
          simp [hxs, AddChar.norm_apply]
        · rw [if_neg hxunit]
          simp [hxs]
      · have hc := (hcondition x).not.mpr hxs
        by_cases hxunit : IsUnit x
        · rw [if_pos hxunit, if_neg hc]
          simp [hxs]
        · rw [if_neg hxunit]
          simp [hxs]
    _ = ∑ _x ∈ s, (p ^ d : ℝ) :=
      Finset.sum_ite_mem_eq s (fun _x ↦ (p ^ d : ℝ))
    _ = (s.card : ℝ) * (p ^ d : ℝ) := by
      simp [nsmul_eq_mul]
    _ ≤ ((2 * p ^ (m - d) : ℕ) : ℝ) * (p ^ d : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_cubicDerivativeCastRootFinset_le hp hp5 hd hdm
      · positivity
    _ = 2 * (p : ℝ) ^ m := by
      push_cast
      have hpowers : (p : ℝ) ^ (m - d) * (p : ℝ) ^ d =
          (p : ℝ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hdm]
      rw [mul_assoc, hpowers]

/-- The stationary-phase estimate summed over all unit frequencies and
normalized as a singular-series coefficient. -/
theorem norm_singularSeriesTerm_primePower_block_le
    {p m d n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hd : 0 < d) (hdm : d ≤ m) :
    ‖singularSeriesTerm n T (p ^ m * p ^ d)‖ ≤
      ‖((Nat.totient (p ^ m * p ^ d) : ℂ)⁻¹)‖ ^ n *
        (Nat.totient (p ^ m * p ^ d) : ℝ) *
          (2 * (p : ℝ) ^ m) ^ n := by
  rw [singularSeriesTerm_of_pos n T (by positivity)]
  unfold singularSeriesCoefficient
  rw [norm_mul, norm_pow]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∑ a : (ZMod (p ^ m * p ^ d))ˣ,
        unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
          standardAdditiveCharacter
            (-((a : ZMod (p ^ m * p ^ d)) *
              (T : ZMod (p ^ m * p ^ d))))‖ ≤
        ∑ a : (ZMod (p ^ m * p ^ d))ˣ,
          ‖unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
            standardAdditiveCharacter
              (-((a : ZMod (p ^ m * p ^ d)) *
                (T : ZMod (p ^ m * p ^ d))))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod (p ^ m * p ^ d))ˣ,
        (2 * (p : ℝ) ^ m) ^ n := by
      apply Finset.sum_le_sum
      intro a _ha
      have hsum := norm_unitCubicExponentialSum_primePower_block_le
        hp hp5 hm hd hdm (a : ZMod (p ^ m * p ^ d)) a.isUnit
      calc
        ‖unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
            standardAdditiveCharacter
              (-((a : ZMod (p ^ m * p ^ d)) *
                (T : ZMod (p ^ m * p ^ d))))‖ =
            ‖unitCubicExponentialSum
              (a : ZMod (p ^ m * p ^ d))‖ ^ n := by
                simp [norm_pow, AddChar.norm_apply]
        _ ≤ (2 * (p : ℝ) ^ m) ^ n :=
          pow_le_pow_left₀
            (norm_nonneg (unitCubicExponentialSum
              (a : ZMod (p ^ m * p ^ d)))) hsum n
    _ = (Nat.totient (p ^ m * p ^ d) : ℝ) *
        (2 * (p : ℝ) ^ m) ^ n := by
      simp [ZMod.card_units_eq_totient, nsmul_eq_mul]

/-- The normalized stationary-phase bound at every positive even
prime-power level. -/
theorem norm_singularSeriesTerm_primePower_even_le
    {p m n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) :
    ‖singularSeriesTerm n T (p ^ (2 * m))‖ ≤
      ‖((Nat.totient (p ^ (2 * m)) : ℂ)⁻¹)‖ ^ n *
        (Nat.totient (p ^ (2 * m)) : ℝ) *
          (2 * (p : ℝ) ^ m) ^ n := by
  have h := norm_singularSeriesTerm_primePower_block_le
    (p := p) (m := m) (d := m) (n := n) (T := T)
    hp hp5 hm (by omega) (by omega)
  simpa only [← pow_add, two_mul] using h

/-- The normalized stationary-phase bound at every odd prime-power level
strictly above the prime modulus. -/
theorem norm_singularSeriesTerm_primePower_odd_le
    {p m n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) :
    ‖singularSeriesTerm n T (p ^ (2 * m + 1))‖ ≤
      ‖((Nat.totient (p ^ (2 * m + 1)) : ℂ)⁻¹)‖ ^ n *
        (Nat.totient (p ^ (2 * m + 1)) : ℝ) *
          (2 * (p : ℝ) ^ (m + 1)) ^ n := by
  have h := norm_singularSeriesTerm_primePower_block_le
    (p := p) (m := m + 1) (d := m) (n := n) (T := T)
    hp hp5 (by omega) (by omega) (by omega)
  have hexp : m + 1 + m = 2 * m + 1 := by omega
  simpa only [← pow_add, hexp] using h

end CookMagyarPrimePower
end SystolicGrowth
