module

/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import CookMagyar.LocalCount
public import CookMagyar.LocalSmallPrimes

@[expose] public section

open scoped BigOperators

namespace SystolicGrowth
namespace CookMagyarSmallPrimeCounts

open CookMagyarLocal
open CookMagyarFiniteFourier

/-! # Quantitative local counts at two and three

This file upgrades the explicit exceptional-prime solutions to large,
injectively parametrized families.  The free coordinates range through a
fixed-index subset of the units; the remaining coordinate is obtained from
an explicit permutation polynomial.  Consequently the normalized local
count has a positive lower bound independent of the prime-power exponent.
-/

/-! ## A one-coordinate solver at powers of two -/

/-- Parameter polynomial in the identity
`(1 + 4z)^3 - (1 + 4z) = 8 * twoAdicSingleParameter z`. -/
def twoAdicSingleParameter {k : ℕ} (z : ZMod (2 ^ k)) : ZMod (2 ^ k) :=
  z + 6 * z ^ 2 + 8 * z ^ 3

theorem isUnit_twoAdicSingleParameter_differenceFactor (k : ℕ)
    (x y : ZMod (2 ^ k)) :
    IsUnit (1 + 6 * (x + y) + 8 * (x ^ 2 + x * y + y ^ 2)) := by
  have hn : IsNilpotent
      ((2 : ZMod (2 ^ k)) *
        (3 * (x + y) + 4 * (x ^ 2 + x * y + y ^ 2))) :=
    prime_mul_isNilpotent 2 k _
  convert hn.isUnit_one_add using 1
  ring

theorem twoAdicSingleParameter_injective (k : ℕ) :
    Function.Injective
      (twoAdicSingleParameter : ZMod (2 ^ k) → ZMod (2 ^ k)) := by
  intro x y hxy
  have hfactor :
      (x - y) *
        (1 + 6 * (x + y) + 8 * (x ^ 2 + x * y + y ^ 2)) = 0 := by
    calc
      _ = twoAdicSingleParameter x - twoAdicSingleParameter y := by
        simp only [twoAdicSingleParameter]
        ring
      _ = 0 := sub_eq_zero.mpr hxy
  have hu := isUnit_twoAdicSingleParameter_differenceFactor k x y
  have hzero : x - y = 0 := by
    apply hu.mul_right_cancel
    simpa using hfactor
  exact sub_eq_zero.mp hzero

theorem twoAdicSingleParameter_surjective (k : ℕ) :
    Function.Surjective
      (twoAdicSingleParameter : ZMod (2 ^ k) → ZMod (2 ^ k)) :=
  Finite.surjective_of_injective (twoAdicSingleParameter_injective k)

noncomputable def twoAdicSinglePreimage (k : ℕ) (m : ZMod (2 ^ k)) :
    ZMod (2 ^ k) :=
  Classical.choose (twoAdicSingleParameter_surjective k m)

@[simp] theorem twoAdicSingleParameter_preimage (k : ℕ)
    (m : ZMod (2 ^ k)) :
    twoAdicSingleParameter (twoAdicSinglePreimage k m) = m :=
  Classical.choose_spec (twoAdicSingleParameter_surjective k m)

theorem cubicResidue_one_add_four_mul (k : ℕ) (z : ZMod (2 ^ k)) :
    CookMagyarLocal.cubicResidue (1 + 4 * z) =
      8 * twoAdicSingleParameter z := by
  simp only [CookMagyarLocal.cubicResidue, twoAdicSingleParameter]
  ring

theorem one_add_four_mul_isUnit (k : ℕ) (z : ZMod (2 ^ k)) :
    IsUnit (1 + 4 * z) := by
  have hn : IsNilpotent ((2 : ZMod (2 ^ k)) * (2 * z)) :=
    prime_mul_isNilpotent 2 k _
  convert hn.isUnit_one_add using 1
  ring

/-! ## Injective free-coordinate ranges -/

/-- Number of freely parametrized unit coordinates at modulus `2 ^ k`. -/
def twoFreeCard (k : ℕ) : ℕ := 2 ^ (k - 2)

/-- Number of freely parametrized unit coordinates at modulus `3 ^ k`. -/
def threeFreeCard (k : ℕ) : ℕ := 3 ^ (k - 1)

def twoFreeValue (k : ℕ) (a : Fin (twoFreeCard k)) : ZMod (2 ^ k) :=
  1 + 4 * (a.val : ZMod (2 ^ k))

def threeFreeValue (k : ℕ) (a : Fin (threeFreeCard k)) : ZMod (3 ^ k) :=
  1 + 3 * (a.val : ZMod (3 ^ k))

theorem four_mul_twoFree_lt (k : ℕ) (a : Fin (twoFreeCard k)) :
    4 * a.val < 2 ^ k := by
  by_cases hk : 2 ≤ k
  · have hkdecomp : k - 2 + 2 = k := Nat.sub_add_cancel hk
    have hpow : 4 * 2 ^ (k - 2) = 2 ^ k := by
      calc
        4 * 2 ^ (k - 2) = 2 ^ (k - 2) * 2 ^ 2 := by ring
        _ = 2 ^ (k - 2 + 2) := by rw [pow_add]
        _ = 2 ^ k := by rw [hkdecomp]
    rw [← hpow]
    have ha : a.val < 2 ^ (k - 2) := by
      simpa [twoFreeCard] using a.isLt
    omega
  · have hklt : k < 2 := Nat.lt_of_not_ge hk
    interval_cases k
    · have ha := a.isLt
      simp [twoFreeCard] at ha
      norm_num [ha]
    · have ha := a.isLt
      simp [twoFreeCard] at ha
      norm_num [ha]

theorem three_mul_threeFree_lt (k : ℕ) (a : Fin (threeFreeCard k)) :
    3 * a.val < 3 ^ k := by
  by_cases hk : 1 ≤ k
  · have hkdecomp : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hpow : 3 * 3 ^ (k - 1) = 3 ^ k := by
      calc
        3 * 3 ^ (k - 1) = 3 ^ (k - 1) * 3 ^ 1 := by ring
        _ = 3 ^ (k - 1 + 1) := by rw [pow_add]
        _ = 3 ^ k := by rw [hkdecomp]
    rw [← hpow]
    have ha : a.val < 3 ^ (k - 1) := by
      simpa [threeFreeCard] using a.isLt
    omega
  · have hkzero : k = 0 := by omega
    subst k
    have ha := a.isLt
    simp [threeFreeCard] at ha
    norm_num [ha]

theorem twoFreeValue_injective (k : ℕ) :
    Function.Injective (twoFreeValue k) := by
  intro a b hab
  have hmul :
      (4 * a.val : ZMod (2 ^ k)) = (4 * b.val : ZMod (2 ^ k)) := by
    have h := congrArg (fun z : ZMod (2 ^ k) ↦ z - 1) hab
    simpa [twoFreeValue] using h
  have hcast :
      ((4 * a.val : ℕ) : ZMod (2 ^ k)) =
        ((4 * b.val : ℕ) : ZMod (2 ^ k)) := by
    simpa [Nat.cast_mul] using hmul
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have heq := hmod.eq_of_lt_of_lt
    (four_mul_twoFree_lt k a) (four_mul_twoFree_lt k b)
  exact Fin.ext (Nat.mul_left_cancel (by norm_num) heq)

theorem threeFreeValue_injective (k : ℕ) :
    Function.Injective (threeFreeValue k) := by
  intro a b hab
  have hmul :
      (3 * a.val : ZMod (3 ^ k)) = (3 * b.val : ZMod (3 ^ k)) := by
    have h := congrArg (fun z : ZMod (3 ^ k) ↦ z - 1) hab
    simpa [threeFreeValue] using h
  have hcast :
      ((3 * a.val : ℕ) : ZMod (3 ^ k)) =
        ((3 * b.val : ℕ) : ZMod (3 ^ k)) := by
    simpa [Nat.cast_mul] using hmul
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have heq := hmod.eq_of_lt_of_lt
    (three_mul_threeFree_lt k a) (three_mul_threeFree_lt k b)
  exact Fin.ext (Nat.mul_left_cancel (by norm_num) heq)

theorem twoFreeValue_isUnit (k : ℕ) (a : Fin (twoFreeCard k)) :
    IsUnit (twoFreeValue k a) :=
  one_add_four_mul_isUnit k _

theorem threeFreeValue_isUnit (k : ℕ) (a : Fin (threeFreeCard k)) :
    IsUnit (threeFreeValue k a) :=
  one_add_three_mul_isUnit k _

theorem cubicResidue_twoFreeValue (k : ℕ) (a : Fin (twoFreeCard k)) :
    CookMagyarLocal.cubicResidue (twoFreeValue k a) =
      8 * twoAdicSingleParameter (a.val : ZMod (2 ^ k)) :=
  cubicResidue_one_add_four_mul k _

theorem cubicResidue_threeFreeValue (k : ℕ) (a : Fin (threeFreeCard k)) :
    CookMagyarLocal.cubicResidue (threeFreeValue k a) =
      3 * threeAdicParameter (a.val : ZMod (3 ^ k)) :=
  cubicResidue_one_add_three_mul k _

/-! ## Injective families of solutions -/

noncomputable def twoResidual {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) : ZMod (2 ^ k) :=
  3 * (u : ZMod (2 ^ k)) -
    ∑ i, twoAdicSingleParameter (a i).val

noncomputable def twoDependentValue {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) : ZMod (2 ^ k) :=
  1 + 4 * twoAdicSinglePreimage k (twoResidual k u a)

theorem twoDependentValue_isUnit {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) :
    IsUnit (twoDependentValue k u a) :=
  one_add_four_mul_isUnit k _

noncomputable def twoUnitTuple {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) :
    Fin (m + 1) → (ZMod (2 ^ k))ˣ :=
  Fin.cons (twoDependentValue_isUnit k u a).unit
    (fun i ↦ (twoFreeValue_isUnit k (a i)).unit)

@[simp] theorem coe_twoUnitTuple_zero {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) :
    (twoUnitTuple k u a 0 : ZMod (2 ^ k)) = twoDependentValue k u a := by
  simp [twoUnitTuple]

@[simp] theorem coe_twoUnitTuple_succ {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) (i : Fin m) :
    (twoUnitTuple k u a i.succ : ZMod (2 ^ k)) = twoFreeValue k (a i) := by
  simp [twoUnitTuple]

theorem twoUnitTuple_equation {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (twoFreeCard k)) :
    letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    unitCubicSum (twoUnitTuple k u a) =
      ((24 * u : ℕ) : ZMod (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [unitCubicSum, Fin.sum_univ_succ]
  change CookMagyarLocal.cubicResidue (twoDependentValue k u a) +
      ∑ i, CookMagyarLocal.cubicResidue (twoFreeValue k (a i)) = _
  rw [show CookMagyarLocal.cubicResidue (twoDependentValue k u a) =
      8 * twoAdicSingleParameter
        (twoAdicSinglePreimage k (twoResidual k u a)) by
    exact cubicResidue_one_add_four_mul k _]
  rw [twoAdicSingleParameter_preimage]
  simp_rw [cubicResidue_twoFreeValue]
  rw [← Finset.mul_sum]
  simp only [twoResidual]
  push_cast
  ring

theorem twoUnitTuple_injective {m : ℕ} (k u : ℕ) :
    Function.Injective (twoUnitTuple (m := m) k u) := by
  intro a b hab
  funext i
  apply twoFreeValue_injective k
  have hi := congrFun hab i.succ
  have hval := congrArg (fun z : (ZMod (2 ^ k))ˣ ↦ (z : ZMod (2 ^ k))) hi
  simpa using hval

noncomputable def threeResidual {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) : ZMod (3 ^ k) :=
  8 * (u : ZMod (3 ^ k)) - ∑ i, threeAdicParameter (a i).val

noncomputable def threeDependentValue {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) : ZMod (3 ^ k) :=
  1 + 3 * Classical.choose
    (threeAdicParameter_surjective k (threeResidual k u a))

@[simp] theorem threeAdicParameter_threeDependentPreimage {m : ℕ}
    (k u : ℕ) (a : Fin m → Fin (threeFreeCard k)) :
    threeAdicParameter
      (Classical.choose
        (threeAdicParameter_surjective k (threeResidual k u a))) =
      threeResidual k u a :=
  Classical.choose_spec
    (threeAdicParameter_surjective k (threeResidual k u a))

theorem threeDependentValue_isUnit {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) :
    IsUnit (threeDependentValue k u a) :=
  one_add_three_mul_isUnit k _

noncomputable def threeUnitTuple {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) :
    Fin (m + 1) → (ZMod (3 ^ k))ˣ :=
  Fin.cons (threeDependentValue_isUnit k u a).unit
    (fun i ↦ (threeFreeValue_isUnit k (a i)).unit)

@[simp] theorem coe_threeUnitTuple_zero {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) :
    (threeUnitTuple k u a 0 : ZMod (3 ^ k)) = threeDependentValue k u a := by
  simp [threeUnitTuple]

@[simp] theorem coe_threeUnitTuple_succ {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) (i : Fin m) :
    (threeUnitTuple k u a i.succ : ZMod (3 ^ k)) = threeFreeValue k (a i) := by
  simp [threeUnitTuple]

theorem threeUnitTuple_equation {m : ℕ} (k u : ℕ)
    (a : Fin m → Fin (threeFreeCard k)) :
    letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    unitCubicSum (threeUnitTuple k u a) =
      ((24 * u : ℕ) : ZMod (3 ^ k)) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rw [unitCubicSum, Fin.sum_univ_succ]
  change CookMagyarLocal.cubicResidue (threeDependentValue k u a) +
      ∑ i, CookMagyarLocal.cubicResidue (threeFreeValue k (a i)) = _
  rw [show CookMagyarLocal.cubicResidue (threeDependentValue k u a) =
      3 * threeAdicParameter
        (Classical.choose
          (threeAdicParameter_surjective k (threeResidual k u a))) by
    exact cubicResidue_one_add_three_mul k _]
  rw [threeAdicParameter_threeDependentPreimage]
  simp_rw [cubicResidue_threeFreeValue]
  rw [← Finset.mul_sum]
  simp only [threeResidual]
  push_cast
  ring

theorem threeUnitTuple_injective {m : ℕ} (k u : ℕ) :
    Function.Injective (threeUnitTuple (m := m) k u) := by
  intro a b hab
  funext i
  apply threeFreeValue_injective k
  have hi := congrFun hab i.succ
  have hval := congrArg (fun z : (ZMod (3 ^ k))ˣ ↦ (z : ZMod (3 ^ k))) hi
  simpa using hval

/-! ## Exact cardinal lower bounds -/

theorem twoFreeCard_pow_le_count (m k u : ℕ) :
    letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    twoFreeCard k ^ m ≤
      unitCubicSolutionCount (m + 1)
        ((24 * u : ℕ) : ZMod (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  classical
  let Solution :=
    {x : Fin (m + 1) → (ZMod (2 ^ k))ˣ //
      unitCubicSum x = ((24 * u : ℕ) : ZMod (2 ^ k))}
  let family : (Fin m → Fin (twoFreeCard k)) → Solution := fun a ↦
    ⟨twoUnitTuple k u a, twoUnitTuple_equation k u a⟩
  have hfamily : Function.Injective family := by
    intro a b hab
    apply twoUnitTuple_injective k u
    exact congrArg Subtype.val hab
  calc
    twoFreeCard k ^ m = Fintype.card (Fin m → Fin (twoFreeCard k)) := by
      simp
    _ ≤ Fintype.card Solution := Fintype.card_le_of_injective family hfamily
    _ = unitCubicSolutionCount (m + 1)
        ((24 * u : ℕ) : ZMod (2 ^ k)) := by
      simp [Solution, unitCubicSolutionCount, Fintype.card_subtype]

theorem threeFreeCard_pow_le_count (m k u : ℕ) :
    letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    threeFreeCard k ^ m ≤
      unitCubicSolutionCount (m + 1)
        ((24 * u : ℕ) : ZMod (3 ^ k)) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  classical
  let Solution :=
    {x : Fin (m + 1) → (ZMod (3 ^ k))ˣ //
      unitCubicSum x = ((24 * u : ℕ) : ZMod (3 ^ k))}
  let family : (Fin m → Fin (threeFreeCard k)) → Solution := fun a ↦
    ⟨threeUnitTuple k u a, threeUnitTuple_equation k u a⟩
  have hfamily : Function.Injective family := by
    intro a b hab
    apply threeUnitTuple_injective k u
    exact congrArg Subtype.val hab
  calc
    threeFreeCard k ^ m = Fintype.card (Fin m → Fin (threeFreeCard k)) := by
      simp
    _ ≤ Fintype.card Solution := Fintype.card_le_of_injective family hfamily
    _ = unitCubicSolutionCount (m + 1)
        ((24 * u : ℕ) : ZMod (3 ^ k)) := by
      simp [Solution, unitCubicSolutionCount, Fintype.card_subtype]

/-- Count lower bound for an arbitrary target satisfying the Cook--Magyar
congruence condition. -/
theorem twoFreeCard_pow_pred_le_count {n k T : ℕ} (hn : 1 ≤ n)
    (hT : 24 ∣ T) :
    letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    twoFreeCard k ^ (n - 1) ≤
      unitCubicSolutionCount n (T : ZMod (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rcases hT with ⟨u, rfl⟩
  obtain ⟨m, rfl : n = m + 1⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simpa using twoFreeCard_pow_le_count m k u

/-- Three-adic counterpart of `twoFreeCard_pow_pred_le_count`. -/
theorem threeFreeCard_pow_pred_le_count {n k T : ℕ} (hn : 1 ≤ n)
    (hT : 24 ∣ T) :
    letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    threeFreeCard k ^ (n - 1) ≤
      unitCubicSolutionCount n (T : ZMod (3 ^ k)) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  rcases hT with ⟨u, rfl⟩
  obtain ⟨m, rfl : n = m + 1⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  simpa using threeFreeCard_pow_le_count m k u

/-! ## Comparison with Euler's totient -/

theorem totient_two_pow_le_twice_twoFreeCard (k : ℕ) :
    Nat.totient (2 ^ k) ≤ 2 * twoFreeCard k := by
  rcases k with _ | k
  · norm_num [twoFreeCard]
  rcases k with _ | k
  · norm_num [twoFreeCard]
  · rw [Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp only [twoFreeCard, Nat.add_sub_cancel, Nat.reduceSubDiff]
    simp [pow_succ, mul_comm]

theorem totient_three_pow_le_twice_threeFreeCard (k : ℕ) :
    Nat.totient (3 ^ k) ≤ 2 * threeFreeCard k := by
  rcases k with _ | k
  · norm_num [threeFreeCard]
  · rw [Nat.totient_prime_pow (by norm_num) (by omega)]
    simp [threeFreeCard, mul_comm]

theorem totient_two_pow_pow_le (m k : ℕ) :
    Nat.totient (2 ^ k) ^ m ≤
      2 ^ m * twoFreeCard k ^ m := by
  calc
    Nat.totient (2 ^ k) ^ m ≤ (2 * twoFreeCard k) ^ m :=
      Nat.pow_le_pow_left (totient_two_pow_le_twice_twoFreeCard k) m
    _ = 2 ^ m * twoFreeCard k ^ m := by rw [mul_pow]

theorem totient_three_pow_pow_le (m k : ℕ) :
    Nat.totient (3 ^ k) ^ m ≤
      2 ^ m * threeFreeCard k ^ m := by
  calc
    Nat.totient (3 ^ k) ^ m ≤ (2 * threeFreeCard k) ^ m :=
      Nat.pow_le_pow_left (totient_three_pow_le_twice_threeFreeCard k) m
    _ = 2 ^ m * threeFreeCard k ^ m := by rw [mul_pow]

/-- Integer form of the quantitative two-adic count. -/
theorem totient_two_pow_pred_le_two_pow_mul_count
    {n k T : ℕ} (hn : 1 ≤ n) (hT : 24 ∣ T) :
    letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    Nat.totient (2 ^ k) ^ (n - 1) ≤
      2 ^ (n - 1) *
        unitCubicSolutionCount n (T : ZMod (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact (totient_two_pow_pow_le (n - 1) k).trans
    (Nat.mul_le_mul_left _ (twoFreeCard_pow_pred_le_count hn hT))

/-- Integer form of the quantitative three-adic count. -/
theorem totient_three_pow_pred_le_two_pow_mul_count
    {n k T : ℕ} (hn : 1 ≤ n) (hT : 24 ∣ T) :
    letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    Nat.totient (3 ^ k) ^ (n - 1) ≤
      2 ^ (n - 1) *
        unitCubicSolutionCount n (T : ZMod (3 ^ k)) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact (totient_three_pow_pow_le (n - 1) k).trans
    (Nat.mul_le_mul_left _ (threeFreeCard_pow_pred_le_count hn hT))

/-! ## Positive exponent-independent normalized bounds -/

theorem normalized_two_power_lower_bound
    {n k T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) :
    letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    1 / (2 : ℝ) ^ (n - 1) ≤
      normalizedUnitCubicCount n (T : ZMod (2 ^ k)) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨m, rfl : n = m + 1⟩ :=
    Nat.exists_eq_succ_of_ne_zero (n := n) (by omega)
  have hcount := totient_two_pow_pred_le_two_pow_mul_count
    (n := m + 1) (k := k) (T := T) (by omega) hT
  have hnat :
      Nat.totient (2 ^ k) ^ (m + 1) ≤
        2 ^ m *
          ((2 ^ k) * unitCubicSolutionCount (m + 1)
            (T : ZMod (2 ^ k))) := by
    rw [pow_succ]
    calc
      Nat.totient (2 ^ k) ^ m * Nat.totient (2 ^ k) ≤
          (2 ^ m * unitCubicSolutionCount (m + 1)
            (T : ZMod (2 ^ k))) * (2 ^ k) :=
        Nat.mul_le_mul hcount (Nat.totient_le _)
      _ = 2 ^ m *
          ((2 ^ k) * unitCubicSolutionCount (m + 1)
            (T : ZMod (2 ^ k))) := by ring
  have hreal :
      (Nat.totient (2 ^ k) : ℝ) ^ (m + 1) ≤
        (2 : ℝ) ^ m *
          (((2 ^ k : ℕ) : ℝ) *
            (unitCubicSolutionCount (m + 1)
              (T : ZMod (2 ^ k)) : ℝ)) := by
    exact_mod_cast hnat
  have htwo : 0 < (2 : ℝ) ^ m := by positivity
  have hphi : 0 < (Nat.totient (2 ^ k) : ℝ) := by
    have hq : 0 < (2 ^ k : ℕ) := pow_pos (by norm_num) _
    exact_mod_cast (Nat.totient_pos.mpr hq)
  unfold normalizedUnitCubicCount
  apply (div_le_div_iff₀ htwo (pow_pos hphi _)).2
  simpa [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using hreal

theorem normalized_three_power_lower_bound
    {n k T : ℕ} (hn : 33 ≤ n) (hT : 24 ∣ T) :
    letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
    1 / (2 : ℝ) ^ (n - 1) ≤
      normalizedUnitCubicCount n (T : ZMod (3 ^ k)) := by
  letI : NeZero (3 ^ k) := ⟨pow_ne_zero _ (by norm_num)⟩
  obtain ⟨m, rfl : n = m + 1⟩ :=
    Nat.exists_eq_succ_of_ne_zero (n := n) (by omega)
  have hcount := totient_three_pow_pred_le_two_pow_mul_count
    (n := m + 1) (k := k) (T := T) (by omega) hT
  have hnat :
      Nat.totient (3 ^ k) ^ (m + 1) ≤
        2 ^ m *
          ((3 ^ k) * unitCubicSolutionCount (m + 1)
            (T : ZMod (3 ^ k))) := by
    rw [pow_succ]
    calc
      Nat.totient (3 ^ k) ^ m * Nat.totient (3 ^ k) ≤
          (2 ^ m * unitCubicSolutionCount (m + 1)
            (T : ZMod (3 ^ k))) * (3 ^ k) :=
        Nat.mul_le_mul hcount (Nat.totient_le _)
      _ = 2 ^ m *
          ((3 ^ k) * unitCubicSolutionCount (m + 1)
            (T : ZMod (3 ^ k))) := by ring
  have hreal :
      (Nat.totient (3 ^ k) : ℝ) ^ (m + 1) ≤
        (2 : ℝ) ^ m *
          (((3 ^ k : ℕ) : ℝ) *
            (unitCubicSolutionCount (m + 1)
              (T : ZMod (3 ^ k)) : ℝ)) := by
    exact_mod_cast hnat
  have htwo : 0 < (2 : ℝ) ^ m := by positivity
  have hphi : 0 < (Nat.totient (3 ^ k) : ℝ) := by
    have hq : 0 < (3 ^ k : ℕ) := pow_pos (by norm_num) _
    exact_mod_cast (Nat.totient_pos.mpr hq)
  unfold normalizedUnitCubicCount
  apply (div_le_div_iff₀ htwo (pow_pos hphi _)).2
  simpa [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using hreal

end CookMagyarSmallPrimeCounts
end SystolicGrowth
